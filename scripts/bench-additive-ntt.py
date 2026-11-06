#!/usr/bin/env python3
"""Build, check and measure packed encoders against pinned, unmodified Rust.

Runs single-threaded on CPU 5 under the shared benchmark lock. Hardware counts
exclude plan/message setup and output consumption. Results are JSON lines.
"""

import argparse
import ctypes
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import statistics
import struct
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REVISION = "9d8bce818aa7c7e18e67026e522a9b1539d0a57d"
LEAN = ROOT / ".lake/build/bin/CompPolyBitsliceNTTBench"
RUST = ROOT / ".lake/additive-rust-target/release/additive-ntt-reference"
LIBC = ctypes.CDLL(None, use_errno=True)
PRODUCTION = [("k", 22, 56, 1), ("e", 21, 16, 4), ("e", 20, 16, 7),
              ("e", 19, 16, 10), ("e", 18, 16, 13)]


def emit(**row):
    print(json.dumps(row), flush=True)


def build():
    subprocess.run(["systemd-run", "--user", "--scope", "-p", "MemoryMax=12G", "--",
                    "lake", "build", "CompPolyBitsliceNTTBench"], cwd=ROOT, check=True,
                   stdout=subprocess.DEVNULL)
    with tempfile.TemporaryDirectory(prefix="comppoly-additive-", suffix="-src") as tmp:
        source = Path(tmp) / "source"
        subprocess.run(["git", "clone", "--quiet", "https://github.com/leanEthereum/leanMultisig.git",
                        str(source)], check=True)
        subprocess.run(["git", "-C", str(source), "checkout", "--quiet", "--detach", REVISION], check=True)
        harness = Path(tmp) / "harness"
        harness.mkdir()
        for name in ("main.rs", "Cargo.lock"):
            shutil.copyfile(ROOT / "bench/rust/additive-ntt" / name, harness / name)
        template = (ROOT / "bench/rust/additive-ntt/Cargo.toml.in").read_text()
        (harness / "Cargo.toml").write_text(template.replace("@SOURCE@", str(source)))
        subprocess.run(["cargo", "build", "--release", "--locked", "--manifest-path",
                        str(harness / "Cargo.toml"), "-j", "4"], check=True,
                       env=dict(os.environ, CARGO_TARGET_DIR=str(ROOT / ".lake/additive-rust-target"),
                                RUSTFLAGS="-C target-cpu=native"))
        if subprocess.check_output(["git", "-C", str(source), "status", "--porcelain"]):
            raise RuntimeError("Rust source checkout was modified")


def counter(pid, event):
    attr = ctypes.create_string_buffer(128)
    struct.pack_into("IIQ", attr, 0, 0, 128, event)
    struct.pack_into("QQ", attr, 32, 3, (1 << 1) | (1 << 5) | (1 << 6))
    fd = LIBC.syscall(298, attr, pid, -1, -1, 8)
    if fd < 0:
        raise OSError(ctypes.get_errno(), "perf_event_open")
    return fd


def counts(fd):
    return struct.unpack("QQQ", os.read(fd, 24))


def rss(pid):
    return int(next(line.split()[1] for line in Path(f"/proc/{pid}/status").read_text().splitlines()
                    if line.startswith("VmRSS:")))


def sample(binary, shape):
    load_before = os.getloadavg()
    release_r, release_w = os.pipe()
    input_r, input_w = os.pipe()
    output_r, output_w = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(release_w)
        os.read(release_r, 1)
        os.close(release_r)
        os.dup2(input_r, 0)
        os.dup2(output_w, 1)
        for fd in (input_r, input_w, output_r, output_w):
            os.close(fd)
        os.sched_setaffinity(0, {5})
        os.execve(binary, [str(binary), "bench", *map(str, shape)],
                  dict(os.environ, LEAN_NUM_THREADS="1", LEANVM_NUM_THREADS="1"))
    os.close(release_r)
    os.close(input_r)
    os.close(output_w)
    fds = []
    waited = False
    try:
        fds = [counter(pid, 1), counter(pid, 0)]
        os.write(release_w, b"x")
        with os.fdopen(output_r) as output, os.fdopen(input_w, "w") as ack:
            begin = output.readline().split()
            if len(begin) != 2 or begin[0] != "begin":
                raise RuntimeError(f"invalid begin marker {begin}")
            setup_rss = rss(pid)
            before = [counts(fd) for fd in fds]
            ack.write("go\n")
            ack.flush()
            end = output.readline().split()
            after = [counts(fd) for fd in fds]
            output_rss = rss(pid)
            ack.write("done\n")
            ack.flush()
            sink = output.readline().split()
        _, status, usage = os.wait4(pid, 0)
        waited = True
        if status or len(end) != 2 or end[0] != "end" or len(sink) != 2 or sink[0] != "sink":
            raise RuntimeError(f"benchmark failed: {status} {end} {sink}")
        values = []
        for a, b in zip(after, before):
            delta = [x - y for x, y in zip(a, b)]
            if delta[1] != delta[2] or delta[0] == 0:
                raise RuntimeError("multiplexed or empty hardware counter; rerun")
            values.append(delta[0])
        return dict(ns=int(end[1]), setup_ns=int(begin[1]), instructions=values[0],
                    cycles=values[1], sink=sink[1], setup_rss_kib=setup_rss,
                    output_rss_kib=output_rss, maxrss_kib=usage.ru_maxrss,
                    load_before=load_before, load_after=os.getloadavg())
    finally:
        if not waited:
            os.kill(pid, 9)
            os.waitpid(pid, 0)
        os.close(release_w)
        for fd in fds:
            os.close(fd)


def check(shape, exact):
    with tempfile.TemporaryDirectory(prefix="comppoly-additive-check-") as tmp:
        results = []
        paths = []
        for name, binary in (("lean", LEAN), ("rust", RUST)):
            path = Path(tmp) / f"{name}.bin"
            command = ["taskset", "-c", "5", str(binary), "dump" if exact else "check",
                       *map(str, shape)] + ([str(path)] if exact else [])
            results.append(subprocess.check_output(command, text=True,
                           env=dict(os.environ, LEAN_NUM_THREADS="1", LEANVM_NUM_THREADS="1")))
            paths.append(path)
        if results[0] != results[1]:
            raise RuntimeError(f"stage mismatch {shape}:\nLean: {results[0]}\nRust: {results[1]}")
        if exact:
            a, b = (p.read_bytes() for p in paths)
            if a != b:
                first = next(i for i, (x, y) in enumerate(zip(a, b)) if x != y)
                raise RuntimeError(f"output byte mismatch {shape} at {first}")
        emit(kind="conformance", shape=shape, exact_bytes=exact,
             checkpoints=[line.split() for line in results[0].splitlines()])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["build", "check", "bench"])
    args = parser.parse_args()
    if args.action == "build":
        build()
        return
    metadata = dict(kind="metadata", recorded_at=datetime.now(timezone.utc).isoformat(),
                    revision=REVISION, base_commit=subprocess.check_output(
                        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                    binary_sha256={name: hashlib.sha256(path.read_bytes()).hexdigest()
                                   for name, path in (("lean", LEAN), ("rust", RUST))},
                    lean_toolchain=(ROOT / "lean-toolchain").read_text().strip(),
                    rustc=subprocess.check_output(["rustc", "--version"], text=True).strip(),
                    cpu=5, threads=1, cache="plans prepared per process; no warmup",
                    cpu_model=next(line.split(":", 1)[1].strip() for line in
                                   Path("/proc/cpuinfo").read_text().splitlines()
                                   if line.startswith("model name")))
    emit(**metadata)
    with open("/tmp/compstark-bench.lock", "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if args.action == "check":
            for shape in [("k", 1, 1, 1), ("e", 4, 2, 4), ("k", 5, 5, 1),
                          ("k", 7, 9, 2), ("e", 5, 2, 1), ("e", 7, 3, 2)]:
                check(shape, True)
            for d in range(13, 23):
                for layout in ("k", "e"):
                    check((layout, d, 1, 1), False)
            for shape in PRODUCTION:
                check(shape, False)
            return
        for shape in PRODUCTION:
            samples = {"lean": [], "rust": []}
            for round_index in range(3):
                order = [("lean", LEAN), ("rust", RUST)]
                if round_index % 2:
                    order.reverse()
                for name, binary in order:
                    row = sample(binary, shape)
                    samples[name].append(row)
                    emit(kind="sample", implementation=name, shape=shape, round=round_index, **row)
            if len({r["sink"] for rs in samples.values() for r in rs}) != 1:
                raise RuntimeError(f"output sink mismatch {shape}")
            medians = {name: {key: statistics.median(r[key] for r in rows)
                              for key in ("ns", "setup_ns", "instructions", "cycles", "maxrss_kib")}
                       for name, rows in samples.items()}
            emit(kind="median", shape=shape, values=medians,
                 lean_rust={key: medians["lean"][key] / medians["rust"][key]
                            for key in ("ns", "instructions", "cycles")})


if __name__ == "__main__":
    main()
