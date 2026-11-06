#!/usr/bin/env python3
"""Measure marked BF64 phases with instructions:u, cycles:u and wall time.

Build CompPolyBF64Bench first. Fixed workloads run three alternating rounds on
CPU 5; counters exclude module initialization and reject multiplexed samples.
"""

import ctypes
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import statistics
import struct
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BENCH = ROOT / ".lake/build/bin/CompPolyBF64Bench"
LIBC = ctypes.CDLL(None, use_errno=True)
WORKLOADS = [("spec", 10000), ("scalar", 1000000), ("throughput", 1000000),
             ("nibble", 1000000), ("byte", 1000000), ("ext3", 1000000), ("masked", 1000000),
             ("masked-throughput", 1000000), ("square", 1000000),
             ("inverse", 10000), ("frobenius", 100000), ("ext-square", 100000),
             ("ext-frobenius", 1000), ("mixed", 100000), ("dot64", 64000),
             ("bitslice", 64000), ("nibble-build", 1000), ("byte-build", 1000),
             ("masked-square", 1000000), ("masked-inverse", 10000),
             ("masked-frobenius", 100000), ("dot64-reduced", 64000), ("ext-qfrobenius", 1000000)]


def counter(pid, event):
    attr = ctypes.create_string_buffer(128)
    struct.pack_into("IIQ", attr, 0, 0, 128, event)
    struct.pack_into("QQ", attr, 32, 3, (1 << 1) | (1 << 5) | (1 << 6))
    fd = LIBC.syscall(298, attr, pid, -1, -1, 8)
    if fd < 0:
        raise OSError(ctypes.get_errno(), "perf_event_open")
    return fd


def read_counter(fd):
    return struct.unpack("QQQ", os.read(fd, 24))


def pin():
    os.sched_setaffinity(0, {5})


def sample(op, n):
    load_before = os.getloadavg()
    go_r, go_w = os.pipe()
    input_r, input_w = os.pipe()
    output_r, output_w = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(go_w)
        os.read(go_r, 1)
        os.dup2(input_r, 0)
        os.dup2(output_w, 1)
        pin()
        os.execve(BENCH, [str(BENCH), op, str(n)], dict(os.environ, LEAN_NUM_THREADS="1"))
    os.close(go_r)
    os.close(input_r)
    os.close(output_w)
    fds = []
    try:
        for event in (1, 0):
            fds.append(counter(pid, event))
        os.write(go_w, b"x")
        with os.fdopen(output_r) as output, os.fdopen(input_w, "w") as ack:
            if output.readline().strip() != "begin":
                raise RuntimeError("missing begin marker")
            before = [read_counter(fd) for fd in fds]
            ack.write("go\n")
            ack.flush()
            line = output.readline().split()
            after = [read_counter(fd) for fd in fds]
            ack.write("done\n")
            ack.flush()
        _, status = os.waitpid(pid, 0)
        if status or len(line) != 3 or line[0] != "end":
            raise RuntimeError(f"invalid end marker {line}")
    except BaseException:
        os.kill(pid, 9)
        os.waitpid(pid, 0)
        raise
    finally:
        os.close(go_w)
        for fd in fds:
            os.close(fd)
    values = []
    for a, b in zip(after, before):
        delta = [x - y for x, y in zip(a, b)]
        if delta[1] != delta[2]:
            raise RuntimeError("multiplexed hardware counter; rerun without other perf sessions")
        if delta[0] == 0:
            raise RuntimeError("empty hardware counter")
        values.append(delta[0] / n)
    return dict(operation=op, count=n, ns_per_op=int(line[1]) / n,
                instructions_per_op=values[0], cycles_per_op=values[1], sink=line[2],
                load_before=load_before, load_after=os.getloadavg())


def main():
    metadata = dict(kind="metadata", recorded_at=datetime.now(timezone.utc).isoformat(),
                    binary_sha256=hashlib.sha256(BENCH.read_bytes()).hexdigest(),
                    base_commit=subprocess.check_output(
                        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                    toolchain=(ROOT / "lean-toolchain").read_text().strip(),
                    cpu=5, rounds=3, platform=os.uname().machine)
    print(json.dumps(metadata), flush=True)
    samples = []
    for round_index in range(3):
        workloads = WORKLOADS if round_index % 2 == 0 else list(reversed(WORKLOADS))
        for op, n in workloads:
            row = sample(op, n)
            samples.append(row)
            print(json.dumps(row), flush=True)
    for operations in (("scalar", "masked", "nibble", "byte"),
                       ("throughput", "masked-throughput"), ("square", "masked-square"),
                       ("inverse", "masked-inverse"), ("frobenius", "masked-frobenius"),
                       ("dot64", "dot64-reduced")):
        sinks = {s["sink"] for s in samples if s["operation"] in operations}
        if len(sinks) != 1:
            raise RuntimeError(f"cross-implementation sink mismatch for {operations}")
    for op, _ in WORKLOADS:
        rows = [s for s in samples if s["operation"] == op]
        if len({s["sink"] for s in rows}) != 1:
            raise RuntimeError(f"unstable sink for {op}")
        print(json.dumps(dict(operation=op, median={
            k: statistics.median(s[k] for s in rows)
            for k in ("ns_per_op", "instructions_per_op", "cycles_per_op")})), flush=True)


if __name__ == "__main__":
    main()
