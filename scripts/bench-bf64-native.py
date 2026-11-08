#!/usr/bin/env python3
"""Compare a frozen software binary, current Lean, and native leanVM field kernels.

The required argument is the frozen software CompPolyBF64Bench path.
The current Lean and pinned native Rust executables are built before measurement. Counts exclude setup and every matched sink must agree.
"""
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import statistics
import shutil
import tempfile
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
WORKLOADS = [("masked", 1000000), ("masked-throughput", 1000000), ("ext3", 1000000), ("mixed", 100000),
             ("masked-square", 1000000), ("masked-inverse", 10000),
             ("masked-frobenius", 100000), ("ext-square", 100000),
             ("ext-qfrobenius", 1000000), ("dot64", 64000), ("dot64-reduced", 64000)]


def build():
    subprocess.run(["systemd-run", "--user", "--scope", "-p", "MemoryMax=12G", "--",
                    "lake", "build", "CompPolyBF64Bench"], cwd=ROOT, check=True,
                   stdout=subprocess.DEVNULL)
    with tempfile.TemporaryDirectory(prefix="comppoly-bf64-") as scratch:
        source = Path(scratch) / "source"
        subprocess.run(["git", "clone", "--quiet", "https://github.com/leanEthereum/leanMultisig.git",
                        str(source)], check=True)
        subprocess.run(["git", "-C", str(source), "checkout", "--quiet", "--detach",
                        "9d8bce818aa7c7e18e67026e522a9b1539d0a57d"], check=True)
        harness = Path(scratch) / "harness"
        harness.mkdir()
        for name in ("main.rs", "Cargo.lock"):
            shutil.copyfile(ROOT / "bench/rust/bf64" / name, harness / name)
        template = (ROOT / "bench/rust/bf64/Cargo.toml.in").read_text()
        (harness / "Cargo.toml").write_text(template.replace("@SOURCE@", str(source)))
        subprocess.run(["cargo", "build", "--release", "--locked", "--manifest-path",
                        str(harness / "Cargo.toml"), "-j", "2"], check=True,
                       env=dict(os.environ, CARGO_TARGET_DIR=str(ROOT / ".lake/bf64-rust-target"),
                                RUSTFLAGS="-C target-cpu=native"))
        if subprocess.check_output(["git", "-C", str(source), "status", "--porcelain"]):
            raise RuntimeError("Rust source checkout was modified")


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: bench-bf64-native.py FROZEN_SOFTWARE_BINARY")
    spec = importlib.util.spec_from_file_location("bf64", ROOT / "scripts/bench-bf64.py")
    runner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(runner)
    build()
    binaries = {"software": Path(sys.argv[1]).resolve(),
                "lean": ROOT / ".lake/build/bin/CompPolyBF64Bench",
                "rust": ROOT / ".lake/bf64-rust-target/release/bf64-reference"}
    print(json.dumps(dict(kind="metadata", recorded_at=datetime.now(timezone.utc).isoformat(),
        commit=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        rust_revision="9d8bce818aa7c7e18e67026e522a9b1539d0a57d",
        rust_flags="-C target-cpu=native", cpu=5, rounds=3,
        toolchain=(ROOT / "lean-toolchain").read_text().strip(),
        binaries={k: hashlib.sha256(v.read_bytes()).hexdigest() for k, v in binaries.items()})),
        flush=True)
    rows = []
    with open("/tmp/compstark-bench.lock", "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        for repetition in range(3):
            for op, n in WORKLOADS:
                engines = list(binaries) if repetition % 2 == 0 else list(reversed(binaries))
                for engine in engines:
                    row = dict(engine=engine, repetition=repetition,
                               **runner.sample(binaries[engine], op, n))
                    print(json.dumps(row), flush=True)
                    rows.append(row)
    for op, _ in WORKLOADS:
        selected = [r for r in rows if r["operation"] == op]
        if len({r["sink"] for r in selected}) != 1:
            raise RuntimeError(f"cross-implementation mismatch: {op}")
        summary = {engine: {k: statistics.median(r[k] for r in selected if r["engine"] == engine)
                            for k in ("instructions_per_op", "cycles_per_op", "ns_per_op")}
                   for engine in binaries}
        print(json.dumps(dict(kind="summary", operation=op, measurements=summary)), flush=True)


if __name__ == "__main__":
    main()
