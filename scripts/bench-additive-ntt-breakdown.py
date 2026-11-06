#!/usr/bin/env python3
"""Measure counter-marked bit-plane substeps; build binaries before invoking."""

import argparse
from datetime import datetime, timezone
import fcntl
import hashlib
import json
from pathlib import Path
import runpy
import statistics

ROOT = Path(__file__).resolve().parents[1]
SAMPLER = runpy.run_path(str(ROOT / "scripts/bench-additive-ntt.py"))["sample"]
STAGES = [("loop", 1000000), ("matrix", 100000), ("transpose", 100000),
          ("prepare", 100000), ("apply", 100000), ("xor", 100000),
          ("kernel", 100000), ("move", 100000), ("stage-0", 10),
          ("stage-8", 10), ("stage-15", 10), ("identity-0", 10),
          ("identity-8", 10), ("identity-15", 10)]
BYTE = [("prepare", 100000), ("apply", 100000), ("combined", 100000)]


def emit(**row):
    print(json.dumps(row), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("suite", choices=["stages", "byte"])
    parser.add_argument("binary", type=Path)
    args = parser.parse_args()
    binary = args.binary.resolve(strict=True)
    emit(kind="metadata", recorded_at=datetime.now(timezone.utc).isoformat(),
         suite=args.suite, binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
         cpu=5, threads=1, cache="setup before marker; dependent chains; no warmup")
    with open("/tmp/compstark-bench.lock", "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        for part, count in STAGES if args.suite == "stages" else BYTE:
            samples = []
            for round_index in range(3):
                row = SAMPLER(binary, (part, count))
                samples.append(row)
                emit(kind="sample", part=part, count=count, round=round_index, **row)
            if len({row["sink"] for row in samples}) != 1:
                raise RuntimeError(f"unstable sink: {part}")
            emit(kind="median", part=part, count=count,
                 instructions_per_iteration=statistics.median(
                     row["instructions"] / count for row in samples),
                 ns_per_iteration=statistics.median(row["ns"] / count for row in samples))


if __name__ == "__main__":
    main()
