#!/usr/bin/env python3
"""Measure one production GS row three times on CPU 5, excluding fixture setup.

Usage: bench-gs.py BINARY initial|middle|final decode|tree|gao-tree dense|affine
Build first. The marked decode interval includes coefficient conversion and distance
filtering. Each interval is capped at 180 seconds; a timeout reports lower bounds.
"""

from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import threading
import time

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("bf64_counters", ROOT / "scripts/bench-bf64.py")
COUNTERS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(COUNTERS)


def sample(binary, level, mode, fixture):
    gate_r, gate_w = os.pipe()
    input_r, input_w = os.pipe()
    output_r, output_w = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(gate_w)
        os.read(gate_r, 1)
        os.dup2(input_r, 0)
        os.dup2(output_w, 1)
        COUNTERS.pin()
        os.execve(binary, [binary, level, mode, fixture],
                  dict(os.environ, LEAN_NUM_THREADS="1", COMP_POLY_COUNTERS="1"))
    os.close(gate_r)
    os.close(input_r)
    os.close(output_w)
    fds = []
    timer = None
    started = None
    lines = []
    reaped = False
    try:
        # Install inherited events before exec: Lean executes IO on a worker thread.
        for event in (1, 0):
            fds.append(COUNTERS.counter(pid, event))
        os.write(gate_w, b"x")
        with os.fdopen(output_r) as output, os.fdopen(input_w, "w") as ack:
            for line in output:
                line = line.strip()
                lines.append(line)
                if line == "begin":
                    before = [COUNTERS.read_counter(fd) for fd in fds]
                    started = time.monotonic()
                    timer = threading.Timer(180, os.kill, args=(pid, 9))
                    timer.start()
                    ack.write("go\n")
                    ack.flush()
                if line.startswith("end "):
                    after = [COUNTERS.read_counter(fd) for fd in fds]
                    elapsed_ns = int(line.split()[1])
                    timer.cancel()
                    ack.write("done\n")
                    ack.flush()
        _, status, usage = os.wait4(pid, 0)
        reaped = True
        returncode = os.waitstatus_to_exitcode(status)
        if started is None:
            raise RuntimeError(f"missing begin marker: {lines}")
        timed_out = returncode == -9 and started is not None
        if timed_out:
            after = [COUNTERS.read_counter(fd) for fd in fds]
            elapsed_ns = int((time.monotonic() - started) * 1e9)
        elif returncode:
            raise RuntimeError(f"decoder failed: {returncode}; {lines}")
        values = []
        for a, b in zip(after, before):
            delta = [x - y for x, y in zip(a, b)]
            if delta[1] != delta[2] or delta[0] == 0:
                raise RuntimeError(f"multiplexed or empty counter: {delta}")
            values.append(delta[0])
        return dict(level=level, mode=mode, fixture=fixture, timeout=timed_out,
                    seconds=elapsed_ns / 1e9, instructions=values[0], cycles=values[1],
                    peak_rss_kib=usage.ru_maxrss, phases=lines)
    finally:
        if timer:
            timer.cancel()
        if not reaped:
            os.kill(pid, 9)
            os.waitpid(pid, 0)
        os.close(gate_w)
        for fd in fds:
            os.close(fd)


def main():
    binary, level, mode, fixture = sys.argv[1:]
    path = Path(binary).resolve()
    print(json.dumps(dict(kind="metadata", recorded_at=datetime.now(timezone.utc).isoformat(),
                          binary_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                          base_commit=subprocess.check_output(
                              ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                          toolchain=(ROOT / "lean-toolchain").read_text().strip(),
                          cpu=5, rounds=3, timeout_seconds=180)), flush=True)
    for _ in range(3):
        row = sample(str(Path(binary).resolve()), level, mode, fixture)
        print(json.dumps(row), flush=True)
        if row["timeout"]:
            break


if __name__ == "__main__":
    main()
