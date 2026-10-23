#!/usr/bin/env python3
"""Bound this lane's shared-runner checks; never invoke Lean or Lake directly.

The fixed stop is the human-requested 23 October 2026 cutoff, with margin.
No retries, scheduling, dependency fetching, or shared-lock mutation occurs.
Only the process group started by this wrapper can be terminated by it.
"""

import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import signal
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--wall-seconds", type=int, default=600)
    args, check_args = parser.parse_known_args()
    if args.wall_seconds <= 0 or not check_args:
        parser.error("A positive wall bound and a checker target are required.")
    stop = datetime(2026, 10, 23, 5, 53, tzinfo=timezone.utc)
    remaining = (stop - datetime.now(timezone.utc)).total_seconds()
    bound = min(args.wall_seconds, remaining)
    if bound <= 0:
        print("STOP WINDOW: no compiler check started.", flush=True)
        return 124
    runner = Path(__file__).resolve().parents[1] / "check_with_mathlib.py"
    child = subprocess.Popen([sys.executable, str(runner), *check_args], start_new_session=True)

    def stop_own_group():
        if child.poll() is not None:
            return
        try:
            os.killpg(child.pid, signal.SIGTERM)
            child.wait(timeout=5)
        except ProcessLookupError:
            pass
        except subprocess.TimeoutExpired:
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            child.wait(timeout=5)

    def interrupted(signum, _frame):
        stop_own_group()
        raise SystemExit(128 + signum)

    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    try:
        return child.wait(timeout=bound)
    except subprocess.TimeoutExpired:
        print("WALL LIMIT: stopping only this wrapper's check process group.", flush=True)
        stop_own_group()
        return 124


if __name__ == "__main__":
    raise SystemExit(main())
