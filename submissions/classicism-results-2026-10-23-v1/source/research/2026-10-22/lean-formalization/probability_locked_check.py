#!/usr/bin/env python3
"""Bound this lane's invocation of the shared locked checker.

Never invokes Lean or Lake directly, touches the global lock, or signals any
process outside the new process group created for this invocation. The human
stop deadline is enforced even if this chat is interrupted.

Run with permission to signal this invocation's own process group. A restricted
sandbox may reject killpg even for this child group; record that failure rather
than claiming that a stop was enforced.
"""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

BASE = Path(__file__).resolve().parent
STOP = datetime.fromisoformat("2026-10-23T05:55:00+00:00")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--lock-wait", type=int, default=300)
    parser.add_argument("--wall-seconds", type=int, default=600)
    parser.add_argument("--keep-going", action="store_true")
    args = parser.parse_args()
    budget = min(args.wall_seconds, int((STOP - datetime.now(timezone.utc)).total_seconds()) - 5)
    if budget <= 0:
        print("No check started: wall budget or human stop deadline reached.")
        return 124
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    folder = BASE / "logs" / "probability-owner"
    folder.mkdir(parents=True, exist_ok=True)
    output = folder / (stamp + ".out")
    metadata = folder / (stamp + ".json")
    command = [sys.executable, str(BASE / "check_module.py"), *args.modules,
               "--timeout", str(args.timeout), "--lock-wait", str(args.lock_wait)]
    if args.keep_going:
        command.append("--keep-going")
    record = dict(modules=args.modules, stop_at=STOP.isoformat(), wall_budget_seconds=budget,
                  command=command, output=str(output), state="starting")
    child = None

    def save():
        metadata.write_text(json.dumps(record, indent=2) + "\n")

    def stop_own_group():
        if child is None:
            return
        try:
            os.killpg(child.pid, signal.SIGTERM)
        except ProcessLookupError:
            child.wait()
            return
        # The runner may exit before its compiler child. Bound the whole
        # dedicated group, not merely the runner PID, without touching others.
        until = time.monotonic() + 2
        while time.monotonic() < until:
            try:
                os.killpg(child.pid, 0)
            except ProcessLookupError:
                child.wait()
                return
            time.sleep(0.05)
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        child.wait()

    def interrupted(_signum, _frame):
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupted)
    started = time.monotonic()
    code = 1
    save()
    try:
        with output.open("w") as stream:
            child = subprocess.Popen(command, stdout=stream, stderr=subprocess.STDOUT,
                                     start_new_session=True)
            record.update(pid=child.pid, process_group=child.pid, state="running")
            save()
            try:
                code = child.wait(timeout=budget)
                record["state"] = "completed"
            except subprocess.TimeoutExpired:
                stop_own_group()
                code = 124
                record["state"] = "own_wall_budget_expired"
    except KeyboardInterrupt:
        stop_own_group()
        code = 130
        record["state"] = "interrupted"
    except PermissionError as error:
        code = 125
        record.update(state="stop_permission_failure", stop_error=str(error),
                      stop_confirmed=False)
    finally:
        try:
            stop_own_group()
        except PermissionError as error:
            code = 125
            record.update(state="stop_permission_failure", stop_error=str(error),
                          stop_confirmed=False)
            save()
    record.update(exit_code=code, seconds=round(time.monotonic() - started, 2))
    save()
    print(json.dumps({"exit_code": code, "output": str(output), "metadata": str(metadata)}))
    return code


if __name__ == "__main__":
    sys.exit(main())
