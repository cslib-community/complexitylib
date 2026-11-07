#!/usr/bin/env python3
"""Retry optional Mathlib downloads in place; ordinary `get` keeps completed archives."""

import argparse
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

ATTEMPTS = 3
ATTEMPT_SECONDS = 180
RETRY_SECONDS = 2
SHUTDOWN_SECONDS = 5
ROOT = Path(__file__).resolve().parents[2]


def stop_attempt(process):
    """Stop only our session's group, including children outliving the Lake parent.

    A reaped parent is not evidence that its children finished. Probe the group
    until it disappears; if that cannot be established, do not start a retry.
    Zombies can conservatively exhaust this bound too. Never remove Git locks.
    """
    def signal_attempt(force):
        try:
            if os.name == "posix":
                os.killpg(process.pid, signal.SIGKILL if force else signal.SIGTERM)
            elif process.poll() is None:
                process.kill() if force else process.terminate()
        except ProcessLookupError:
            pass

    def finished():
        process.poll()  # Reap the direct child before probing its group.
        if os.name != "posix":
            return process.returncode is not None
        try:
            os.killpg(process.pid, 0)
        except ProcessLookupError:
            return True
        return False

    if finished():
        return True
    for force in (False, True):
        signal_attempt(force)
        deadline = time.monotonic() + SHUTDOWN_SECONDS
        while True:
            if finished():
                return True
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                break
            time.sleep(min(.05, remaining))
    return False


def restore(root, env, lean_action=False):
    env = dict(env)
    if lean_action:
        # Preserve lean-action fe408643's unset/empty/explicit URL handling.
        if "MATHLIB_CACHE_GET_URL" not in env:
            env["MATHLIB_CACHE_GET_URL"] = "https://cache.mathlib.org/mathlib4"
        elif not env["MATHLIB_CACHE_GET_URL"]:
            del env["MATHLIB_CACHE_GET_URL"]
    for attempt in range(1, ATTEMPTS + 1):
        print(f"Mathlib cache attempt {attempt}/{ATTEMPTS}", flush=True)
        try:
            process = subprocess.Popen(["lake", "exe", "cache", "get"], cwd=root, env=env,
                                       start_new_session=(os.name == "posix"))
            try:
                status = process.wait(timeout=ATTEMPT_SECONDS)
                reason = f"exit status {status}"
            except (OSError, subprocess.TimeoutExpired) as error:
                status = None
                reason = str(error)
            finally:
                # Also drain descendants when Lake exits before them, regardless of status.
                try:
                    stopped = stop_attempt(process)
                except OSError as error:
                    print(f"warning: could not establish Mathlib cache shutdown: {error}",
                          file=sys.stderr, flush=True)
                    stopped = False
            if not stopped:
                print("warning: Mathlib cache process group did not disappear; "
                      "skipping remaining attempts", file=sys.stderr, flush=True)
                break
            if status == 0:
                return True
        except (OSError, subprocess.TimeoutExpired) as error:
            reason = str(error)
        print(f"warning: Mathlib cache attempt failed: {reason}", file=sys.stderr, flush=True)
        if attempt < ATTEMPTS:
            time.sleep(RETRY_SECONDS)
    print("warning: Mathlib cache download failed; lake build will compile missing outputs",
          file=sys.stderr)
    return False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-action", action="store_true",
                        help="retain lean-action's cache URL defaults")
    args = parser.parse_args()
    root = Path(os.environ.get("COMPLEXITYLIB_CACHE_CHECKOUT") or ROOT)
    restore(root, os.environ, args.lean_action)
    return 0  # Cache availability never substitutes for the subsequent strict build.


if __name__ == "__main__":
    raise SystemExit(main())
