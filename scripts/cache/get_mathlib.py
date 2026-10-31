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
ROOT = Path(__file__).resolve().parents[2]


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
                if process.wait(timeout=ATTEMPT_SECONDS) == 0:
                    return True
                reason = f"exit status {process.returncode}"
            finally:
                if process.poll() is None:
                    if os.name == "posix":
                        try:
                            os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                    else:
                        process.kill()
                    process.wait()
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
