#!/usr/bin/env python3
"""Retry optional Mathlib downloads in place; ordinary `get` keeps completed archives."""

import argparse
import os
from pathlib import Path
import sys
import time

from bounded import UnsafeShutdown, interruptible, note_unsafe, run

ATTEMPTS = 3
ATTEMPT_SECONDS = 180
RETRY_SECONDS = 2
SHUTDOWN_SECONDS = 5
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
            result = run(["lake", "exe", "cache", "get"], cwd=root, env=env,
                         timeout=ATTEMPT_SECONDS, grace=SHUTDOWN_SECONDS)
            if result.returncode == 0:
                return True
            reason = f"exit status {result.returncode}"
        except OSError as error:
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
    if os.environ.get("DISABLE_CACHE_RESTORE", "").lower() in ("true", "1"):
        return 0
    root = Path(os.environ.get("COMPLEXITYLIB_CACHE_CHECKOUT") or ROOT)
    try:
        with interruptible():
            restore(root, os.environ, args.lean_action)
    except UnsafeShutdown as error:
        try:
            note_unsafe(os.environ)
        except OSError:
            pass
        print(f"error: {error}", file=sys.stderr, flush=True)
        return 125
    except KeyboardInterrupt:
        return 124
    return 0  # Cache availability never substitutes for the subsequent strict build.


if __name__ == "__main__":
    raise SystemExit(main())
