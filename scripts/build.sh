#!/usr/bin/env bash
# Restore optional caches, then forward all arguments and the exit status to `lake build`.
# Usage: scripts/build.sh [Lake build arguments]
set -u
cd "$(dirname "$0")/.." || exit 1
scripts/cache/ensure.sh || exit $?
exec lake build "$@"
