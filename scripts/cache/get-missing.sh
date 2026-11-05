#!/usr/bin/env bash
# Restore only Complexitylib input hashes absent from root .lake build traces. Local and CI
# clients share revision discovery, ordered mirrors and bounded optional failure handling.
set -u
script_dir="$(cd "$(dirname "$0")" && pwd)" || exit 1
exec python3 "$script_dir/restore.py" --missing-only "$@"
