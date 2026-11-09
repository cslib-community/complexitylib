#!/usr/bin/env bash
# Restore only outputs absent from .lake, trying configured native Lake mirrors in order.
# Every origin has an overall deadline; failures leave completed outputs for the next mirror
# and the ordinary source build. See scripts/cache/README.md.
set -u
script_dir="$(cd "$(dirname "$0")" && pwd)" || exit 1
cd "$script_dir/../.." || exit 1
exec python3 -B "$script_dir/restore.py" --missing --checkout "$PWD"
