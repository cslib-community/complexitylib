#!/usr/bin/env bash
# Publish an already staged publication to GCS.
# Usage: scripts/cache/upload.sh <bucket> <publication-directory>
set -euo pipefail
if [ "$#" -ne 2 ]; then
  printf 'Usage: %s <bucket> <publication-directory>\n' "$0" >&2
  exit 2
fi
exec python3 "$(dirname "$0")/publish.py" gcs "$@"
