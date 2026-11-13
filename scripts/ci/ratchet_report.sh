#!/usr/bin/env bash
# Report a readability count ratchet outside pull requests; on a main push, check every module.
#
# Usage: scripts/ci/ratchet_report.sh scripts/check_<name>.py
#
# Pull requests enforce each ratchet on the modules they change. Merge groups only report, so that
# queued pull requests written before an entry was lowered are not ejected. A main push
# (`MAIN_PUSH=true`) checks every module instead, so a module above its entry, which a stale
# pull-request run can let through, gets an error annotation on main's run. The step still
# succeeds, because cache publication needs the job to succeed.
set -uo pipefail

check=$1
if [[ "${MAIN_PUSH:-}" != true ]]; then
  exec python3 -B "$check" --report
fi
if python3 -B "$check" --all; then
  exit 0
fi
echo "::error title=Readability baseline exceeded on main::$check --all found modules above" \
  "their baseline entry. Remedy them, or record them with --update-baseline --allow-increase" \
  "(manual/workflows/troubleshooting.md, Diagnose a readability ratchet failure)."
exit 0
