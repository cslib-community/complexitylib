#!/usr/bin/env bash
# Check the manuals and run the Lean validation sequence of AGENTS.md; report each gate.
# Usage: scripts/check.sh [--quick [--base REF]] (from the repository root or any worktree)
set -u
cd "$(dirname "$0")/.." || exit 1
quick=0
if (($#)); then
  if [ "$1" = "--quick" ]; then
    shift
    quick=1
  else
    echo "Usage: scripts/check.sh [--quick [--base REF]]" >&2
    exit 2
  fi
fi
log_dir=$(mktemp -d "${TMPDIR:-/tmp}/complexitylib-check.XXXXXX") || exit 1
status=0
gate=0
run() {
  local name=$1
  shift
  gate=$((gate + 1))
  local log="$log_dir/$gate.log"
  if "$@" >"$log" 2>&1; then
    printf 'ok    %s\n' "$name"
  else
    printf 'FAIL  %s\n' "$name"
    cat "$log"
    status=1
  fi
}
finish() {
  if ((status)); then
    printf 'Full logs: %s\n' "$log_dir"
  else
    rm "$log_dir"/*.log
    rmdir "$log_dir"
  fi
}
# Run on both the full and quick routes. Lean-only edits can invalidate a manual excerpt,
# and these stdlib checks can report drift before a cold checkout restores any build cache.
run "operator manual links and excerpts" python3 -B scripts/check_operator_manual.py
run "operator manual tooling tests" python3 -B scripts/test_operator_manual.py
if ((status)); then
  finish
  exit "$status"
fi
# A quick check may restart this script for all six gates. Restore only once in that process
# chain, even if planning takes longer than the bootstrap's ordinary retry window.
if [ "${COMPLEXITYLIB_CACHE_CHECK_STARTED-}" != "1" ]; then
  scripts/cache/ensure.sh || { cache_status=$?; finish; exit "$cache_status"; }
  export COMPLEXITYLIB_CACHE_CHECK_STARTED=1
fi
if ((quick)); then
  finish
  exec python3 -B scripts/quick_check.py "$@"
fi
# `lint-style` lints the modules that the modules it is given import directly, by default those of
# the root aggregators, which import directory shards rather than every module (scripts/mk_all.py).
lint_style() {
  local modules
  modules=$(python3 -B scripts/mk_all.py --aggregates) || return
  # One module name per line: word splitting is intended.
  # shellcheck disable=SC2086
  lake exe lint-style $modules
}
run "build --wfail --iofail" lake build --wfail --iofail
run "mk_all --check" python3 -B scripts/mk_all.py --check
run "test --wfail --iofail" lake test --wfail --iofail
run "lint" lake lint
run "lint-style" lint_style
run "checkInitImports" lake exe checkInitImports
finish
exit $status
