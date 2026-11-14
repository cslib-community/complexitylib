#!/usr/bin/env python3
"""Run CI's locally reproducible source and Lean validation; `scripts/check.sh` calls this.

Usage: python3 scripts/full_check.py [--base REF]

`ci-checks` in `.github/workflows/lean_action_ci.yml` is the repository's only required status
check. It requires the parallel `source-checks` and `lean-checks` jobs to succeed. `STEPS` repeats
each step of those jobs that can run on a contributor's machine, preserving each job's order and
using CI's commands, so that a local full check fails where pull-request CI would. Steps that
compare a change with its base use the merge base of REF (default `origin/main`) with `HEAD`, and
the working tree, where pull-request CI uses the first parent of its merge commit. Every step runs
even after a failure, and each is reported as `ok` or `FAIL` with its log.

`PREFLIGHT` lists the steps that `scripts/check.sh` runs itself, before the cache bootstrap.
`CI_ONLY` lists the remaining steps with the reason each does not run here: advisory notices that
never fail the job, cache and runner plumbing (`scripts/cache/ensure.sh` restores caches locally),
and steps that need GitHub context, tokens or secrets. `scripts/test_full_check.py` fails when a
source or Lean step is in none of the three; when a mirrored or preflight step's `run` script has a
line that is neither one of its commands here nor the listed `BASE` plumbing; when such a step sets
something the local run does not reproduce (another working directory or environment, `shell`,
`continue-on-error`, a timeout); or when the mirrored steps are out of order within their CI job.
It separately tests the required aggregator's dependencies, publication output and failure
semantics.

`LOCAL_STEPS` run after the mirrored steps and have no CI counterpart. They check failures that
only a local machine can produce.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import os
from pathlib import Path
import shutil
import sys
import tempfile
from typing import TextIO

try:
    import check_vm_map_count
    from check_progress import run_logged
except ModuleNotFoundError:
    from scripts import check_vm_map_count
    from scripts.check_progress import run_logged

ROOT = Path(__file__).resolve().parent.parent


@dataclass(frozen=True)
class Step:
    """A source- or Lean-check step: its CI name and every line of its `run` script except
    `set -e` and the computation of CI's base commit, which `BASE` replaces (`PLUMBING` in
    `scripts/test_full_check.py`)."""
    name: str
    commands: tuple[str, ...]
    cwd: str | None = None  # the step's `working-directory`
    env: dict[str, str] = field(default_factory=dict)  # the step's literal `env` values
    progress: bool = False  # stream the local cache audit's progress, retaining its full log


STEPS = (
    # The source-check job has no Lean installation, so the suite's Lean-gated tests skip there;
    # here Lean is installed and they run. It includes the manual checker's tests that check.sh
    # runs first.
    Step("Test Python tooling", ("python3 -m unittest discover -s scripts -p 'test_*.py'",)),
    Step("Source hygiene", ("python3 -B scripts/check_hygiene.py --check-simp",)),
    Step("Encoding readability ratchet (changed modules)",
         ('python3 -B scripts/check_encoding_readability.py --base "$BASE"',)),
    Step("Projection chain ratchet (changed modules)",
         ('python3 -B scripts/check_projection_chains.py --base "$BASE"',)),
    Step("Documentation pins", ("python3 -B scripts/check_docs.py --config-only",)),
    Step("Test Lake build handoff reuse",
         ("python3 -B -m unittest test_cache_handoff.HandoffTests"
          ".test_real_lake_reuses_module_and_native_outputs_without_setup_inputs",),
         cwd="scripts", env={"COMPLEXITYLIB_TEST_LAKE_HANDOFF": "1"}),
    Step("Test real Lake cache publication staging",
         ("python3 -B -m unittest scripts.test_cache_publish.RealLakePublicationTests",)),
    Step("lake build",
         ("lake build --wfail --iofail @cslib-frontier @/mk_all @/checkInitImports "
          "@mathlib/lint-style",)),
    Step("lake test", ("lake test --wfail --iofail",)),
    Step("lake lint", ("lake lint",)),
    Step("Tidy statement ratchet",
         ("command -v lake",
          "test -d .lake/packages",
          "python3 -B -m unittest scripts/test_check_tidy_surface.py",
          "python3 -B scripts/check_tidy_surface.py")),
    Step("Security premise ratchet (changed modules)",
         ("python3 -B -m unittest scripts/test_check_security_premises.py",
          'python3 -B scripts/check_security_premises.py --base "$BASE"')),
    Step("Result registry references", ("python3 -B scripts/results_registry.py --compiled",)),
    Step("Changed-file lints", ('python3 -B scripts/check_changed_files.py --base "$BASE"',)),
    Step("lake exe mk_all --check", ("lake exe mk_all --check",)),
    Step("Test import generation with custom source directories",
         ("test -x .lake/build/bin/mk_all",
          "python3 -B -m unittest discover -s scripts -p 'test_mk_all.py'")),
    Step("lake exe lint-style", ("lake exe lint-style",)),
    Step("checkInitImports", ("command -v lean",
                              "python3 -B -m unittest scripts/test_check_init_imports.py",
                              "lake exe checkInitImports")),
)

# Run after `STEPS`; not CI steps, so `scripts/test_full_check.py` keeps their names apart from CI's.
LOCAL_STEPS = (
    # The local artifact cache restores outputs without their warnings, which `--wfail` and
    # `--iofail` then miss (#4523). CI's remote cache is published only from `main`.
    Step("Re-elaborate root-package files restored from the artifact cache",
         ("python3 -B scripts/check_cache_restores.py --progress",), progress=True),
)

# Run by scripts/check.sh before the cache bootstrap, in both full and quick modes.
PREFLIGHT = {
    "Operator manual links and excerpts": "python3 -B scripts/check_operator_manual.py",
}

CI_ONLY = {
    "Encoding readability report":
        "merge groups and main pushes only; reports and always succeeds",
    "Projection chain report":
        "merge groups and main pushes only; reports and always succeeds",
    "Security premise report":
        "merge groups and main pushes only; reports and always succeeds",
    "Repeated-proof-block notice (advisory)":
        "advisory; never fails the job. Run `scripts/proof_copies.py --base REF` to see it",
    "Reclaim unused hosted-runner SDK space": "hosted-runner disk cleanup",
    "Restore .lake from the Actions cache": "CI cache; check.sh runs scripts/cache/ensure.sh",
    "Restore Mathlib cache with retries": "CI cache; check.sh runs scripts/cache/ensure.sh",
    "Restore build outputs from the remote cache":
        "CI cache; check.sh runs scripts/cache/ensure.sh",
    "Restore validated merge-group build outputs":
        "main pushes only; downloads a merge-group artifact through the GitHub API",
    "Save .lake to the Actions cache": "main pushes only; CI cache",
    "Parallel-definition and duplicate-statement notices (advisory)":
        "advisory; never fails the job. Run `scripts/parallel_defs.py [--theorems]` to see it",
    "PR description names (advisory)":
        "advisory; reads the pull request event. Run `scripts/check_pr_names.py --pr N`",
    "Stage merge-group build outputs": "merge groups only; build handoff to main",
    "Upload merge-group build outputs": "merge groups only; build handoff to main",
    "Stage cache publication": "main pushes only; cache publication",
    "Hand off staged files to the enabled publishers": "main pushes only; cache publication",
}


def run_steps(steps: tuple[Step, ...], base: str, root: Path = ROOT,
              out: TextIO = sys.stdout) -> int:
    """Run every step, as GitHub runs a `run` script (`bash -e`), with `BASE` set; report each."""
    log_dir = Path(tempfile.mkdtemp(prefix="cslib-frontier-check."))
    status = 0
    for number, step in enumerate(steps, 1):
        log = log_dir / f"{number}.log"
        with log.open("wb") as stream:
            result = run_logged(
                ["bash", "-e", "-c", "\n".join(step.commands)],
                cwd=root / step.cwd if step.cwd else root,
                env={**os.environ, **step.env, "BASE": base},
                log=stream, progress=out if step.progress else None)
        if result.returncode:
            status = 1
            out.write(f"FAIL  {step.name}\n" + log.read_text(errors="replace"))
        else:
            out.write(f"ok    {step.name}\n")
        out.flush()
    if status:
        out.write(f"Full logs: {log_dir}\n")
    else:
        shutil.rmtree(log_dir)
    return status


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--base", default="origin/main",
                        help="comparison ref; changes are taken from its merge base with HEAD")
    parser.add_argument("--skip-map-count-check", action="store_true",
                        help="skip the Linux vm.max_map_count preflight for whole-library imports")
    args = parser.parse_args(argv)
    if not args.skip_map_count_check and check_vm_map_count.preflight(ROOT, sys.stdout) != 0:
        return 1
    return run_steps(STEPS + LOCAL_STEPS, args.base)


if __name__ == "__main__":
    sys.exit(main())
