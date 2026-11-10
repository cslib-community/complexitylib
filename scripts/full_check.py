#!/usr/bin/env python3
"""Run the required steps of CI's `ci-checks` job locally; `scripts/check.sh` calls this.

Usage: python3 scripts/full_check.py [--base REF]

`ci-checks` in `.github/workflows/lean_action_ci.yml` is the repository's only required status
check. `STEPS` repeats each of its steps that can run on a contributor's machine, in CI's order and
with CI's commands, so that a local full check fails where a pull request's CI would. Steps that
compare a change with its base use the merge base of REF (default `origin/main`) with `HEAD`, and
the working tree, where pull-request CI uses the first parent of its merge commit. Every step runs
even after a failure, and each is reported as `ok` or `FAIL` with its log.

`PREFLIGHT` lists the steps that `scripts/check.sh` runs itself, before the cache bootstrap.
`CI_ONLY` lists the remaining steps with the reason each does not run here: advisory notices that
never fail the job, cache and runner plumbing (`scripts/cache/ensure.sh` restores caches locally),
and steps that need GitHub context, tokens or secrets. `scripts/test_full_check.py` fails when a
`ci-checks` step is in none of the three; when a mirrored or preflight step's `run` script has a
line that is neither one of its commands here nor the listed `BASE` plumbing; when such a step sets
something the local run does not reproduce (another working directory or environment, `shell`,
`continue-on-error`, a timeout); or when the mirrored steps are out of CI's order.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from typing import TextIO

ROOT = Path(__file__).resolve().parent.parent


@dataclass(frozen=True)
class Step:
    """A `ci-checks` step: its CI name and every line of its `run` script except `set -e` and the
    computation of CI's base commit, which `BASE` replaces (`PLUMBING` in
    `scripts/test_full_check.py`)."""
    name: str
    commands: tuple[str, ...]
    cwd: str | None = None  # the step's `working-directory`
    env: dict[str, str] = field(default_factory=dict)  # the step's literal `env` values


STEPS = (
    # CI runs this before installing Lean, so the suite's Lean-gated tests skip there; here Lean is
    # installed and they run. It includes the manual checker's tests that check.sh runs first.
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
    Step("Result registry references", ("python3 -B scripts/results_registry.py --compiled",)),
    Step("Changed-file lints", ('python3 -B scripts/check_changed_files.py --base "$BASE"',)),
    Step("lake exe mk_all --check", ("lake exe mk_all --check",)),
    Step("Test import generation with custom source directories",
         ("test -x .lake/build/bin/mk_all",
          "python3 -B -m unittest discover -s scripts -p 'test_mk_all.py'")),
    Step("lake exe lint-style", ("lake exe lint-style",)),
    Step("checkInitImports", ("lake exe checkInitImports",)),
)

# Run by scripts/check.sh before the cache bootstrap, in both full and quick modes.
PREFLIGHT = {
    "Operator manual links and excerpts": "python3 -B scripts/check_operator_manual.py",
}

CI_ONLY = {
    "Prepare optional handoff measurement":
        "main-push cache experiment (#1728); needs the GitHub API",
    "Encoding readability report":
        "merge groups and main pushes only; reports and always succeeds",
    "Projection chain report":
        "merge groups and main pushes only; reports and always succeeds",
    "Repeated-proof-block notice (advisory)":
        "advisory; never fails the job. Run `scripts/proof_copies.py --base REF` to see it",
    "Reclaim unused hosted-runner SDK space": "hosted-runner disk cleanup",
    "Restore .lake from the Actions cache": "CI cache; check.sh runs scripts/cache/ensure.sh",
    "Restore Mathlib cache with retries": "CI cache; check.sh runs scripts/cache/ensure.sh",
    "Restore build outputs from the remote cache":
        "CI cache; check.sh runs scripts/cache/ensure.sh",
    "Optional controlled handoff measurement":
        "main-push cache experiment (#1728); needs the GitHub API",
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
    "Record optional handoff measurement": "main-push cache experiment (#1728)",
}


def run_steps(steps: tuple[Step, ...], base: str, root: Path = ROOT,
              out: TextIO = sys.stdout) -> int:
    """Run every step, as GitHub runs a `run` script (`bash -e`), with `BASE` set; report each."""
    log_dir = Path(tempfile.mkdtemp(prefix="cslib-frontier-check."))
    status = 0
    for number, step in enumerate(steps, 1):
        log = log_dir / f"{number}.log"
        with log.open("w") as stream:
            result = subprocess.run(
                ["bash", "-e", "-c", "\n".join(step.commands)],
                cwd=root / step.cwd if step.cwd else root,
                env={**os.environ, **step.env, "BASE": base},
                stdout=stream, stderr=subprocess.STDOUT)
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
    args = parser.parse_args(argv)
    return run_steps(STEPS, args.base)


if __name__ == "__main__":
    sys.exit(main())
