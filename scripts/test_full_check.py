"""`scripts/full_check.py` mirrors CI's required `ci-checks` job, and its runner reports each step.

The parity test reads `.github/workflows/lean_action_ci.yml` as text (CI's Python has no YAML
library) and fails when a `ci-checks` step is neither mirrored by `full_check.STEPS`, run by
`scripts/check.sh` before the cache bootstrap (`PREFLIGHT`), nor listed in `CI_ONLY`. A mirrored
step must have CI's commands, working directory and literal environment, in CI's order. Commands
are the lines of a step's `run` script that start with `python3`, `lake`, `test` or `command`
(the last two are guards that keep Lean-gated tests from skipping); the rest (`set -e`, `git fetch`,
the computation of `BASE`) is shell plumbing that the local run replaces by the merge base of
`--base`.
"""

import importlib.util
import io
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("full_check", Path(__file__).with_name("full_check.py"))
full = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = full
SPEC.loader.exec_module(full)
REPO = Path(__file__).resolve().parent.parent
WORKFLOW = REPO / ".github/workflows/lean_action_ci.yml"
COMMAND_HEADS = ("python3", "lake", "test", "command")


def unquote(value: str) -> str:
    value = value.strip()
    if len(value) > 1 and value[0] == value[-1] and value[0] in "'\"":
        return value[1:-1]
    return value


def job_steps(text: str, job: str) -> list[dict]:
    """The steps of `job`, each a dict of its top-level keys (`with` and `env` as raw lines).

    Handles the forms this workflow uses: plain or quoted scalars and `|`/`>` block scalars."""
    lines = text.splitlines()
    start = lines.index(f"  {job}:")
    end = next((i for i in range(start + 1, len(lines))
                if re.match(r"  \S", lines[i])), len(lines))
    body = lines[start:end]
    first = body.index("    steps:") + 1
    steps: list[dict] = []
    folded: set[tuple[int, str]] = set()  # (step index, key) of `>` block scalars
    current: dict | None = None
    key = None
    for line in body[first:]:
        if not line.strip() or line.lstrip().startswith("#"):
            if key and current is not None and isinstance(current.get(key), list):
                current[key].append("")
            continue
        match = re.match(r"      (- |  )([A-Za-z-]+):(?: (.*))?$", line)
        if match:
            if match[1] == "- ":
                current = {}
                steps.append(current)
            key, value = match[2], (match[3] or "")
            current[key] = [] if value.strip() in ("|", "|-", ">", ">-", "") else unquote(value)
            if value.strip().startswith(">"):
                folded.add((len(steps) - 1, key))
            continue
        if current is None or key is None or not isinstance(current.get(key), list):
            raise AssertionError(f"unparsed workflow line: {line!r}")
        current[key].append(line.strip())
    for index, step in enumerate(steps):
        for name, value in step.items():
            if isinstance(value, list) and name != "env":
                step[name] = (" " if (index, name) in folded else "\n").join(value).strip()
    return steps


def commands(run: str) -> tuple[str, ...]:
    return tuple(line.strip() for line in run.splitlines()
                 if line.strip().split(" ", 1)[0] in COMMAND_HEADS)


def literal_env(lines: list[str]) -> dict[str, str]:
    env = {}
    for line in lines:
        name, _, value = line.partition(":")
        if line and "${{" not in value:
            env[name.strip()] = unquote(value)
    return env


class WorkflowParityTests(unittest.TestCase):
    def setUp(self):
        self.steps = job_steps(WORKFLOW.read_text(), "ci-checks")
        self.named = [step for step in self.steps if "name" in step]

    def test_parser_reads_the_steps_it_compares(self):
        # A parser that silently lost steps would make the parity test vacuous.
        names = [step["name"] for step in self.named]
        self.assertIn("Tidy statement ratchet", names)
        self.assertIn("lake build", names)
        self.assertGreater(len(names), 25)
        unnamed = [step for step in self.steps if "name" not in step]
        self.assertTrue(all("uses" in step and "run" not in step for step in unnamed), unnamed)
        handoff = next(step for step in self.named if step["name"] == "Test Lake build handoff reuse")
        local = next(step for step in full.STEPS if step.name == handoff["name"])
        self.assertEqual(commands(handoff["run"]), local.commands)  # a folded `>-` scalar

    def test_every_ci_step_is_mirrored_run_by_check_sh_or_recorded_as_ci_only(self):
        mirrored = {step.name: step for step in full.STEPS}
        for step in self.named:
            name = step["name"]
            with self.subTest(step=name):
                homes = [name in mirrored, name in full.PREFLIGHT, name in full.CI_ONLY]
                self.assertEqual(sum(homes), 1, "add the step to full_check.STEPS, or record "
                                 "why it stays in CI in full_check.CI_ONLY")
        names = {step["name"] for step in self.named}
        stale = (set(mirrored) | set(full.PREFLIGHT) | set(full.CI_ONLY)) - names
        self.assertEqual(stale, set(), "entries for steps that ci-checks no longer has")

    def test_mirrored_steps_match_ci_commands_environment_and_order(self):
        by_name = {step["name"]: step for step in self.named}
        for local in full.STEPS:
            with self.subTest(step=local.name):
                ci = by_name[local.name]
                self.assertNotIn("continue-on-error", ci, "advisory steps stay CI-only")
                self.assertTrue(local.commands)
                self.assertEqual(local.commands, commands(ci["run"]))
                self.assertEqual(local.cwd, ci.get("working-directory"))
                self.assertEqual(local.env, literal_env(ci.get("env", [])))
        order = [step["name"] for step in self.named if step["name"] in
                 {local.name for local in full.STEPS}]
        self.assertEqual(order, [local.name for local in full.STEPS])

    def test_preflight_steps_run_in_check_sh_with_ci_commands(self):
        check_sh = (REPO / "scripts/check.sh").read_text()
        by_name = {step["name"]: step for step in self.named}
        for name, command in full.PREFLIGHT.items():
            with self.subTest(step=name):
                self.assertEqual(commands(by_name[name]["run"]), (command,))
                self.assertIn(command, check_sh)

    def test_post_build_audits_follow_the_build(self):
        names = [step.name for step in full.STEPS]
        for audit in ("Tidy statement ratchet", "Result registry references", "Changed-file lints"):
            self.assertGreater(names.index(audit), names.index("lake build"))


class RunnerTests(unittest.TestCase):
    def run_steps(self, steps, base="example-base"):
        out = io.StringIO()
        with tempfile.TemporaryDirectory() as temp, \
             patch.object(full.tempfile, "tempdir", temp):
            root = Path(temp) / "checkout"
            (root / "sub").mkdir(parents=True)
            status = full.run_steps(steps, base, root=root, out=out)
            leftover = sorted(p.name for p in Path(temp).glob("cslib-frontier-check.*"))
        return status, out.getvalue(), leftover

    def test_every_step_runs_and_failures_are_reported_with_logs(self):
        steps = (
            full.Step("first", ('test "$BASE" = example-base', "echo first-output")),
            full.Step("second", ("echo second-log", "false", "echo unreachable")),
            full.Step("third", ('test "$(basename "$PWD")" = sub', 'test "$FLAG" = on'),
                      cwd="sub", env={"FLAG": "on"}),
        )
        status, out, leftover = self.run_steps(steps)
        self.assertEqual(status, 1)
        self.assertIn("ok    first\n", out)
        self.assertNotIn("first-output", out)
        self.assertIn("FAIL  second\nsecond-log\n", out)
        self.assertNotIn("unreachable", out)  # `bash -e`, as GitHub runs a step
        self.assertIn("ok    third\n", out)
        self.assertIn("Full logs: ", out)
        self.assertEqual(len(leftover), 1)

    def test_success_removes_the_logs(self):
        status, out, leftover = self.run_steps((full.Step("only", ("true",)),))
        self.assertEqual((status, out, leftover), (0, "ok    only\n", []))

    def test_main_passes_the_base_to_the_steps(self):
        with patch.object(full, "run_steps", return_value=0) as run:
            self.assertEqual(full.main(["--base", "abc123"]), 0)
            self.assertEqual(run.call_args.args, (full.STEPS, "abc123"))
            full.main([])
            self.assertEqual(run.call_args.args, (full.STEPS, "origin/main"))


if __name__ == "__main__":
    unittest.main()
