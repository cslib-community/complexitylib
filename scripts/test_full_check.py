"""`scripts/full_check.py` mirrors CI's source and Lean jobs, and its runner reports each step.

The parity test reads `.github/workflows/lean_action_ci.yml` as text (CI's Python has no YAML
library) and fails closed. Every named `source-checks` and `lean-checks` step must be mirrored by
`full_check.STEPS`, run by `scripts/check.sh` before the cache bootstrap (`PREFLIGHT`), or listed in
`CI_ONLY`. The `run` script of a mirrored or preflight step may contain only its local commands, in
order, and the lines in `PLUMBING` (`set -e` and the computation of `BASE`), which the local run
replaces by the merge base of `--base`; any other line is reported. So is a step key the local run
does not reproduce (anything outside `MIRRORED_KEYS`, such as `shell`, `continue-on-error` or
`timeout-minutes`), a working directory or literal environment that differs from CI's, an
environment value taken from GitHub context other than `CONTEXT_ENV`, a job-level `defaults` or
literal `env`, and mirrored steps out of order within either CI job. A step's `if:` condition is
not compared: the local run always runs a mirrored step, which is the stricter direction for steps
that CI runs only on some events. `ParityProblemTests` mutates the workflow to check that each kind
of drift is reported. Separate aggregator tests require both jobs to succeed and check that its
publication output is forwarded from `lean-checks`.
"""

import importlib.util
import io
import os
from pathlib import Path
import re
import subprocess
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
EXECUTION_JOBS = ("source-checks", "lean-checks")
AGGREGATOR_JOB = "ci-checks"
SOURCE_CHECK_NAMES = frozenset({
    "Test Python tooling",
    "Operator manual links and excerpts",
    "Source hygiene",
    "Encoding readability ratchet (changed modules)",
    "Encoding readability report",
    "Projection chain ratchet (changed modules)",
    "Projection chain report",
    "Repeated-proof-block notice (advisory)",
    "Documentation pins",
})
# The only `run` lines of a mirrored step that the local run does not repeat: they compute CI's
# base commit, which `full_check.py` passes as `BASE` instead.
PLUMBING = frozenset({
    "set -e",
    "BASE=",
    'if [ "$GITHUB_EVENT_NAME" = pull_request ]; then',
    "BASE=$(git cat-file -p HEAD | sed -n 's/^parent //p' | head -n 1)",
    "fi",
    "BASE=${BASE:-$RECORDED_BASE}",
    'git fetch --no-tags --depth=1 origin "$BASE"',
})
# Step keys the local run accounts for: `if` is deliberately not reproduced (see above), and `id`
# only names the step for later steps.
MIRRORED_KEYS = frozenset({"name", "run", "working-directory", "env", "if", "id"})
# Environment a mirrored step may take from GitHub context: CI's base commit, replaced by `BASE`.
CONTEXT_ENV = frozenset({"RECORDED_BASE"})
STEP_KEY = re.compile(r"      (- |  )([A-Za-z-]+):(?: (.*))?$")  # a step key, indented 8


def unquote(value: str) -> str:
    value = value.strip()
    if len(value) > 1 and value[0] == value[-1] and value[0] in "'\"":
        return value[1:-1]
    return value


def job_lines(text: str, job: str) -> list[str]:
    """The lines of `job`, from its key to the next job."""
    lines = text.splitlines()
    start = lines.index(f"  {job}:")
    end = next((i for i in range(start + 1, len(lines))
                if re.match(r"  \S", lines[i])), len(lines))
    return lines[start:end]


def job_steps(text: str, job: str) -> list[dict]:
    """The steps of `job`, each a dict of its top-level keys (`with` and `env` as raw lines).

    Handles the forms this workflow uses: plain or quoted scalars and `|`/`>` block scalars. A line
    that is neither a step key nor indented deeper than one (inside a block scalar) raises
    `ValueError`, so a misindented key cannot be absorbed into the previous step."""
    lines = job_lines(text, job)
    steps: list[dict] = []
    folded: set[tuple[int, str]] = set()  # (step index, key) of `>` block scalars
    current: dict | None = None
    key = None
    for line in lines[lines.index("    steps:") + 1:]:
        if not line.strip() or line.lstrip().startswith("#"):
            if key and current is not None and isinstance(current.get(key), list):
                current[key].append("")
            continue
        match = STEP_KEY.match(line)
        if match:
            if match[1] == "- ":
                current = {}
                steps.append(current)
            key, value = match[2], (match[3] or "")
            current[key] = [] if value.strip() in ("|", "|-", ">", ">-", "") else unquote(value)
            if value.strip().startswith(">"):
                folded.add((len(steps) - 1, key))
            continue
        if (current is None or key is None or not isinstance(current.get(key), list)
                or len(line) - len(line.lstrip()) <= 8):
            raise ValueError(f"unparsed workflow line: {line!r}")
        current[key].append(line.strip())
    for index, step in enumerate(steps):
        for name, value in step.items():
            if isinstance(value, list) and name != "env":
                step[name] = (" " if (index, name) in folded else "\n").join(value).strip()
    return steps


def script_lines(run: str) -> tuple[str, ...]:
    """The lines of a `run` script other than blank lines and `PLUMBING`."""
    return tuple(line.strip() for line in run.splitlines()
                 if line.strip() and line.strip() not in PLUMBING)


def literal_env(lines: list[str]) -> dict[str, str]:
    env = {}
    for line in lines:
        name, _, value = line.partition(":")
        if line and "${{" not in value:
            env[name.strip()] = unquote(value)
    return env


def header_problems(lines: list[str], job: str) -> list[str]:
    """Job-level settings that would change how CI runs the mirrored steps."""
    problems, section = [], None
    for line in lines[1:lines.index("    steps:")]:
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        if re.match(r"    \S", line):
            section = line.strip().split(":", 1)[0]
            if section == "defaults":
                problems.append(f"{job} sets job-level `defaults`, which the local run does not "
                                "reproduce")
        elif section == "env" and "${{" not in line:
            problems.append(f"{job} sets job-level `env` {line.strip()!r}, which the local run "
                            "does not reproduce")
    return problems


def parity_problems(text: str) -> list[str]:
    """Each way the source and Lean jobs of workflow `text` differ from the local check."""
    problems = []
    steps_by_job = {job: job_steps(text, job) for job in EXECUTION_JOBS}
    for job in EXECUTION_JOBS:
        problems.extend(header_problems(job_lines(text, job), job))
    steps = [step for job in EXECUTION_JOBS for step in steps_by_job[job]]
    for step in steps:
        if "name" not in step and "run" in step:
            problems.append(f"an unnamed `run` step ({step['run'].splitlines()[0]!r}) cannot be "
                            "classified; name it")
    named_steps = [step for step in steps if "name" in step]
    named = {step["name"]: step for step in named_steps}
    if len(named) != len(named_steps):
        problems.append("source-checks and lean-checks have two steps with the same name")
    mirrored = {step.name: step for step in full.STEPS}
    homes = (mirrored, full.PREFLIGHT, full.CI_ONLY)
    for name in named:
        if sum(name in home for home in homes) != 1:
            problems.append(f"{name}: add the step to exactly one of full_check.STEPS or "
                            "full_check.PREFLIGHT, or record why it stays in CI in "
                            "full_check.CI_ONLY")
    for name in sorted(set().union(*homes) - set(named)):
        problems.append(f"{name}: listed in full_check, but CI no longer has this step in either "
                        "execution job")
    local = [(step.name, step.commands, step.cwd, step.env) for step in full.STEPS]
    local += [(name, (command,), None, {}) for name, command in full.PREFLIGHT.items()]
    for name, commands, cwd, env in local:
        ci = named.get(name)
        if ci is None:
            continue
        extra = sorted(set(ci) - MIRRORED_KEYS)
        if extra:
            hint = "; advisory steps stay CI-only" if "continue-on-error" in extra else ""
            problems.append(f"{name}: sets {', '.join(extra)}, which the local run does not "
                            f"reproduce{hint}")
        lines = script_lines(ci.get("run", ""))
        if lines != commands:
            unknown = [line for line in lines if line not in commands]
            note = f"; neither PLUMBING nor local commands: {unknown}" if unknown else ""
            problems.append(f"{name}: CI runs {lines}, the local run {commands}{note}")
        if cwd != ci.get("working-directory"):
            problems.append(f"{name}: working-directory {ci.get('working-directory')!r} in CI, "
                            f"{cwd!r} locally")
        if env != literal_env(ci.get("env", [])):
            problems.append(f"{name}: literal env {literal_env(ci.get('env', []))} in CI, "
                            f"{env} locally")
        for line in ci.get("env", []):
            variable, _, value = line.partition(":")
            if "${{" in value and variable.strip() not in CONTEXT_ENV:
                problems.append(f"{name}: env {variable.strip()} comes from GitHub context, "
                                "which the local run does not reproduce")
    for job, job_entries in steps_by_job.items():
        order = [step["name"] for step in job_entries
                 if step.get("name") in mirrored]
        expected = [step.name for step in full.STEPS if step.name in order]
        if order != expected:
            problems.append(f"mirrored steps run in {job} in the order {order}, "
                            f"in full_check.STEPS in the order {expected}")
    return problems


class WorkflowParityTests(unittest.TestCase):
    def setUp(self):
        self.text = WORKFLOW.read_text()
        self.named_by_job = {
            job: [step for step in job_steps(self.text, job) if "name" in step]
            for job in EXECUTION_JOBS
        }
        self.named = [step for job in EXECUTION_JOBS for step in self.named_by_job[job]]

    def test_parser_reads_the_steps_it_compares(self):
        # A parser that silently lost steps would make the parity test vacuous.
        names = [step["name"] for step in self.named]
        source_names = [step["name"] for step in self.named_by_job["source-checks"]]
        lean_names = [step["name"] for step in self.named_by_job["lean-checks"]]
        self.assertEqual(set(source_names), SOURCE_CHECK_NAMES)
        self.assertIn("Tidy statement ratchet", names)
        self.assertIn("lake build", lean_names)
        self.assertGreater(len(names), 25)
        handoff = next(step for step in self.named if step["name"] == "Test Lake build handoff reuse")
        local = next(step for step in full.STEPS if step.name == handoff["name"])
        self.assertEqual(script_lines(handoff["run"]), local.commands)  # a folded `>-` scalar

    def test_full_check_mirrors_ci(self):
        problems = parity_problems(self.text)
        self.assertEqual(problems, [], "\n".join(problems))

    def test_preflight_steps_run_in_check_sh_with_ci_commands(self):
        lines = [line.strip() for line in (REPO / "scripts/check.sh").read_text().splitlines()
                 if not line.lstrip().startswith("#")]
        for name, command in full.PREFLIGHT.items():
            with self.subTest(step=name):
                self.assertTrue(any(line.endswith(f" {command}") for line in lines), command)

    def test_post_build_audits_follow_the_build(self):
        names = [step.name for step in full.STEPS]
        for audit in ("Tidy statement ratchet", "Result registry references", "Changed-file lints"):
            self.assertGreater(names.index(audit), names.index("lake build"))

    def test_local_steps_are_not_ci_steps(self):
        # A local step must neither pass for a mirror of a CI step nor hide one from the parity check.
        ci = {step["name"] for step in self.named}
        others = {step.name for step in full.STEPS} | set(full.PREFLIGHT) | set(full.CI_ONLY)
        for step in full.LOCAL_STEPS:
            with self.subTest(step=step.name):
                self.assertNotIn(step.name, ci | others)


class AggregatorTests(unittest.TestCase):
    def setUp(self):
        self.text = WORKFLOW.read_text()
        self.lines = job_lines(self.text, AGGREGATOR_JOB)
        self.steps = job_steps(self.text, AGGREGATOR_JOB)

    def test_required_context_depends_on_both_jobs_and_forwards_lean_publication(self):
        header = "\n".join(self.lines[:self.lines.index("    steps:")])
        self.assertIn("needs: [source-checks, lean-checks]", header)
        self.assertIn("if: always()", header)
        self.assertIn("publication: ${{ needs.lean-checks.outputs.publication }}", header)
        self.assertNotIn("steps.upload-publication.outputs", header)
        self.assertEqual([step.get("name") for step in self.steps],
                         ["Require source and Lean validation"])
        env = self.steps[0]["env"]
        self.assertIn("SOURCE_RESULT: ${{ needs.source-checks.result }}", env)
        self.assertIn("LEAN_RESULT: ${{ needs.lean-checks.result }}", env)

    def test_execution_jobs_can_start_in_parallel(self):
        for job in EXECUTION_JOBS:
            with self.subTest(job=job):
                lines = job_lines(self.text, job)
                header = "\n".join(lines[:lines.index("    steps:")])
                self.assertNotIn("needs:", header)

    def test_only_two_successful_dependencies_pass(self):
        script = self.steps[0]["run"]
        results = ("success", "failure", "cancelled", "skipped")
        for source_result in results:
            for lean_result in results:
                with self.subTest(source=source_result, lean=lean_result):
                    result = subprocess.run(
                        ["bash", "-e", "-c", script],
                        env={**os.environ, "SOURCE_RESULT": source_result,
                             "LEAN_RESULT": lean_result},
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                    self.assertEqual(result.returncode == 0,
                                     source_result == lean_result == "success", result.stdout)


TIDY = "          python3 -B scripts/check_tidy_surface.py\n"
REGISTRY = ('      - name: "Result registry references"\n'
            "        run: python3 -B scripts/results_registry.py --compiled\n")


class ParityProblemTests(unittest.TestCase):
    """Negative controls: each edit makes CI do something the local run would not."""

    def report(self, *edits: tuple[str, str]) -> list[str]:
        text = WORKFLOW.read_text()
        for old, new in edits:
            self.assertEqual(text.count(old), 1, old)
            text = text.replace(old, new)
        return parity_problems(text)

    def assertReported(self, problems: list[str], *fragments: str):
        self.assertTrue(any(all(f in p for f in fragments) for p in problems),
                        f"no problem mentions {fragments}: {problems}")

    def test_extra_lines_in_a_mirrored_script(self):
        for line in ("bash scripts/ci/extra_gate.sh", "cd scripts", "export TIDY_STRICT=1",
                     "python3 -B scripts/extra_gate.py", "if true; then"):
            with self.subTest(line=line):
                problems = self.report((TIDY, f"          {line}\n{TIDY}"))
                self.assertReported(problems, "Tidy statement ratchet", line)

    def test_changed_arguments(self):
        problems = self.report((REGISTRY, REGISTRY.replace("--compiled", "--compiled --strict")))
        self.assertReported(problems, "Result registry references", "--strict")

    def test_step_settings_the_local_run_does_not_reproduce(self):
        for setting, fragment in (("working-directory: scripts", "working-directory"),
                                  ("env:\n          STRICT: \"1\"", "literal env"),
                                  ("env:\n          TOKEN: ${{ secrets.TOKEN }}", "GitHub context"),
                                  ("shell: sh {0}", "shell"),
                                  ("continue-on-error: true", "advisory"),
                                  ("timeout-minutes: 5", "timeout-minutes")):
            with self.subTest(setting=setting):
                problems = self.report((REGISTRY, f"{REGISTRY}        {setting}\n"))
                self.assertReported(problems, "Result registry references", fragment)

    def test_mirrored_step_becomes_an_action(self):
        problems = self.report((REGISTRY, '      - name: "Result registry references"\n'
                                          "        uses: ./.github/actions/registry\n"))
        self.assertReported(problems, "Result registry references", "uses")

    def test_unclassified_unnamed_removed_and_reordered_steps(self):
        new = '      - name: "New gate"\n        run: python3 -B scripts/new_gate.py\n'
        self.assertReported(self.report((REGISTRY, new + REGISTRY)), "New gate", "CI_ONLY")
        unnamed = "      - run: python3 -B scripts/new_gate.py\n"
        self.assertReported(self.report((REGISTRY, unnamed + REGISTRY)), "unnamed")
        self.assertReported(self.report((REGISTRY, "")), "Result registry references",
                            "no longer")
        tidy = '      - name: "Tidy statement ratchet"\n'
        self.assertReported(self.report((REGISTRY, ""), (tidy, REGISTRY + tidy)), "order")

    def test_preflight_drift(self):
        command = "python3 -B scripts/check_operator_manual.py"
        problems = self.report((f"run: {command}\n", f"run: {command} --strict\n"))
        self.assertReported(problems, "Operator manual links and excerpts", "--strict")

    def test_job_level_settings(self):
        anchor = "  lean-checks:\n"
        defaults = "    defaults:\n      run:\n        shell: sh\n"
        env = "    env:\n      STRICT: \"1\"\n"
        self.assertReported(self.report((anchor, anchor + defaults)), "defaults")
        self.assertReported(self.report((anchor, anchor + env)), "STRICT")

    def test_misindented_key_is_not_absorbed(self):
        with self.assertRaisesRegex(ValueError, "unparsed workflow line"):
            self.report((REGISTRY, REGISTRY.replace("      - name", "      -   name")))


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
        with patch.object(full.check_vm_map_count, "preflight", return_value=0), \
             patch.object(full, "run_steps", return_value=0) as run:
            self.assertEqual(full.main(["--base", "abc123"]), 0)
            self.assertEqual(run.call_args.args, (full.STEPS + full.LOCAL_STEPS, "abc123"))
            full.main([])
            self.assertEqual(run.call_args.args, (full.STEPS + full.LOCAL_STEPS, "origin/main"))

    def test_main_stops_when_vm_map_count_preflight_fails(self):
        with patch.object(full.check_vm_map_count, "preflight", return_value=1), \
             patch.object(full, "run_steps", return_value=0) as run:
            self.assertEqual(full.main([]), 1)
            run.assert_not_called()
            self.assertEqual(full.main(["--skip-map-count-check"]), 0)
            run.assert_called_once()


if __name__ == "__main__":
    unittest.main()
