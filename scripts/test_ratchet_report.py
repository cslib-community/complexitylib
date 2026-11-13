"""The ratchet report step: report outside main, check every module on a main push, never fail."""

import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/ci/ratchet_report.sh"
WORKFLOW = ROOT / ".github/workflows/lean_action_ci.yml"
RATCHETS = ("check_encoding_readability.py", "check_projection_chains.py",
            "check_experiment_readability.py", "check_probability_idioms.py")


class RatchetReportTests(unittest.TestCase):
    def run_report(self, main_push, check_exit=0):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "commands"
            stub = Path(directory) / "python3"
            stub.write_text('#!/bin/sh\nprintf "%s\\n" "$*" >> "$REPORT_COMMAND_LOG"\n'
                            'exit "$REPORT_CHECK_EXIT"\n')
            stub.chmod(0o755)
            env = {**os.environ, "PATH": f"{directory}:{os.environ['PATH']}",
                   "REPORT_COMMAND_LOG": str(log), "REPORT_CHECK_EXIT": str(check_exit),
                   "MAIN_PUSH": main_push}
            result = subprocess.run(["/bin/bash", str(SCRIPT), "scripts/check_demo.py"], env=env,
                                    text=True, capture_output=True, check=False)
            return result, log.read_text().splitlines()

    def test_merge_groups_and_dispatch_only_report(self):
        for main_push in ("false", ""):
            with self.subTest(main_push=main_push):
                result, commands = self.run_report(main_push)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(commands, ["-B scripts/check_demo.py --report"])

    def test_main_push_checks_every_module(self):
        result, commands = self.run_report("true")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(commands, ["-B scripts/check_demo.py --all"])
        self.assertNotIn("::error", result.stdout)

    def test_main_push_overage_is_annotated_without_failing(self):
        result, commands = self.run_report("true", check_exit=1)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(commands, ["-B scripts/check_demo.py --all"])
        self.assertRegex(result.stdout, r"^::error title=[^:]+::scripts/check_demo\.py --all ")

    def test_every_ratchet_reports_through_the_script_on_main_pushes(self):
        workflow = WORKFLOW.read_text()
        for check in RATCHETS:
            with self.subTest(check=check):
                step = re.search(r'- name: "[^"]* report"\n((?:        .*\n)+?)'
                                 r"        run: scripts/ci/ratchet_report\.sh scripts/"
                                 + re.escape(check) + r"\n", workflow)
                self.assertIsNotNone(step, check)
                self.assertIn("if: github.event_name != 'pull_request'", step[1])
                self.assertIn("MAIN_PUSH: ${{ github.event_name == 'push' && "
                              "github.ref == 'refs/heads/main' }}", step[1])


if __name__ == "__main__":
    unittest.main()
