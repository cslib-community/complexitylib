"""Exercise the hosted-runner cleanup boundary without deleting real SDKs.

Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
"""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/ci/prepare-runner.sh"


class PrepareRunnerTests(unittest.TestCase):
    def run_cleanup(self, **overrides):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            log = root / "commands"
            for command in ("df", "sudo"):
                stub = root / command
                body = ('#!/bin/sh\nprintf "%s\\n" "' + command +
                        ' $*" >> "$CLEANUP_COMMAND_LOG"\n')
                if command == "sudo":
                    body += 'exit "${CLEANUP_TEST_EXIT:-0}"\n'
                stub.write_text(body)
                stub.chmod(0o755)
            env = {**os.environ, "GITHUB_ACTIONS": "true",
                   "RUNNER_ENVIRONMENT": "github-hosted", "RUNNER_OS": "Linux",
                   "PATH": directory, "CLEANUP_COMMAND_LOG": str(log), **overrides}
            result = subprocess.run(["/bin/bash", str(SCRIPT)], env=env,
                                    text=True, capture_output=True, check=False)
            return result, log.read_text().splitlines() if log.exists() else []

    def test_no_cleanup_on_local_self_hosted_or_other_os(self):
        for override in ({"GITHUB_ACTIONS": ""}, {"RUNNER_ENVIRONMENT": ""},
                         {"RUNNER_ENVIRONMENT": "self-hosted"}, {"RUNNER_OS": "macOS"}):
            with self.subTest(override=override):
                result, commands = self.run_cleanup(**override)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(commands, [])
                self.assertIn("Skipping", result.stdout)

    def test_only_unused_sdks_between_disk_reports(self):
        result, commands = self.run_cleanup()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(commands, ["df -h /",
                                   "sudo rm -rf -- /usr/local/lib/android /usr/share/dotnet",
                                   "df -h /"])

    def test_cleanup_failure_is_reported(self):
        result, commands = self.run_cleanup(CLEANUP_TEST_EXIT="23")
        self.assertEqual(result.returncode, 23)
        self.assertEqual(len(commands), 2)

    def test_workflow_reclaims_space_before_restoring_cache(self):
        workflow = (ROOT / ".github/workflows/lean_action_ci.yml").read_text()
        self.assertLess(workflow.index("scripts/ci/prepare-runner.sh"),
                        workflow.index("- name: Restore .lake from the Actions cache"))


if __name__ == "__main__":
    unittest.main()
