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
                else:
                    body += ('if [ "${CLEANUP_TEST_ALL_DF_EXIT:-0}" != 0 ]; then\n'
                             '  exit "$CLEANUP_TEST_ALL_DF_EXIT"\n'
                             'fi\n'
                             'if [ "$1" = "-Pk" ]; then\n'
                             '  printf "Filesystem 1024-blocks Used Available Capacity Mounted on\\n"\n'
                             '  printf "/dev/root 304087040 62914560 %s 21%% /\\n" '
                             '"${CLEANUP_TEST_FREE_KIB:-92274688}"\n'
                             '  exit "${CLEANUP_TEST_DF_EXIT:-0}"\n'
                             'fi\n')
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
        self.assertEqual(commands, ["df -h /", "df -Pk /",
                                   "sudo rm -rf -- /usr/local/lib/android /usr/share/dotnet",
                                   "df -h /"])

    def test_free_space_threshold(self):
        threshold = 100 * 1024 * 1024
        for free_kib in (threshold - 1, threshold, 231 * 1024 * 1024):
            with self.subTest(free_kib=free_kib):
                result, commands = self.run_cleanup(CLEANUP_TEST_FREE_KIB=str(free_kib))
                self.assertEqual(result.returncode, 0, result.stderr)
                if free_kib >= threshold:
                    self.assertEqual(commands, ["df -h /", "df -Pk /"])
                    self.assertIn("Skipping SDK cleanup", result.stdout)
                else:
                    self.assertTrue(any(command.startswith("sudo ") for command in commands))

    def test_unavailable_space_measurement_keeps_cleanup(self):
        for override in ({"CLEANUP_TEST_FREE_KIB": "unknown"},
                         {"CLEANUP_TEST_FREE_KIB": "242221056", "CLEANUP_TEST_DF_EXIT": "1"},
                         {"CLEANUP_TEST_ALL_DF_EXIT": "1"}):
            with self.subTest(override=override):
                result, commands = self.run_cleanup(**override)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertTrue(any(command.startswith("sudo ") for command in commands))

    def test_cleanup_failure_is_reported(self):
        result, commands = self.run_cleanup(CLEANUP_TEST_EXIT="23")
        self.assertEqual(result.returncode, 23)
        self.assertEqual(len(commands), 3)

    def test_workflow_reclaims_space_before_restoring_cache(self):
        workflow = (ROOT / ".github/workflows/lean_action_ci.yml").read_text()
        self.assertLess(workflow.index("scripts/ci/prepare-runner.sh"),
                        workflow.index("- name: Restore .lake from the Actions cache"))


if __name__ == "__main__":
    unittest.main()
