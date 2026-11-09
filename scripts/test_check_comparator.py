"""Regression checks for challenge preparation and fail-closed comparator invocation."""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


class ComparatorRunnerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.script = self.root / "scripts/check_comparator.py"
        self.script.parent.mkdir()
        shutil.copyfile(Path(__file__).with_name("check_comparator.py"), self.script)
        self.generated = self.root / "comparator/ComplexityComparatorChallenges"

    def run_script(self, *arguments: str, env: dict[str, str] | None = None):
        return subprocess.run(
            [sys.executable, str(self.script), *arguments],
            capture_output=True, text=True, env=env,
        )

    def test_default_preparation_needs_no_positional_suites(self) -> None:
        result = self.run_script("--prepare-only")
        self.assertEqual(result.returncode, 0, result.stderr)
        for suite in ("basic", "automation"):
            config = json.loads((self.generated / f"{suite}.json").read_text())
            self.assertEqual(len(config["theorem_names"]), 2)
        self.assertFalse((self.generated / "sat.json").exists())

    def test_preparation_preserves_unrecognized_sources(self) -> None:
        self.generated.mkdir(parents=True)
        source = self.generated / "Basic.lean"
        original = "-- A source not owned by the generator.\n"
        source.write_text(original)
        result = self.run_script("basic", "--prepare-only")
        self.assertEqual(result.returncode, 2)
        self.assertEqual(source.read_text(), original)

    @unittest.skipIf(os.name == "nt", "requires POSIX symlinks")
    def test_challenges_cannot_be_redirected_into_writable_lake(self) -> None:
        writable = self.root / ".lake"
        writable.mkdir()
        self.generated.parent.mkdir()
        self.generated.symlink_to(writable, target_is_directory=True)
        result = self.run_script("--prepare-only")
        self.assertEqual(result.returncode, 2)
        self.assertEqual(list(writable.iterdir()), [])

    @unittest.skipIf(os.name == "nt", "requires a POSIX executable stub")
    def test_unavailable_sandbox_is_failure_without_a_retry_or_bypass(self) -> None:
        binaries = self.root / "bin"
        binaries.mkdir()
        lake = binaries / "lake"
        lake.write_text(
            f"#!{sys.executable}\n"
            "import json, pathlib, sys\n"
            "with pathlib.Path(__file__).with_suffix('.calls').open('a') as f:\n"
            "    f.write(json.dumps(sys.argv[1:]) + '\\n')\n"
            "sys.exit(2)\n"
        )
        lake.chmod(0o755)
        env = dict(os.environ)
        env["PATH"] = str(binaries) + os.pathsep + env.get("PATH", "")
        result = self.run_script("basic", env=env)
        self.assertEqual(result.returncode, 2, result.stderr)
        calls = lake.with_suffix(".calls").read_text().splitlines()
        self.assertEqual(len(calls), 1)
        arguments = json.loads(calls[0])
        self.assertEqual(arguments[:2], ["comparator", "--paranoid"])
        self.assertFalse(any("no-sandbox" in argument for argument in arguments))


if __name__ == "__main__":
    unittest.main()
