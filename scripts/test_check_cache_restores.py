"""Unit tests for scripts/check_cache_restores.py, with a real Lake regression test (#4523)."""

from __future__ import annotations

import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_cache_restores as c  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
LAKEFILE = """name = "restorefixture"
enableArtifactCache = true
restoreAllArtifacts = true

[[lean_lib]]
name = "Demo"

[[lean_lib]]
name = "DemoTests"
roots = []
globs = ["DemoTests.+"]

[[lean_exe]]
name = "tool"
srcDir = "tools"
root = "Tool"
"""


class Fixture(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Restore fixture")
        self.git("config", "user.email", "restore@example.invalid")
        self.write(".gitignore", ".lake/\n")
        self.write("lakefile.toml", LAKEFILE)
        self.write("Demo.lean", "import Demo.Base\n")
        self.write("Demo/Base.lean", "def value : Nat := 1\n")
        self.write("DemoTests/Client.lean", "import Demo.Base\nexample : value = 1 := rfl\n")
        self.write("tools/Tool.lean", "def main : IO Unit := pure ()\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")

    def write(self, name: str, text: str) -> None:
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def git(self, *args: str) -> str:
        env = {**os.environ, "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}
        return subprocess.check_output(["git", *args], cwd=self.root, env=env, text=True).strip()

    def commit(self) -> None:
        self.git("add", ".")
        self.git("commit", "-qm", "fixture")

    def trace(self, module_path: str, **fields) -> None:
        self.write(f".lake/build/lib/lean/{module_path}.trace", json.dumps(fields))


class RestoredFileTests(Fixture):
    def test_only_changed_files_with_synthetic_traces_are_selected(self) -> None:
        self.write("Demo/Committed.lean", "def committed := 1\n")
        self.commit()
        self.write("Demo/Staged.lean", "def staged := 1\n")
        self.git("add", "Demo/Staged.lean")
        self.write("DemoTests/Client.lean", "import Demo.Base\nexample : value = 1 := rfl -- edit\n")
        self.write("DemoTests/Untracked.lean", "example : 1 = 1 := rfl\n")
        self.write("DemoTests/Unbuilt.lean", "example : 2 = 2 := rfl\n")
        self.write("tools/Tool.lean", "def main : IO Unit := pure () -- edit\n")
        self.write("notes.md", "not Lean\n")
        for module in ("Demo/Committed", "Demo/Staged", "DemoTests/Untracked", "Tool"):
            self.trace(module, synthetic=True, log=[])
        self.trace("DemoTests/Client", log=[])  # built here: its log was replayed
        self.trace("Demo/Base", synthetic=True, log=[])  # restored, but unchanged
        self.assertEqual(c.restored_files(self.root, "origin/main"),
                         ["Demo/Committed.lean", "Demo/Staged.lean", "DemoTests/Untracked.lean",
                          "tools/Tool.lean"])

    def test_unreadable_trace_counts_as_restored(self) -> None:
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.write(".lake/build/lib/lean/Demo/Base.trace", "{not json")
        self.assertEqual(c.restored_files(self.root, "origin/main"), ["Demo/Base.lean"])

    def test_custom_source_directories_and_build_directory(self) -> None:
        self.write("lakefile.toml", 'name = "f"\nsrcDir = "src"\nbuildDir = "out"\n'
                   '[[lean_lib]]\nname = "Demo"\n[[lean_exe]]\nname = "t"\nsrcDir = "tools"\n')
        lib_dir, dirs = c.layout(self.root)
        self.assertEqual((lib_dir, dirs), (self.root / "out/lib/lean",
                                           [Path("src/tools"), Path("src")]))
        self.write("out/lib/lean/Tool.trace", "{}")
        self.assertEqual(c.trace_path("src/tools/Tool.lean", lib_dir, dirs),
                         self.root / "out/lib/lean/Tool.trace")
        self.assertIsNone(c.trace_path("Elsewhere/Tool.lean", lib_dir, dirs))


class MainTests(Fixture):
    def setUp(self) -> None:
        super().setUp()
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.trace("Demo/Base", synthetic=True, log=[])

    def run_main(self, returncode: int, output: str) -> tuple[int, str, list[str]]:
        calls = []

        def elaborate(root, rel):
            calls.append(rel)
            return subprocess.CompletedProcess([], returncode, output)

        out, err = io.StringIO(), io.StringIO()
        with patch.object(c, "elaborate", side_effect=elaborate), \
             redirect_stdout(out), redirect_stderr(err):
            status = c.main([], self.root)
        return status, out.getvalue() + err.getvalue(), calls

    def test_clean_restored_file_passes(self) -> None:
        status, out, calls = self.run_main(0, "")
        self.assertEqual((status, calls), (0, ["Demo/Base.lean"]))
        self.assertIn("cleanly (1)", out)

    def test_any_output_fails_although_lean_exits_zero(self) -> None:
        warning = "warning: Demo/Base.lean:1:4: This line exceeds the 100 character limit"
        for output in (warning, "info: Demo/Base.lean:1:0: 2\n"):
            with self.subTest(output=output):
                status, out, _ = self.run_main(0, output)
                self.assertEqual(status, 1)
                self.assertIn("FAIL  Demo/Base.lean", out)
                self.assertIn(output.strip(), out)

    def test_failed_elaboration_fails(self) -> None:
        self.assertEqual(self.run_main(1, "")[0], 1)

    def test_unresolvable_base_fails(self) -> None:
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
            c.main(["--base", "no-such-ref"], self.root)
        self.assertTrue(raised.exception.code)


class RealLakeTests(Fixture):
    """Lake restores a module that logged a warning without the warning; the check catches it.

    CI's "Test Python tooling" step runs before Lean is installed, so CI skips this test; it runs
    in a local `scripts/check.sh` or `python3 -m unittest` with the repository's toolchain.
    """

    def setUp(self) -> None:
        # CI runs Python tests before installing Lean.
        if not shutil.which("elan"):
            self.skipTest("installed Lean toolchain unavailable")
        toolchain = (REPO / "lean-toolchain").read_text().strip()
        listed = subprocess.run(["elan", "toolchain", "list"], capture_output=True, text=True)
        if toolchain not in listed.stdout:
            self.skipTest("repository Lean toolchain not installed")
        super().setUp()
        self.write("lean-toolchain", toolchain + "\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        # A private artifact cache, so the test neither reads nor fills the machine's shared one.
        cache = tempfile.TemporaryDirectory()
        self.addCleanup(cache.cleanup)
        environment = patch.dict(os.environ, {"LAKE_CACHE_DIR": cache.name})
        environment.start()
        self.addCleanup(environment.stop)

    def lake(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(["lake", *args], cwd=self.root, capture_output=True, text=True)

    def test_warning_dropped_by_a_cache_restore_is_reported(self) -> None:
        self.write("Demo/Base.lean", "theorem dropped : 1 = 2 := by sorry\n")
        first = self.lake("build", "--wfail", "--iofail", "Demo.Base")
        self.assertNotEqual(first.returncode, 0, first.stdout + first.stderr)
        for output in (self.root / ".lake/build").rglob("Base.*"):
            output.unlink()
        self.lake("build", "--wfail", "--iofail", "Demo.Base")  # restores from the cache
        trace = self.root / ".lake/build/lib/lean/Demo/Base.trace"
        if not c.restored(trace):
            self.skipTest("this Lake rebuilt the module instead of restoring it")
        out = io.StringIO()
        with redirect_stdout(out), redirect_stderr(out):
            self.assertEqual(c.main([], self.root), 1)
        self.assertIn("sorry", out.getvalue())


if __name__ == "__main__":
    unittest.main()
