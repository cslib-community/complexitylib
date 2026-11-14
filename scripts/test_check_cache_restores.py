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
import quick_check as quick  # noqa: E402

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
    def test_full_check_includes_unchanged_built_clients_and_executables(self) -> None:
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
        self.trace("Demo/Base", synthetic=True, log=[])  # unchanged sources are covered too
        self.assertEqual(c.restored_files(self.root),
                         ["Demo/Base.lean", "Demo/Committed.lean", "Demo/Staged.lean",
                          "DemoTests/Untracked.lean", "tools/Tool.lean"])

    def test_full_check_does_not_depend_on_changed_file_selection(self) -> None:
        self.trace("DemoTests/Client", synthetic=True, log=[])
        self.trace("Demo/Base", synthetic=True, log=[])
        (self.root / "Demo/Base.lean").unlink()
        self.write("lean-toolchain", "a different toolchain\n")
        self.assertEqual(c.restored_files(self.root), ["DemoTests/Client.lean"])

    def test_explicit_scope_covers_unchanged_client_and_missing_traces(self) -> None:
        self.trace("Demo/Base", synthetic=True, log=[])
        self.trace("DemoTests/Client", synthetic=True, log=[])
        self.assertEqual(c.restored_files(self.root, ["DemoTests/Client.lean", "tools/Tool.lean"]),
                         ["DemoTests/Client.lean", "tools/Tool.lean"])

    def test_full_check_includes_outputs_without_traces(self) -> None:
        self.write(".lake/build/lib/lean/DemoTests/Client.olean", "compiled output")
        self.assertEqual(c.restored_files(self.root), ["DemoTests/Client.lean"])

    def test_executable_scope_includes_built_helpers_without_expanding_library_scope(self) -> None:
        self.write("tools/Helper.lean", "import Demo.Base\n")
        for module in ("Demo/Base", "DemoTests/Client", "Tool", "Helper"):
            self.trace(module, synthetic=True, log=[])
        self.assertEqual(c.restored_files(self.root, ["Demo/Base.lean"], ["tools"]),
                         ["Demo/Base.lean", "tools/Helper.lean", "tools/Tool.lean"])

    def test_optional_aggregate_is_checked_only_when_built(self) -> None:
        self.assertEqual(c.restored_files(self.root, [], ["Demo.lean"]), [])
        self.write(".lake/build/lib/lean/Demo.olean", "compiled output")
        self.assertEqual(c.restored_files(self.root, [], ["Demo.lean"]), ["Demo.lean"])

    def test_paths_with_whitespace_are_preserved(self) -> None:
        self.write("Demo/has space\nand newline.lean", "example : True := trivial\n")
        self.trace("Demo/has space\nand newline", synthetic=True, log=[])
        self.assertEqual(c.restored_files(self.root), ["Demo/has space\nand newline.lean"])

    def test_unreadable_trace_counts_as_restored(self) -> None:
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.write(".lake/build/lib/lean/Demo/Base.trace", "{not json")
        self.assertEqual(c.restored_files(self.root), ["Demo/Base.lean"])

    def test_custom_source_directories_and_build_directory(self) -> None:
        self.write("lakefile.toml", 'name = "f"\nsrcDir = "src"\nbuildDir = "out"\n'
                   '[[lean_lib]]\nname = "Demo"\n[[lean_exe]]\nname = "t"\nsrcDir = "tools"\n')
        lib_dir, dirs = c.layout(self.root)
        self.assertEqual((lib_dir, dirs), (self.root / "out/lib/lean",
                                           [Path("src/tools"), Path("src")]))
        self.write("src/tools/Tool.lean", "def main : IO Unit := pure ()\n")
        self.write("out/lib/lean/Tool.trace", '{"synthetic": true}')
        self.assertEqual(c.trace_path("src/tools/Tool.lean", lib_dir, dirs),
                         self.root / "out/lib/lean/Tool.trace")
        self.assertIsNone(c.trace_path("Elsewhere/Tool.lean", lib_dir, dirs))
        self.assertEqual(c.restored_files(self.root), ["src/tools/Tool.lean"])


class MainTests(Fixture):
    def setUp(self) -> None:
        super().setUp()
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.trace("Demo/Base", synthetic=True, log=[])

    def run_main(self, returncode: int, output: str,
                 argv: list[str] | None = None) -> tuple[int, str, list[str]]:
        calls = []

        def elaborate(root, rel):
            calls.append(rel)
            return subprocess.CompletedProcess([], returncode, output)

        out, err = io.StringIO(), io.StringIO()
        with patch.object(c, "elaborate", side_effect=elaborate), \
             redirect_stdout(out), redirect_stderr(err):
            status = c.main(argv or [], self.root)
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

    def test_progress_announces_count_and_current_file_before_elaboration(self) -> None:
        self.trace("DemoTests/Client", synthetic=True, log=[])
        out = io.StringIO()

        def elaborate(root, rel):
            self.assertIn(rel, out.getvalue())
            self.assertNotIn("cleanly", out.getvalue())
            return subprocess.CompletedProcess([], 0, "")

        with patch.object(c, "elaborate", side_effect=elaborate) as run, \
             patch.object(c.time, "monotonic", side_effect=[10, 10.5, 12, 17]), \
             redirect_stdout(out):
            self.assertEqual(c.main(["--progress"], self.root), 0)
        self.assertEqual(run.call_count, 2)
        self.assertIn("checking 2 source(s) serially", out.getvalue())
        self.assertIn("[1/2]: Demo/Base.lean (elapsed 0.5s)", out.getvalue())
        self.assertIn("[2/2]: DemoTests/Client.lean (elapsed 2.0s)", out.getvalue())
        self.assertIn("cleanly (2) in 7.0s", out.getvalue())

    def test_ci_is_quiet_by_default_but_progress_can_be_requested(self) -> None:
        with patch.dict(os.environ, {"CI": "true"}):
            self.assertNotIn("Cache-restore audit", self.run_main(0, "")[1])
            self.assertIn("Cache-restore audit", self.run_main(0, "", ["--progress"])[1])
        with patch.dict(os.environ, {"CI": ""}):
            self.assertIn("Cache-restore audit", self.run_main(0, "")[1])
            self.assertNotIn("Cache-restore audit", self.run_main(0, "", ["--quiet"])[1])

    def test_quiet_does_not_hide_warnings_or_change_failure(self) -> None:
        status, out, calls = self.run_main(0, "warning: retained\n", ["--quiet"])
        self.assertEqual((status, calls), (1, ["Demo/Base.lean"]))
        self.assertNotIn("Cache-restore audit", out)
        self.assertIn("FAIL  Demo/Base.lean", out)
        self.assertIn("warning: retained", out)
        self.assertIn("Audit elapsed", out)

    def test_cancellation_does_not_continue_or_report_completion(self) -> None:
        self.trace("DemoTests/Client", synthetic=True, log=[])
        out = io.StringIO()
        with patch.object(c, "elaborate", side_effect=KeyboardInterrupt) as run, \
             redirect_stdout(out), self.assertRaises(KeyboardInterrupt):
            c.main(["--progress"], self.root)
        self.assertEqual(run.call_count, 1)
        self.assertIn("[1/2]: Demo/Base.lean", out.getvalue())
        self.assertNotIn("[2/2]", out.getvalue())
        self.assertNotIn("cleanly", out.getvalue())

    def test_invalid_scope_fails_instead_of_becoming_an_empty_check(self) -> None:
        for contents in ('{"files": []}', '[1]', '["missing.lean"]', 'null', 'not JSON'):
            with self.subTest(contents=contents):
                scope = self.root / "scope.json"
                scope.write_text(contents)
                with redirect_stderr(io.StringIO()):
                    self.assertEqual(c.main(["--files-from", str(scope)], self.root), 1)

    def test_explicit_json_scope_excludes_unaffected_restores(self) -> None:
        self.trace("DemoTests/Client", synthetic=True, log=[])
        scope = self.root / "scope.json"
        scope.write_text(json.dumps(["DemoTests/Client.lean"]))
        with patch.object(c, "elaborate", return_value=subprocess.CompletedProcess([], 0, "")) as run, \
             redirect_stdout(io.StringIO()):
            self.assertEqual(c.main(["--files-from", str(scope)], self.root), 0)
        self.assertEqual(run.call_args.args, (self.root, "DemoTests/Client.lean"))


class IsolatedLakeFixture(Fixture):
    """A dependency-free project using the installed toolchain and a private artifact cache.

    CI's "Test Python tooling" step runs before Lean is installed, so CI skips this test; it runs
    in a local `scripts/check.sh` or `python3 -m unittest` with the repository's toolchain.
    """

    def setUp(self) -> None:
        # CI runs Python tests before installing Lean.
        if not shutil.which("lake"):
            self.skipTest("installed Lean toolchain unavailable")
        toolchain = (REPO / "lean-toolchain").read_text().strip()
        if shutil.which("elan"):
            listed = subprocess.run(["elan", "toolchain", "list"], capture_output=True, text=True)
            if toolchain not in listed.stdout:
                self.skipTest("repository Lean toolchain not installed")
        version = subprocess.run(["lake", "--version"], cwd=REPO, capture_output=True, text=True)
        if version.returncode or f"Lean version {toolchain.rsplit(':v', 1)[-1]})" not in version.stdout:
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
        return subprocess.run(["lake", *args], cwd=self.root, capture_output=True, text=True,
                              timeout=120)


class RealLakeTests(IsolatedLakeFixture):
    """Lake restores a warned module without its messages; the warning audit catches it."""

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

    def test_changed_import_makes_unchanged_restored_client_warn_in_full_and_quick_checks(self) -> None:
        self.write("Demo/Base.lean", "def value : Nat := 1\ndef oldValue : Nat := value\n")
        self.write("DemoTests/Client.lean", "import Demo.Base\nexample : Nat := oldValue\n")
        self.assert_unchanged_warning(
            'def value : Nat := 1\n@[deprecated value (since := "2026-11-11")]\n'
            'def oldValue : Nat := value\n', "DemoTests/Client.lean")

    def test_unchanged_aggregate_import_warning_is_checked(self) -> None:
        self.write("DemoTests/Client.lean", "import Demo\nexample : Nat := value\n")
        self.assert_unchanged_warning(
            'def value : Nat := 1\ndeprecated_module (since := "2026-11-11")\n', "Demo.lean")

    def assert_unchanged_warning(self, edited_base: str, warning_file: str) -> None:
        """A changed import can hide a warning in any unchanged source on a built client's path."""
        # Run quick mode's actual subprocess audit in this private project, stopping at its failure.
        for name in ("quick_check.py", "check_progress.py", "check_cache_restores.py", "QuickImports.lean"):
            self.write(f"scripts/{name}", (REPO / "scripts" / name).read_text())
        baseline = self.lake("build", "--wfail", "--iofail", "DemoTests.Client")
        self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)
        self.commit()  # include the generated manifest before measuring the Lean-only change
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.write("Demo/Base.lean", edited_base)
        populate = self.lake("build", "DemoTests.Client")
        self.assertEqual(populate.returncode, 0, populate.stdout + populate.stderr)
        self.assertIn("deprecated", populate.stdout + populate.stderr)
        self.assertEqual(self.git("diff", "--name-only"), "Demo/Base.lean")
        shutil.rmtree(self.root / ".lake/build")  # only this fixture's disposable outputs
        restored = self.lake("build", "--wfail", "--iofail", "DemoTests.Client")
        self.assertEqual(restored.returncode, 0, restored.stdout + restored.stderr)
        self.assertTrue(c.restored(self.root / ".lake/build/lib/lean/DemoTests/Client.trace"))
        for check in (c.main, quick.main):
            with self.subTest(check=check.__module__):
                out = io.StringIO()
                with redirect_stdout(out), redirect_stderr(out):
                    self.assertEqual(check([], self.root), 1, out.getvalue())
                self.assertIn("deprecated", out.getvalue())
                self.assertIn(f"FAIL  {warning_file}", out.getvalue())


if __name__ == "__main__":
    unittest.main()
