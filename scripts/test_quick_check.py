"""Quick-plan safety and command dispatch, with a real broken importing-client fixture."""

import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("quick_check", Path(__file__).with_name("quick_check.py"))
quick = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = quick
SPEC.loader.exec_module(quick)
REPO = Path(__file__).resolve().parent.parent


class QuickCheckTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Quick fixture")
        self.git("config", "user.email", "quick@example.invalid")
        self.write(".gitignore", ".lake/\n")
        self.write("lakefile.toml", 'name = "quickfixture"\n[[lean_lib]]\nname = "Demo"\n'
                   '[[lean_lib]]\nname = "DemoTests"\n')
        self.write("Demo.lean", "import Demo.Base\nimport Demo.Middle\n")
        self.write("Demo/Base.lean", "def value : Nat := 1\n")
        self.write("Demo/Middle.lean", "import Demo.Base\ndef middle := value\n")
        self.write("DemoTests.lean", "import DemoTests.Client\nimport DemoTests.AllClient\n")
        self.write("DemoTests/Client.lean", "import Demo.Middle\nexample : Nat := middle\n")
        self.write("DemoTests/AllClient.lean", "import Demo\nexample : Nat := value\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, text=True).strip()

    def commit(self):
        self.git("add", ".")
        self.git("commit", "-qm", "fixture")

    @staticmethod
    def simple_headers(root, paths):
        # Deliberately only for graph fixtures; production and parser tests use Lean's parser.
        return {p: re.findall(r"^import ([\w.]+)", (root / p).read_text(), re.M) for p in paths}

    def plan(self, base="origin/main"):
        return quick.make_plan(self.root, base, parser=self.simple_headers)

    def test_transitive_clients_and_clients_importing_aggregate(self):
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.assertEqual(self.plan().targets,
                         ["Demo.Base", "Demo.Middle", "DemoTests.AllClient", "DemoTests.Client"])

    def use_glob_test_library(self, globs='["DemoTests.+"]'):
        """Switch the fixture's test library to the repository's glob layout: no aggregator."""
        self.write("lakefile.toml", 'name = "quickfixture"\n[[lean_lib]]\nname = "Demo"\n'
                   f'[[lean_lib]]\nname = "DemoTests"\nroots = []\nglobs = {globs}\n')
        (self.root / "DemoTests.lean").unlink()
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")

    def test_glob_test_library_plans_affected_tests(self):
        self.use_glob_test_library()
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.assertEqual(self.plan().targets,
                         ["Demo.Base", "Demo.Middle", "DemoTests.AllClient", "DemoTests.Client"])

    def test_other_glob_layouts_fall_back(self):
        self.use_glob_test_library('["DemoTests.*"]')
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        with self.assertRaises(quick.FullCheck):
            self.plan()

    def test_glob_library_with_aggregator_falls_back(self):
        self.use_glob_test_library()
        self.write("DemoTests.lean", "import DemoTests.Client\n")
        with self.assertRaises(quick.FullCheck):
            self.plan()

    def test_test_helper_and_diamond(self):
        self.write("DemoTests/Helper.lean", "import Demo.Middle\n")
        self.write("DemoTests/Client.lean", "import Demo.Base\nimport DemoTests.Helper\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.assertEqual(self.plan().targets.count("DemoTests.Client"), 1)
        self.assertIn("DemoTests.Helper", self.plan().targets)

    def test_all_git_change_layers(self):
        self.write("Demo/Committed.lean", "def committed := 1\n")
        self.commit()
        self.write("Demo/Staged.lean", "def staged := 1\n")
        self.git("add", "Demo/Staged.lean")
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.write("Demo/Untracked.lean", "def untracked := 1\n")
        selected = set(self.plan().targets)
        self.assertTrue({"Demo.Committed", "Demo.Staged", "Demo.Base", "Demo.Untracked"} <= selected)

    def test_relocated_source_directory(self):
        with (self.root / "lakefile.toml").open("a") as f:
            f.write('[[lean_lib]]\nname = "Abstracts"\nsrcDir = "abstracts"\n')
        self.write("abstracts/Abstracts.lean", "import Abstracts.Topic\n")
        self.write("abstracts/Abstracts/Topic.lean", "import Demo.Base\n")
        self.write("DemoTests/Client.lean", "import Abstracts\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.assertIn("Abstracts.Topic", self.plan().targets)
        self.assertIn("DemoTests.Client", self.plan().targets)

    def test_explicit_base_uses_merge_base(self):
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.commit()
        self.assertEqual(self.plan("origin/main").base, self.git("rev-parse", "origin/main"))

    def test_clean_checkout_is_valid_empty_plan(self):
        self.assertEqual(self.plan().targets, [])

    def test_missing_base_is_not_empty_success(self):
        with self.assertRaises(quick.FullCheck):
            self.plan("missing-reference")

    def test_ambiguous_base_falls_back(self):
        self.git("branch", "shared-name")
        self.git("tag", "shared-name")
        with self.assertRaises(quick.FullCheck):
            self.plan("shared-name")

    def test_unmerged_entries_fall_back(self):
        original = quick.git
        with patch.object(quick, "git", side_effect=lambda r, *a: "unmerged" if a[0] == "ls-files"
                          else original(r, *a)):
            with self.assertRaises(quick.FullCheck):
                self.plan()

    def test_nonlean_pin_config_and_aggregate_changes_fall_back(self):
        for path in ["README.md", "lean-toolchain", "lake-manifest.json", "lakefile.toml", "Demo.lean"]:
            with self.subTest(path=path):
                old = (self.root / path).read_text() if (self.root / path).exists() else None
                self.write(path, (old or "") + "\n-- changed\n")
                with self.assertRaises(quick.FullCheck):
                    self.plan()
                if old is None:
                    (self.root / path).unlink()
                else:
                    self.write(path, old)

    def test_deleted_or_renamed_module_falls_back(self):
        (self.root / "Demo/Base.lean").rename(self.root / "Demo/Renamed.lean")
        with self.assertRaises(quick.FullCheck):
            self.plan()

    def test_unknown_library_options_fall_back(self):
        with (self.root / "lakefile.toml").open("a") as f:
            f.write('roots = ["Other"]\n')
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        with self.assertRaises(quick.FullCheck):
            self.plan()

    def test_missing_local_import_falls_back(self):
        self.write("Demo/Middle.lean", "import Demo.Missing\n")
        with self.assertRaises(quick.FullCheck):
            self.plan()

    def add_executable(self, imports, name="demoTool"):
        with (self.root / "lakefile.toml").open("a") as config:
            config.write(f'[[lean_exe]]\nname = "{name}"\nroot = "Tool"\nsrcDir = "tools"\n')
        self.write("tools/Tool.lean", imports + "\ndef main : IO Unit := pure ()\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")

    def test_executable_importing_changed_library_is_built_explicitly(self):
        self.add_executable("import Demo.Base")
        self.write("Demo/Base.lean", "def value : Bool := true\n")
        self.assertIn("@/demoTool", self.plan().targets)

    def test_executable_local_helper_cannot_hide_an_importing_client(self):
        self.write("tools/Helper.lean", "import Demo.Base\ndef result : Nat := value\n")
        self.add_executable("import Helper")
        self.write("Demo/Base.lean", "def value : Bool := true\n")
        self.assertIn("@/demoTool", self.plan().targets)

    def test_hyphenated_executable_name_is_built_explicitly(self):
        self.add_executable("import Demo.Base", "demo-tool")
        self.write("Demo/Base.lean", "def value : Bool := true\n")
        self.assertIn("@/demo-tool", self.plan().targets)

    def test_shared_executable_root_uses_normalized_source_identity(self):
        (self.root / "tools").mkdir()
        with (self.root / "lakefile.toml").open("a") as config:
            config.write('[[lean_exe]]\nname = "demoTool"\nroot = "Demo.Base"\n'
                         'srcDir = "tools/.."\n')
        self.write("Demo/Base.lean", "import Init\ndef value : Nat := 1\n"
                   "def main : IO Unit := pure ()\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.write("Demo/Base.lean", "import Init\ndef value : Nat := 2\n"
                   "def main : IO Unit := pure ()\n")
        self.assertIn("@/demoTool", self.plan().targets)

    def test_dependency_only_executables_preserve_quick_plan(self):
        self.add_executable("import Lean\nimport Mathlib.Lean.CoreM")
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.assertEqual(self.plan().targets,
                         ["Demo.Base", "Demo.Middle", "DemoTests.AllClient", "DemoTests.Client"])

    def test_clean_checkout_with_local_executable_still_has_empty_plan(self):
        self.add_executable("import Demo.Base")
        self.assertEqual(self.plan().targets, [])

    def test_ignored_source_falls_back(self):
        self.write(".gitignore", ".lake/\nDemo/Hidden.lean\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.write("Demo/Hidden.lean", "def hidden := 1\n")
        with self.assertRaises(quick.FullCheck):
            self.plan()

    def test_source_symlink_cannot_escape_checkout(self):
        outside = tempfile.TemporaryDirectory()
        self.addCleanup(outside.cleanup)
        target = Path(outside.name) / "outside.lean"
        target.write_text("def outside := 1\n")
        (self.root / "Demo/Linked.lean").symlink_to(target)
        with self.assertRaises(quick.FullCheck):
            self.plan()

    def test_parser_failure_falls_back(self):
        with self.assertRaises(quick.FullCheck):
            quick.make_plan(self.root, parser=lambda *_: (_ for _ in ()).throw(quick.FullCheck("bad header")))

    def test_tracked_nested_directory_symlink_falls_back(self):
        self.write("Outside/Client.lean", "import Demo.Base\nexample : Nat := value\n")
        (self.root / "Demo/Linked").symlink_to("../Outside", target_is_directory=True)
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.write("Demo/Base.lean", "def value : Bool := true\n")
        with self.assertRaisesRegex(quick.FullCheck, "symlinked source"):
            self.plan()

    def test_library_root_directory_symlink_falls_back(self):
        (self.root / "Demo").rename(self.root / "ActualDemo")
        (self.root / "Demo").symlink_to("ActualDemo", target_is_directory=True)
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        with self.assertRaisesRegex(quick.FullCheck, "symlinked source"):
            self.plan()

    def test_overlapping_source_module_identities_fall_back(self):
        with (self.root / "lakefile.toml").open("a") as f:
            f.write('[[lean_lib]]\nname = "Base"\nsrcDir = "Demo"\n')
        self.write("Demo/Base/Extra.lean", "def extra : Nat := 1\n")
        self.write("DemoTests/Client.lean", "import Demo.Base.Extra\nexample : Nat := extra\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.write("Demo/Base/Extra.lean", "def extra : Bool := true\n")
        with self.assertRaisesRegex(quick.FullCheck, "overlapping library source"):
            self.plan()

    def test_fallback_runs_default_check_without_quick_argument(self):
        with patch.object(quick, "make_plan", side_effect=quick.FullCheck("unsafe")), \
             patch.object(quick.subprocess, "run") as run:
            run.return_value.returncode = 7
            self.assertEqual(quick.main([], self.root), 7)
            self.assertEqual(run.call_args.args[0], [str(self.root / "scripts/check.sh")])

    def test_default_command_keeps_six_gate_order_and_rejects_unknown_args(self):
        self.write("scripts/check.sh", (REPO / "scripts/check.sh").read_text())
        self.write("scripts/cache/ensure.sh", "#!/usr/bin/env bash\nexit 0\n")
        (self.root / "scripts/cache/ensure.sh").chmod(0o755)
        self.write("bin/lake", '#!/usr/bin/env python3\nimport json,os,sys\n'
                   'with open(os.environ["QUICK_COMMAND_LOG"], "a") as f:\n'
                   ' f.write(json.dumps(sys.argv[1:])+"\\n")\n')
        (self.root / "bin/lake").chmod(0o755)
        log = self.root / "commands.jsonl"
        env = {**os.environ, "PATH": str(self.root / "bin") + os.pathsep + os.environ["PATH"],
               "QUICK_COMMAND_LOG": str(log)}
        command = ["bash", str(self.root / "scripts/check.sh")]
        result = subprocess.run(command, cwd=self.root, env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual([json.loads(x) for x in log.read_text().splitlines()], [
            ["build", "--wfail", "--iofail"], ["exe", "mk_all", "--check"],
            ["test", "--wfail", "--iofail"], ["lint"], ["exe", "lint-style"],
            ["exe", "checkInitImports"]])
        log.unlink()
        bad = subprocess.run([*command, "--not-an-option"], cwd=self.root, env=env,
                             capture_output=True, text=True)
        self.assertEqual(bad.returncode, 2)
        self.assertFalse(log.exists())

    def test_quick_failure_from_importing_client_is_not_dropped(self):
        self.write("Demo/Base.lean", "def value : Bool := true\n")
        original = quick.make_plan
        calls = []

        def run(root, command, label):
            calls.append(command)
            return 1 if "DemoTests.Client" in command else 0

        with patch.object(quick, "make_plan", side_effect=lambda r, b: original(r, b, parser=self.simple_headers)), \
             patch.object(quick, "run_check", side_effect=run):
            self.assertEqual(quick.main([], self.root), 1)
        self.assertIn("DemoTests.Client", calls[0])
        self.assertEqual(calls[0][1:4], ["build", "--wfail", "--iofail"])


class NativeLeanTests(unittest.TestCase):
    write = QuickCheckTests.write
    git = QuickCheckTests.git
    commit = QuickCheckTests.commit
    add_executable = QuickCheckTests.add_executable

    def setUp(self):
        # CI runs Python tests before installing Lean; always run planner/dispatch tests above.
        if not shutil.which("elan"):
            self.skipTest("installed Lean toolchain unavailable")
        toolchain = (REPO / "lean-toolchain").read_text().strip()
        check = subprocess.run(["elan", "toolchain", "list"], capture_output=True, text=True)
        if toolchain not in check.stdout:
            self.skipTest("repository Lean toolchain not installed")
        QuickCheckTests.setUp(self)
        self.write("lean-toolchain", toolchain + "\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")

    def test_native_public_meta_and_nested_comment_headers(self):
        self.write("Demo/Base.lean", '/- outer /- inner -/ comment -/\nmodule\n'
                   'public import Init\npublic meta import Lean\n\ndef value := 1\n')
        parsed = quick.imports_from_lean(self.root, ["Demo/Base.lean"])
        self.assertIn("Init", parsed["Demo/Base.lean"])
        self.assertIn("Lean", parsed["Demo/Base.lean"])

    def test_native_header_error_cannot_be_an_empty_graph(self):
        self.write("Demo/Base.lean", "/- unterminated comment")
        with self.assertRaises(quick.FullCheck):
            quick.make_plan(self.root)

    def test_real_broken_importing_client_fails_selected_build(self):
        # No project build: a tiny dependency-free Lake fixture catches omitted consumers.
        baseline = subprocess.run(["lake", "build", "DemoTests.Client"], cwd=self.root,
                                  capture_output=True, text=True)
        self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.write("Demo/Base.lean", "def value : Bool := true\n")
        plan = quick.make_plan(self.root)
        self.assertIn("DemoTests.Client", plan.targets)
        broken = subprocess.run(["lake", "build", "--wfail", "--iofail", *plan.targets],
                                cwd=self.root, capture_output=True, text=True)
        self.assertNotEqual(broken.returncode, 0)
        self.assertIn("DemoTests/Client.lean", broken.stdout + broken.stderr)

    def test_nondefault_executable_client_is_not_omitted(self):
        self.add_executable("import Demo.Base")
        self.write("tools/Tool.lean", "import Demo.Base\ndef main : IO Unit := IO.println (value : Nat)\n")
        baseline = subprocess.run(["lake", "build", "@/demoTool"], cwd=self.root,
                                  capture_output=True, text=True)
        self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.write("Demo/Base.lean", "def value : Bool := true\n")
        plan = quick.make_plan(self.root)
        self.assertIn("@/demoTool", plan.targets)
        broken = subprocess.run(["lake", "build", "--wfail", "--iofail", *plan.targets],
                                cwd=self.root, capture_output=True, text=True)
        self.assertNotEqual(broken.returncode, 0)
        self.assertIn("tools/Tool.lean", broken.stdout + broken.stderr)


if __name__ == "__main__":
    unittest.main()
