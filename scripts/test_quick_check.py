"""Quick-plan safety and command dispatch, with a real broken importing-client fixture."""

import importlib.util
import io
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
# The audit of affected files restored from the artifact cache, run after the build (#4523).
RESTORES = [sys.executable, "-B", "scripts/check_cache_restores.py"]


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
        # Ignore the user's Git configuration: `tag.gpgsign`, for one, makes `git tag` open an
        # editor for a message.
        env = {**os.environ, "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}
        return subprocess.check_output(["git", *args], cwd=self.root, env=env, text=True).strip()

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
        plan = self.plan()
        self.assertEqual(plan.targets,
                         ["Demo.Base", "Demo.Middle", "DemoTests.AllClient", "DemoTests.Client"])
        self.assertEqual(plan.restore_files,
                         ["Demo/Base.lean", "Demo/Middle.lean", "DemoTests/AllClient.lean",
                          "DemoTests/Client.lean"])
        self.assertEqual(plan.restore_built, ["Demo.lean"])

    def test_unused_aggregate_is_not_audited_or_built(self):
        (self.root / "DemoTests/AllClient.lean").unlink()
        self.write("DemoTests.lean", "import DemoTests.Client\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.write(".lake/build/lib/lean/Demo.trace", '{"synthetic": true}')
        self.assertEqual(self.plan().restore_built, [])

    def record_command(self, command, plan):
        """Read the audit's temporary manifest while it exists, then normalize its random path."""
        if command[:3] == RESTORES:
            self.assertEqual(command[3], "--files-from")
            self.assertEqual(json.loads(Path(command[4]).read_text()), plan.restore_files)
            self.assertEqual(command[5:], [part for path in plan.restore_built
                                          for part in ("--built-under", path)])
            return RESTORES
        return command

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
            f.write('[[lean_lib]]\nname = "Relocated"\nsrcDir = "relocated"\n')
        self.write("relocated/Relocated.lean", "import Relocated.Topic\n")
        self.write("relocated/Relocated/Topic.lean", "import Demo.Base\n")
        self.write("DemoTests/Client.lean", "import Relocated\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.assertIn("Relocated.Topic", self.plan().targets)
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

    def test_aggregate_importing_only_added_modules_keeps_the_quick_plan(self):
        self.write("Demo/Added.lean", "import Demo.Base\ndef added := value\n")
        # The aggregate's own importing client is built; the aggregate is audited, not targeted.
        for text in ("import Demo.Added\nimport Demo.Base\nimport Demo.Middle\n",
                     # What `lake exe mk_all` writes, as in `CslibFrontier.lean`.
                     "import Demo.Base\nimport Demo.Middle\npublic import Demo.Added\n"):
            with self.subTest(text=text):
                self.write("Demo.lean", text)
                plan = self.plan()
                self.assertEqual(plan.targets, ["Demo.Added", "DemoTests.AllClient"])
                self.assertEqual(plan.restore_built, ["Demo.lean"])

    def test_aggregate_edit_beyond_added_imports_falls_back(self):
        self.write("Demo/Added.lean", "def added := 1\n")
        cases = {
            # A module that exists at the base is not one this change adds.
            "an existing module": "import Demo.Base\nimport Demo.Middle\nimport Demo.Middle\n",
            "a removed import": "import Demo.Base\nimport Demo.Added\n",
            "a reordered import": "import Demo.Middle\nimport Demo.Base\nimport Demo.Added\n",
            "a trailing comment": "import Demo.Base\nimport Demo.Middle\nimport Demo.Added -- new\n",
            "other text": "import Demo.Base\nimport Demo.Middle\nimport Demo.Added\n-- note\n",
            "no added import": "import Demo.Base\nimport Demo.Middle\n\n",
        }
        for name, text in cases.items():
            with self.subTest(name):
                self.write("Demo.lean", text)
                with self.assertRaisesRegex(quick.FullCheck, "aggregate Demo changed beyond"):
                    self.plan()

    def test_encoding_baseline_change_runs_its_lint_instead_of_falling_back(self):
        baseline = "scripts/encoding_readability_baseline.json"
        self.write(baseline, "{}\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        base = self.git("rev-parse", "HEAD")
        lint = ("encoding readability ratchet",
                [sys.executable, "-B", "scripts/check_encoding_readability.py", "--base", base])
        self.write(baseline, '{"Demo/Base.lean": {}}\n')
        plan = self.plan()
        self.assertEqual((plan.targets, plan.checks), ([], [lint]))
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        plan = self.plan()
        self.assertEqual(plan.checks, [lint])
        self.assertIn("DemoTests.Client", plan.targets)
        # Code under `scripts/`, other data files and a deleted baseline still fall back.
        for path in ("scripts/check_encoding_readability.py", "scripts/tidy_surface_baseline.json"):
            with self.subTest(path=path):
                self.write(path, "changed\n")
                with self.assertRaisesRegex(quick.FullCheck, "non-Lean change"):
                    self.plan()
                (self.root / path).unlink()
        (self.root / baseline).unlink()
        with self.assertRaisesRegex(quick.FullCheck, "deleted"):
            self.plan()

    def test_projection_baseline_change_runs_its_ratchet_instead_of_falling_back(self):
        baseline = "scripts/projection_chains_baseline.json"
        self.write(baseline, '{"Demo/Base.lean": 3}\n')
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        base = self.git("rev-parse", "HEAD")
        ratchet = ("projection chain ratchet",
                   [sys.executable, "-B", "scripts/check_projection_chains.py", "--base", base])
        # A migration lowers the entry together with the Lean change that removes the chains.
        self.write(baseline, "{}\n")
        plan = self.plan()
        self.assertEqual((plan.targets, plan.checks), ([], [ratchet]))
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        plan = self.plan()
        self.assertEqual(plan.checks, [ratchet])
        self.assertIn("DemoTests.Client", plan.targets)
        (self.root / baseline).unlink()
        with self.assertRaisesRegex(quick.FullCheck, "deleted"):
            self.plan()

    def test_data_checks_run_before_the_build_and_stop_it_on_failure(self):
        plan = quick.Plan("base", ["Demo.Base"], [("lint", ["lint", "--base", "base"])])
        for lint_status, expected in ((0, [["lint", "--base", "base"],
                                           ["lake", "build", "--wfail", "--iofail", "Demo.Base"],
                                           RESTORES,
                                           ["lake", "exe", "mk_all", "--check"]]),
                                      (3, [["lint", "--base", "base"]])):
            with self.subTest(lint_status=lint_status):
                calls = []

                def run(root, command, label):
                    calls.append(self.record_command(command, plan))
                    return lint_status if command[0] == "lint" else 0

                with patch.object(quick, "make_plan", return_value=plan), \
                     patch.object(quick, "run_check", side_effect=run):
                    self.assertEqual(quick.main([], self.root), lint_status)
                self.assertEqual(calls, expected)

    def use_lint_driver(self, extra=""):
        """Configure runLinter for the default `Demo` and `Other` libraries; tests stay unlinted.

        `Demo.Side` is a second importer of `Demo.Base`, and `Other.Use` one in another package.
        """
        self.write("lakefile.toml", 'name = "quickfixture"\nlintDriver = "batteries/runLinter"\n'
                   'defaultTargets = ["Demo", "Other"]\n' + extra + '[[lean_lib]]\nname = "Demo"\n'
                   '[[lean_lib]]\nname = "DemoTests"\n[[lean_lib]]\nname = "Other"\n')
        self.write("Demo.lean", "import Demo.Base\nimport Demo.Middle\nimport Demo.Side\n")
        self.write("Demo/Side.lean", "import Demo.Base\ndef side := value\n")
        self.write("Other.lean", "import Other.Use\n")
        self.write("Other/Use.lean", "import Demo.Middle\ndef use := middle\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")

    def test_lint_lists_affected_library_modules_and_lints_each_package_through_its_clients(self):
        self.use_lint_driver()
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        plan = self.plan()
        # `Demo.Base` is checked once, through one of its two importers in `Demo`. `Other.Use`
        # imports it too, but linting `Other.Use` covers only package `Other`.
        self.assertEqual(plan.lint, {"Demo.Middle": ["Demo.Base", "Demo.Middle"],
                                     "Demo.Side": ["Demo.Side"], "Other.Use": ["Other.Use"]})
        self.assertIn("DemoTests.Client", plan.targets)

    def test_lint_scope_without_driver_or_library_changes(self):
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.assertEqual(self.plan().lint, {})
        self.use_lint_driver()
        self.write("DemoTests/Client.lean", "import Demo.Middle\nexample : Nat := middle + 1\n")
        self.assertEqual(self.plan().lint, {})

    def test_other_lint_driver_or_changed_linter_falls_back(self):
        self.write("lakefile.toml", 'lintDriver = "other/driver"\n'
                   + (self.root / "lakefile.toml").read_text())
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        with self.assertRaisesRegex(quick.FullCheck, "lint driver"):
            self.plan()
        self.use_lint_driver()
        self.write("Demo/Base.lean", "@[env_linter] def value : Nat := 2\n")
        with self.assertRaisesRegex(quick.FullCheck, "linter"):
            self.plan()

    def test_lint_runs_one_process_per_target_after_the_build(self):
        lint = {"Demo.Middle": ["Demo.Base", "Demo.Middle"], "Demo.Side": ["Demo.Side"]}
        plan = quick.Plan("base", ["Demo.Base", "Demo.Middle", "Demo.Side"], [], lint)
        for lint_status in (0, 5):
            with self.subTest(lint_status=lint_status):
                calls, listings = [], []

                def run(root, command, label):
                    calls.append(self.record_command(command, plan))
                    if command[:2] == ["lake", "lint"]:
                        listing = Path(command[4].removeprefix("--only-modules="))
                        listings.append(listing)
                        self.assertEqual(listing.read_text().split(), lint[command[5]])
                        # The first target fails; the second still runs, reporting all failures.
                        return lint_status if len(listings) == 1 else 0
                    return 0

                with patch.object(quick, "make_plan", return_value=plan), \
                     patch.object(quick, "run_check", side_effect=run):
                    self.assertEqual(quick.main([], self.root), lint_status)
                expected = [["lake", "build", "--wfail", "--iofail", *plan.targets], RESTORES,
                            *(["lake", "lint", "--", "--no-build", f"--only-modules={listing}",
                               target] for listing, target in zip(listings, lint))]
                if not lint_status:
                    expected.append(["lake", "exe", "mk_all", "--check"])
                self.assertEqual(calls, expected)
                self.assertEqual(len(listings), 2)
                self.assertFalse(any(listing.exists() for listing in listings))

    def test_cache_restore_audit_follows_the_build_and_stops_on_failure(self):
        for targets, audit_status, expected in (
                (["Demo.Base"], 4, [["lake", "build", "--wfail", "--iofail", "Demo.Base"],
                                    RESTORES]),
                # Without Lean changes nothing was built, so there is nothing to audit.
                ([], 4, [["lake", "exe", "mk_all", "--check"]])):
            with self.subTest(targets=targets):
                calls = []
                plan = quick.Plan("base", targets, [], restore_files=["Demo/Base.lean"])

                def run(root, command, label):
                    command = self.record_command(command, plan)
                    calls.append(command)
                    return audit_status if command == RESTORES else 0

                with patch.object(quick, "make_plan", return_value=plan), \
                     patch.object(quick, "run_check", side_effect=run):
                    self.assertEqual(quick.main([], self.root), audit_status if targets else 0)
                self.assertEqual(calls, expected)

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
        plan = self.plan()
        self.assertIn("@/demoTool", plan.targets)
        self.assertIn("tools/Tool.lean", plan.restore_files)
        self.assertEqual(plan.restore_built, ["Demo.lean", "DemoTests.lean", "tools"])

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

    def test_fallback_runs_full_check_with_the_same_base(self):
        with patch.object(quick, "make_plan", side_effect=quick.FullCheck("unsafe")), \
             patch.object(quick.subprocess, "run") as run:
            run.return_value.returncode = 7
            self.assertEqual(quick.main([], self.root), 7)
            self.assertEqual(run.call_args.args[0],
                             [str(self.root / "scripts/check.sh"), "--base", "origin/main"])
            self.assertEqual(quick.main(["--base", "example-base"], self.root), 7)
            self.assertEqual(run.call_args.args[0],
                             [str(self.root / "scripts/check.sh"), "--base", "example-base"])

    def test_no_full_fallback_reports_the_reason_without_running_the_full_check(self):
        with patch.object(quick, "make_plan", side_effect=quick.FullCheck("unsafe")), \
             patch.object(quick.subprocess, "run") as run, \
             patch("sys.stdout", new_callable=io.StringIO) as out:
            self.assertEqual(quick.main(["--no-full-fallback"], self.root), quick.NO_FALLBACK_STATUS)
        run.assert_not_called()
        self.assertIn("cannot plan this change: unsafe", out.getvalue())

    def test_changed_library_and_test_files_get_source_checks(self):
        base = self.git("rev-parse", "HEAD")
        hygiene = [sys.executable, "-B", "scripts/check_hygiene.py", "--check-simp", "--"]
        encoding = ("encoding readability ratchet",
                    [sys.executable, "-B", "scripts/check_encoding_readability.py", "--base", base])
        projection = ("projection chain ratchet",
                      [sys.executable, "-B", "scripts/check_projection_chains.py", "--base", base])
        source_lints = ("changed-file source lints (doc-name lint skipped)",
                        [sys.executable, "-B", "scripts/check_changed_files.py", "--base", base,
                         "--source-only"])
        labels = ["source hygiene (changed files)", source_lints[0],
                  "encoding readability ratchet", "projection chain ratchet"]
        with patch.object(quick, "HYGIENE_ROOTS", ("Demo/", "DemoTests/")), \
             patch.object(quick, "RATCHET_ROOT", "Demo/"):
            self.write("DemoTests/Client.lean", "import Demo.Middle\nexample : Nat := middle + 0\n")
            self.assertEqual(self.plan().checks, [
                ("source hygiene (changed files)", [*hygiene, "DemoTests/Client.lean"]),
                source_lints])
            self.write("Demo/Base.lean", "def value : Nat := 2\n")
            self.assertEqual(self.plan().checks, [
                ("source hygiene (changed files)",
                 [*hygiene, "Demo/Base.lean", "DemoTests/Client.lean"]), source_lints, encoding,
                projection])
            # A changed baseline already selects its ratchet; each ratchet runs once.
            for baseline in ("scripts/encoding_readability_baseline.json",
                             "scripts/projection_chains_baseline.json"):
                with self.subTest(baseline=baseline):
                    self.write(baseline, "{}\n")
                    self.assertEqual(sorted(label for label, _ in self.plan().checks),
                                     sorted(labels))
        # The aggregates sit outside both roots, as `CslibFrontier.lean` does.
        self.assertEqual(quick.HYGIENE_ROOTS, ("CslibFrontier/", "CslibFrontierTests/"))

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


class LocalManualGateTests(unittest.TestCase):
    """Exercise the shell entry point with a real checker and no Lean or publishing tools."""

    write = QuickCheckTests.write

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="cslib-frontier-manual-gates-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for source in ("scripts/check.sh", "scripts/check_operator_manual.py", "manual/data/visuals.py"):
            self.write(source, (REPO / source).read_text())
        self.write("manual/README.md", "# Manual\n\n[Drivers](AGENT_OPERATORS.md)\n"
                   "[Example](workflows/example.md)\n")
        self.write("manual/AGENT_OPERATORS.md", "# Directing agents\n")
        self.write("Client.lean", "example : True := .intro\n")
        self.write("manual/workflows/example.md", "# First client\n\n[Source](../../Client.lean)\n\n"
                   "<!-- excerpt: first -->\n```lean\nexample : True := .intro\n```\n")
        self.write("manual/workflows/data/test-excerpts.json", json.dumps([{
            "id": "first", "document": "workflows/example.md", "source_path": "Client.lean"}]))
        # The production controls run separately in this suite. This small test script lets us
        # force their nonzero status and check that the shell does not discard it.
        self.write("scripts/test_operator_manual.py", "import os, unittest\n"
                   "class Controls(unittest.TestCase):\n"
                   " def test_control(self):\n"
                   "  self.assertNotEqual(os.environ.get('MANUAL_TEST_FAILURE'), '1')\n"
                   "unittest.main()\n")
        self.write("scripts/check_vm_map_count.py", "raise SystemExit(0)\n")
        recorder = ('#!/usr/bin/env python3\nimport json,os,sys\n'
                    'with open(os.environ["QUICK_COMMAND_LOG"], "a") as f:\n'
                    ' f.write(json.dumps([sys.argv[0].split("/")[-1], *sys.argv[1:]])+"\\n")\n')
        for path in ("bin/lake", "scripts/cache/ensure.sh", "scripts/quick_check.py",
                     "scripts/full_check.py"):
            self.write(path, recorder)
            (self.root / path).chmod(0o755)
        self.log = self.root / "commands.jsonl"
        self.env = {**os.environ, "PATH": str(self.root / "bin") + os.pathsep + os.environ["PATH"],
                    "TMPDIR": str(self.root), "QUICK_COMMAND_LOG": str(self.log)}
        self.env.pop("COMPLEXITYLIB_CACHE_CHECK_STARTED", None)
        self.env.pop("MANUAL_TEST_FAILURE", None)

    def run_gate(self, *args):
        return subprocess.run(["bash", str(self.root / "scripts/check.sh"), *args],
                              cwd=self.root, env=self.env, capture_output=True, text=True)

    def test_full_and_quick_routes_run_manual_checks_before_lean(self):
        for args in ((), ("--quick", "--base", "example-base")):
            with self.subTest(args=args):
                result = self.run_gate(*args)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("ok    operator manual links and excerpts", result.stdout)
                self.assertIn("ok    operator manual tooling tests", result.stdout)
                commands = [json.loads(x) for x in self.log.read_text().splitlines()]
                self.assertEqual(commands[0], ["ensure.sh"])
                expected = [["quick_check.py", "--base", "example-base"]] if args else [
                    ["full_check.py", "--base", "origin/main"]]
                self.assertEqual(commands[1:], expected)
                self.assertFalse(list(self.root.glob("cslib-frontier-check.*")))
                self.log.unlink()
        bad = self.run_gate("--not-an-option")
        self.assertEqual(bad.returncode, 2)
        self.assertFalse(self.log.exists())

    def test_no_full_fallback_reaches_quick_mode_only(self):
        result = self.run_gate("--quick", "--no-full-fallback")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        commands = [json.loads(x) for x in self.log.read_text().splitlines()]
        self.assertEqual(commands[1:], [["quick_check.py", "--base", "origin/main",
                                         "--no-full-fallback"]])
        self.log.unlink()
        bad = self.run_gate("--no-full-fallback")
        self.assertEqual(bad.returncode, 2)
        self.assertFalse(self.log.exists())

    def test_broken_link_blocks_full_and_quick_routes_before_cache(self):
        with (self.root / "manual/README.md").open("a") as stream:
            stream.write("\n[Missing](missing.md)\n")
        for args in ((), ("--quick",)):
            with self.subTest(args=args):
                result = self.run_gate(*args)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("missing local link: missing.md", result.stdout)
                self.assertFalse(self.log.exists())

    def test_failed_controls_block_full_and_quick_routes_before_cache(self):
        self.env["MANUAL_TEST_FAILURE"] = "1"
        for args in ((), ("--quick",)):
            with self.subTest(args=args):
                result = self.run_gate(*args)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("FAIL  operator manual tooling tests", result.stdout)
                self.assertFalse(self.log.exists())


class RepositoryLayoutTests(unittest.TestCase):
    def test_repository_libraries_are_in_quick_scope(self):
        # An unsupported library layout in the real lakefile sends every quick check to the full
        # check; #1729's `defaultFacets = []` once did so unnoticed.
        modules, aggregates, roots = quick.source_modules(REPO)
        self.assertIn("CslibFrontier", aggregates)
        self.assertIn("CslibFrontierResults", aggregates)
        self.assertIn("CslibFrontierTests", roots)
        self.assertIn("CslibFrontierTests.Axioms", modules)

    def test_repository_lint_driver_is_in_quick_scope(self):
        # Another lint driver or invalid default targets would send every quick check to the full
        # check; the default libraries' modules are linted and the tests are not, as in CI.
        lint = quick.lint_scope(
            REPO, {"CslibFrontier", "CslibFrontierResults"},
            {"CslibFrontier.A", "CslibFrontierResults.B", "CslibFrontierTests.C"},
            quick.defaultdict(set))
        self.assertEqual(lint, {"CslibFrontier.A": ["CslibFrontier.A"],
                                "CslibFrontierResults.B": ["CslibFrontierResults.B"]})


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
