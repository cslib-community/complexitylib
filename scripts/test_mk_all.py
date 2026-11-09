#!/usr/bin/env python3
"""CLI regressions for the source-directory-aware local mk_all executable."""

from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / ".lake/build/bin/mk_all"
MODULE_HEADER = "module  -- shake: keep-all --deprecated_module: ignore\n\n"


@unittest.skipUnless(BINARY.is_file(), "Build the local executable with lake build mk_all")
class MkAllTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="test-mk-all-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "lakefile.toml").write_text(
            'name = "mk_all_fixture"\n'
            '[[lean_lib]]\nname = "Plain"\n'
            '[[lean_lib]]\nname = "Moved"\nsrcDir = "relocated"\n')
        shutil.copyfile(ROOT / "lean-toolchain", self.root / "lean-toolchain")
        self.source("Plain/Zed.lean")
        self.source("Plain/Alpha.lean")
        self.source("relocated/Moved/Beta.lean")
        self.source("relocated/Moved/Sub/Child.lean")

    def source(self, path):
        source = self.root / path
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text("-- fixture source; discovery does not elaborate it\n")
        return source

    def run_cli(self, *args, expected=0):
        result = subprocess.run(["lake", "env", str(BINARY), *args], cwd=self.root,
                                text=True, capture_output=True)
        self.assertNotIn("uncaught exception:", result.stdout + result.stderr)
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        return result

    def test_default_generation_missing_roots_and_sorted_module_names(self):
        self.run_cli("--check", expected=2)
        self.assertFalse((self.root / "Plain.lean").exists())
        self.assertFalse((self.root / "relocated/Moved.lean").exists())
        self.run_cli(expected=2)
        self.assertEqual((self.root / "Plain.lean").read_text(),
                         "import Plain.Alpha\nimport Plain.Zed\n")
        self.assertEqual((self.root / "relocated/Moved.lean").read_text(),
                         "import Moved.Beta\nimport Moved.Sub.Child\n")
        self.assertFalse((self.root / "Moved.lean").exists())
        # Both roots must be visited despite the temporary source-directory changes.
        self.run_cli("--check")

    def test_moved_library_detects_missing_import_and_repairs_it(self):
        self.run_cli("--lib", "Moved", expected=1)
        self.source("relocated/Moved/New.lean")
        before = (self.root / "relocated/Moved.lean").read_text()
        self.run_cli("--check", "--lib", "Moved", expected=1)
        self.assertEqual((self.root / "relocated/Moved.lean").read_text(), before)
        self.run_cli("--lib", "Moved", expected=1)
        self.assertIn("import Moved.New\n", (self.root / "relocated/Moved.lean").read_text())
        self.run_cli("--check", "--lib", "Moved")
        self.assertFalse((self.root / "Plain.lean").exists())

    def test_module_flag_and_inferred_style_and_library_subfolder(self):
        self.run_cli("--lib", "Moved", "--module", expected=1)
        self.assertEqual((self.root / "relocated/Moved.lean").read_text(),
                         MODULE_HEADER + "public import Moved.Beta\npublic import Moved.Sub.Child\n")
        self.source("relocated/Moved/Added.lean")
        self.run_cli("--lib", "Moved", expected=1)
        self.assertTrue((self.root / "relocated/Moved.lean").read_text().startswith(MODULE_HEADER))
        self.run_cli("--lib", "Moved/Sub", expected=1)
        self.assertEqual((self.root / "relocated/Moved/Sub.lean").read_text(),
                         "import Moved.Sub.Child\n")

    def test_workspace_with_interpreted_dependency_configuration(self):
        dependency = self.root / "dependency"
        dependency.mkdir()
        (dependency / "lakefile.lean").write_text(
            "import Lake\nopen Lake DSL\n"
            "package fixtureDependency where\n"
            "lean_lib Fixture where\n  roots := #[`Fixture]\n")
        lakefile = self.root / "lakefile.toml"
        lakefile.write_text(lakefile.read_text() +
                           '[[require]]\nname = "fixtureDependency"\npath = "dependency"\n')
        self.run_cli("--lib", "Moved", expected=1)
        self.assertTrue((self.root / "relocated/Moved.lean").is_file())

    def test_git_discovers_tracked_paths_relative_to_the_source_directory(self):
        subprocess.run(["git", "init", "--quiet"], cwd=self.root, check=True)
        subprocess.run(["git", "add", "."], cwd=self.root, check=True)
        self.source("relocated/Moved/Untracked.lean")
        self.run_cli("--git", "--lib", "Moved", expected=1)
        self.assertEqual((self.root / "relocated/Moved.lean").read_text(),
                         "import Moved.Beta\nimport Moved.Sub.Child\n")
        self.run_cli("--git", "--lib", "Moved", "--check")
        self.run_cli("--lib", "Moved", "--check", expected=1)


if __name__ == "__main__":
    unittest.main()
