"""Unit tests for scripts/lean_outputs.py."""

from __future__ import annotations

import hashlib
import json
import os
import pathlib
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import lean_outputs as lo  # noqa: E402
import test_check_cache_restores as cache_tests  # noqa: E402


class ModuleTests(unittest.TestCase):
    def test_module_roles(self) -> None:
        self.assertEqual(lo.module_role("CslibFrontier.Foundations.Data.List.Basic"), "lib")
        self.assertEqual(lo.module_role("CslibFrontierTests.Smoke"), "test")


class OutputCheckTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.reference = pathlib.Path(tmp.name) / "current"
        self.copy = pathlib.Path(tmp.name) / "copy"
        for directory in (self.reference, self.copy):
            self.write(directory, "CslibFrontier/A.ilean", "{}")
            self.write(directory, "CslibFrontier/A.olean", "a")
            self.write(directory, "CslibFrontier/A.c", "ignored")

    @staticmethod
    def write(directory: pathlib.Path, rel: str, text: str) -> None:
        path = directory / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def check(self, build_dir: pathlib.Path, skip: bool = False, current: bool = True) -> str:
        return lo.check_outputs(build_dir, skip, current=lambda: current, reference=self.reference)

    def test_identical_custom_directory_is_checked(self) -> None:
        self.write(self.copy, "CslibFrontier/A.c", "other files do not matter")
        self.assertIn("identical", self.check(self.copy))
        self.assertIn("lake build --no-build", self.check(self.reference))

    def test_stale_custom_directory_is_refused(self) -> None:
        # The current outputs gained a declaration that the copied directory lacks.
        self.write(self.reference, "CslibFrontier/A.olean", "a with a new declaration")
        self.write(self.reference, "CslibFrontier/B.ilean", "{}")
        with self.assertRaises(SystemExit) as error:
            self.check(self.copy)
        self.assertIn("2 file(s)", str(error.exception.code))
        self.assertEqual(lo.output_differences(self.copy, self.reference),
                         ["CslibFrontier/A.olean", "CslibFrontier/B.ilean"])

    def test_stale_default_outputs_are_refused(self) -> None:
        with self.assertRaises(SystemExit):
            self.check(self.reference, current=False)

    def test_missing_output_directory_is_refused_without_lake(self) -> None:
        missing = self.reference.parent / "missing"
        with mock.patch.object(lo.subprocess, "run", side_effect=AssertionError("Lake ran")) as run:
            with self.assertRaises(SystemExit) as error:
                lo.check_outputs(missing, False, reference=missing)
        self.assertIn("build outputs are missing", str(error.exception.code))
        run.assert_not_called()
        self.assertFalse(missing.exists())

    def test_unchecked_missing_directory_does_not_call_lake(self) -> None:
        missing = self.reference.parent / "missing"
        with mock.patch.object(lo.subprocess, "run", side_effect=AssertionError("Lake ran")) as run:
            status = lo.check_outputs(missing, True, reference=missing)
        self.assertIn("not checked", status)
        run.assert_not_called()
        self.assertFalse(missing.exists())

    def test_stale_root_output_is_refused(self) -> None:
        for directory in (self.reference, self.copy):
            self.write(directory, "CslibFrontier.ilean", "root")
        self.write(self.copy, "CslibFrontier.ilean", "stale root")
        self.assertEqual(lo.output_differences(self.copy, self.reference), ["CslibFrontier.ilean"])
        with self.assertRaises(SystemExit):
            self.check(self.copy)

    def test_unchecked_reports_say_so(self) -> None:
        self.write(self.reference, "CslibFrontier/A.olean", "changed")
        self.assertIn("not checked", self.check(self.copy, skip=True))

    def write_ileans(self, modules: dict[str, list[str]]) -> None:
        """Write an `.ilean` file for each module, with the given direct imports."""
        for module, imports in modules.items():
            self.write(self.reference, module.replace(".", "/") + ".ilean", json.dumps(
                {"module": module, "directImports": [[i, False, False, False] for i in imports]}))

    def test_outputs_of_deleted_modules_are_ignored(self) -> None:
        self.write_ileans({"CslibFrontier": ["CslibFrontier.A"],
                           "CslibFrontier.A": ["Mathlib.Init"], "CslibFrontier.Deleted": []})
        self.assertEqual(list(lo.load_ileans(self.reference, glob=lambda root: [])),
                         ["CslibFrontier.A"])

    def test_glob_library_modules_are_read_from_sources(self) -> None:
        self.write_ileans({"CslibFrontier": [],
                           "CslibFrontierTests.T": ["CslibFrontier.B"], "CslibFrontier.B": [],
                           "CslibFrontierTests.Stale": []})
        glob = lambda root: ["CslibFrontierTests.T"] if root == "CslibFrontierTests" else []
        self.assertEqual(sorted(lo.load_ileans(self.reference, glob=glob)),
                         ["CslibFrontier.B", "CslibFrontierTests.T"])
        self.assertEqual(lo.root_modules(glob),
                         ["CslibFrontier", "CslibFrontierTests.T"])

    def test_missing_reachable_output_is_refused(self) -> None:
        self.write_ileans({"CslibFrontier": ["CslibFrontier.Live"],
                           "CslibFrontier.Live": ["CslibFrontier.Missing"]})
        with self.assertRaises(SystemExit) as error:
            lo.load_ileans(self.reference, glob=lambda root: [])
        self.assertIn("Missing.ilean is missing (imported by CslibFrontier.Live)",
                      str(error.exception.code))

    def test_missing_root_output_is_refused(self) -> None:
        self.write_ileans({"CslibFrontier.A": []})
        with self.assertRaises(SystemExit) as error:
            lo.load_ileans(self.reference, glob=lambda root: [])
        self.assertIn("CslibFrontier.ilean is missing (a root)", str(error.exception.code))


class InventoryTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory(prefix="audit-inventory-")
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.build = self.root / ".lake/build/lib/lean"

    def artifacts(self, module: str, split: bool = False, **extra) -> None:
        base = self.build / module.replace(".", "/")
        base.parent.mkdir(parents=True, exist_ok=True)
        parts = ["olean", "olean.server", "olean.private"] if split else ["olean"]
        outputs = {"m": split, "o": ["0" * 16 + "." + ext for ext in parts],
                   "i": "0" * 16 + ".ilean", **extra}
        base.with_suffix(".trace").write_text(json.dumps({"outputs": outputs}))
        for ext in [*parts, "ilean"]:
            pathlib.Path(str(base) + "." + ext).write_text("fixture")

    def test_legacy_and_module_outputs_and_optional_ir(self) -> None:
        for split in (False, True):
            with self.subTest(split=split):
                self.artifacts("Demo", split)
                self.assertTrue(lo.module_outputs_present(self.build, "Demo"))
                trace = self.build / "Demo.trace"
                data = json.loads(trace.read_text())
                del data["outputs"]["m"]  # Lake also infers the format from the OLean parts.
                trace.write_text(json.dumps(data))
                self.assertTrue(lo.module_outputs_present(self.build, "Demo"))
        (self.build / "Demo.olean.private").unlink()
        self.assertFalse(lo.module_outputs_present(self.build, "Demo"))
        self.artifacts("Demo", c="0" * 16 + ".c")
        self.assertFalse(lo.module_outputs_present(self.build, "Demo"))
        ir = self.root / ".lake/build/ir/Demo.c"
        ir.parent.mkdir(parents=True)
        ir.write_text("fixture")
        self.assertTrue(lo.module_outputs_present(self.build, "Demo"))

    def test_missing_and_malformed_trace_is_refused(self) -> None:
        self.assertFalse(lo.module_outputs_present(self.build, "Demo"))
        for bad in ({}, {"o": []}, {"o": "not parts", "i": "0" * 16 + ".ilean"},
                    {"m": True, "o": ["0" * 16 + ".olean"], "i": "0" * 16 + ".ilean"},
                    {"o": ["bad.olean"], "i": "0" * 16 + ".ilean"},
                    {"o": ["0" * 16 + ".olean"], "i": "0" * 16 + ".ilean", "unknown": 1}):
            with self.subTest(outputs=bad):
                self.artifacts("Demo")
                (self.build / "Demo.trace").write_text(json.dumps({"outputs": bad}))
                self.assertFalse(lo.module_outputs_present(self.build, "Demo"))
        (self.build / "Demo.trace").write_text("{")
        self.assertFalse(lo.module_outputs_present(self.build, "Demo"))

    def test_current_sources_include_new_imports_and_glob_tests(self) -> None:
        for module in ("Demo", "Demo.Base", "DemoTests.Client"):
            source = self.root / (module.replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("-- fixture\n")
            self.artifacts(module)
        with mock.patch.multiple(lo, ROOT=self.root, ROOTS=("Demo", "DemoTests"),
                                 GLOB_ROOTS=("DemoTests",)):
            self.assertTrue(lo.output_inventory_complete(self.build))
            (self.root / "Demo/New.lean").write_text("-- newly imported source\n")
            self.assertFalse(lo.output_inventory_complete(self.build))
            self.artifacts("Demo.New")
            self.assertTrue(lo.output_inventory_complete(self.build))
            (self.build / "Demo.olean").unlink()
            self.assertFalse(lo.output_inventory_complete(self.build))
            self.artifacts("Demo")
            (self.build / "DemoTests/Client.ilean").unlink()
            self.assertFalse(lo.output_inventory_complete(self.build))

    def test_incomplete_inventory_never_invokes_lake(self) -> None:
        with mock.patch.object(lo, "output_inventory_complete", return_value=False), \
             mock.patch.object(lo.subprocess, "run", side_effect=AssertionError("Lake ran")):
            self.assertFalse(lo.lake_outputs_current())

    def test_default_inventory_covers_results_aggregate_and_sources(self) -> None:
        modules = ("CslibFrontier", "CslibFrontierTests.Client", "CslibFrontierResults",
                   "CslibFrontierResults.Registry", "CslibFrontierResults.Entries")
        for module in modules:
            source = self.root / (module.replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("-- fixture\n")
            self.artifacts(module)
        with mock.patch.object(lo, "ROOT", self.root):
            self.assertTrue(lo.output_inventory_complete(self.build))
            self.assertTrue(lo.output_inventory_complete(self.build, ("CslibFrontierTests",)))
            (self.build / "CslibFrontier.olean").unlink()
            self.assertFalse(lo.output_inventory_complete(self.build, ("CslibFrontierTests",)))
            self.artifacts("CslibFrontier")
            for module in modules[2:]:
                output = self.build / (module.replace(".", "/") + ".olean")
                output.unlink()
                self.assertFalse(lo.output_inventory_complete(self.build))
                self.assertTrue(lo.output_inventory_complete(self.build, ("CslibFrontier",)))
                self.artifacts(module)
            (self.root / "CslibFrontierResults/New.lean").write_text("-- newly imported result\n")
            self.assertFalse(lo.output_inventory_complete(self.build))


class InventoryLakeTests(cache_tests.IsolatedLakeFixture):
    """Exercise the actual preflight against cache entries and a build-local archive."""

    def setUp(self) -> None:
        super().setUp()
        self.write("Demo/Module.lean", "module\npublic def moduleValue : Nat := 2\n")
        self.write("Demo.lean", "import Demo.Base\nimport Demo.Module\n")
        with (self.root / "lakefile.toml").open("a") as config:
            config.write('\n[[lean_lib]]\nname = "DemoResults"\n')
        self.write("DemoResults.lean", "import DemoResults.Registry\nimport DemoResults.Entries\n")
        self.write("DemoResults/Registry.lean", "def registryValue : Nat := 4\n")
        self.write("DemoResults/Entries.lean", "def entryValue : Nat := 5\n")
        self.write("DemoTests/Client.lean", "import Demo.Base\nimport DemoResults\n"
                   "example : value = 1 := rfl\n")
        result = self.lake("build", "--wfail", "--iofail", "Demo", "DemoTests")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.build = self.root / ".lake/build/lib/lean"
        patch = mock.patch.multiple(lo, ROOT=self.root, ROOTS=("Demo", "DemoTests"),
                                    GLOB_ROOTS=("DemoTests",), DEFAULT_BUILD_DIR=self.build,
                                    ROOT_OUTPUT_DEPENDENCIES={"DemoTests": ("Demo", "DemoResults")})
        patch.start()
        self.addCleanup(patch.stop)
        self.assertTrue(lo.lake_outputs_current())
        self.addCleanup(self.assert_small_fixture)

    def assert_small_fixture(self) -> None:
        paths = [self.root, pathlib.Path(os.environ["LAKE_CACHE_DIR"])]
        self.assertLess(sum(p.stat().st_size for root in paths for p in root.rglob("*")
                            if p.is_file()), 50 * 1024 * 1024)

    @staticmethod
    def snapshot(root: pathlib.Path) -> dict:
        return {str(p.relative_to(root)): (p.stat().st_mtime_ns,
                hashlib.sha256(p.read_bytes()).hexdigest())
                for p in root.rglob("*") if p.is_file()}

    def assert_refused_without_restore(self, output: pathlib.Path,
                                      roots: tuple[str, ...] | None = None) -> None:
        output.unlink()
        cache = pathlib.Path(os.environ["LAKE_CACHE_DIR"])
        before = self.snapshot(self.root / ".lake/build"), self.snapshot(cache)
        with self.assertRaises(SystemExit) as error:
            lo.check_outputs(self.build, False, reference=self.build,
                             current=lambda: lo.lake_outputs_current(roots))
        self.assertIn("missing or stale", str(error.exception.code))
        self.assertFalse(output.exists())
        self.assertEqual(before, (self.snapshot(self.root / ".lake/build"), self.snapshot(cache)))

    def test_seeded_cache_does_not_supply_missing_imported_output(self) -> None:
        output = self.build / "Demo/Module.olean"
        self.assert_refused_without_restore(output)
        # Control: the unchanged Lake probe really could restore this missing output.
        result = self.lake("build", "--no-build", "Demo")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue(output.exists())

    def test_local_archive_does_not_supply_missing_output(self) -> None:
        result = self.lake("build", "+Demo.Module:ltar")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue((self.root / ".lake/build/ir/Demo/Module.ltar").is_file())
        cache = tempfile.TemporaryDirectory(prefix="audit-archive-cache-")
        self.addCleanup(cache.cleanup)
        with mock.patch.dict(os.environ, {"LAKE_CACHE_DIR": cache.name}):
            output = self.build / "Demo/Module.olean"
            self.assert_refused_without_restore(output)
            result = self.lake("build", "--no-build", "Demo")
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertTrue(output.exists())

    def test_missing_glob_test_is_refused(self) -> None:
        self.assert_refused_without_restore(self.build / "DemoTests/Client.ilean")

    def test_library_only_probe_does_not_require_or_restore_tests(self) -> None:
        omitted = [self.build / p for p in ("DemoTests/Client.ilean", "DemoResults.olean",
                                            "DemoResults/Entries.olean")]
        for output in omitted:
            output.unlink()
        self.assertTrue(lo.lake_outputs_current(("Demo",)))
        self.assertFalse(any(output.exists() for output in omitted))
        self.assert_refused_without_restore(self.build / "Demo/Module.olean", ("Demo",))

    def test_missing_results_aggregate_and_modules_are_refused(self) -> None:
        for path in ("DemoResults.olean", "DemoResults/Registry.olean", "DemoResults/Entries.olean"):
            with self.subTest(path=path):
                output = self.build / path
                self.assert_refused_without_restore(output)
                result = self.lake("build", "--no-build", "DemoTests")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertTrue(output.exists())

    def test_tests_only_probe_covers_both_imported_libraries(self) -> None:
        for path in ("Demo/Base.olean", "DemoResults.olean"):
            with self.subTest(path=path):
                output = self.build / path
                self.assert_refused_without_restore(output, ("DemoTests",))
                result = self.lake("build", "--no-build", "DemoTests")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertTrue(output.exists())

    def test_newly_imported_results_source_is_refused(self) -> None:
        self.write("DemoResults/New.lean", "def newResult : Nat := 6\n")
        with (self.root / "DemoResults.lean").open("a") as aggregate:
            aggregate.write("import DemoResults.New\n")
        cache = pathlib.Path(os.environ["LAKE_CACHE_DIR"])
        before = self.snapshot(self.root / ".lake/build"), self.snapshot(cache)
        self.assertFalse(lo.lake_outputs_current())
        self.assertEqual(before, (self.snapshot(self.root / ".lake/build"), self.snapshot(cache)))

    def test_complete_stale_sources_still_fail_lake_freshness(self) -> None:
        self.write("Demo/Base.lean", "def value : Nat := 3\n")
        self.assertTrue(lo.output_inventory_complete(self.build))
        self.assertFalse(lo.lake_outputs_current())


if __name__ == "__main__":
    unittest.main()
