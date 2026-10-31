"""Unit tests for scripts/lean_outputs.py."""

from __future__ import annotations

import json
import pathlib
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import lean_outputs as lo  # noqa: E402


class ModuleTests(unittest.TestCase):
    def test_module_roles(self) -> None:
        self.assertEqual(lo.module_role("Complexity.Foundations.Data.List.Basic"), "lib")
        self.assertEqual(lo.module_role("ComplexityTests.Smoke"), "test")
        self.assertEqual(lo.module_role("ComplexityTests.Abstracts.All"), "abstract")
        self.assertEqual(lo.module_role("ComplexityAbstracts.CookLevinBridge"), "abstract")


class OutputCheckTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.reference = pathlib.Path(tmp.name) / "current"
        self.copy = pathlib.Path(tmp.name) / "copy"
        for directory in (self.reference, self.copy):
            self.write(directory, "Complexity/A.ilean", "{}")
            self.write(directory, "Complexity/A.olean", "a")
            self.write(directory, "Complexity/A.c", "ignored")

    @staticmethod
    def write(directory: pathlib.Path, rel: str, text: str) -> None:
        path = directory / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def check(self, build_dir: pathlib.Path, skip: bool = False, current: bool = True) -> str:
        return lo.check_outputs(build_dir, skip, current=lambda: current, reference=self.reference)

    def test_identical_custom_directory_is_checked(self) -> None:
        self.write(self.copy, "Complexity/A.c", "other files do not matter")
        self.assertIn("identical", self.check(self.copy))
        self.assertIn("lake build --no-build", self.check(self.reference))

    def test_stale_custom_directory_is_refused(self) -> None:
        # The current outputs gained a declaration that the copied directory lacks.
        self.write(self.reference, "Complexity/A.olean", "a with a new declaration")
        self.write(self.reference, "Complexity/B.ilean", "{}")
        with self.assertRaises(SystemExit) as error:
            self.check(self.copy)
        self.assertIn("2 file(s)", str(error.exception.code))
        self.assertEqual(lo.output_differences(self.copy, self.reference),
                         ["Complexity/A.olean", "Complexity/B.ilean"])

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
            self.write(directory, "Complexity.ilean", "root")
        self.write(self.copy, "Complexity.ilean", "stale root")
        self.assertEqual(lo.output_differences(self.copy, self.reference), ["Complexity.ilean"])
        with self.assertRaises(SystemExit):
            self.check(self.copy)

    def test_unchecked_reports_say_so(self) -> None:
        self.write(self.reference, "Complexity/A.olean", "changed")
        self.assertIn("not checked", self.check(self.copy, skip=True))

    def write_ileans(self, modules: dict[str, list[str]]) -> None:
        """Write an `.ilean` file for each module, with the given direct imports."""
        for module, imports in modules.items():
            self.write(self.reference, module.replace(".", "/") + ".ilean", json.dumps(
                {"module": module, "directImports": [[i, False, False, False] for i in imports]}))

    def test_outputs_of_deleted_modules_are_ignored(self) -> None:
        self.write_ileans({"Complexity": ["Complexity.A"], "ComplexityAbstracts": [],
                           "Complexity.A": ["Mathlib.Init"], "Complexity.Deleted": []})
        self.assertEqual(list(lo.load_ileans(self.reference, glob=lambda root: [])),
                         ["Complexity.A"])

    def test_glob_library_modules_are_read_from_sources(self) -> None:
        self.write_ileans({"Complexity": [], "ComplexityAbstracts": [],
                           "ComplexityTests.T": ["Complexity.B"], "Complexity.B": [],
                           "ComplexityTests.Stale": []})
        glob = lambda root: ["ComplexityTests.T"] if root == "ComplexityTests" else []
        self.assertEqual(sorted(lo.load_ileans(self.reference, glob=glob)),
                         ["Complexity.B", "ComplexityTests.T"])
        self.assertEqual(lo.root_modules(glob),
                         ["Complexity", "ComplexityTests.T", "ComplexityAbstracts"])

    def test_missing_reachable_output_is_refused(self) -> None:
        self.write_ileans({"Complexity": ["Complexity.Live"], "ComplexityAbstracts": [],
                           "Complexity.Live": ["Complexity.Missing"]})
        with self.assertRaises(SystemExit) as error:
            lo.load_ileans(self.reference, glob=lambda root: [])
        self.assertIn("Missing.ilean is missing (imported by Complexity.Live)",
                      str(error.exception.code))

    def test_missing_root_output_is_refused(self) -> None:
        self.write_ileans({"Complexity": []})
        with self.assertRaises(SystemExit) as error:
            lo.load_ileans(self.reference, glob=lambda root: [])
        self.assertIn("ComplexityAbstracts.ilean is missing (a root)", str(error.exception.code))


if __name__ == "__main__":
    unittest.main()
