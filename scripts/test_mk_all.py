#!/usr/bin/env python3
"""Regressions for `scripts/mk_all.py` on small fixture repositories (no Lean needed)."""

from __future__ import annotations

import contextlib
import io
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import mk_all  # noqa: E402

HEADER = mk_all.MODULE_HEADER + "\n"
SHARD_HEADER = mk_all.MODULE_HEADER + mk_all.SHARD_MARKER + "\n"


class MkAllTests(unittest.TestCase):
    def setUp(self) -> None:
        temp = tempfile.TemporaryDirectory(prefix="test-mk-all-")
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.write("lakefile.toml",
                   'name = "fixture"\ndefaultTargets = ["Lib"]\n'
                   '[[lean_lib]]\nname = "Lib"\n'
                   '[[lean_lib]]\nname = "Moved"\nsrcDir = "abstracts"\n'
                   '[[lean_lib]]\nname = "Globbed"\nroots = []\nglobs = ["Globbed.+"]\n')
        self.write("Lib.lean", HEADER)
        self.write("abstracts/Moved.lean", "import Moved.Old\n")
        for path in ("Lib/Init.lean", "Lib/Zed.lean", "Lib/A/One.lean", "Lib/A/Two.lean",
                     "Lib/A/B/Deep.lean", "Lib/A/B.lean", "Lib/C/D/Only.lean",
                     "abstracts/Moved/Beta.lean", "Globbed/Test.lean"):
            self.write(path, "-- fixture source; the generator never reads it\n")

    def write(self, path: str, text: str) -> Path:
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
        return target

    def read(self, path: str) -> str:
        return (self.root / path).read_text()

    def run_cli(self, *args: str, expected: int = 0) -> str:
        output = io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            status = mk_all.main(list(args), root=self.root)
        self.assertEqual(status, expected, output.getvalue())
        return output.getvalue()

    def test_generates_root_and_one_shard_per_directory(self) -> None:
        self.run_cli("--check", expected=1)
        self.run_cli()
        self.assertEqual(self.read("Lib.lean"), HEADER +
                         "public import Lib.All.A\npublic import Lib.All.C\n"
                         "public import Lib.Init\npublic import Lib.Zed\n")
        # `Lib/A/B.lean` and the directory `Lib/A/B/` coexist; the shard lives under `All/`.
        # A subdirectory's shard sits where its name sorts, after the module of the same name.
        self.assertEqual(self.read("Lib/All/A.lean"), SHARD_HEADER +
                         "public import Lib.A.B\npublic import Lib.All.A.B\n"
                         "public import Lib.A.One\npublic import Lib.A.Two\n")
        self.assertEqual(self.read("Lib/All/A/B.lean"), SHARD_HEADER + "public import Lib.A.B.Deep\n")
        self.assertEqual(self.read("Lib/All/C.lean"), SHARD_HEADER + "public import Lib.All.C.D\n")
        self.assertEqual(self.read("Lib/All/C/D.lean"), SHARD_HEADER + "public import Lib.C.D.Only\n")
        # A plain-import root keeps its style, relative to its own source directory.
        self.assertEqual(self.read("abstracts/Moved.lean"), "import Moved.Beta\n")
        self.assertFalse((self.root / "Globbed.lean").exists())
        self.assertIn("All aggregators are current.", self.run_cli("--check"))
        self.assertIn("No update necessary", self.run_cli())

    def test_new_module_changes_only_its_directory_shard(self) -> None:
        self.run_cli()
        before = {p: p.read_text() for p in self.root.rglob("*.lean")}
        self.write("Lib/A/B/Extra.lean", "-- new module\n")
        out = self.run_cli("--check", expected=1)
        self.assertIn("Lib/All/A/B.lean is out of date", out)
        self.assertIn("Lib.lean does not import Lib.A.B.Extra", out)
        self.run_cli()
        changed = {str(p.relative_to(self.root)) for p in self.root.rglob("*.lean")
                   if before.get(p) != p.read_text()}
        self.assertEqual(changed, {"Lib/A/B/Extra.lean", "Lib/All/A/B.lean"})

    def test_new_directory_adds_a_shard_and_one_parent_line(self) -> None:
        self.run_cli()
        self.write("Lib/A/New/Mod.lean", "-- new module\n")
        self.assertEqual(set(self.run_cli().splitlines()),
                         {"Updating Lib/All/A.lean", "Creating Lib/All/A/New.lean"})
        self.assertIn("public import Lib.All.A.New\n", self.read("Lib/All/A.lean"))

    def test_removed_directory_removes_its_shards(self) -> None:
        self.run_cli()
        (self.root / "Lib/C/D/Only.lean").unlink()
        out = self.run_cli("--check", expected=1)
        self.assertIn("Lib/All/C.lean is not the shard of a directory with modules", out)
        self.assertIn("Lib/All/C/D.lean is not the shard of a directory with modules", out)
        self.run_cli()
        self.assertFalse((self.root / "Lib/All/C").exists())
        self.assertFalse((self.root / "Lib/All/C.lean").exists())
        self.run_cli("--check")

    def test_stale_and_hand_edited_aggregators_are_reported(self) -> None:
        self.run_cli()
        self.write("Lib/All/A.lean", self.read("Lib/All/A.lean").replace(
            "public import Lib.A.One\n", ""))
        out = self.run_cli("--check", expected=1)
        self.assertIn("Lib/All/A.lean is out of date", out)
        self.assertIn("Lib.lean does not import Lib.A.One", out)
        # A union merge can keep both sides' lines in the wrong order.
        self.run_cli()
        text = self.read("Lib.lean").splitlines(keepends=True)
        self.write("Lib.lean", "".join(text[:2] + text[2:][::-1]))
        self.assertIn("Lib.lean is out of date", self.run_cli("--check", expected=1))

    def test_reserved_directory_refuses_foreign_files(self) -> None:
        self.run_cli()
        self.write("Lib/All/A/Real.lean", "theorem t : True := trivial\n")
        self.assertIn("reserved for generated shards", self.run_cli(expected=2))
        self.assertTrue((self.root / "Lib/All/A/Real.lean").exists())
        self.assertIn("reserved for generated shards", self.run_cli("--check", expected=2))

    def test_reserved_module_name_beside_the_shard_directory(self) -> None:
        self.write("Lib/All.lean", "-- would be the module Lib.All\n")
        self.assertIn("is reserved", self.run_cli(expected=2))

    def test_a_module_named_all_below_the_root_is_an_ordinary_module(self) -> None:
        self.write("Lib/A/All.lean", "-- a module about `List.all`\n")
        self.run_cli()
        self.assertIn("public import Lib.A.All\n", self.read("Lib/All/A.lean"))

    def test_unsupported_module_path(self) -> None:
        self.write("Lib/A/bad-name.lean", "-- not an identifier\n")
        self.assertIn("not a plain Lean identifier path", self.run_cli("--check", expected=2))

    def test_aggregates_lists_default_target_aggregators(self) -> None:
        self.run_cli()
        self.assertEqual(self.run_cli("--aggregates").split(),
                         ["Lib", "Lib.All.A", "Lib.All.A.B", "Lib.All.C", "Lib.All.C.D"])

    def test_expanding_the_shards_gives_one_sorted_list(self) -> None:
        self.write("Lib/A/Aa.lean", "-- sorts between `Lib.A` and `Lib.A.B`\n")
        self.write("Lib/A/B0.lean", "-- sorts after everything under `Lib/A/B/`\n")
        self.run_cli()

        def expand(path: str) -> list[str]:
            names = []
            for line in self.read(path).splitlines():
                if line.startswith("public import "):
                    name = line.removeprefix("public import ")
                    names += (expand("Lib/All/" + name.removeprefix("Lib.All.").replace(".", "/")
                                     + ".lean") if name.startswith("Lib.All.") else [name])
            return names

        names = expand("Lib.lean")
        modules = {".".join(p.relative_to(self.root).with_suffix("").parts)
                   for p in (self.root / "Lib").rglob("*.lean") if "All" not in p.parts}
        self.assertEqual(names, sorted(modules))

    def test_repository_aggregators_are_current(self) -> None:
        self.assertEqual(mk_all.check(mk_all.ROOT), [])


if __name__ == "__main__":
    unittest.main()
