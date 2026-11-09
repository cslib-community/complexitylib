"""Unit tests for scripts/check_tidy_surface.py, on synthetic build outputs and, when Lean is
available, on a compiled module (`CompiledFixtureTests`).

The fixtures have the shape of what `scripts/LeanOutputs.lean` and the `.ilean` files record for
a module like this one, where only `stated`, `exposed` and `Cert.cert` have tidy statements:

    theorem proved (h : ComputableInPolyTime f e e') : ComputableInPolyTime f e e' := by
      have h' : ComputableTidilyInPolyTime f e e' := h.tidy
      exact .of_tidy h'
    theorem stated (h : ComputableInPolyTime f e e') : ComputableTidilyInPolyTime f e e' := h.tidy
    private theorem hidden (h : …) : ComputableTidilyInPolyTime f e e' := h.tidy
    @[expose] def exposed … : Prop := ComputableTidilyInPolyTime f e e'
    def opaqueBody … : Prop := ComputableTidilyInPolyTime f e e'
    structure Cert … : Prop where
      cert : ComputableTidilyInPolyTime f e e'
"""

from __future__ import annotations

import contextlib
import io
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_tidy_surface as c  # noqa: E402
import lean_outputs as lo  # noqa: E402

TIDY = "Turing.MultiTapeTM.ComputableTidilyInPolyTime"
PLAIN = "Turing.MultiTapeTM.ComputableInPolyTime"
TIDY_MODULE = "CslibFrontier.Machines.Tidy"


def declaration(module: str, name: str, line: int, kind: str = "thm", exported: str = "axiom",
                tidy: tuple[str, ...] = (), body: tuple[str, ...] = (),
                parent: str | None = None) -> tuple[str, dict, dict]:
    """The `.ilean` reference key and entry of a declaration, and its constant row."""
    key = json.dumps({"c": {"m": module, "n": name}})
    span = [line - 1, 8, line - 1, 8 + len(name)]
    info = {"definition": span + ([parent] if parent else []), "usages": []}
    row = {"n": name, "m": module, "k": kind, "e": exported, "doc": True, "tidy": list(tidy),
           "tb": list(body), "u": [], "r": [line, 0, line + 2, 0, line, 8, line, 8 + len(name)]}
    return key, info, row


def reference(name: str, line: int, user: str) -> tuple[str, dict, None]:
    """The `.ilean` entry of a reference to `name`, from another module, in `user`'s proof."""
    key = json.dumps({"c": {"m": TIDY_MODULE, "n": name}})
    return key, {"definition": None, "usages": [[line - 1, 4, line - 1, 30, user]]}, None


def module_fixture(module: str, short: str) -> list[tuple[str, dict, dict | None]]:
    """The declarations of the module in the docstring, named `short.…`, and the references to
    the predicates from their proofs."""
    return [
        reference(TIDY, 11, f"{short}.proved"),
        reference(PLAIN, 15, f"{short}.stated"),
        declaration(module, f"{short}.proved", 10),
        declaration(module, f"{short}.stated", 15, tidy=(TIDY,)),
        declaration(module, f"_private.{module}.0.{short}.hidden", 18, exported="",
                    tidy=(TIDY,)),
        declaration(module, f"{short}.exposed", 21, kind="def", exported="def", body=(TIDY,)),
        declaration(module, f"{short}.opaqueBody", 24, kind="def"),
        declaration(module, f"{short}.Cert", 27, kind="induct", exported="induct",
                    parent=f"{short}.Cert"),
        declaration(module, f"{short}.Cert.cert", 28, tidy=(TIDY,), parent=f"{short}.Cert"),
    ]


class FakeLibrary(lo.Library):
    """`lean_outputs.Library` over in-memory `.ilean` data and constant rows."""

    def __init__(self, modules: dict[str, list[tuple[str, dict, dict | None]]]):
        self.ileans, self.constants, self.sources = {}, {}, {}
        for module, entries in modules.items():
            self.ileans[module] = {"module": module, "directImports": [],
                                   "references": {key: info for key, info, _ in entries}}
            self.constants.update({row["n"]: row for _, _, row in entries if row})
        self.modules = sorted(self.ileans)
        self.duplicate_rows = []


class CountingTests(unittest.TestCase):
    def setUp(self) -> None:
        module = "CslibFrontier.Classes.A"
        self.lib = FakeLibrary({module: module_fixture(module, "A")})

    def names(self, allowlist: set[str] = frozenset()) -> list[str]:
        found = c.tidy_statements(self.lib, set(allowlist))
        return [name for rows in found.values() for name, _, _ in rows]

    def test_statements_count_and_proofs_do_not(self) -> None:
        found = c.tidy_statements(self.lib, set())
        self.assertEqual(list(found), ["CslibFrontier/Classes/A.lean"])
        self.assertEqual(found["CslibFrontier/Classes/A.lean"][0], ("A.stated", 15, [TIDY]))
        # `proved` mentions the tidy predicate in its proof only.
        self.assertNotIn("A.proved", self.names())

    def test_private_declarations_do_not_count(self) -> None:
        self.assertFalse([n for n in self.names() if "hidden" in n])

    def test_exposed_bodies_and_fields_count(self) -> None:
        self.assertEqual(self.names(), ["A.stated", "A.exposed", "A.Cert.cert"])
        self.assertNotIn("A.opaqueBody", self.names())

    def test_allowlisted_modules_are_exempt(self) -> None:
        self.assertEqual(self.names({"CslibFrontier/Classes/A.lean"}), [])
        self.assertEqual(len(self.names({"CslibFrontier/Classes/B.lean"})), 3)

    def test_generated_constants_do_not_count(self) -> None:
        key, info, row = declaration("CslibFrontier.Classes.A", "A.exposed_apply", 30,
                                     tidy=(TIDY,), parent="A.exposed")
        self.lib.ileans["CslibFrontier.Classes.A"]["references"][key] = info
        self.lib.constants[row["n"]] = row
        self.assertNotIn("A.exposed_apply", self.names())


class RatchetTests(unittest.TestCase):
    def test_compare(self) -> None:
        over, under = c.compare({"A.lean": 3, "B.lean": 1, "New.lean": 1},
                                {"A.lean": 2, "B.lean": 4, "Gone.lean": 5})
        self.assertEqual(over, {"A.lean": (3, 2), "New.lean": (1, 0)})
        self.assertEqual(under, {"B.lean": (1, 4), "Gone.lean": (0, 5)})

    def test_baseline_text_drops_empty_modules(self) -> None:
        self.assertEqual(json.loads(c.baseline_text({"B.lean": 2, "A.lean": 0})), {"B.lean": 2})

    def test_malformed_baseline_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "baseline.json"
            for text in ('["A.lean"]', '{"A.lean": 0}', '{"A.lean": "2"}', '{"A.lean": true}'):
                path.write_text(text)
                with self.assertRaises(SystemExit, msg=text):
                    c.load_baseline(path)


class MainTests(unittest.TestCase):
    """The command on the fixture library, with a temporary allowlist and baseline."""

    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.dir = pathlib.Path(tmp.name)
        self.allowlist = self.dir / "allowlist.txt"
        self.allowlist.write_text("# raw machines\nCslibFrontier/Machines/Raw.lean\n")
        self.baseline = self.dir / "baseline.json"
        self.modules = {m: module_fixture(m, m.rsplit(".", 1)[-1])
                        for m in ("CslibFrontier.Classes.A", "CslibFrontier.Machines.Raw")}

    def run_main(self, baseline: dict[str, int] | None, *flags: str) -> tuple[int, str, str]:
        if baseline is not None:
            self.baseline.write_text(json.dumps(baseline))
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(lo, "Library", lambda _: FakeLibrary(self.modules)), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = c.main(["--no-build-check", "--allowlist", str(self.allowlist),
                           "--baseline", str(self.baseline), *flags])
        return code, out.getvalue(), err.getvalue()

    def test_at_the_baseline_passes(self) -> None:
        code, out, _ = self.run_main({"CslibFrontier/Classes/A.lean": 3})
        self.assertEqual(code, 0)
        self.assertIn("3 public tidy statement(s) in 1 module(s)", out)

    def test_growth_fails(self) -> None:
        code, _, err = self.run_main({"CslibFrontier/Classes/A.lean": 2})
        self.assertEqual(code, 1)
        self.assertIn("CslibFrontier/Classes/A.lean: 3 tidy statement(s), baseline 2", err)
        self.assertIn("CslibFrontier/Classes/A.lean:15: A.stated mentions " + TIDY, err)

    def test_new_module_with_a_tidy_statement_fails(self) -> None:
        self.modules["CslibFrontier.Classes.New"] = [
            declaration("CslibFrontier.Classes.New", "New.ok", 10),
            declaration("CslibFrontier.Classes.New", "New.bad", 12, tidy=(TIDY,))]
        code, _, err = self.run_main({"CslibFrontier/Classes/A.lean": 3})
        self.assertEqual(code, 1)
        self.assertIn("CslibFrontier/Classes/New.lean: 1 tidy statement(s), baseline 0", err)
        self.assertNotIn("CslibFrontier/Classes/A.lean", err)

    def test_missing_baseline_allows_nothing(self) -> None:
        code, _, err = self.run_main(None)
        self.assertEqual(code, 1)
        self.assertIn("CslibFrontier/Classes/A.lean: 3 tidy statement(s), baseline 0", err)

    def test_stale_baseline_fails(self) -> None:
        code, _, err = self.run_main({"CslibFrontier/Classes/A.lean": 5, "CslibFrontier/Gone.lean": 1})
        self.assertEqual(code, 1)
        self.assertIn(c.UPDATE, err)
        self.assertIn("CslibFrontier/Classes/A.lean: 3 (baseline 5)", err)
        self.assertIn("CslibFrontier/Gone.lean: 0 (baseline 1)", err)

    def test_removed_statement_cannot_come_back(self) -> None:
        # Review 5636914097: removing a tidy statement must not leave reusable allowance.
        module = "CslibFrontier.Classes.A"
        full = self.modules[module]
        self.modules[module] = [e for e in full if not (e[2] and e[2]["n"] == "A.stated")]
        code, _, err = self.run_main({"CslibFrontier/Classes/A.lean": 3})
        self.assertEqual(code, 1)
        self.assertIn("CslibFrontier/Classes/A.lean: 2 (baseline 3)", err)
        self.assertEqual(self.run_main(None, "--update")[0], 0)
        self.assertEqual(json.loads(self.baseline.read_text()), {"CslibFrontier/Classes/A.lean": 2})
        self.assertEqual(self.run_main(None)[0], 0)
        self.modules[module] = full
        code, _, err = self.run_main(None)
        self.assertEqual(code, 1)
        self.assertIn("CslibFrontier/Classes/A.lean: 3 tidy statement(s), baseline 2", err)

    def test_update_lowers_the_baseline(self) -> None:
        code, _, _ = self.run_main({"CslibFrontier/Classes/A.lean": 5, "CslibFrontier/Gone.lean": 1},
                                   "--update")
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(self.baseline.read_text()), {"CslibFrontier/Classes/A.lean": 3})

    def test_update_does_not_raise_the_baseline_by_default(self) -> None:
        code, _, err = self.run_main({"CslibFrontier/Classes/A.lean": 2}, "--update")
        self.assertEqual(code, 1)
        self.assertIn("--allow-increase", err)
        self.assertEqual(json.loads(self.baseline.read_text()), {"CslibFrontier/Classes/A.lean": 2})
        code, _, _ = self.run_main(None, "--update", "--allow-increase")
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(self.baseline.read_text()), {"CslibFrontier/Classes/A.lean": 3})

    def test_allow_increase_needs_update(self) -> None:
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            c.main(["--no-build-check", "--allow-increase"])


# A compiled module for `CompiledFixtureTests`; `ComputableTidilyFake` counts as a tidy constant.
FIXTURE = """module
public import Init
public section

@[expose] def ComputableTidilyFake (n : Nat) : Prop := n = n

/-- Review 5636911963: tidy only in a proof-local `have` of an exposed body. -/
@[expose] def proofLocal (n : Nat) : {m : Nat // m = n} := by
  have ht : ComputableTidilyFake n := rfl
  exact ⟨n, ht⟩

@[expose] def proofTerm (n : Nat) : {m : Nat // m = n} :=
  ⟨n, (show ComputableTidilyFake n from rfl)⟩

theorem proved (n : Nat) : n = n := by
  have ht : ComputableTidilyFake n := rfl
  exact ht

def opaqueBody (n : Nat) : Prop := ComputableTidilyFake n

private theorem privateStated (n : Nat) : ComputableTidilyFake n := rfl

theorem stated (n : Nat) : ComputableTidilyFake n := rfl

@[expose] def Alias (n : Nat) : Prop := ComputableTidilyFake n

@[expose] def Pred : Nat → Prop := fun n => ∃ _ : ComputableTidilyFake n, n = 0

def inType (n : Nat) : {m : Nat // ComputableTidilyFake m} := ⟨n, rfl⟩

structure Cert (n : Nat) : Prop where
  cert : ComputableTidilyFake n

end
"""


@unittest.skipUnless(shutil.which("lake") and (c.ROOT / ".lake/packages").is_dir(),
                     "needs Lean and the repository's packages (CI runs this after the build)")
class CompiledFixtureTests(unittest.TestCase):
    """The whole count on a compiled module: what `scripts/LeanOutputs.lean` records as a
    statement, and what it leaves to proofs."""

    @classmethod
    def setUpClass(cls) -> None:
        tmp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(tmp.cleanup)
        root = pathlib.Path(tmp.name)
        build = root / "build"
        build.mkdir()
        (root / "TidyFixture.lean").write_text(FIXTURE)
        subprocess.run(["lake", "env", "lean", f"--root={root}", "-o",
                        str(build / "TidyFixture.olean"), "-i", str(build / "TidyFixture.ilean"),
                        str(root / "TidyFixture.lean")], cwd=c.ROOT, check=True,
                       capture_output=True)
        ilean = json.loads((build / "TidyFixture.ilean").read_text())
        constants, _ = lo.load_constants(build, ["TidyFixture"])
        cls.constants = constants
        lib = FakeLibrary({})
        lib.ileans, lib.modules, lib.constants = {"TidyFixture": ilean}, ["TidyFixture"], constants
        cls.counted = {name for rows in c.tidy_statements(lib, set()).values()
                       for name, _, _ in rows}

    def test_proofs_inside_exposed_bodies_do_not_count(self) -> None:
        for name in ("proofLocal", "proofTerm"):
            self.assertEqual(self.constants[name]["tidy"], [], name)
            self.assertEqual(self.constants[name]["tb"], [], name)
            self.assertNotIn(name, self.counted)

    def test_statements_count(self) -> None:
        self.assertEqual(self.constants["Alias"]["tb"], ["ComputableTidilyFake"])
        self.assertEqual(self.counted, {"stated", "Alias", "Pred", "inType", "Cert.cert"})


class CommittedFilesTests(unittest.TestCase):
    def test_allowlist_paths_exist(self) -> None:
        for path in c.load_allowlist(c.ALLOWLIST):
            self.assertTrue((c.ROOT / path).is_file(), path)

    def test_baseline_is_well_formed_and_outside_the_allowlist(self) -> None:
        baseline = c.load_baseline(c.BASELINE)
        self.assertEqual(c.BASELINE.read_text(), c.baseline_text(baseline))
        self.assertFalse(set(baseline) & c.load_allowlist(c.ALLOWLIST))


if __name__ == "__main__":
    unittest.main()
