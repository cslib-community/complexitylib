"""Unit tests for scripts/check_encoding_readability.py, on synthetic Lean modules."""

from __future__ import annotations

import contextlib
import io
import json
import pathlib
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_encoding_readability as c  # noqa: E402

HEADER = "module\n-- upstream: candidate\n\npublic import Complexity.Init\n\npublic section\n\n"
TERM = "encPair encNat (encList encBool)"


def theorem(name: str, term: str = TERM, prefix: str = "") -> str:
    return (f"{prefix}theorem {name} (f : ℕ × List Bool → Bool) :\n"
            f"    ComputableInPolyTime f ({term}) encBool := by\n  sorry\n\n")


def violations(source: str) -> dict[str, list[str]]:
    """The violations of a module, as `term -> declaration names`."""
    return {v.term: [name for name, _ in v.declarations]
            for v in c.module_violations(c.public_declarations(HEADER + source))}


class RuleTests(unittest.TestCase):
    def test_three_declarations_are_a_violation_and_two_are_not(self) -> None:
        self.assertEqual(violations(theorem("a") + theorem("b")), {})
        self.assertEqual(violations(theorem("a") + theorem("b") + theorem("c")),
                         {TERM: ["a", "b", "c"]})

    def test_uses_in_one_declaration_count_once(self) -> None:
        twice = (f"theorem a (f : ℕ × List Bool → Bool) :\n    ComputableInPolyTime f ({TERM})\n"
                 f"      encBool ∧ ComputableInPolyTime f ({TERM}) encBool := sorry\n\n")
        self.assertEqual(violations(twice + theorem("b")), {})

    def test_single_combinator_applications_are_not_compound(self) -> None:
        flat = "encPair encNat encNat"
        self.assertEqual(violations("".join(theorem(n, flat) for n in "abcde")), {})
        # The inner combinator must be an argument of the outer one, not of another function.
        indirect = "encPair encNat (encCSP (encOption encBool) encNat)"
        self.assertEqual(violations("".join(theorem(n, indirect) for n in "abc")), {})

    def test_whitespace_and_comments_do_not_matter(self) -> None:
        spaced = "encPair  encNat\n      ( encList /- bits -/ encBool )"
        self.assertEqual(violations(theorem("a") + theorem("b", spaced) + theorem("c")),
                         {TERM: ["a", "b", "c"]})

    def test_local_variables_are_compared_up_to_renaming(self) -> None:
        source = "".join(
            f"theorem {n} ({e} : σ ↪ List Bool) (f : σ × Option Bool → σ) :\n"
            f"    ComputableInPolyTime f (encPair {e} (encOption encBool)) {e} := sorry\n\n"
            for n, e in (("a", "encS"), ("b", "encT"), ("c", "e")))
        self.assertEqual(violations(source), {"encPair ?1 (encOption encBool)": ["a", "b", "c"]})
        # Without binders the names are constants, which differ.
        self.assertEqual(violations(source.replace("(encS : σ ↪ List Bool) ", "")), {})

    def test_section_variables_are_local(self) -> None:
        source = ("variable {σ : Type} (encS : σ ↪ List Bool)\n\n"
                  + "".join(theorem(n, "encPair encS (encOption encBool)") for n in "abc"))
        self.assertEqual(violations(source), {"encPair ?1 (encOption encBool)": ["a", "b", "c"]})

    def test_restated_input_encodings_count(self) -> None:
        bound = (lambda n: f"theorem {n} (encS : σ ↪ List Bool) :\n"
                 "    ComputableInSpace M.next encS encS\n"
                 "      fun p => (encPair encS (encOption encBool) p).length := sorry\n\n")
        self.assertEqual(violations(bound("a") + bound("b") + bound("c")),
                         {"encPair ?1 (encOption encBool)": ["a", "b", "c"]})

    def test_private_and_non_public_declarations_do_not_count(self) -> None:
        source = theorem("a") + theorem("b") + theorem("c", prefix="private ")
        self.assertEqual(violations(source), {})
        # Outside a `public section`, only declarations marked `public` count.
        outside = ("end\n\n" + theorem("c") + theorem("d", prefix="public ")
                   + theorem("e", prefix="@[simp] public "))
        self.assertEqual(violations(theorem("a") + theorem("b") + outside),
                         {TERM: ["a", "b", "d", "e"]})

    def test_internal_namespaces_do_not_count(self) -> None:
        internal = "namespace Foo.Internal\n\n" + theorem("c") + "end Foo.Internal\n\n"
        self.assertEqual(violations(theorem("a") + theorem("b") + internal), {})
        self.assertEqual(violations(theorem("a") + theorem("b") + theorem("Internal.c")), {})
        # `end Foo.Internal` closes both scopes.
        self.assertEqual(violations(theorem("a") + theorem("b") + internal + theorem("d")),
                         {TERM: ["a", "b", "d"]})

    def test_bodies_and_proofs_do_not_count(self) -> None:
        source = (f"/-- Named. -/\nabbrev encNamed : ℕ × List Bool ↪ List Bool := {TERM}\n\n"
                  f"def encOther : ℕ × List Bool ↪ List Bool :=\n  {TERM}\n\n"
                  f"theorem t : encNamed = {TERM} := by\n  show {TERM} = {TERM}\n  rfl\n\n"
                  + theorem("a"))
        self.assertEqual(violations(source), {})

    def test_structure_fields_count(self) -> None:
        source = (f"structure S (enc : σ ↪ List Bool) : Prop where\n"
                  f"  /-- First. -/\n"
                  f"  first : ComputableInPolyTime g ({TERM}) encBool\n"
                  f"  second (n : ℕ) :\n    ComputableInPolyTime g ({TERM}) encBool\n\n"
                  + theorem("a"))
        self.assertEqual(violations(source), {TERM: ["S.first", "S.second", "a"]})

    def test_an_outer_term_is_reported_instead_of_its_parts(self) -> None:
        outer = f"encPair encUnary ({TERM})"
        self.assertEqual(violations("".join(theorem(n, outer) for n in "abc")), {outer: ["a", "b", "c"]})
        # The inner term is reported too when it is repeated on its own.
        both = "".join(theorem(n, outer) for n in "abc") + "".join(theorem(n) for n in "xyz")
        self.assertEqual(violations(both), {outer: ["a", "b", "c"], TERM: ["x", "y", "z"]})

    def test_combinators_are_defined(self) -> None:
        root = pathlib.Path(c.ROOT, "Complexity/Computability/Machines/Turing/MultiTape/Encodings")
        source = "\n".join(p.read_text() for p in root.rglob("*.lean"))
        for name, arity in c.COMBINATORS.items():
            with self.subTest(name=name):
                definition = re.search(rf"\bdef {name}\b((?:\s*(?:\{{[^}}]*\}}|\([^)]*\)))*)",
                                       source)
                self.assertIsNotNone(definition)
                self.assertEqual(definition[1].count("("), arity)


class RatchetTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.baseline = self.root / "baseline.json"
        self.module = self.root / "Complexity/Area/A.lean"
        self.module.parent.mkdir(parents=True)
        self.write("abc")
        # Not checked: an `Internal` module, the tests and the abstracts.
        for rel in ("Complexity/Area/Internal/B.lean", "ComplexityTests/C.lean",
                    "abstracts/D.lean"):
            path = self.root / rel
            path.parent.mkdir(parents=True)
            path.write_text(HEADER + "".join(theorem(n) for n in "abc"))

    def write(self, names: str) -> None:
        self.module.write_text(HEADER + "".join(theorem(n) for n in names))

    def run_main(self, baseline: dict | None, *flags: str) -> tuple[int, str, str]:
        if baseline is not None:
            self.baseline.write_text(json.dumps(baseline))
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = c.main(["--root", str(self.root), "--baseline", str(self.baseline), *flags])
        return code, out.getvalue(), err.getvalue()

    def test_at_the_baseline_passes(self) -> None:
        code, out, _ = self.run_main({"Complexity/Area/A.lean": {TERM: 3}})
        self.assertEqual(code, 0)
        self.assertIn("1 repeated compound encoding(s) in 1 module(s), matching", out)

    def test_a_new_violation_fails_with_its_declarations(self) -> None:
        code, _, err = self.run_main({})
        self.assertEqual(code, 1)
        self.assertIn(f"Complexity/Area/A.lean: `{TERM}` in 3 public signatures:", err)
        self.assertIn("Complexity/Area/A.lean:8: a", err)
        self.assertIn("documented reducible `abbrev`", err)
        self.assertEqual(self.run_main(None)[0], 1)  # a missing baseline allows nothing

    def test_growth_fails(self) -> None:
        self.write("abcd")
        code, _, err = self.run_main({"Complexity/Area/A.lean": {TERM: 3}})
        self.assertEqual(code, 1)
        self.assertIn("in 4 public signatures, baseline 3", err)

    def test_shrinking_and_vanished_entries_are_stale(self) -> None:
        for names, count in (("abc", 3), ("ab", 0)):
            with self.subTest(names=names):
                self.write(names)
                code, _, err = self.run_main({"Complexity/Area/A.lean": {TERM: 4}})
                self.assertEqual(code, 1)
                self.assertIn("the baseline is stale", err)
                self.assertIn(f"`{TERM}` in {count} public signature(s), baseline 4", err)

    def test_update_lowers_the_baseline(self) -> None:
        self.write("ab")
        code, out, _ = self.run_main({"Complexity/Area/A.lean": {TERM: 3}}, "--update-baseline")
        self.assertEqual(code, 0)
        self.assertIn("0 repeated compound encoding(s)", out)
        self.assertEqual(json.loads(self.baseline.read_text()), {})
        self.assertEqual(self.run_main(None)[0], 0)

    def test_update_refuses_growth_unless_allowed(self) -> None:
        code, _, err = self.run_main({}, "--update-baseline")
        self.assertEqual(code, 1)
        self.assertIn("--allow-increase", err)
        self.assertEqual(json.loads(self.baseline.read_text()), {})
        code, _, _ = self.run_main(None, "--update-baseline", "--allow-increase")
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(self.baseline.read_text()),
                         {"Complexity/Area/A.lean": {TERM: 3}})

    def test_malformed_baseline_is_refused(self) -> None:
        for bad in ([], {"Complexity/Area/A.lean": 3}, {"Complexity/Area/A.lean": {TERM: 2}}):
            with self.subTest(bad=bad), self.assertRaises(SystemExit):
                self.run_main(bad)

    def test_summary(self) -> None:
        code, out, _ = self.run_main(None, "--summary")
        self.assertEqual(code, 0)
        self.assertIn("1 repeated compound encoding(s) in 1 module(s), spelled out in 3", out)
        self.assertIn("Area\t1\t1", out)
        self.assertIn("1\t3\tComplexity/Area/A.lean", out)


if __name__ == "__main__":
    unittest.main()
