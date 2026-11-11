"""Unit tests for scripts/check_encoding_readability.py, on synthetic Lean modules."""

from __future__ import annotations

import contextlib
import io
import json
import pathlib
import re
import subprocess
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

    def test_names_bound_inside_the_type_are_local(self) -> None:
        forall = "".join(
            f"theorem {n} : ∀ ({e} : ℕ ↪ List Bool),\n"
            f"    encPair {e} (encOption encBool) = encPair {e} (encOption encBool) := by\n"
            "  intro; rfl\n\n" for n, e in (("a", "ea"), ("b", "eb"), ("c", "ec")))
        lam = "".join(
            f"theorem {n} : P (fun ({e} : ℕ ↪ List Bool) => encPair {e} (encOption encBool)) :=\n"
            "  sorry\n\n" for n, e in (("a", "ea"), ("b", "eb"), ("c", "ec")))
        arrow = "".join(
            f"theorem {n} : ({e} : ℕ ↪ List Bool) → P (encPair {e} (encOption encBool)) :=\n"
            "  sorry\n\n" for n, e in (("a", "ea"), ("b", "eb"), ("c", "ec")))
        for source in (forall, lam, arrow):
            with self.subTest(source=source.split(":=")[0]):
                self.assertEqual(violations(source),
                                 {"encPair ?1 (encOption encBool)": ["a", "b", "c"]})

    def test_values_and_binder_types_see_the_outer_scope(self) -> None:
        # In `let e := e; e` the value is the outer `e`; in `fun (e : T e) => e`, so is the type.
        let = "".join(
            f"theorem {n} ({o} : ℕ ↪ List Bool) :\n"
            f"    encPair {o} (encList (let {i} := {o}; {i})) =\n"
            f"      encPair {o} (encList (let {i} := {o}; {i})) := rfl\n\n"
            for n, o, i in (("a", "e", "e"), ("b", "x", "y"), ("c", "z", "w")))
        lam = "".join(
            f"theorem {n} ({o} : ℕ ↪ List Bool) :\n"
            f"    P (encPair {o} (encList (g fun ({i} : T {o}) => {i}))) := sorry\n\n"
            for n, o, i in (("a", "e", "e"), ("b", "x", "y"), ("c", "z", "w")))
        # A `let` on its own line binds from the next line at its column; a value continued on
        # more indented lines does not see the name (here a constant `k`).
        body = "".join(
            f"theorem {n} :\n    let {k} := 0\n    P (encPair {k} (encOption encBool)) := sorry\n\n"
            for n, k in (("a", "k"), ("b", "m"), ("c", "j")))
        value = "".join(
            f"theorem {n} :\n    let {k} :=\n      f (encPair k (encOption encBool))\n"
            "    True := sorry\n\n" for n, k in (("a", "k"), ("b", "m"), ("c", "j")))
        for source, term in ((let, "encPair ?1 (encList (let ?2 := ?1; ?2))"),
                             (lam, "encPair ?1 (encList (g fun (?2 : T ?1) => ?2))"),
                             (body, "encPair ?1 (encOption encBool)"),
                             (value, "encPair k (encOption encBool)")):
            with self.subTest(term=term):
                self.assertEqual(violations(source), {term: ["a", "b", "c"]})

    def test_binder_scopes_end_with_their_brackets(self) -> None:
        # Outside `(∀ e, …)`, `e` is a constant again.
        scoped = (lambda n: f"theorem {n} : (∀ e : ℕ ↪ List Bool, True) ∧\n"
                  "    P (encPair e (encOption encBool)) := sorry\n\n")
        bound = ("theorem c : ∀ e : ℕ ↪ List Bool, P (encPair e (encOption encBool)) :=\n"
                 "  sorry\n\n")
        self.assertEqual(violations(scoped("a") + scoped("b") + bound), {})
        self.assertEqual(violations(scoped("a") + scoped("b") + scoped("c")),
                         {"encPair e (encOption encBool)": ["a", "b", "c"]})

    def test_inner_binders_shadow_outer_ones(self) -> None:
        def decl(n: str, outer: str, inner: str, use: str) -> str:
            return (f"theorem {n} ({outer} : ℕ ↪ List Bool) :\n"
                    f"    P (encPair {outer} (encList (g fun {inner} => {use}))) := sorry\n\n")
        # `fun e => e` binds a new `e`, so a, b and d spell the same term; c uses the outer one.
        source = (decl("a", "e", "e", "e") + decl("b", "x", "y", "y")
                  + decl("c", "e", "y", "e") + decl("d", "e", "z", "z"))
        self.assertEqual(violations(source),
                         {"encPair ?1 (encList (g fun ?2 => ?2))": ["a", "b", "d"]})

    def test_bound_names_that_are_not_encodings(self) -> None:
        term = lambda k: f"encPair (encFinite (Fin {k})) (encList encBool)"  # noqa: E731
        source = "".join(f"theorem {n} : ∀ {k} : ℕ, P ({term(k)}) := sorry\n\n"
                         for n, k in (("a", "k"), ("b", "m"), ("c", "j")))
        self.assertEqual(violations(source),
                         {"encPair (encFinite (Fin ?1)) (encList encBool)": ["a", "b", "c"]})
        # The same name, used freely (a constant `k`), is a different term.
        free = f"theorem d : P ({term('k')}) := sorry\n\n"
        self.assertEqual(violations(source.split("theorem c")[0] + free), {})

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
        self.assertEqual(violations("".join(theorem(n, outer) for n in "abc")),
                         {outer: ["a", "b", "c"]})
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
        """Run the check in the whole tree (`--all`) unless `flags` choose another scope."""
        if baseline is not None:
            self.baseline.write_text(json.dumps(baseline))
        scope = [] if {"--base", "--report", "--list"} & set(flags) else ["--all"]
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = c.main(["--root", str(self.root), "--baseline", str(self.baseline), *scope,
                           *flags])
        return code, out.getvalue(), err.getvalue()

    def test_at_the_baseline_passes(self) -> None:
        code, out, _ = self.run_main({"Complexity/Area/A.lean": {TERM: 3}})
        self.assertEqual(code, 0)
        self.assertIn("1 repeated compound encoding(s) in 1 module(s); every module matches", out)

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

    def test_list_ignores_the_baseline_and_always_succeeds(self) -> None:
        for baseline in ({"Complexity/Area/A.lean": {TERM: 3}}, {}, None):
            with self.subTest(baseline=baseline):
                code, out, err = self.run_main(baseline, "--list")
                self.assertEqual((code, err), (0, ""))
                self.assertIn(f"Complexity/Area/A.lean: `{TERM}` in 3 public signatures:", out)
                self.assertIn("Complexity/Area/A.lean:8: a", out)
                self.assertNotIn("baseline 3", out)
                self.assertIn("1 repeated compound encoding(s) in 1 of 1 checked module(s), and "
                              "0 local notation(s)", out)
                self.assertNotIn("Internal", out)
        self.assertEqual(self.run_main({}, "--all")[0], 1)  # the same tree fails enforcement

    def test_list_restricts_to_a_path_prefix(self) -> None:
        other = self.root / "Complexity/Areas/B.lean"
        other.parent.mkdir(parents=True)
        other.write_text(HEADER + "".join(theorem(n) for n in "xyz"))
        for prefix, shown, status in (
                ("Complexity/Area", "A.lean", "1 repeated compound encoding(s) in 1 of 1 checked "
                                              "module(s) under Complexity/Area,"),
                ("./Complexity/Areas/", "B.lean", "in 1 of 1 checked module(s) under"),
                ("Complexity/Area/A.lean", "A.lean", "in 1 of 1 checked module(s) under"),
                ("Complexity/Are", None, "0 repeated compound encoding(s) in 0 of 0 checked"),
                ("", "A.lean", "2 repeated compound encoding(s) in 2 of 2 checked module(s), and")):
            with self.subTest(prefix=prefix):
                code, out, _ = self.run_main(None, "--list", prefix)
                self.assertEqual(code, 0)
                self.assertIn(status, out)
                for name in ("A.lean", "B.lean"):
                    (self.assertIn if name == shown or not prefix else self.assertNotIn)(
                        f"{name}: `{TERM}`", out)

    def test_list_reports_local_notations_for_compound_encodings(self) -> None:
        self.module.write_text(
            HEADER + f'/-- A doc. -/\nlocal notation "encX" =>\n  {TERM}\n\n'
            'local notation "encY" => encPair encNat encBool\n'
            'notation "encZ" => encPair encNat (encList encBool)\n'
            'namespace Internal\nlocal notation "encW" => encList (encList encBool)\nend Internal\n'
            'local notation "encV" e => encPair e (encOption encBool)\n'
            "theorem a : True := trivial\n")
        code, out, _ = self.run_main(None, "--list")
        self.assertEqual(code, 0)
        self.assertIn(f'Complexity/Area/A.lean:9: local notation "encX" => {TERM}\n', out)
        self.assertIn('Complexity/Area/A.lean:17: local notation "encV" e => '
                      "encPair e (encOption encBool)\n", out)
        for name in ("encY", "encZ", "encW"):
            self.assertNotIn(name, out)
        self.assertIn("0 repeated compound encoding(s) in 0 of 1 checked module(s), and 2 local "
                      "notation(s)", out)
        self.assertEqual(self.run_main({}, "--all")[0], 0)  # notations never fail the check

    def test_list_combines_with_no_other_mode(self) -> None:
        for flags in (("--all",), ("--report",), ("--base", "origin/main"), ("--update-baseline",),
                      ("--update-baseline", "--allow-increase"), ("--summary",)):
            with self.subTest(flags=flags), self.assertRaises(SystemExit) as raised:
                self.run_main({}, "--list", *flags)
            self.assertEqual(raised.exception.code, 2)



class ScopeTests(unittest.TestCase):
    """A pull request enforces the baseline only in the modules it changes; merge groups and
    pushes only report."""

    OTHER = "encPair encUnary (encList encBool)"

    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.baseline = self.root / "baseline.json"
        self.write("Complexity/Area/A.lean", "abc")
        # `main` holds one more use in B than the baseline records: drift from a merge.
        self.write("Complexity/Other/B.lean", "abcd")
        self.entries = {"Complexity/Area/A.lean": {TERM: 3}, "Complexity/Other/B.lean": {TERM: 3}}
        self.baseline.write_text(json.dumps(self.entries))
        for args in (("init", "-q"), ("config", "user.name", "Fixture"),
                     ("config", "user.email", "fixture@example.invalid"), ("add", "."),
                     ("commit", "-qm", "base"), ("update-ref", "refs/remotes/origin/main", "HEAD")):
            subprocess.run(["git", *args], cwd=self.root, check=True, capture_output=True)

    def write(self, rel: str, names: str, term: str = TERM) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(HEADER + "".join(theorem(n, term) for n in names))

    def run_main(self, *flags: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = c.main(["--root", str(self.root), "--baseline", str(self.baseline), *flags])
        return code, out.getvalue(), err.getvalue()

    def test_a_new_violation_in_a_changed_module_fails(self) -> None:
        module = self.root / "Complexity/Area/A.lean"
        module.write_text(module.read_text() + "".join(theorem(n, self.OTHER) for n in "xyz"))
        code, _, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn(f"Complexity/Area/A.lean: `{self.OTHER}` in 3 public signatures:", err)
        self.assertNotIn("B.lean", err)

    def test_an_unchanged_module_above_the_baseline_is_only_reported(self) -> None:
        self.write("Complexity/Area/C.lean", "a")  # a change that adds no violation
        code, out, err = self.run_main()
        self.assertEqual((code, err), (0, ""))
        self.assertIn("Not enforced: 1 difference(s) from the baseline", out)
        self.assertEqual(self.run_main("--all")[0], 1)

    def test_a_stale_entry_in_a_changed_module_fails(self) -> None:
        self.write("Complexity/Area/A.lean", "ab")
        code, _, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("the baseline is stale", err)
        self.assertIn(f"Complexity/Area/A.lean: `{TERM}` in 0 public signature(s), baseline 3",
                      err)
        # Deleting a module touches it too.
        (self.root / "Complexity/Area/A.lean").unlink()
        self.assertEqual(self.run_main()[0], 1)

    def test_a_stale_entry_in_an_unchanged_module_is_only_reported(self) -> None:
        self.entries["Complexity/Other/B.lean"] = {TERM: 5}
        self.baseline.write_text(json.dumps(self.entries))
        self.write("Complexity/Area/C.lean", "a")
        code, out, _ = self.run_main()
        self.assertEqual(code, 0)
        self.assertIn("Not enforced: 1 difference(s)", out)

    def test_report_mode_always_succeeds(self) -> None:
        self.write("Complexity/Area/A.lean", "ab")
        self.write("Complexity/Area/C.lean", "xyz", self.OTHER)
        code, out, err = self.run_main("--report")
        self.assertEqual((code, err), (0, ""))
        self.assertIn(f"Complexity/Area/C.lean: `{self.OTHER}` in 3 public signatures:", out)
        self.assertIn("Stale baseline entries:", out)
        self.assertIn("report only, nothing is enforced", out)

    def test_update_rewrites_only_the_changed_modules(self) -> None:
        self.write("Complexity/Area/A.lean", "ab")
        code, out, _ = self.run_main("--update-baseline")
        self.assertEqual(code, 0)
        self.assertIn("for 1 changed module(s)", out)
        self.assertEqual(json.loads(self.baseline.read_text()),
                         {"Complexity/Other/B.lean": {TERM: 3}})
        self.assertEqual(self.run_main()[0], 0)

if __name__ == "__main__":
    unittest.main()
