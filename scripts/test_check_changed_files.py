"""Unit tests for scripts/check_changed_files.py."""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_changed_files as c  # noqa: E402

MODULE = """module
-- upstream: candidate

/-!
# Demo

## Main definitions

* `Demo.thing`: a definition.
* `Demo.Thing.field`, `privateHelper`: a field and a private helper.
* `demo_tactic`, `fun_prop`: a tactic this library declares and an upstream one.
* `Qᶜ`, `thing_*`, `a ≤ b`: notation and patterns are not checked; `notChecked` follows a colon.

## Main results

* `thing_spec`: by its last components.
"""


def ilean(module: str, decls: list[str], references: list[str] = ()) -> dict:
    return {"module": module, "decls": {name: [] for name in decls}, "directImports": [],
            "references": {json.dumps({"c": {"m": module, "n": name}}): {}
                           for name in references}}


ILEANS = {
    "Complexity.Demo": ilean("Complexity.Demo",
                             ["Demo.thing", "Demo.thing_spec",
                              "_private.Complexity.Demo.0.Demo.privateHelper"],
                             ["Demo.Thing.field"]),
}


class DocNameTests(unittest.TestCase):
    def check(self, text: str, ileans: dict = ILEANS) -> list[str]:
        syntax = c.syntax_names('syntax (name := demoTactic) "demo_tactic" : tactic\n')
        return c.unresolved_doc_names("Complexity/Demo.lean", text, c.known_names(ileans), syntax)

    def test_listed_names_resolve(self) -> None:
        self.assertEqual(self.check(MODULE + "-/\n"), [])

    def test_module_doc_examples_in_literals_and_comments_are_ignored(self) -> None:
        doc = "/-!\n## Main results\n\n* `Missing.example`: example only.\n-/"
        for text in (f'def text := "{doc}"\n', f'def text := r##"{doc}"##\n',
                     "/- Example:\n" + doc + "\n-/\n",
                     "-- " + doc.replace("\n", "\n-- ") + "\n"):
            with self.subTest(text=text):
                self.assertEqual(self.check(text), [])

    def test_module_doc_names_after_nested_comments_are_checked(self) -> None:
        text = ("/-!\n# Demo\n/- Outer /- nested -/ comment -/\n\n"
                "## Main results\n\n* `Missing.actual`: must be checked.\n-/\n")
        self.assertEqual(self.check(text), [
            "Complexity/Demo.lean:7: `Missing.actual` is listed in a \"Main …\" section of the "
            "module docstring but names no declaration"])

    def test_declaration_docstrings_are_not_module_docs(self) -> None:
        text = ("/-!\n## Main results\n\n* `thing_spec`: a real module entry.\n-/\n"
                "/--\n## Main results\n\n* `Missing.example`: a declaration's example.\n-/\n"
                "theorem exampleTheorem : True := trivial\n")
        self.assertEqual(c.listed_identifiers(text), ["thing_spec"])
        self.assertEqual(self.check(text), [])

    def test_missing_name_is_reported_once_with_its_line(self) -> None:
        text = MODULE + "\n## Main statements\n\n* `Demo.renamed`, `renamed`: gone.\n-/\n"
        self.assertEqual(self.check(text.replace("`renamed`", "`Demo.renamed`")), [
            "Complexity/Demo.lean:20: `Demo.renamed` is listed in a \"Main …\" section of the "
            "module docstring but names no declaration"])

    def test_suffix_must_end_on_a_component_boundary(self) -> None:
        self.assertEqual(len(self.check("/-!\n## Main results\n\n* `ing_spec`: x\n-/\n")), 1)
        self.assertEqual(len(self.check("/-!\n## Main results\n\n* `Other.thing`: x\n-/\n")), 1)

    def test_other_sections_and_descriptions_are_not_checked(self) -> None:
        text = "/-!\n## Implementation notes\n\n* `missing`: x\n\nSee `missing` too.\n-/\n"
        self.assertEqual(self.check(text), [])

    def test_listed_names(self) -> None:
        doc = """
# Title

Mentions `Ignored.name` in prose.

## Main definitions

* `Foo.bar`, `Foo.baz`: two things, related to `NotListed`.
* `Long.first`,
  `Long.second`: a bullet continued on the next line.
* `.relative`: a name relative to the previous one.
* `u ≼ v` is notation, not a name.

## Main results

* `Foo.bar_spec`

## References
* `Not.a.result`: references are not listed.
"""
        self.assertEqual(c.listed_names(doc), [
            "Foo.bar", "Foo.baz", "Long.first", "Long.second", "relative", "Foo.bar_spec"])

    def test_syntax_names(self) -> None:
        text = ('syntax (name := foSimp) "fo_simp" (simpArgs)? : tactic\n'
                'scoped macro "ppt " : tactic => `(tactic| rfl)\n'
                '@[inherit_doc] local elab "x_y" : term => pure default\n'
                'declare_aesop_rule_sets [PolyTime, PPT]\n'
                'register_simp_attr fo_realize\n'
                '  syntax "indented" : tactic\n')
        self.assertEqual(c.syntax_names(text),
                         {"fo_simp", "ppt", "x_y", "PolyTime", "PPT", "fo_realize"})

    def test_identifiers(self) -> None:
        for name in ("a.b", "α_1'", "ℓ₂", "Nat.«term_+_»", "x!?"):
            self.assertTrue(c.NAME.fullmatch(name), name)
        for name in ("Qᶜ", "foo_*", "a ≤ b", "1x", "λ"):
            self.assertFalse(c.NAME.fullmatch(name), name)

    def test_ileans_load_only_when_a_listed_name_needs_them(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            (root / "Complexity").mkdir()
            (root / "Complexity/Plain.lean").write_text("/-! # No lists -/\n")
            (root / "Complexity/Demo.lean").write_text(MODULE + "-/\n")

            def unavailable() -> dict:
                raise AssertionError("loaded build outputs")
            self.assertEqual(c.check_doc_names(root, ["Complexity/Plain.lean"], unavailable), [])
            errors = c.check_doc_names(root, ["Complexity/Demo.lean"], lambda: ILEANS)
            self.assertEqual(errors, ["Complexity/Demo.lean:11: `demo_tactic` is listed in a "
                                      "\"Main …\" section of the module docstring but names no "
                                      "declaration"])


class RestatementTests(unittest.TestCase):
    HEADER = "import Complexity.Demo\n\nnamespace DemoTests\n\n"

    def test_restatements_only_fail(self) -> None:
        text = self.HEADER + ("/-- doc -/\nexample (n : Nat) : n = n := @Demo.self_eq\n"
                              "example := @Demo.thing  -- comment\n"
                              "example : True := by exact Demo.thing_spec\n"
                              "example (h : Nat := 0) :\n    True :=\n  Demo.thing_spec\n")
        self.assertTrue(c.restatement_only(text))

    def test_a_concrete_example_passes(self) -> None:
        for body in ("Demo.thing 3", "by decide", "⟨trivial, trivial⟩", "by\n  exact foo\n  rfl",
                     "rfl", "@rfl", "by exact trivial"):
            with self.subTest(body=body):
                text = self.HEADER + f"example := @Demo.thing\nexample : P := {body}\n"
                self.assertFalse(c.restatement_only(text))

    def test_where_and_equation_examples_are_not_restatements(self) -> None:
        self.assertFalse(c.restatement_only(self.HEADER + "example : Foo where\n  x := y\n"))
        self.assertFalse(c.restatement_only(self.HEADER + "example : Nat → Nat\n  | n => n\n"))

    def test_files_without_examples_and_abstract_clients_pass(self) -> None:
        self.assertFalse(c.restatement_only(self.HEADER + "theorem t : True := trivial\n"))
        self.assertFalse(c.restatement_only(
            "import ComplexityAbstracts.DemoAbstract\n\nexample := @Demo.thing\n"))
        self.assertFalse(c.restatement_only(
            "open ComplexityAbstracts.DemoAbstract in\nexample := @demoHeadline\n"))
        # A mention in a comment does not pin anything.
        self.assertTrue(c.restatement_only(
            "-- see ComplexityAbstracts\nexample := @Demo.thing\n"))


class ChangedFileTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.write("Complexity/Old.lean", "/-! # Old\n\n## Main results\n\n* `gone`: x\n-/\n")
        self.write("Complexity/Kept.lean", "def kept := 1\n")
        self.write("ComplexityTests/Old.lean", "example := @kept\n")
        self.git("add", ".")
        self.git("commit", "-qm", "base")
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")

    def git(self, *args: str) -> str:
        return subprocess.check_output(["git", *args], cwd=self.root, text=True)

    def write(self, rel: str, text: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def run_main(self) -> tuple[int, str]:
        import contextlib
        import io
        err = io.StringIO()
        with contextlib.redirect_stderr(err), contextlib.redirect_stdout(io.StringIO()):
            code = c.main(["--no-build-check"], root=self.root)
        return code, err.getvalue()

    def test_only_added_and_modified_files_are_checked(self) -> None:
        self.write("Complexity/Kept.lean", "def kept := 2\n")
        self.write("ComplexityTests/New.lean", "example := @kept\n")
        self.git("add", "ComplexityTests/New.lean")
        self.git("commit", "-qm", "change")
        self.write("ComplexityTests/Untracked.lean", "example : True := trivial\n")
        self.git("checkout", "-q", "-b", "side")
        (self.root / "Complexity/Old.lean").unlink()
        self.assertEqual(c.changed_files(self.root, "origin/main"),
                         (["ComplexityTests/New.lean", "ComplexityTests/Untracked.lean"],
                          ["Complexity/Kept.lean"]))
        code, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertEqual(err.count("ERROR"), 1)
        self.assertIn("ERROR: ComplexityTests/New.lean: every example only restates", err)

    def test_base_without_merge_base_is_compared_directly(self) -> None:
        self.git("checkout", "-q", "--orphan", "unrelated")
        self.write("ComplexityTests/Old.lean", "example : 1 + 1 = 2 := rfl\n")
        self.git("add", ".")
        self.git("commit", "-qm", "unrelated")
        self.assertEqual(c.changed_files(self.root, "origin/main"),
                         ([], ["ComplexityTests/Old.lean"]))


if __name__ == "__main__":
    unittest.main()
