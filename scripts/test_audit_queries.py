"""Unit tests for scripts/audit_queries.py."""

from __future__ import annotations

import contextlib
import io
import pathlib
import sys
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import audit_queries as aq  # noqa: E402


class HelperTests(unittest.TestCase):
    def test_generated_constants_belong_to_their_owner(self) -> None:
        owners = {"Foo": "Foo", "Foo.bar": "Foo", "baz": "baz", "Ns.f": "Ns.f"}
        self.assertEqual(aq.owner_of("Foo.bar", owners), "Foo")
        self.assertEqual(aq.owner_of("baz.eq_1", owners), "baz")
        self.assertEqual(aq.owner_of("baz.eq_def", owners), "baz")
        self.assertEqual(aq.owner_of("Foo.mk.injEq", owners), "Foo")
        self.assertEqual(aq.owner_of("Ns.f._proof_3", owners), "Ns.f")
        self.assertEqual(aq.owner_of("Ns.f.match_2.splitter", owners), None)
        self.assertIsNone(aq.owner_of("Foo.unrelated", owners))
        self.assertIsNone(aq.owner_of("Mathlib.thing", owners))

    def test_unfolding_by_name(self) -> None:
        self.assertTrue(aq.unfolds_by_name("f.eq_1", "f"))
        self.assertTrue(aq.unfolds_by_name("f.eq_def", "f"))
        self.assertTrue(aq.unfolds_by_name("f.induct", "f"))
        self.assertFalse(aq.unfolds_by_name("f", "f"))
        self.assertFalse(aq.unfolds_by_name("f.mk", "f"))
        self.assertFalse(aq.unfolds_by_name("fg.eq_1", "f"))

    def test_utf16_columns(self) -> None:
        self.assertEqual(aq.utf16_index("abc def", 4), 4)
        line = "𝔅 x := foo"  # 𝔅 takes two UTF-16 units
        self.assertEqual(line[aq.utf16_index(line, 8):], "foo")
        self.assertEqual(aq.utf16_index("ℕ → foo", 4), 4)

    def test_unfolding_positions(self) -> None:
        def at(before: str, previous: tuple[str, ...] = ()) -> bool:
            lines = [*previous, before + "target rest"]
            return aq.unfolds_at(lines, len(lines) - 1, len(before))

        self.assertTrue(at("  unfold "))
        self.assertTrue(at("  unfold other "))
        self.assertTrue(at("  delta "))
        self.assertTrue(at("  simp only [foo, "))
        self.assertTrue(at("  rw [← "))
        self.assertTrue(at("  simp (config := {}) only ["))
        self.assertTrue(at("    ", ("  simp only [foo,",)))
        self.assertFalse(at("  exact "))
        self.assertFalse(at("  rw [sum_coe_sort T fun i => p."))
        self.assertFalse(at("  simp [f "))
        self.assertFalse(at("  rw [show a = b from "))
        self.assertFalse(at("  exact ⟨"))
        self.assertFalse(at("  refine foo ["))

    def test_attributes_and_keywords(self) -> None:
        keyword, attrs = aq.header_info(
            "@[simp, aesop safe apply (rule_sets := [PolyTime]), local instance] theorem foo")
        self.assertEqual(keyword, "theorem")
        self.assertEqual(attrs, {"simp", "aesop"})
        self.assertEqual(aq.header_info("@[expose] public def bar")[0], "def")
        self.assertEqual(aq.header_info("@[deprecated (since := \"2026-10-19\")] alias x")[1],
                         {"deprecated"})
        self.assertEqual(aq.header_info("noncomputable instance")[0], "instance")
        self.assertEqual(aq.attribute_names("scoped simp, simps!"), {"simp", "simps"})

    def test_name_matching(self) -> None:
        self.assertTrue(aq.matches("Cslib.Foo.bar", "Foo.bar"))
        self.assertTrue(aq.matches("Cslib.Foo.bar", "Cslib.Foo.bar"))
        self.assertFalse(aq.matches("Cslib.Foo.foobar", "bar"))
        self.assertTrue(aq.matches("_private.Complexity.A.B.0.Cslib.Foo.bar", "Foo.bar"))


def declaration(name: str, line: int, sort: str = "theorem", **refs) -> dict:
    return {"name": name, "module": "CslibFrontier.A", "path": "A.lean", "role": "decl",
            "range": [line, 0, line, 1, line, 8, line, 9], "sort": sort, "local_uses": 0,
            "implicit": [], "lib_refs": set(), "test_refs": set(), "abstract_refs": set(),
            **refs}


class QueryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.decls = {
            "A.used": declaration("A.used", 3, lib_refs={"CslibFrontier.B", "CslibFrontier.C"},
                                  test_refs={"CslibFrontierTests.A"}),
            "A.local": declaration("A.local", 5, local_uses=2, implicit=["simp"]),
            "A.none": declaration("A.none", 7, sort="definition"),
            "A.tested": declaration("A.tested", 9, abstract_refs={"CslibFrontierAbstracts.X"}),
        }
        self.decls["B.used"] = {**declaration("B.used", 4), "module": "CslibFrontier.B",
                                "path": "B.lean"}

    def test_references_list_users_by_role(self) -> None:
        self.assertEqual(aq.reference_lines(self.decls, ["CslibFrontier/A.lean"], unused=False), [
            "CslibFrontier/A.lean:3: A.used (theorem): library CslibFrontier.B, CslibFrontier.C; "
            "tests CslibFrontierTests.A",
            "CslibFrontier/A.lean:5: A.local (theorem): only its own module "
            "[used implicitly through simp?]",
            "CslibFrontier/A.lean:7: A.none (definition): nowhere",
            "CslibFrontier/A.lean:9: A.tested (theorem): abstracts CslibFrontierAbstracts.X",
        ])

    def test_unused_keeps_declarations_no_other_module_names(self) -> None:
        for decl in self.decls.values():
            decl["category"] = ("outside" if decl["lib_refs"] else "tests_only"
                                if decl["test_refs"] or decl["abstract_refs"] else "unreferenced")
        lines = aq.reference_lines(self.decls, ["CslibFrontier/"], unused=True)
        self.assertEqual([line.split(": ")[1].split()[0] for line in lines],
                         ["A.local", "A.none", "B.used"])

    def test_duplicates_with_a_member_under_a_prefix(self) -> None:
        groups = [{"kind": "thm", "members": [("CslibFrontier.A", "A.used"),
                                              ("CslibFrontier.B", "B.used")]}]
        expected = ["alpha-equivalent statements:", "  CslibFrontier/A.lean:3: A.used",
                    "  CslibFrontier/B.lean:4: B.used"]
        self.assertEqual(aq.duplicate_lines(groups, self.decls, []), expected)
        self.assertEqual(aq.duplicate_lines(groups, self.decls, ["CslibFrontier/B"]), expected)
        self.assertEqual(aq.duplicate_lines(groups, self.decls, ["CslibFrontier/C"]), [])

    def test_command_line(self) -> None:
        for decl in self.decls.values():
            decl["category"] = "outside" if decl["lib_refs"] else "unreferenced"
        out = io.StringIO()
        with mock.patch.object(aq.lo, "check_outputs"), mock.patch.object(aq.lo, "Library"), \
                mock.patch.object(aq.lo, "collect_declarations", return_value=(self.decls, {})), \
                mock.patch.object(aq, "annotate_headers"), \
                mock.patch.object(aq, "collect_references"), mock.patch.object(aq, "classify"), \
                contextlib.redirect_stdout(out):
            self.assertEqual(aq.main(["references", "--unused", "CslibFrontier/B.lean"]), 0)
        self.assertEqual(out.getvalue(), "CslibFrontier/B.lean:4: B.used (theorem): nowhere\n")
        for argv in (["references"], ["duplicates", "--unused"]):
            with self.subTest(argv=argv), self.assertRaises(SystemExit), \
                    contextlib.redirect_stderr(io.StringIO()):
                aq.main(argv)

    def test_classify(self) -> None:
        decl = {**declaration("A.inst", 1), "kind": "def", "keyword": "instance",
                "attrs": {"simp"}}
        aq.classify({"A.inst": decl})
        self.assertEqual((decl["category"], decl["sort"], decl["implicit"]),
                         ("unreferenced", "instance", ["simp", "instance"]))


if __name__ == "__main__":
    unittest.main()
