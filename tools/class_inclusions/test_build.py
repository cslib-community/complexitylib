"""Unit tests for tools/class_inclusions/build.py."""

from __future__ import annotations

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import build as ci  # noqa: E402


class CloseTests(unittest.TestCase):
    def test_chains_inclusions(self) -> None:
        sub, non = ci.close(["A", "B", "C"], [("A", "subset", "B"), ("B", "subset", "C")],
                            complements=False)
        self.assertIn(("A", "C"), sub)
        self.assertNotIn(("C", "A"), sub)
        self.assertEqual(non, set())

    def test_equality_gives_both_directions(self) -> None:
        sub, _ = ci.close(["A", "B"], [("A", "eq", "B")], complements=False)
        self.assertIn(("A", "B"), sub)
        self.assertIn(("B", "A"), sub)

    def test_non_inclusion_propagates_outward(self) -> None:
        # Z ⊄ Y with Z ⊆ A and B ⊆ Y gives A ⊄ B.
        facts = [("Z", "subset", "A"), ("B", "subset", "Y"), ("Z", "not_subset", "Y")]
        _, non = ci.close(["A", "B", "Y", "Z"], facts, complements=False)
        self.assertIn(("A", "B"), non)
        self.assertIn(("Z", "Y"), non)
        self.assertNotIn(("B", "A"), non)

    def test_strict_inclusion_refutes_reverse(self) -> None:
        sub, non = ci.close(["A", "B"], [("A", "ssubset", "B")], complements=False)
        self.assertIn(("A", "B"), sub)
        self.assertIn(("B", "A"), non)

    def test_complements(self) -> None:
        # NP ⊆ P would give coNP ⊆ P, since P is closed under complement.
        sub, _ = ci.close(["P", "NP", "coNP"], [("NP", "subset", "P")], complements=True)
        self.assertIn(("coNP", "P"), sub)
        sub, _ = ci.close(["P", "NP", "coNP"], [("NP", "subset", "P")], complements=False)
        self.assertNotIn(("coNP", "P"), sub)


class LiteratureTests(unittest.TestCase):
    def test_literature_layer_is_consistent(self) -> None:
        for _, grid in ci.GRIDS:
            literature = [f for f in ci.LITERATURE if f[0] in grid and f[2] in grid]
            known, false = ci.close(list(grid), literature, complements=grid is ci.UNIFORM)
            self.assertEqual(known & false, set())

    def test_expspace(self) -> None:
        known, false = ci.close(list(ci.UNIFORM), [f for f in ci.LITERATURE if f[0] in ci.UNIFORM],
                                complements=True)
        self.assertIn(("NP", "EXPSPACE"), known)
        self.assertIn(("EXPSPACE", "coNP"), false)
        # EXP = EXPSPACE and NEXP = EXPSPACE are open.
        for a in ("EXP", "NEXP"):
            self.assertNotIn(("EXPSPACE", a), known | false)

    def test_complement_pairs_are_symmetric(self) -> None:
        for a, b in ci.COMPLEMENT.items():
            self.assertEqual(ci.COMPLEMENT[b], a)
            self.assertNotIn(a, ci.CO_CLOSED)


def theorem(module: str, name: str) -> dict:
    return {"kind": "theorem", "docLink": f"./CslibFrontier/{module}.html#{name}"}


class IndexTests(unittest.TestCase):
    def test_reads_local_theorems_and_links_from_the_site_root(self) -> None:
        index = {"declarations": {
            "Cslib.Complexity.P_subset_NP": theorem("Classes/NP", "Cslib.Complexity.P_subset_NP"),
            "Cslib.Complexity.NP_def": {"kind": "def", "docLink": "./CslibFrontier/X.html#d"},
            "Mathlib.Foo.P_subset_NP": {"kind": "theorem", "docLink": "./Mathlib/Foo.html#x"},
        }}
        self.assertEqual(ci.load_theorems(index), {"P_subset_NP": (
            "Cslib.Complexity.P_subset_NP",
            "../CslibFrontier/Classes/NP.html#Cslib.Complexity.P_subset_NP")})

    def test_render_links_direct_marks_and_rejects_contradictions(self) -> None:
        names = ["P_subset_NP", "NC_subset_AC", "NC_mono", "AC_subset_NC_succ",
                 "NC_subset_PPoly", "AC_subset_PPoly"]
        index = {"declarations": {f"Cslib.{n}": theorem("M", f"Cslib.{n}") for n in names}}
        page = ci.render(index)
        self.assertIn('href="../CslibFrontier/M.html#Cslib.P_subset_NP"', page)
        self.assertIn('class="known"', page)
        # The library cannot prove what the literature layer calls open.
        index["declarations"]["Cslib.NP_subset_P"] = theorem("M", "Cslib.NP_subset_P")
        with self.assertRaisesRegex(ValueError, "NP vs P"):
            ci.render(index)

    def test_missing_extra_theorem_is_reported(self) -> None:
        with self.assertRaisesRegex(ValueError, "NC_subset_AC"):
            ci.render({"declarations": {}})


if __name__ == "__main__":
    unittest.main()
