"""Unit tests for scripts/class_inclusions.py."""

from __future__ import annotations

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import class_inclusions as ci  # noqa: E402


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

    def test_complement_pairs_are_symmetric(self) -> None:
        for a, b in ci.COMPLEMENT.items():
            self.assertEqual(ci.COMPLEMENT[b], a)
            self.assertNotIn(a, ci.CO_CLOSED)


if __name__ == "__main__":
    unittest.main()
