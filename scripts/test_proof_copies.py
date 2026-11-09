"""Unit tests for scripts/proof_copies.py: local names, logical lines, which repeated blocks are
reported, the changed-lines mode on a scratch repository, the reports and the advisory exits."""

from __future__ import annotations

import contextlib
import io
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import proof_copies as pc  # noqa: E402

HEADER = "module\n\npublic section\n\nnamespace Fixture\n\n"


def block(h: str = "h", k: str = "k", hk: str = "hk", lemma: str = "Nat.add_comm",
          indent: str = "  ") -> str:
    """Five substantive tactic lines, as a copied block; the names can vary."""
    lines = [f"obtain ⟨{k}, {hk}⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt_succ {h})",
             f"rw [{hk}, {lemma}, Nat.add_sub_cancel] at {h}",
             f"refine Nat.le_trans (Nat.le_add_right {k} 1) ?_",
             f"exact Nat.succ_le_succ (Nat.zero_le (List.length (List.replicate {k} true)))",
             "exact absurd (Nat.lt_irrefl 0) (Nat.not_lt_zero 0)"]
    return "".join(f"{indent}{line}\n" for line in lines)


def theorem(name: str, body: str, binder: str = "h") -> str:
    return f"theorem {name} (n : Nat) ({binder} : n < 5) : n ≤ 5 := by\n{body}\n"


class LocalNameTests(unittest.TestCase):
    def names(self, line: str) -> set[str]:
        return pc.bound_names(pc.tokens(line))

    def test_binding_forms(self) -> None:
        self.assertEqual(self.names("intro x hx"), {"x", "hx"})
        self.assertEqual(self.names("rintro ⟨x, rfl⟩ | ⟨y, hy⟩"), {"x", "y", "hy"})
        self.assertEqual(self.names("obtain ⟨k, hk⟩ : ∃ k, P k := foo"), {"k", "hk"})
        self.assertEqual(self.names("rcases h with ⟨a, b⟩"), {"a", "b"})
        self.assertEqual(self.names("have hle (x : α) : f x ≤ g x := bar"), {"hle", "x"})
        self.assertEqual(self.names("set m := n + 1 with hm"), {"m", "hm"})
        self.assertEqual(self.names("refine fun a ha => ?_"), {"a", "ha"})
        self.assertEqual(self.names("case succ n ih => simp"), {"n", "ih"})
        self.assertEqual(self.names("| succ n ih => exact ih"), {"n", "ih"})
        self.assertEqual(self.names("| x :: xs => rfl"), {"x", "xs"})
        self.assertEqual(self.names("by_cases hp : p.Prime"), {"hp"})
        # Without a name, `by_cases` binds nothing: `Nat.Prime` and `p` are not bound here.
        self.assertEqual(self.names("by_cases Nat.Prime p"), set())
        self.assertEqual(self.names("have : ∀ y ∈ s, y ≤ t := foo"), {"y"})

    def test_signature(self) -> None:
        # Anonymous instance binders and the statement's free names are not local.
        self.assertEqual(pc.signature_names(" {α : Type} [Fintype α] (s t : Finset α) "
                                            "[inst : DecidableEq α] : ∀ x ∈ s, f x = g t"),
                         {"α", "s", "t", "inst", "x"})
        self.assertEqual(pc.signature_names(" ⦃a b⦄ (h : a ≤ b) : {x | x ≤ a} ⊆ {y | y ≤ b}"),
                         {"a", "b", "h", "x", "y"})

    def test_normalize_keeps_projections(self) -> None:
        line = pc.Line(1, 1, pc.tokens("· exact (hle.trans h.le).ge"))
        pc.normalize(line, {"hle", "h"})
        self.assertEqual(" ".join(line.norm), "exact ( ?.trans ?.le ) . ge")


class ScanTests(unittest.TestCase):
    def test_logical_lines_comments_and_names(self) -> None:
        text = HEADER + (
            "/-- A docstring that mentions theorem bogus : True := by trivial -/\n"
            "theorem one (n : Nat) (h : n < 5) : n ≤ 5 := by\n"
            "  -- a comment\n"
            "  simp only [Nat.add_zero,\n"
            "    Nat.zero_add]\n"
            "  /- a block comment -/\n"
            "  exact Nat.le_of_lt h\n"
            "def notAProof : Nat := 3\n"
            "private lemma two : True := trivial\n")
        proofs = pc.scan_file(text, "CslibFrontier/A.lean")
        self.assertEqual([(p.name, p.line) for p in proofs], [("one", 8), ("two", 15)])
        lines = proofs[0].lines
        self.assertEqual([(line.start, line.end) for line in lines], [(10, 11), (13, 13)])
        self.assertEqual(" ".join(lines[1].norm), "exact Nat.le_of_lt ?")

    def test_unterminated_comment_is_skipped(self) -> None:
        self.assertEqual(pc.scan_file("theorem t : True := by\n  /- open\n", "X.lean"), [])


class DetectionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.tmp.name)

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def write(self, rel: str, *theorems: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(HEADER + "\n".join(theorems), encoding="utf-8")

    def find(self, **thresholds: int) -> list[pc.Copy]:
        paths = sorted(str(p.relative_to(self.root))
                       for p in (self.root / "CslibFrontier").rglob("*.lean"))
        return pc.find(self.root, paths, None, **thresholds)[0]

    def pairs(self, **thresholds: int) -> list[tuple[str, str]]:
        return sorted(tuple(sorted((c.a.name, c.b.name))) for c in self.find(**thresholds))

    def test_copy_in_one_file_with_renamed_locals(self) -> None:
        self.write("CslibFrontier/Area/A.lean",
                   theorem("first", block()),
                   theorem("second", "  have hpos : 0 < 1 := Nat.one_pos\n"
                           + block(h="hlt", k="m", hk="hm"), binder="hlt"),
                   theorem("unrelated", "  exact Nat.le_of_lt (Nat.lt_succ_of_lt h)"))
        found = self.find()
        self.assertEqual([(c.a.name, c.b.name) for c in found], [("first", "second")])
        copy = found[0]
        self.assertEqual((copy.n, copy.renamed, copy.span("a"), copy.span("b")),
                         (5, (), (8, 12), (17, 21)))
        self.assertIn("`first` (lines 8–12) and `second` (lines 17–21) share 5 tactic lines",
                      copy.text())

    def test_copy_across_files_of_a_directory_only(self) -> None:
        self.write("CslibFrontier/Area/A.lean", theorem("first", block()))
        self.write("CslibFrontier/Area/B.lean", theorem("second", block(indent="    ")))
        self.write("CslibFrontier/Other/C.lean", theorem("third", block()))
        self.assertEqual(self.pairs(), [("first", "second")])
        copy = self.find()[0]
        self.assertIn("(CslibFrontier/Area/B.lean, lines 8–12)", copy.text())

    def test_renamed_constants(self) -> None:
        self.write("CslibFrontier/Area/A.lean", theorem("first", block()),
                   theorem("second", block(lemma="Nat.mul_comm")))
        copy = self.find()[0]
        self.assertEqual(copy.renamed, (("Nat.add_comm", "Nat.mul_comm"),))
        self.assertIn("with `Nat.add_comm` in place of `Nat.mul_comm`", copy.text())
        self.assertEqual(self.pairs(max_renamed=0), [])

    def test_one_differing_line_is_bridged(self) -> None:
        tail = ("  have hq := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 4) (Nat.le_refl 5)\n"
                "  rw [Nat.mul_comm, Nat.mul_one] at hq\n"
                "  exact Nat.le_trans (Nat.le_of_lt hq) (Nat.le_succ 5)\n"
                "  refine Or.elim (Nat.lt_or_ge n 3) (fun _ => ?_) (fun _ => ?_)\n"
                "  exact Nat.le_succ_of_le (Nat.le_refl 5)\n")
        changed = tail.replace("have hq := Nat.lt_of_lt_of_le", "apply le_of_eq <|")
        self.write("CslibFrontier/Area/A.lean", theorem("first", block() + tail),
                   theorem("second", block() + changed))
        copy, = self.find()
        self.assertEqual((copy.n, copy.gaps), (10, 1))
        self.assertIn("1 line(s) differ", copy.text())

    def test_trivial_repetition_is_not_reported(self) -> None:
        trivial = ("  intro x hx\n  simp only [Nat.add_zero, Nat.zero_add, Nat.add_comm, "
                   "Nat.mul_one]\n  simp only [Nat.one_mul, Nat.mul_comm] at hx\n  constructor\n"
                   "  · omega\n  · rfl\n  exact hx\n")
        self.write("CslibFrontier/Area/A.lean", theorem("first", trivial),
                   theorem("second", trivial))
        self.assertEqual(self.pairs(), [])

    def test_short_or_light_blocks_are_not_reported(self) -> None:
        short = "".join(block().splitlines(keepends=True)[:3])
        self.write("CslibFrontier/Area/A.lean", theorem("first", short),
                   theorem("second", short))
        self.assertEqual(self.pairs(), [])
        self.assertEqual(self.pairs(min_lines=3, min_weight=10), [("first", "second")])

    def test_repeated_line_pattern_is_not_reported(self) -> None:
        facts = "".join(f"  have h{i} : Fits w {i} := Fits.of_le hfit (Nat.le_of_lt (by decide))\n"
                        for i in range(1, 9))
        self.write("CslibFrontier/Area/A.lean", theorem("first", facts),
                   theorem("second", facts))
        self.assertEqual(self.pairs(), [])

    def test_repetition_within_one_proof(self) -> None:
        self.write("CslibFrontier/Area/A.lean",
                   theorem("both", "  constructor\n  · " + block(indent="    ")[4:]
                           + "  · " + block(h="h", k="j", hk="hj", indent="    ")[4:]))
        found = self.find()
        self.assertEqual([(c.a.name, c.b.name, c.span("a"), c.span("b")) for c in found],
                         [("both", "both", (9, 13), (14, 18))])

    def test_common_plumbing_is_skipped(self) -> None:
        self.write("CslibFrontier/Area/A.lean",
                   *(theorem(f"t{i}", block()) for i in range(4)))
        self.assertEqual(len(self.pairs()), 6)
        self.assertEqual(self.pairs(max_copies=3), [])


class ChangedLinesTests(unittest.TestCase):
    def test_new_copy_of_an_old_block(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)

            def git(*args: str) -> None:
                subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)

            def write(rel: str, *theorems: str) -> None:
                (root / rel).parent.mkdir(parents=True, exist_ok=True)
                (root / rel).write_text(HEADER + "\n".join(theorems), encoding="utf-8")

            git("init", "-q", "-b", "main")
            git("config", "user.name", "Fixture")
            git("config", "user.email", "fixture@example.invalid")
            git("config", "color.ui", "always")
            # Old repetition between two untouched proofs.
            write("CslibFrontier/Area/Old.lean", theorem("old_one", block()),
                  theorem("old_two", block(k="m", hk="hm")))
            write("CslibFrontier/Area/Other.lean",
                  theorem("other", "  exact Nat.le_of_lt (Nat.lt_succ_of_lt h)"))
            git("add", ".")
            git("commit", "-q", "-m", "base")
            git("checkout", "-q", "-b", "topic")
            write("CslibFrontier/Area/Other.lean",
                  theorem("other", "  exact Nat.le_of_lt (Nat.lt_succ_of_lt h)"),
                  theorem("fresh", block(k="j", hk="hj")))
            git("commit", "-qam", "copy")

            changed = pc.changed_ranges(root, "main")
            self.assertEqual(changed, {"CslibFrontier/Area/Other.lean": [(9, 16)]})
            found, examined = pc.find(root, sorted(changed), changed)
            self.assertEqual(examined, 2)
            self.assertEqual(sorted((c.a.name, c.b.name) for c in found),
                             [("fresh", "old_one"), ("fresh", "old_two")])
            self.assertTrue(all(c.a.path.endswith("Other.lean") for c in found))

            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertEqual(pc.main(["--base", "main", "--root", tmp, "--github"]), 0)
            text = out.getvalue()
            self.assertIn("2 candidate pair(s) of repeated proof blocks in the 2 proofs", text)
            self.assertIn("::notice file=CslibFrontier/Area/Other.lean,line=11,endLine=15,"
                          "title=Possible repeated proof block::`fresh`", text)
            self.assertNotIn("`old_one` (lines", text)


class ReportTests(unittest.TestCase):
    def copy(self) -> pc.Copy:
        lines = [pc.Line(10 + k, 10 + k, []) for k in range(4)]
        a = pc.Proof("CslibFrontier/A.lean", "alpha", 9, lines)
        b = pc.Proof("CslibFrontier/B.lean", "beta", 19, [pc.Line(20 + k, 20 + k, [])
                                                          for k in range(4)])
        return pc.Copy(a, b, 0, 0, 4, renamed=(("size", "wireCount"),), weight=20)

    def test_markdown(self) -> None:
        text = pc.markdown([self.copy()] * 3, 7, 2)
        self.assertIn("3 candidate pair(s) of repeated proof blocks in the 7 proofs examined. "
                      "The first 2 are listed. These are candidates, not findings.", text)
        self.assertEqual(text.count("\n- CslibFrontier/A.lean:10: `alpha` (lines 10–13) and "
                                    "`beta` (CslibFrontier/B.lean, lines 20–23) share 4 tactic "
                                    "lines, alike up to local names, with `size` in place of "
                                    "`wireCount`."), 2)
        self.assertIn("No repeated proof block in the 7 proofs examined.", pc.markdown([], 7, 2))

    def test_annotations_are_escaped(self) -> None:
        line, = pc.annotations([self.copy()], 10)
        self.assertTrue(line.startswith("::notice file=CslibFrontier/A.lean,line=10,endLine=13,"
                                        "title=Possible repeated proof block::`alpha`"))
        copy = self.copy()
        copy.a.path = "CslibFrontier/A,b:c.lean"
        self.assertIn("file=CslibFrontier/A%2Cb%3Ac.lean,", pc.annotations([copy], 10)[0])


class DriverTests(unittest.TestCase):
    def run_main(self, *argv: str) -> tuple[int, str]:
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = pc.main(list(argv))
        return code, out.getvalue()

    def test_bad_base_does_not_fail(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            subprocess.run(["git", "init", "-q"], cwd=tmp, check=True)
            code, out = self.run_main("--base", "no-such-ref", "--root", tmp)
        self.assertEqual(code, 0)
        self.assertIn("Repeated-proof-block notice skipped: the tool failed", out)

    def test_failure_goes_to_the_summary(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            (root / "CslibFrontier").mkdir()
            (root / "CslibFrontier/A.lean").write_text("theorem t : True := trivial\n")
            summary = root / "summary.md"
            with mock.patch.dict(os.environ, {"GITHUB_STEP_SUMMARY": str(summary)}), \
                    mock.patch.object(pc, "find", side_effect=RuntimeError("boom")):
                code, out = self.run_main("--all", "--root", tmp, "--github")
            self.assertEqual(code, 0)
            self.assertIn("skipped: the tool failed (boom)", out)
            self.assertIn("skipped: the tool failed (boom)", summary.read_text())

    def test_all_and_nothing_changed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            code, out = self.run_main("--all", "--root", tmp)
            self.assertEqual(code, 0)
            self.assertIn("no `CslibFrontier/` file added or modified", out)
            root = pathlib.Path(tmp)
            (root / "CslibFrontier").mkdir()
            (root / "CslibFrontier/A.lean").write_text(
                HEADER + theorem("first", block()) + theorem("second", block()))
            code, out = self.run_main("--all", "--root", tmp)
            self.assertEqual(code, 0)
            self.assertIn("1 candidate pair(s) of repeated proof blocks in the 2 proofs", out)


if __name__ == "__main__":
    unittest.main()
