"""Unit tests for scripts/check_probability_idioms.py, on synthetic Lean modules."""

from __future__ import annotations

import contextlib
import io
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_probability_idioms as c  # noqa: E402

HEADER = "module\n-- upstream: candidate\n\npublic import CslibFrontier.Init\n\npublic section\n\n"


def found(source: str) -> list[tuple[str, int, str]]:
    return [(row.declaration, row.line, row.category) for row in c.module_findings(HEADER + source)]


def categories(source: str) -> list[str]:
    return [category for _, _, category in found(source)]


class RuleTests(unittest.TestCase):
    def test_raw_success_probabilities_in_statements_count(self) -> None:
        self.assertEqual(found("theorem t : (ProbComp.eval game true).toReal ≤ 1 / 2 := sorry\n"),
                         [("t", 8, "eval_statement")])
        self.assertEqual(categories(
            "theorem t (q : ℕ) :\n    ProbComp.eval (game q) true ≤ 1 / q := sorry\n"
            "lemma u : (Cslib.ProbComp.eval (do let b ← g; pure b) true).toReal = 0 := sorry\n"
            "theorem v : Game.succProbability (ProbComp.eval (game 1)) ≤ ε := sorry\n"),
            ["eval_statement"] * 3)
        # Hypotheses are part of the statement.
        self.assertEqual(categories("theorem t (h : ProbComp.eval g true ≤ ε) : True := sorry\n"),
                         ["eval_statement"])

    def test_distribution_equalities_and_other_outcomes_do_not_count(self) -> None:
        self.assertEqual(categories(
            "theorem t : ProbComp.eval g₁ = ProbComp.eval g₂ := sorry\n"
            "theorem u : ProbComp.eval g false = 1 / 2 := sorry\n"
            "theorem v : ProbComp.evalWith g true = 0 := sorry\n"
            "theorem w : Pr[g] ≤ 1 / 2 := sorry\n"), [])

    def test_mass_facts_private_theorems_and_proofs_do_not_count(self) -> None:
        self.assertEqual(categories(
            "theorem eval_game_true : ProbComp.eval game true = 1 / 2 := sorry\n"
            "@[simp] theorem Foo.bind_apply_true : ProbComp.eval g true = 0 := sorry\n"
            "private theorem t : ProbComp.eval game true ≤ 1 := sorry\n"
            "theorem u : True := by\n  have := ProbComp.eval game true\n  trivial\n"
            "/-- `ProbComp.eval game true` -/\ntheorem v : True := trivial\n"), [])
        # `toReal_eval_*` names are renamed to `probability_*`, so they count.
        self.assertEqual(categories(
            "theorem toReal_eval_game : (ProbComp.eval game true).toReal = 1 := sorry\n"),
            ["eval_statement"])

    def test_uniform_calls_in_definition_bodies_count(self) -> None:
        self.assertEqual(found("def game : ProbComp Bool := do\n"
                               "  let a ← ProbComp.uniform (ZMod 5)\n  pure (a = 0)\n"),
                         [("game", 9, "uniform_call")])
        self.assertEqual(categories(
            "private def g : ProbComp Bool := Cslib.ProbComp.uniform Bool\n"
            "abbrev h : ProbComp Bool := ProbComp.uniform Bool\n"
            "noncomputable instance : Inhabited (ProbComp Bool) := ⟨ProbComp.uniform Bool⟩\n"),
            ["uniform_call"] * 3)

    def test_notation_lemma_names_statements_and_certificates_do_not_count(self) -> None:
        self.assertEqual(categories(
            "def game : ProbComp Bool := do\n  let a ← $ᵗ (ZMod 5)\n  pure (a = 0)\n"
            "def g : ProbComp Bool := ProbComp.uniform_bind_eq ▸ x\n"
            "theorem t : ProbComp.eval (ProbComp.uniform Bool) true = 1 / 2 := sorry\n"
            "def h : ProbComp Bool := by exact ProbComp.uniform Bool\n"
            "@[program_certificate] def k : ProbComp Bool := ProbComp.uniform Bool\n"),
            ["eval_statement"])


class RatchetTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.write("CslibFrontier/Crypto/A.lean", self.module(1))
        self.write("CslibFrontier/Probability/P.lean", self.module(2))
        self.write("scripts/probability_idioms_baseline.json", json.dumps(
            {"CslibFrontier/Crypto/A.lean": {"eval_statement": 1, "uniform_call": 1}}))
        self.git("add", ".")
        self.git("commit", "-qm", "base")
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")

    @staticmethod
    def module(n: int) -> str:
        return HEADER + "".join(f"theorem t{i} : (ProbComp.eval g true).toReal ≤ 1 := sorry\n"
                                f"def g{i} : ProbComp Bool := ProbComp.uniform Bool\n"
                                for i in range(n))

    def git(self, *args: str) -> str:
        return subprocess.check_output(["git", *args], cwd=self.root, text=True)

    def write(self, rel: str, text: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def run_main(self, *args: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = c.main([*args, "--root", str(self.root)])
        return code, out.getvalue(), err.getvalue()

    def test_a_changed_module_may_not_add_findings_of_a_category(self) -> None:
        self.write("CslibFrontier/Crypto/A.lean",
                   self.module(1) + "def h : ProbComp Bool := ProbComp.uniform Bool\n")
        code, _, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("CslibFrontier/Crypto/A.lean [uniform_call]: 2 finding(s), baseline 1:", err)
        self.assertIn("CslibFrontier/Crypto/A.lean:10: h: uniform_call `ProbComp.uniform`", err)
        self.assertIn("`$ᵗ α`", err)

    def test_new_modules_start_at_zero_and_pmf_algebra_modules_are_not_checked(self) -> None:
        self.write("CslibFrontier/Crypto/New.lean", self.module(1))
        self.assertEqual(self.run_main()[0], 1)
        self.write("CslibFrontier/Crypto/New.lean", HEADER + "theorem t : Pr[g] ≤ 1 := sorry\n")
        self.write("CslibFrontier/Probability/P.lean", self.module(3))
        self.write("CslibFrontier/Languages/Probabilistic/Q.lean", self.module(1))
        self.assertEqual(self.run_main()[0], 0)
        self.assertEqual(self.run_main("--all")[0], 0)

    def test_the_whole_baseline_regenerates_without_excluded_modules(self) -> None:
        (self.root / "scripts/probability_idioms_baseline.json").unlink()
        self.assertEqual(self.run_main("--update-baseline", "--all", "--allow-increase")[0], 0)
        self.assertEqual(
            json.loads((self.root / "scripts/probability_idioms_baseline.json").read_text()),
            {"CslibFrontier/Crypto/A.lean": {"eval_statement": 1, "uniform_call": 1}})


class RepositoryTests(unittest.TestCase):
    def test_the_checked_in_baseline_is_well_formed(self) -> None:
        baseline = c.ratchet.load_baseline(c.RATCHET, c.BASELINE)
        self.assertEqual(c.BASELINE.read_text(), c.ratchet.baseline_text(c.RATCHET, baseline))
        self.assertFalse([path for path, _ in baseline if path.startswith(c.EXCLUDED)])


if __name__ == "__main__":
    unittest.main()
