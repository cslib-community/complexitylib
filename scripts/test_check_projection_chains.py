"""Unit tests for scripts/check_projection_chains.py, on synthetic Lean modules."""

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
import check_projection_chains as c  # noqa: E402

HEADER = "module\n-- upstream: candidate\n\npublic import CslibFrontier.Init\n\npublic section\n\n"


def found(source: str) -> list[tuple[str, int, str]]:
    return [(row.declaration, row.line, row.chain)
            for row in c.module_chains(HEADER + source)]


def chains(source: str) -> list[str]:
    return [chain for _, _, chain in found(source)]


class RuleTests(unittest.TestCase):
    def test_statements_and_definition_bodies_count(self) -> None:
        self.assertEqual(found("theorem t (c : (ℕ × ℕ) × ℕ) : c.1.2 = c.1.2 := rfl\n"),
                         [("t", 8, ".1.2"), ("t", 8, ".1.2")])
        self.assertEqual(found("def f (c : (ℕ × ℕ) × ℕ) : ℕ :=\n  c.1.2 + c.2.fst\n"),
                         [("f", 9, ".1.2"), ("f", 9, ".2.fst")])
        self.assertEqual(chains("def f (c : (ℕ × ℕ) × ℕ) : ℕ :=\n  c.1.2 + (g c).2.1.1\n"),
                         [".1.2", ".2.1.1"])
        self.assertEqual(chains("instance : Foo ((ℕ × ℕ) × ℕ) := ⟨fun c => c.1.1⟩\n"), [".1.1"])
        self.assertEqual(chains("structure S where\n  f : (ℕ × ℕ) × ℕ\n  h : f.1.2 = 0\n"),
                         [".1.2"])
        self.assertEqual(chains("def f : (ℕ × ℕ) × ℕ → ℕ := (·.1.2)\n"), [".1.2"])

    def test_single_projections_and_literals_do_not_count(self) -> None:
        self.assertEqual(chains("theorem t (p : ℕ × ℕ) : p.1 + p.2 = p.2 + p.1 := by omega\n"
                                "def x : Float := 1.5\ndef v : String := \"1.5.2\"\n"), [])
        self.assertEqual(chains("def f := g 1.5.2\n"), [])

    def test_proofs_and_tactic_blocks_do_not_count(self) -> None:
        self.assertEqual(chains("theorem t (c : (ℕ × ℕ) × ℕ) : True := by\n"
                                "  have := c.1.2\n  trivial\n"), [])
        self.assertEqual(chains("theorem t (c : (ℕ × ℕ) × ℕ) : True := ⟨c.1.2⟩\n"), [])
        self.assertEqual(chains("def f (c : (ℕ × ℕ) × ℕ) : {n // n = c.1.1} :=\n"
                                "  ⟨c.1.1, by simp [c.1.2]⟩\n"), [".1.1", ".1.1"])
        self.assertEqual(chains("def f : ℕ → ℕ\n  | n => n\ntermination_by n => n.1.2\n"), [])

    def test_private_declarations_comments_and_variables_do_not_count(self) -> None:
        self.assertEqual(chains("private def f (c : (ℕ × ℕ) × ℕ) : ℕ := c.1.2\n"
                                "-- def g := c.1.2\n/-- `c.1.2` in a docstring -/\n"
                                "theorem t : True := trivial\n"
                                "variable (h : ∀ c : (ℕ × ℕ) × ℕ, c.1.2 = 0)\n"), [])
        self.assertEqual(c.module_chains("module\n\ntheorem t (c : (ℕ × ℕ) × ℕ) : c.1.2 = 0 := "
                                         "sorry\n"), [])  # not public in a module

    def test_internal_declarations_count(self) -> None:
        self.assertEqual(chains("namespace Internal\n\n"
                                "theorem t (c : (ℕ × ℕ) × ℕ) : c.1.2 = 0 := sorry\n\nend Internal\n"),
                         [".1.2"])

    def test_standing_exceptions(self) -> None:
        # Conclusions that automation looks up by head.
        self.assertEqual(chains("@[program_certificate] theorem t :\n"
                                "    ComputableInPolyTime (fun c => step c.1.1 c.1.2) e e := sorry\n"
                                "@[fun_prop] theorem u : Foo (fun c => c.1.2) := sorry\n"), [])
        self.assertEqual(chains("theorem t (h : c.1.2 = 0) :\n"
                                "    ComputableInPolyTime (fun c => step c.1.1 c.1.2) e e := sorry\n"),
                         [".1.2"])
        # Named accessors are the remedy.
        self.assertEqual(chains("abbrev Ctx.desc (c : Ctx) : D := c.1.1\n"
                                "def Ctx.cfg : Ctx → C := fun c => c.1.2\n"), [])
        self.assertEqual(chains("def Ctx.both (c : Ctx) : D × C := (c.1.1, c.1.2)\n"),
                         [".1.1", ".1.2"])


class RatchetTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.write("CslibFrontier/A.lean", self.module(2))
        self.write("CslibFrontier/B.lean", self.module(1))
        self.write("scripts/projection_chains_baseline.json",
                   json.dumps({"CslibFrontier/A.lean": 2, "CslibFrontier/B.lean": 1}))
        self.git("add", ".")
        self.git("commit", "-qm", "base")
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")

    @staticmethod
    def module(n: int) -> str:
        return HEADER + "".join(f"theorem t{i} (c : (ℕ × ℕ) × ℕ) : c.1.2 = 0 := sorry\n"
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

    def baseline(self) -> dict[str, int]:
        return json.loads((self.root / "scripts/projection_chains_baseline.json").read_text())

    def test_a_changed_module_may_not_add_chains(self) -> None:
        self.write("CslibFrontier/A.lean", self.module(3))
        code, _, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("CslibFrontier/A.lean: 3 chain(s), baseline 2:", err)
        self.assertIn("CslibFrontier/A.lean:10: t2: `.1.2`", err)

    def test_a_new_module_starts_at_zero(self) -> None:
        self.write("CslibFrontier/New.lean", self.module(1))
        self.assertEqual(self.run_main()[0], 1)
        self.write("CslibFrontier/New.lean", HEADER + "theorem t (p : ℕ × ℕ) : p.1 = p.1 := rfl\n")
        self.assertEqual(self.run_main()[0], 0)

    def test_fewer_chains_pass_with_a_note_and_the_baseline_comes_down(self) -> None:
        self.write("CslibFrontier/A.lean", self.module(1))
        code, out, _ = self.run_main()
        self.assertEqual(code, 0)
        self.assertIn("CslibFrontier/A.lean: 1 (baseline 2)", out)
        self.assertEqual(self.run_main("--update-baseline")[0], 0)
        self.assertEqual(self.baseline(), {"CslibFrontier/A.lean": 1, "CslibFrontier/B.lean": 1})
        # A deleted module's entry goes away.
        (self.root / "CslibFrontier/B.lean").unlink()
        self.assertEqual(self.run_main("--update-baseline")[0], 0)
        self.assertEqual(self.baseline(), {"CslibFrontier/A.lean": 1})

    def test_untouched_modules_are_only_enforced_with_all(self) -> None:
        self.write("CslibFrontier/B.lean", self.module(2))
        self.git("commit", "-qam", "drift")
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.assertEqual(self.run_main()[0], 0)
        self.assertEqual(self.run_main("--all")[0], 1)
        code, out, _ = self.run_main("--report")
        self.assertEqual(code, 0)
        self.assertIn("CslibFrontier/B.lean: 2 chain(s), baseline 1:", out)

    def test_the_baseline_only_goes_up_on_request(self) -> None:
        self.write("CslibFrontier/A.lean", self.module(3))
        code, _, err = self.run_main("--update-baseline")
        self.assertEqual(code, 1)
        self.assertIn("--allow-increase", err)
        self.assertEqual(self.baseline()["CslibFrontier/A.lean"], 2)
        self.assertEqual(self.run_main("--update-baseline", "--allow-increase")[0], 0)
        self.assertEqual(self.baseline()["CslibFrontier/A.lean"], 3)

    def test_the_whole_baseline_regenerates(self) -> None:
        (self.root / "scripts/projection_chains_baseline.json").unlink()
        self.assertEqual(self.run_main("--update-baseline", "--all", "--allow-increase")[0], 0)
        self.assertEqual(self.baseline(), {"CslibFrontier/A.lean": 2, "CslibFrontier/B.lean": 1})

    def test_list(self) -> None:
        code, out, _ = self.run_main("--list", "CslibFrontier/A.lean")
        self.assertEqual(code, 0)
        self.assertTrue(out.startswith("2 counted projection chain(s) in 1 module(s)."))
        self.assertIn("CslibFrontier/A.lean:8: t0: `.1.2`", out)


class RepositoryTests(unittest.TestCase):
    def test_the_checked_in_baseline_is_well_formed(self) -> None:
        baseline = c.load_baseline(c.BASELINE)
        self.assertEqual(c.BASELINE.read_text(), c.baseline_text(baseline))


if __name__ == "__main__":
    unittest.main()
