"""Unit tests for scripts/check_experiment_readability.py, on synthetic Lean modules."""

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
import check_experiment_readability as c  # noqa: E402

HEADER = "module\n-- upstream: candidate\n\npublic import CslibFrontier.Init\n\npublic section\n\n"
VOCAB = frozenset({"encPair", "encBits", "encode", "encDesc", "enc"})


def found(source: str, vocab: frozenset[str] = VOCAB) -> list[tuple[str, str, str]]:
    return [(row.declaration, row.category, row.text)
            for row in c.module_findings(HEADER + source, vocab)]


def categories(source: str) -> list[str]:
    return [category for _, category, _ in found(source)]


class ExperimentTests(unittest.TestCase):
    def test_a_textbook_experiment_has_no_findings(self) -> None:
        # The fixed-group CDH experiment of the typed Diffie–Hellman pilot (#4678).
        self.assertEqual(found(
            "def cdhExperiment (A : G → G → ProbComp G) : ProbComp Bool := do\n"
            "  let a ← ProbComp.uniform (ZMod q)\n  let b ← ProbComp.uniform (ZMod q)\n"
            "  let z ← A (a • g) (b • g)\n  return z = (a * b) • g\n"), [])

    def test_the_family_form_may_evaluate_the_fixed_experiment(self) -> None:
        self.assertEqual(found(
            "def cdhGame (setup : ℕ → PMF F.Desc) (adversary : F.CDHAdversary) (n : ℕ) : Game := do\n"
            "  let d ← setup n\n"
            "  ProbComp.eval (cdhExperiment (F.order d) (F.generator d) (adversary n d))\n"
            "def koaGame (A : Adv) : Game := keys.bind fun pk => ProbComp.eval <| koaExperiment pk A\n"),
            [])

    def test_word_plumbing_in_an_experiment_counts(self) -> None:
        self.assertEqual(found(
            "def elGamalCPAGameOn (adversary : Adv) (bit : Bool) (n : ℕ) : Game := do\n"
            "  let d ← setup n\n"
            "  let pk := encPair F.encDesc encBits (d, F.encode d g)\n"
            "  let choice ← ProbComp.eval (adversary.choose n pk)\n"
            "  ProbComp.eval (adversary.guess n choice.2.1 pk)\n"),
            [("elGamalCPAGameOn", "encoding", "encPair"),
             ("elGamalCPAGameOn", "encoding", "F.encDesc"),
             ("elGamalCPAGameOn", "encoding", "encBits"),
             ("elGamalCPAGameOn", "encoding", "F.encode"),
             ("elGamalCPAGameOn", "eval", "ProbComp.eval"),
             ("elGamalCPAGameOn", "eval", "ProbComp.eval"),
             ("elGamalCPAGameOn", "chain", ".2.1")])

    def test_reductions_count_and_honest_algorithms_do_not(self) -> None:
        self.assertEqual(categories(
            "def cdhToDDH (A : Adv) (x : X) : ProbComp Bool := do\n  return (encBits x).isEmpty\n"
            "def eavToDistinguisher (A : Adv) : ℕ → ProbComp Bool := fun n => A (encBits n)\n"),
            ["encoding", "encoding"])
        self.assertEqual(categories(
            "def verify (pk : PK) (m : M) (s : S) : ProbComp Bool := pure (encBits m == s)\n"
            "def cdhGame (A : Adv) : ℝ≥0 := (encBits 0).length\n"), [])

    def test_codomain_after_the_last_arrow(self) -> None:
        self.assertEqual(categories(
            "def fooGame (A : Adv) : (n : ℕ) → Bool → ProbOracleComp Spec Bool :=\n"
            "  fun n b => pure (encBits n).isEmpty\n"
            "def barGame (A : Adv) : ℕ → ProbComp (List Bool) := fun n => pure (encBits n)\n"),
            ["encoding"])

    def test_names_and_shadowing(self) -> None:
        # A codec binder counts; a binder of another type shadows a codec of the same name when it
        # is used unqualified, but not a qualified use.
        self.assertEqual(found(
            "def aGame (encS : S ↪ List Bool) (enc : Scheme) (s : S) : ProbComp Bool := do\n"
            "  let c ← enc s\n  return (encS s).isEmpty && (F.enc s).isEmpty\n"),
            [("aGame", "encoding", "encS"), ("aGame", "encoding", "F.enc")])
        # Section variables shadow and declare codecs too.
        self.assertEqual(categories(
            "variable (enc : Scheme) (eKey : K ↪ List Bool)\n"
            "def bGame (k : K) : ProbComp Bool := do\n  let c ← enc k\n  return (eKey k).isEmpty\n"),
            ["encoding"])

    def test_tactic_blocks_comments_and_strings_do_not_count(self) -> None:
        self.assertEqual(categories(
            "def cGame (x : X) : ProbComp Bool := do\n"
            "  -- encBits x\n  let y : {l // l = encBits x} := ⟨_, by simp [encBits]⟩\n"
            "  return \"encBits\".isEmpty\n"),
            ["encoding"])

    def test_eager_random_oracle_tables(self) -> None:
        self.assertEqual(found(
            "def eagerGame (S : Scheme) (A : Adv) : Game := do\n"
            "  let G ← pi (α := fun _ : M => R) (fun _ => ProbComp.eval S.sampleCoins)\n"
            "  let H ← Probability.PMF.pi fun _ : CT => ProbComp.eval S.sampleKey\n"
            "  let k ← ProbComp.eval S.sampleKey\n"
            "  return G = G\n"),
            [("eagerGame", "eval", "ProbComp.eval")])

    def test_private_internal_and_certificates_are_not_checked(self) -> None:
        self.assertEqual(categories(
            "private def pGame (x : X) : ProbComp Bool := pure (encBits x).isEmpty\n"
            "namespace Internal\ndef qGame (x : X) : ProbComp Bool := pure (encBits x).isEmpty\n"
            "end Internal\n"
            "@[program_certificate] def rGame (x : X) : ProbComp Bool := pure (encBits x).isEmpty\n"
            "theorem sGame (x : X) : ProbComp.eval (pure (encBits x).isEmpty) = 0 := sorry\n"), [])


class AdversaryTests(unittest.TestCase):
    def test_word_adversary_types(self) -> None:
        self.assertEqual(found(
            "structure CPAAdversary where\n"
            "  choose : ℕ → List Bool → ProbComp ((M × M) × List Bool)\n"
            "  isPPT : IsPPT encPair (fun x : List Bool × List Bool => choose 0 x.1)\n"
            "  guess : ℕ → List Bool → ProbComp Bool\n"
            "def WordDistinguisher : Type := ℕ → WordOracleComp Bool\n"),
            [("CPAAdversary", "word_adversary", "List Bool"),
             ("CPAAdversary", "word_adversary", "List Bool"),
             ("CPAAdversary", "word_adversary", "List Bool"),
             ("WordDistinguisher", "word_adversary", "WordOracleComp")])

    def test_typed_adversaries_and_their_efficiency_predicates(self) -> None:
        self.assertEqual(found(
            "structure CDHAdversary (G : Type) where\n  run : G → G → ProbComp G\n"
            "def CDHAdversary.IsPPT (A : CDHAdversary G) : Prop :=\n"
            "  IsPPT (encPair encBits encBits) fun p : List Bool × List Bool => A.run 0 0\n"
            "def AdversaryAdvantage (A : Adv) : List Bool := []\n"), [])

    def test_word_adversary_binders(self) -> None:
        self.assertEqual(found(
            "def sisGame (adversary : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) : Game :=\n"
            "  pure true\n"
            "def dGame (A₁ : Adv) (x : List Bool) (h : IsPPT (fun _ : List Bool => x)) : Game :=\n"
            "  pure true\n"),
            [("sisGame", "word_adversary", "List Bool"),
             ("sisGame", "word_adversary", "List Bool")])


class VocabularyTests(unittest.TestCase):
    def test_codecs_by_name_and_type(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            (root / "CslibFrontier").mkdir()
            (root / "CslibFrontier/A.lean").write_text(
                "def encFoo : Foo ↪ List Bool := sorry\n"
                "@[expose] def decodeFoo :\n    List Bool → Option Foo\n  | _ => none\n"
                "def encrypt (k : K) (m : List Bool) : List Bool := m\n"
                "def encBound (n : ℕ) : ℕ := n\n"
                "structure Group where\n  eElem : Carrier ↪ List Bool\n  encode : Carrier → ℕ\n"
                "enc_structure encRecord : Record\n"
                "-- def encComment : C ↪ List Bool := sorry\n")
            vocab = c.vocabulary(root)
        self.assertLessEqual({"encFoo", "decodeFoo", "eElem", "encRecord", "encPair"}, vocab)
        self.assertFalse({"encrypt", "encBound", "encode", "encComment"} & vocab)


class RatchetTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.write("CslibFrontier/Crypto/A.lean", self.module(2))
        self.write("CslibFrontier/Crypto/B.lean", self.module(1))
        self.write("CslibFrontier/Other.lean", self.module(3))
        self.write("scripts/experiment_readability_baseline.json", json.dumps({
            "CslibFrontier/Crypto/A.lean": {"encoding": 2},
            "CslibFrontier/Crypto/B.lean": {"encoding": 1}}))
        self.git("add", ".")
        self.git("commit", "-qm", "base")
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")

    @staticmethod
    def module(n: int, evals: int = 0) -> str:
        return HEADER + "".join(
            f"def g{i}Game (encN : ℕ ↪ List Bool) : ProbComp Bool := pure (encN {i}).isEmpty\n"
            for i in range(n)) + "".join(
            f"def h{i}Game (A : Adv) : Game := ProbComp.eval (A {i})\n" for i in range(evals))

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

    def baseline(self) -> dict[str, dict[str, int]]:
        return json.loads((self.root / "scripts/experiment_readability_baseline.json").read_text())

    def test_each_category_is_ratcheted(self) -> None:
        self.write("CslibFrontier/Crypto/A.lean", self.module(3))
        code, _, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("CslibFrontier/Crypto/A.lean [encoding]: 3 finding(s), baseline 2:", err)
        self.assertIn("CslibFrontier/Crypto/A.lean:10: g2Game: encoding `encN`", err)
        # Fewer encodings do not pay for a new eval.
        self.write("CslibFrontier/Crypto/A.lean", self.module(1, evals=1))
        code, out, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("[eval]: 1 finding(s), baseline 0:", err)
        self.assertIn("CslibFrontier/Crypto/A.lean [encoding]: 1 (baseline 2)", out)

    def test_a_new_module_starts_at_zero_and_others_are_not_checked(self) -> None:
        self.write("CslibFrontier/Crypto/New.lean", self.module(1))
        self.assertEqual(self.run_main()[0], 1)
        self.write("CslibFrontier/Crypto/New.lean", self.module(0))
        self.write("CslibFrontier/Other.lean", self.module(5))
        code, out, _ = self.run_main()
        self.assertEqual(code, 0)
        self.assertIn("checking 1 changed module(s)", out)

    def test_fewer_findings_pass_and_the_baseline_comes_down(self) -> None:
        self.write("CslibFrontier/Crypto/A.lean", self.module(1))
        code, out, _ = self.run_main()
        self.assertEqual(code, 0)
        self.assertIn("--update-baseline", out)
        self.assertEqual(self.run_main("--update-baseline")[0], 0)
        self.assertEqual(self.baseline(), {"CslibFrontier/Crypto/A.lean": {"encoding": 1},
                                           "CslibFrontier/Crypto/B.lean": {"encoding": 1}})
        (self.root / "CslibFrontier/Crypto/B.lean").unlink()
        self.assertEqual(self.run_main("--update-baseline")[0], 0)
        self.assertEqual(self.baseline(), {"CslibFrontier/Crypto/A.lean": {"encoding": 1}})

    def test_the_baseline_only_goes_up_on_request_and_regenerates(self) -> None:
        self.write("CslibFrontier/Crypto/A.lean", self.module(2, evals=1))
        self.assertEqual(self.run_main("--update-baseline")[0], 1)
        self.assertEqual(self.run_main("--update-baseline", "--allow-increase")[0], 0)
        self.assertEqual(self.baseline()["CslibFrontier/Crypto/A.lean"],
                         {"encoding": 2, "eval": 1})
        (self.root / "scripts/experiment_readability_baseline.json").unlink()
        self.assertEqual(self.run_main("--update-baseline", "--all", "--allow-increase")[0], 0)
        self.assertEqual(self.baseline(), {"CslibFrontier/Crypto/A.lean": {"encoding": 2, "eval": 1},
                                           "CslibFrontier/Crypto/B.lean": {"encoding": 1}})

    def test_report_and_list(self) -> None:
        self.write("CslibFrontier/Crypto/B.lean", self.module(2))
        self.git("commit", "-qam", "drift")
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.assertEqual(self.run_main()[0], 0)
        self.assertEqual(self.run_main("--all")[0], 1)
        code, out, _ = self.run_main("--report")
        self.assertEqual(code, 0)
        self.assertIn("CslibFrontier/Crypto/B.lean [encoding]: 2 finding(s), baseline 1:", out)
        code, out, _ = self.run_main("--list", "CslibFrontier/Crypto/A.lean")
        self.assertEqual(code, 0)
        self.assertTrue(out.startswith("2 counted experiment readability finding(s) in 1 module(s) "
                                       "(encoding: 2, eval: 0, chain: 0, word_adversary: 0)."))

    def test_the_allowlist_suppresses_and_only_shrinks(self) -> None:
        allowlist = "scripts/experiment_readability_allowlist.txt"
        self.write("CslibFrontier/Crypto/A.lean", self.module(3))
        self.write(allowlist, "CslibFrontier/Crypto/A.lean g2Game encoding  # reviewed\n")
        self.assertEqual(self.run_main()[0], 0)
        self.write(allowlist, "CslibFrontier/Crypto/A.lean * encoding  # reviewed\n")
        self.assertEqual(self.run_main("--update-baseline")[0], 0)
        self.assertNotIn("CslibFrontier/Crypto/A.lean", self.baseline())
        # An entry that suppresses nothing in a checked module fails.
        self.write(allowlist, "CslibFrontier/Crypto/A.lean g2Game encoding  # reviewed\n"
                              "CslibFrontier/Crypto/A.lean g9Game eval  # stale\n")
        self.write("CslibFrontier/Crypto/A.lean", self.module(0))
        code, _, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("line 2: CslibFrontier/Crypto/A.lean g9Game eval", err)
        self.assertIn("line 1: CslibFrontier/Crypto/A.lean g2Game encoding", err)
        # A reason is required.
        self.write(allowlist, "CslibFrontier/Crypto/A.lean g2Game encoding\n")
        with self.assertRaises(SystemExit):
            self.run_main()

    def test_removing_an_allowlist_entry_checks_its_module(self) -> None:
        allowlist = "scripts/experiment_readability_allowlist.txt"
        self.write("CslibFrontier/Crypto/A.lean", self.module(3))
        self.write(allowlist, "CslibFrontier/Crypto/A.lean g2Game encoding  # reviewed\n")
        self.git("add", ".")
        self.git("commit", "-qm", "allow")
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.write(allowlist, "# reviewed exceptions\n")
        code, _, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("CslibFrontier/Crypto/A.lean [encoding]: 3 finding(s), baseline 2:", err)


class RepositoryTests(unittest.TestCase):
    def test_the_checked_in_files_are_well_formed(self) -> None:
        baseline = c.ratchet.load_baseline(c.RATCHET, c.BASELINE)
        self.assertEqual(c.BASELINE.read_text(), c.ratchet.baseline_text(c.RATCHET, baseline))
        for entry in c.load_allowlist(c.ALLOWLIST):
            with self.subTest(entry=entry):
                self.assertTrue((c.ROOT / entry.path).is_file())
                self.assertTrue(entry.path.startswith(c.TREE + "/"))


if __name__ == "__main__":
    unittest.main()
