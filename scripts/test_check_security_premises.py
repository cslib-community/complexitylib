"""Unit tests for scripts/check_security_premises.py, on synthetic reader output and, when Lean is
available, on a compiled module (`CompiledFixtureTests`) read by scripts/SecurityPremises.lean."""

from __future__ import annotations

import contextlib
import io
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_security_premises as c  # noqa: E402

SCHNORR = "Cslib.Crypto.Schnorr.negligible_eufCma"
HELPER = "Cslib.Crypto.Garbling.advantage_le_mul"
SCHNORR_PATH = "CslibFrontier/Crypto/Schnorr.lean"
HELPER_PATH = "CslibFrontier/Crypto/Garbling.lean"


def row(name: str, module: str, line: int, *premises: tuple[str, str, str]) -> str:
    """A line of the reader's output: premises as `(binder, kind, constructed constant)`."""
    return json.dumps({"n": name, "m": module, "l": line,
                       "h": [{"b": b, "k": [k], "c": [const]} for b, k, const in premises]})


OUTPUT = "\n".join([
    row(SCHNORR, "CslibFrontier.Crypto.Schnorr", 10,
        ("hDL", "negligible", "Cslib.Crypto.Schnorr.reduction")),
    row(HELPER, "CslibFrontier.Crypto.Garbling", 20,
        ("hε", "advantage", "Cslib.Crypto.Garbling.reduction"),
        ("hε", "member", "Cslib.Crypto.Garbling.reduction")),
    json.dumps({"theorems": 2, "modules": 2, "missing": []}),
])


def entry(path: str, premises: list[str], why: str = "justified") -> dict:
    return {"module": path, "premises": premises, "why": why}


class ParseTests(unittest.TestCase):
    def test_rows_and_summary(self) -> None:
        hits, summary = c.parse(OUTPUT)
        self.assertEqual(summary["theorems"], 2)
        self.assertEqual(hits[SCHNORR].path, SCHNORR_PATH)
        self.assertEqual(hits[SCHNORR].line, 10)
        # Two findings for one binder merge their kinds.
        self.assertEqual(hits[HELPER].premises["hε"],
                         (("advantage", "member"), ("Cslib.Crypto.Garbling.reduction",)))


class CompareTests(unittest.TestCase):
    def setUp(self) -> None:
        self.hits, _ = c.parse(OUTPUT)

    def test_recorded_premises_pass(self) -> None:
        baseline = {SCHNORR: entry(SCHNORR_PATH, ["hDL"]), HELPER: entry(HELPER_PATH, ["hε"])}
        self.assertFalse(c.compare(self.hits, baseline, None))

    def test_unrecorded_premise_fails_only_in_scope(self) -> None:
        baseline = {HELPER: entry(HELPER_PATH, ["hε"])}
        problems = c.compare(self.hits, baseline, {SCHNORR_PATH})
        self.assertEqual([(h.name, b) for h, b in problems.new], [(SCHNORR, ["hDL"])])
        self.assertFalse(c.compare(self.hits, baseline, {HELPER_PATH}))

    def test_a_new_premise_of_a_recorded_theorem_fails(self) -> None:
        hits = dict(self.hits)
        hits[SCHNORR] = c.Hit(SCHNORR, SCHNORR_PATH, 10, {
            **self.hits[SCHNORR].premises, "hKey": (("efficiency",), ("keyGen",))})
        problems = c.compare(hits, {SCHNORR: entry(SCHNORR_PATH, ["hDL"])}, {SCHNORR_PATH})
        self.assertEqual([b for _, b in problems.new], [["hKey"]])

    def test_stale_entries_fail_in_their_module(self) -> None:
        baseline = {HELPER: entry(HELPER_PATH, ["hε"]), SCHNORR: entry(SCHNORR_PATH, ["hDL"]),
                    "Cslib.Crypto.Gone.thm": entry("CslibFrontier/Crypto/Gone.lean", ["h"])}
        del self.hits[SCHNORR]
        problems = c.compare(self.hits, baseline, {SCHNORR_PATH})
        self.assertEqual([name for name, _, _ in problems.stale], [SCHNORR])
        everywhere = c.compare(self.hits, baseline, None)
        self.assertEqual([name for name, _, _ in everywhere.stale],
                         ["Cslib.Crypto.Gone.thm", SCHNORR])
        self.assertIn("no longer flagged: hDL", c.report(problems))

    def test_moved_theorem_needs_its_entry_updated(self) -> None:
        baseline = {SCHNORR: entry("CslibFrontier/Crypto/Old.lean", ["hDL"])}
        problems = c.compare(self.hits, baseline, {SCHNORR_PATH})
        self.assertEqual([gone for _, _, gone in problems.stale], [[]])
        self.assertIn("module moved", c.report(problems))

    def test_entries_need_a_justification(self) -> None:
        baseline = {SCHNORR: entry(SCHNORR_PATH, ["hDL"], why=" ")}
        problems = c.compare(self.hits, baseline, {SCHNORR_PATH})
        self.assertEqual(problems.unjustified, [SCHNORR])


class BaselineTests(unittest.TestCase):
    def test_text_round_trips_one_entry_per_line(self) -> None:
        baseline = {HELPER: entry(HELPER_PATH, ["hε"]), SCHNORR: entry(SCHNORR_PATH, ["hDL"])}
        text = c.baseline_text(baseline)
        self.assertEqual(json.loads(text), baseline)
        self.assertEqual(len(text.splitlines()), 4)
        # Grouped by module: Garbling before Schnorr.
        self.assertLess(text.index(HELPER), text.index(SCHNORR))
        self.assertEqual(c.baseline_text({}), "{\n}\n")

    def test_update_keeps_justifications_and_drops_stale_entries(self) -> None:
        hits, _ = c.parse(OUTPUT)
        baseline = {SCHNORR: entry(SCHNORR_PATH, ["hDL"], "kept"),
                    "Cslib.Crypto.Gone.thm": entry("CslibFrontier/Crypto/Gone.lean", ["h"])}
        updated = c.update(hits, baseline, {SCHNORR_PATH, HELPER_PATH})
        self.assertEqual(updated[SCHNORR]["why"], "kept")
        self.assertEqual(updated[HELPER], entry(HELPER_PATH, ["hε"], ""))
        # Out of scope: kept as it is.
        self.assertIn("Cslib.Crypto.Gone.thm", updated)
        self.assertNotIn("Cslib.Crypto.Gone.thm", c.update(hits, baseline, None))


class CheckerChangedTests(unittest.TestCase):
    def test_only_the_checker_and_its_baseline_count(self) -> None:
        for changed, expected in ((["scripts/security_premises_baseline.json"], True),
                                  (["scripts/SecurityPremises.lean"], True),
                                  (["CslibFrontier/Crypto/Schnorr.lean", "AGENTS.md"], False)):
            with mock.patch.object(c.cer.ccf, "changed_files", return_value=(changed, [])):
                self.assertEqual(c.checker_changed(c.ROOT, "origin/main"), expected, changed)


class MainTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.baseline = pathlib.Path(tmp.name) / "baseline.json"
        hits, _ = c.parse(OUTPUT)
        self.checker_changed = mock.patch.object(c, "checker_changed", return_value=False)
        for patcher in (mock.patch.object(c, "scan", return_value=hits),
                        mock.patch.object(c.cer, "touched_modules", return_value={SCHNORR_PATH}),
                        self.checker_changed):
            patcher.start()
            self.addCleanup(patcher.stop)

    def run_main(self, baseline: dict | None, *args: str) -> tuple[int, str, str]:
        if baseline is not None:
            self.baseline.write_text(c.baseline_text(baseline))
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = c.main(["--no-build-check", "--baseline", str(self.baseline), *args])
        return code, out.getvalue(), err.getvalue()

    def test_pull_request_mode_fails_on_a_new_premise(self) -> None:
        code, _, err = self.run_main({})
        self.assertEqual(code, 1)
        self.assertIn(f"{SCHNORR_PATH}:10: {SCHNORR}", err)
        self.assertIn("premise hDL: negligible about `Cslib.Crypto.Schnorr.reduction`", err)
        self.assertNotIn(HELPER, err)

    def test_pull_request_mode_reports_untouched_modules(self) -> None:
        code, out, err = self.run_main({SCHNORR: entry(SCHNORR_PATH, ["hDL"])})
        self.assertEqual(code, 0)
        self.assertIn("Not enforced", out)
        self.assertIn(f"{HELPER_PATH}:20: {HELPER}", out)
        self.assertEqual(err, "")
        with mock.patch.dict(c.os.environ, {"GITHUB_ACTIONS": "true"}):
            out = self.run_main(None)[1]
        self.assertIn("::notice title=Security premises::1 difference(s)", out)

    def test_a_change_to_the_checker_enforces_every_module(self) -> None:
        with mock.patch.object(c, "checker_changed", return_value=True):
            code, out, err = self.run_main({SCHNORR: entry(SCHNORR_PATH, ["hDL"])})
        self.assertEqual(code, 1)
        self.assertIn("every module is enforced", out)
        self.assertIn(f"{HELPER_PATH}:20: {HELPER}", err)

    def test_report_mode_succeeds(self) -> None:
        code, out, _ = self.run_main({}, "--report")
        self.assertEqual(code, 0)
        self.assertIn(HELPER, out)
        self.assertIn("report only", out)

    def test_update_then_justify(self) -> None:
        self.assertEqual(self.run_main({}, "--update-baseline")[0], 0)
        written = json.loads(self.baseline.read_text())
        self.assertEqual(written, {SCHNORR: entry(SCHNORR_PATH, ["hDL"], "")})
        code, _, err = self.run_main(None)
        self.assertEqual(code, 1)
        self.assertIn("without a justification", err)
        written[SCHNORR]["why"] = "#5293 §1: to be removed under #5293"
        self.assertEqual(self.run_main(written)[0], 0)


# A compiled module for `CompiledFixtureTests`, under `CslibFrontier/Crypto` so that it is scanned.
FIXTURE = """module
public import Init
public section

/-- Stands in for Mathlib's `PMF`: an infrastructure type by name. -/
structure PMF (α : Type) where
  weight : α → Nat

/-- Stands in for Mathlib's `Filter.Eventually`, written `∀ᶠ`. -/
def Filter.Eventually {α : Type} (p : α → Prop) (_f : Nat) : Prop := ∀ a, p a

namespace Cslib.Crypto

/-- Stands in for `Game`: an infrastructure type by name. -/
abbrev Game := Nat → Nat

namespace Fixture

def Negligible (f : Nat → Nat) : Prop := ∀ n, f n = 0

structure Adversary where
  run : Nat → Bool

def Adversary.IsPPT (_A : Adversary) : Prop := True
def IsPPTOn (_f : Nat → List Bool) : Prop := True

/-- A class of adversaries, for memberships. -/
structure Class where
  admits : Adversary → Prop

instance : Membership Adversary Class := ⟨fun C A => C.admits A⟩

def advantage (_A : Adversary) (n : Nat) : Nat := n
def securityGame (A : Adversary) : Game := advantage A
def reduction (A : Adversary) : Adversary := A
def reductionWith (A : Adversary) (_m : Nat) : Adversary := A
def distinguisher (A : Adversary) : Nat → List Bool := fun n => [A.run n]
def keyLaw (_n : Nat) : Nat := 0
def isValid (_n : Nat) : Bool := true
def simulatorView (_A : Adversary) (_n : Nat) : PMF Bool := ⟨fun _ => 0⟩
def realView (_A : Adversary) (_n : Nat) : PMF Bool := ⟨fun _ => 1⟩
def generatorLaw (_generator : Nat → Nat) (_n : Nat) : PMF Bool := ⟨fun _ => 0⟩
def keyLawOf (_k _n : Nat) : PMF Bool := ⟨fun _ => 0⟩
def idealKeys (_n : Nat) : PMF Bool := ⟨fun _ => 1⟩
def forgeExperiment (_A : Adversary) (n : Nat) : Nat := n
def ComputationallyIndistinguishable (_X _Y : Nat → PMF Bool) : Prop := True

/-- A group description, and one that the library fixes. -/
structure Group where
  order : Nat
def concreteGroup : Group := ⟨5⟩
def groupAdvantage (G : Group) (_A : Adversary) (n : Nat) : Nat := G.order + n
/-- A named assumption relative to a group. -/
def GroupHard (G : Group) : Prop := ∀ A : Adversary, Negligible (groupAdvantage G A)

/-- A named assumption about bound adversaries only. -/
def Hard : Prop := ∀ A : Adversary, A.IsPPT → Negligible (advantage A)
/-- A notion applied to its argument. -/
def Secure (A : Adversary) : Prop := Negligible (advantage A)
/-- A premise that hides the constructed object in its own body. -/
def ReductionSecure (A : Adversary) : Prop := Negligible (advantage (reduction A))

theorem negligiblePremise (A : Adversary) (_h : Negligible (advantage (reduction A))) : True :=
  trivial
theorem boundPremise (A : Adversary) (ε : Nat) (_h : advantage (reduction A) 0 ≤ ε) : True :=
  trivial
theorem reversedBoundPremise (A : Adversary) (ε : Nat) (_h : ε ≥ advantage (reduction A) 0) :
    True := trivial
theorem memberPremise (A : Adversary) (C : Class) (_h : reduction A ∈ C) : True := trivial
theorem admissiblePremise (Admissible : Adversary → Prop)
    (_h : ∀ A, Admissible A → Admissible (reduction A)) : True := trivial
theorem efficiencyPremise (A : Adversary) (_h : (reduction A).IsPPT) : True := trivial
theorem quantifiedPremise
    (_h : ∀ A : Adversary, A.IsPPT → advantage (reduction A) 0 ≤ 1 ∧ True) : True := trivial
theorem functionPremise (A : Adversary)
    (_h : Negligible (fun n => (distinguisher A n).length)) : True := trivial
theorem notionPremise (A : Adversary) (_h : Secure (reduction A)) : True := trivial
theorem existentialConclusion (A : Adversary) :
    ∃ m : Nat, advantage A 0 ≤ advantage (reductionWith A m) 0 := ⟨0, Nat.le_refl _⟩
theorem simulatorPremise (A : Adversary)
    (_h : ComputationallyIndistinguishable (realView A) (simulatorView A)) : True := trivial
theorem arrowPremise (A : Adversary) : Negligible (advantage (reduction A)) → True :=
  fun _ => trivial
/-- Flagged by design: a named assumption at a library object goes in the baseline. -/
theorem instantiatedAssumption (_h : GroupHard concreteGroup) : True := trivial

/-- The reduction is taken from the caller as `D`, with a premise that it realizes the constructed
one. -/
theorem realizationPremise (A D : Adversary) (_hD : D.IsPPT)
    (_h : ∀ n, D.run n = (reduction A).run n) : True := trivial
theorem eventualRealization (A D : Adversary) (_hD : D.IsPPT)
    (_h : Filter.Eventually (fun n => D.run n = (reduction A).run n) 0) : True := trivial
theorem testRealization (A : Adversary) (test : Nat → List Bool) (_htest : IsPPTOn test)
    (_h : ∀ n, distinguisher A n = test n) : True := trivial
theorem memberRealization (A D : Adversary) (C : Class) (_hD : D ∈ C) (_h : D = reduction A) :
    True := trivial
/-- The input adversary is certified too; that does not hide the realization, in either
direction. -/
theorem bothCertifiedRealization (A D : Adversary) (_hA : A.IsPPT) (_hD : D.IsPPT)
    (_h : ∀ n, D.run n = (reduction A).run n) : True := trivial
theorem reversedBothCertifiedRealization (A D : Adversary) (_hA : A.IsPPT) (_hD : D.IsPPT)
    (_h : ∀ n, (reduction A).run n = D.run n) : True := trivial

theorem adversaryPremise (A : Adversary) (_hA : A.IsPPT) (_h : Negligible (advantage A)) :
    True := trivial
theorem admissibleAdversary (Admissible : Adversary → Prop) (A : Adversary) (_h : Admissible A) :
    True := trivial
theorem assumptionPremise (_h : Hard) : True := trivial
theorem infrastructurePremise (A : Adversary) (_h : Negligible (securityGame A))
    (_h' : Negligible keyLaw) (_h'' : Negligible (fun n => if isValid n then 0 else 1)) : True :=
  trivial
theorem existentialWitness : ∃ B : Adversary, advantage B 0 ≤ 1 := ⟨⟨fun _ => true⟩, by decide⟩
theorem hiddenPremise (A : Adversary) (_h : ReductionSecure A) : True := trivial
theorem generatorPremise (generator : Nat → Nat)
    (_h : ComputationallyIndistinguishable (generatorLaw generator) idealKeys) : True := trivial
theorem fixedKeyLawPremise (_h : ComputationallyIndistinguishable (keyLawOf 3) idealKeys) : True :=
  trivial
theorem unnamedBoundPremise (A : Adversary) (ε : Nat) (_h : forgeExperiment (reduction A) 0 ≤ ε) :
    True := trivial
/-- An equation between variables, as when a word program certifies a caller's typed program. -/
theorem variableRealization (D E : Adversary) (_hD : D.IsPPT) (_h : ∀ n, D.run n = E.run n) :
    True := trivial
theorem bothCertifiedVariables (A D : Adversary) (_hA : A.IsPPT) (_hD : D.IsPPT)
    (_h : ∀ n, D.run n = A.run n) : True := trivial
/-- No premise certifies `D`. -/
theorem uncertifiedEquation (A D : Adversary) (_h : D = reduction A) : True := trivial
theorem inequalityRealization (A D : Adversary) (_hD : D.IsPPT)
    (_h : ∀ n, forgeExperiment D n ≤ forgeExperiment (reduction A) n) : True := trivial
private theorem privatePremise (A : Adversary) (_h : Negligible (advantage (reduction A))) :
    True := trivial

end Fixture
end Cslib.Crypto
"""


@unittest.skipUnless(shutil.which("lake") and (c.ROOT / ".lake/packages").is_dir(),
                     "needs Lean and the repository's packages (CI runs this after the build)")
class CompiledFixtureTests(unittest.TestCase):
    """What `scripts/SecurityPremises.lean` flags in a compiled module."""

    @classmethod
    def setUpClass(cls) -> None:
        tmp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(tmp.cleanup)
        root = pathlib.Path(tmp.name)
        source = root / "src/CslibFrontier/Crypto/Fixture.lean"
        olean = root / "build/CslibFrontier/Crypto/Fixture.olean"
        source.parent.mkdir(parents=True)
        olean.parent.mkdir(parents=True)
        source.write_text(FIXTURE)
        subprocess.run(["lake", "env", "lean", f"--root={root / 'src'}", "-o", str(olean),
                        str(source)], cwd=c.ROOT, check=True, capture_output=True)
        out = subprocess.run(["lake", "env", "lean", "--run", c.TOOL, str(root / "build")],
                             cwd=c.ROOT, input="CslibFrontier.Crypto.Fixture\n",
                             capture_output=True, text=True, check=True).stdout
        hits, cls.summary = c.parse(out)
        cls.flagged = {name.removeprefix("Cslib.Crypto.Fixture."): hit.premises
                       for name, hit in hits.items()}

    def kinds(self, name: str, binder: str = "_h") -> tuple[str, ...]:
        return self.flagged[name][binder][0]

    def test_premises_about_constructed_objects_are_flagged(self) -> None:
        self.assertEqual(self.kinds("negligiblePremise"), ("negligible",))
        self.assertEqual(self.kinds("boundPremise"), ("advantage",))
        self.assertEqual(self.kinds("reversedBoundPremise"), ("advantage",))
        self.assertEqual(self.kinds("memberPremise"), ("member",))
        self.assertEqual(self.kinds("admissiblePremise"), ("member",))
        self.assertEqual(self.kinds("efficiencyPremise"), ("efficiency",))
        self.assertEqual(self.kinds("quantifiedPremise"), ("advantage",))
        self.assertEqual(self.kinds("functionPremise"), ("negligible",))
        self.assertEqual(self.flagged["functionPremise"]["_h"][1],
                         ("Cslib.Crypto.Fixture.distinguisher",))
        self.assertEqual(self.kinds("notionPremise"), ("unfolded negligible",))
        self.assertEqual(self.kinds("existentialConclusion", c.CONCLUSION), ("exists advantage",))
        self.assertEqual(self.kinds("simulatorPremise"), ("indistinguishable",))
        self.assertEqual(self.flagged["simulatorPremise"]["_h"][1],
                         ("Cslib.Crypto.Fixture.realView", "Cslib.Crypto.Fixture.simulatorView"))
        # A premise written with an arrow is reported by its position.
        self.assertEqual(self.kinds("arrowPremise", "#2"), ("negligible",))

    def test_realizations_are_flagged(self) -> None:
        # A variable with an efficiency or membership premise, and an equation saying that it
        # realizes a constructed object applied to another variable.
        for name in ("realizationPremise", "eventualRealization", "testRealization",
                     "memberRealization", "bothCertifiedRealization",
                     "reversedBothCertifiedRealization"):
            self.assertEqual(self.kinds(name), ("realization",), name)
            self.assertNotIn("_hD", self.flagged[name], name)
        self.assertEqual(self.flagged["realizationPremise"]["_h"][1],
                         ("Cslib.Crypto.Fixture.reduction",))
        self.assertEqual(self.flagged["testRealization"]["_h"][1],
                         ("Cslib.Crypto.Fixture.distinguisher",))

    def test_a_certified_input_adversary_does_not_hide_a_realization(self) -> None:
        # With `_hA : A.IsPPT` beside `_hD : D.IsPPT`, the equation still says that `D` realizes
        # `reduction A`, whichever side `D` is on; only the realizing variable is excluded.
        for name in ("bothCertifiedRealization", "reversedBothCertifiedRealization"):
            self.assertEqual(self.flagged[name],
                             {"_h": (("realization",), ("Cslib.Crypto.Fixture.reduction",))},
                             name)
        # Two certified variables equated, with no constructed constant, are not a realization.
        self.assertNotIn("bothCertifiedVariables", self.flagged)

    def test_named_assumptions_at_library_objects_are_flagged(self) -> None:
        # Allowed by the rule, so such a premise needs a baseline entry with its justification.
        self.assertEqual(self.kinds("instantiatedAssumption"), ("unfolded negligible",))
        self.assertEqual(self.flagged["instantiatedAssumption"]["_h"][1],
                         ("Cslib.Crypto.Fixture.concreteGroup",))

    def test_bound_variables_assumptions_and_infrastructure_are_not(self) -> None:
        for name in ("adversaryPremise", "admissibleAdversary", "assumptionPremise",
                     "infrastructurePremise", "existentialWitness", "generatorPremise",
                     "variableRealization", "bothCertifiedVariables", "uncertifiedEquation"):
            self.assertNotIn(name, self.flagged)

    def test_private_theorems_are_not_scanned(self) -> None:
        self.assertFalse([n for n in self.flagged if "privatePremise" in n])

    def test_known_limitations(self) -> None:
        # Review covers these cases (the reader's docstring, "Known gaps").
        # `ReductionSecure A` builds `reduction A` inside its own body; only constructed objects
        # passed as arguments are followed into an unfolded definition.
        self.assertNotIn("hiddenPremise", self.flagged)
        # A distribution applied only to numbers counts as an ideal law.
        self.assertNotIn("fixedKeyLawPremise", self.flagged)
        # A bound without an advantage-named constant is not a security claim.
        self.assertNotIn("unnamedBoundPremise", self.flagged)
        # A realization stated as an inequality rather than an equation.
        self.assertNotIn("inequalityRealization", self.flagged)

    def test_exactly_the_expected_theorems(self) -> None:
        self.assertEqual(len(self.flagged), 19)
        self.assertEqual(self.summary["missing"], [])


class CommittedFilesTests(unittest.TestCase):
    """These run on every event, merge groups included, so they check only the baseline file
    itself. Whether its entries match the library (a moved or deleted module, say) is the pull
    request check's job, which merge groups only report."""

    def test_baseline_is_canonical_and_justified(self) -> None:
        baseline = c.load_baseline(c.BASELINE)
        self.assertEqual(c.BASELINE.read_text(encoding="utf-8"), c.baseline_text(baseline))
        for name, value in baseline.items():
            self.assertTrue(value["why"].strip(), name)
            self.assertTrue(value["premises"], name)


if __name__ == "__main__":
    unittest.main()
