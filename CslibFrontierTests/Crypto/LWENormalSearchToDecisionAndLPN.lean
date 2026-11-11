import CslibFrontier.Crypto.Computational.LWE.NormalForm
import CslibFrontier.Crypto.Computational.LPN
import CslibFrontier.Crypto.Computational.LWE.SearchToDecision

namespace CslibFrontierTests.Crypto.LWENormalSearchToDecisionAndLPN

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeLWE

/--
info: 'Cslib.Crypto.PrimeLWE.decisionNormalForm' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms decisionNormalForm

/--
info: 'Cslib.Crypto.PrimeLWE.searchNormalForm' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms searchNormalForm

/--
info: 'Cslib.Crypto.SearchLPN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.SearchLPN

/-- Boundary example for decisionNormalForm: zero dims and zero samples -/
example {noise : PMF (ZMod 2)} (adversary : List Bool → ProbComp Bool) :
    ↑((distinguishingGame (realEnsembleErrorSecret (fun _ => 0) (fun _ => 0) (fun _ => 2)
      (fun _ => noise) 0) adversary).advantage
      (distinguishingGame (uniformEnsemble (fun _ => 0) (fun _ => 0) (fun _ => 2) 0)
      adversary)) ≤
    ↑((distinguishingGame (realEnsemble (fun _ => 0) (fun _ => 0) (fun _ => 2)
      (fun _ => noise) 0) (reduceNormalDecision (n := 0) (m := 0) (q := 2) adversary)).advantage
      (distinguishingGame (uniformEnsemble (fun _ => 0) (fun _ => 0) (fun _ => 2) 0)
      (reduceNormalDecision (n := 0) (m := 0) (q := 2) adversary))) +
    ((PMF.uniformOfFintype (Matrix (Fin 0) (Fin 0) (ZMod 2))).toOuterMeasure
      {A | A.det = 0}).toReal :=
  decisionNormalForm (n := 0) (m := 0) (q := 2) adversary

/-- Boundary example for searchNormalForm: zero dims and zero samples -/
example {noise : PMF (ZMod 2)} (adversary : List Bool → ProbComp (List Bool)) :
    ↑(searchGameErrorSecret 0 0 2 noise adversary).succProbability ≤
    ↑(searchGame 0 0 2 noise
      (reduceNormalSearch (n := 0) (m := 0) (q := 2) adversary)).succProbability +
    ((PMF.uniformOfFintype (Matrix (Fin 0) (Fin 0) (ZMod 2))).toOuterMeasure
      {A | A.det = 0}).toReal :=
  searchNormalForm (n := 0) (m := 0) (q := 2) adversary

/-- LPN boundary -/
example : SearchLPN (fun _ => 0) (fun _ => 0) (fun _ => 0) ↔
  SearchLWE (fun _ => 0) (fun _ => 0) (fun _ => 2) (fun _ => bernoulliZMod2 0) := Iff.rfl

-- Singular top block reduction logic on zero word
example : reduceNormalDecision (n := 1) (m := 0) (q := 2) (fun _ => pure true) [false, false] = pure false := rfl

end CslibFrontierTests.Crypto.LWENormalSearchToDecisionAndLPN
