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

-- Genuine positive-gap LWE distinguisher instance plugged into the reduction bound
def posGapDistinguisher (b : List Bool) : ProbComp Bool :=
  pure (b = encMatrix 1 2 2 ![![0, 0]] ∨ b = encMatrix 1 2 2 ![![1, 0]])

example :
    ↑((distinguishingGame (realEnsembleErrorSecret (fun _ => 1) (fun _ => 1) (fun _ => 2)
      (fun _ => pure 0) 0) posGapDistinguisher).advantage
      (distinguishingGame (uniformEnsemble (fun _ => 1) (fun _ => 1) (fun _ => 2) 0)
      posGapDistinguisher)) ≤
    ↑((distinguishingGame (realEnsemble (fun _ => 1) (fun _ => 2) (fun _ => 2)
      (fun _ => pure 0) 0) (reduceNormalDecision (n := 1) (m := 1) (q := 2)
      posGapDistinguisher)).advantage
      (distinguishingGame (uniformEnsemble (fun _ => 1) (fun _ => 2) (fun _ => 2) 0)
      (reduceNormalDecision (n := 1) (m := 1) (q := 2) posGapDistinguisher))) +
    ((PMF.uniformOfFintype (Matrix (Fin 1) (Fin 1) (ZMod 2))).toOuterMeasure
      {A | A.det = 0}).toReal :=
  decisionNormalForm (n := 1) (m := 1) (q := 2) posGapDistinguisher

-- Singular top block reduction logic on zero word
example : reduceNormalDecision (n := 1) (m := 0) (q := 2) (fun _ => pure true) [false, false]
    = pure false := by
  have h : Turing.MultiTapeTM.frames [false, false] = [[], []] := by
    rw [Turing.MultiTapeTM.frames]
    dsimp [Turing.MultiTapeTM.unframe, Turing.MultiTapeTM.dropFrame]
    rw [Turing.MultiTapeTM.frames]
    dsimp [Turing.MultiTapeTM.unframe, Turing.MultiTapeTM.dropFrame]
    rw [Turing.MultiTapeTM.frames]
    rfl
  simp [reduceNormalDecision, topBlock, decodeMatrix, gaussInv?, h]

-- Genuine encoded singular block
example : reduceNormalDecision (n := 1) (m := 0) (q := 2) (fun _ => pure true)
    (encMatrix 1 2 2 ![![0, 0]]) = pure false := by
  have : encMatrix 1 2 2 ![![0, 0]] = [true, true, true, false, true, false,
      true, true, true, false, true, false, false] := rfl
  rw [this]
  have h1 : Turing.MultiTapeTM.frames [true, true, true, false, true, false,
      true, true, true, false, true, false, false] =
      [[true, false, false, true, false, false]] := by
    rw [Turing.MultiTapeTM.frames]
    dsimp [Turing.MultiTapeTM.unframe, Turing.MultiTapeTM.dropFrame]
    rw [Turing.MultiTapeTM.frames]; rfl
  have h2 : Turing.MultiTapeTM.frames [true, false, false, true, false, false] =
      [[false], [false]] := by
    rw [Turing.MultiTapeTM.frames]
    dsimp [Turing.MultiTapeTM.unframe, Turing.MultiTapeTM.dropFrame]
    rw [Turing.MultiTapeTM.frames]
    dsimp [Turing.MultiTapeTM.unframe, Turing.MultiTapeTM.dropFrame]
    rw [Turing.MultiTapeTM.frames]; rfl
  have h3 : Turing.MultiTapeTM.Decoder.nat.decode [] = 0 := by decide
  simp [reduceNormalDecision, topBlock, decodeMatrix, gaussInv?, h1, h2,
    Turing.MultiTapeTM.decodeIntBin, h3]

-- Genuine encoded invertible block
example : reduceNormalDecision (n := 1) (m := 0) (q := 2) (fun _ => pure true)
    (encMatrix 1 2 2 ![![0, 1]]) = pure true := by
  have : encMatrix 1 2 2 ![![0, 1]] = [true, true, true, false, true, false,
      true, true, true, false, true, true, true, true, true, false, false] := rfl
  rw [this]
  have h1 : Turing.MultiTapeTM.frames [true, true, true, false, true, false,
      true, true, true, false, true, true, true, true, true, false, false] =
      [[true, false, false, true, false, true, true, false]] := by
    rw [Turing.MultiTapeTM.frames]
    dsimp [Turing.MultiTapeTM.unframe, Turing.MultiTapeTM.dropFrame]
    rw [Turing.MultiTapeTM.frames]; rfl
  have h2 : Turing.MultiTapeTM.frames [true, false, false, true, false, true, true, false] =
      [[false], [false, true]] := by
    rw [Turing.MultiTapeTM.frames]
    dsimp [Turing.MultiTapeTM.unframe, Turing.MultiTapeTM.dropFrame]
    rw [Turing.MultiTapeTM.frames]
    dsimp [Turing.MultiTapeTM.unframe, Turing.MultiTapeTM.dropFrame]
    rw [Turing.MultiTapeTM.frames]; rfl
  have h3 : Turing.MultiTapeTM.Decoder.nat.decode [true] = 1 := by decide
  simp [reduceNormalDecision, topBlock, decodeMatrix, gaussInv?, h1, h2,
    Turing.MultiTapeTM.decodeIntBin, h3]

-- Distributional boundary
noncomputable def half_prob : unitInterval := ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩

example : bernoulliZMod2 half_prob = PMF.uniformOfFintype (ZMod 2) := by
  ext x
  fin_cases x
  · change bernoulliZMod2 half_prob 0 = PMF.uniformOfFintype (ZMod 2) 0
    simp [bernoulliZMod2, PMF.uniformOfFintype_apply, PMF.map, PMF.bind_apply,
      PMF.pure_apply, PMF.coin_apply, half_prob]
    norm_num [ENNReal.ofReal_sub, ENNReal.ofReal_div_of_pos]
  · change bernoulliZMod2 half_prob 1 = PMF.uniformOfFintype (ZMod 2) 1
    simp [bernoulliZMod2, PMF.uniformOfFintype_apply, PMF.map, PMF.bind_apply,
      PMF.pure_apply, PMF.coin_apply, half_prob]

end CslibFrontierTests.Crypto.LWENormalSearchToDecisionAndLPN
