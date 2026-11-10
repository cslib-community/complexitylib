/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.Strategic.Mixed
import CslibFrontier.GameTheory.Strategic.Nash
import CslibFrontier.GameTheory.Strategic.NoRegret
import CslibFrontier.GameTheory.Strategic.Potential
import CslibFrontier.GameTheory.Strategic.Smooth

/-!
# Strategic games, mixed Nash equilibria, potentials and coarse correlated equilibria

The Prisoner's Dilemma of [MondererShapley1996], Section 2, in cost form, has an exact potential
and therefore a pure Nash equilibrium, mutual defection, at which the social cost exceeds that of
mutual cooperation. Matching pennies has no pure Nash equilibrium, so it has neither the finite
improvement property nor a generalized ordinal potential. A pure Nash equilibrium is a coarse
correlated equilibrium as a point mass. In matching pennies, uniform mixing is a coarse correlated
equilibrium. A pure equilibrium played in every round has no regret, so Proposition 3.1 of
[Roughgarden2013CS364A], Lecture 17, recovers it from its time average.

Uniform mixing is the mixed Nash equilibrium of matching pennies, and its product distribution
recovers the coarse correlated equilibrium above. Nash's theorem gives matching pennies a mixed
Nash equilibrium, which cannot consist of point masses because there is no pure one. In the
Prisoner's Dilemma, point masses at mutual defection form a mixed Nash equilibrium and point masses
at mutual cooperation do not.
-/

namespace CslibFrontierTests.GameTheory.Strategic

open Cslib.GameTheory

/-- The Prisoner's Dilemma payoffs of [MondererShapley1996], Section 2, as costs (negated payoffs):
`true` is "defect" and `false` is "cooperate". -/
def pdCost (i : Fin 2) (s : Fin 2 → Bool) : ℝ :=
  match s 0, s 1 with
  | false, false => -6
  | false, true => if i = 0 then 0 else -9
  | true, false => if i = 0 then -9 else 0
  | true, true => -1

def pd : CostGame (Fin 2) (fun _ => Bool) := ⟨pdCost⟩

/-- The exact potential of [MondererShapley1996], Section 2, negated for costs. -/
def pdPotential (s : Fin 2 → Bool) : ℝ :=
  match s 0, s 1 with
  | false, false => 0
  | false, true => -3
  | true, false => -3
  | true, true => -4

private theorem pd_cases (s : Fin 2 → Bool) : s = ![s 0, s 1] := by
  funext j
  fin_cases j <;> rfl

theorem pd_isExactPotential : pd.IsExactPotential pdPotential := by
  intro s i a
  rw [pd_cases s]
  fin_cases i <;> cases a <;> cases h0 : s 0 <;> cases h1 : s 1 <;>
    norm_num [pd, pdCost, pdPotential, Function.update]

/-- Mutual defection is a pure Nash equilibrium. -/
theorem pd_isPureNash_defect : pd.IsPureNash fun _ => true := by
  intro i a
  fin_cases i <;> cases a <;> norm_num [pd, pdCost, Function.update]

/-- Mutual cooperation is not a pure Nash equilibrium. -/
theorem pd_not_isPureNash_cooperate : ¬ pd.IsPureNash fun _ => false := by
  intro h
  have h0 := h 0 true
  norm_num [pd, pdCost, Function.update] at h0

/-- The equilibrium is inefficient: social cost `-2` against `-12` under cooperation. -/
example : pd.socialCost (fun _ => true) = -2 ∧ pd.socialCost (fun _ => false) = -12 := by
  norm_num [CostGame.socialCost, pd, pdCost, Fin.sum_univ_two]

/-- Existence through the potential (Monderer–Shapley Corollary 2.2). -/
example : ∃ s, pd.IsPureNash s :=
  pd_isExactPotential.isGeneralizedOrdinalPotential.exists_isPureNash

example : pd.HasFIP := pd_isExactPotential.isGeneralizedOrdinalPotential.hasFIP

/-- Better-response dynamics from mutual cooperation reach an equilibrium. -/
example : ∃ t, Relation.ReflTransGen (flip pd.Improves) (fun _ => false) t ∧ pd.IsPureNash t :=
  (pd_isExactPotential.isGeneralizedOrdinalPotential.hasFIP).exists_reflTransGen_isPureNash _

/-- Two exact potentials differ by a constant (Monderer–Shapley Lemma 2.7). -/
example (s t : Fin 2 → Bool) :
    pdPotential s - (pdPotential s + 7) = pdPotential t - (pdPotential t + 7) :=
  pd_isExactPotential.sub_eq_sub (Ψ := fun s => pdPotential s + 7)
    (fun s i a => by rw [pd_isExactPotential s i a]; ring) s t

/-- A pure Nash equilibrium is a coarse correlated equilibrium as a point mass. -/
example : pd.IsCoarseCorrelatedEquilibrium (Convexity.StdSimplex.single fun _ => true) :=
  pd_isPureNash_defect.isCoarseCorrelatedEquilibrium

/-- Matching pennies in cost form: player `0` wants to match, player `1` to mismatch. -/
def pennies : CostGame (Fin 2) (fun _ => Bool) where
  cost i s := if (s 0 == s 1) = (i == 0) then 0 else 1

theorem pennies_not_isPureNash (s : Fin 2 → Bool) : ¬ pennies.IsPureNash s := by
  intro h
  rw [pd_cases s] at h
  cases h0 : s 0 <;> cases h1 : s 1 <;> rw [h0, h1] at h
  · have := h 1 true
    norm_num [pennies, Function.update] at this
  · have := h 0 true
    norm_num [pennies, Function.update] at this
  · have := h 0 false
    norm_num [pennies, Function.update] at this
  · have := h 1 false
    norm_num [pennies, Function.update] at this

/-- Matching pennies has an infinite improvement path, hence no generalized ordinal potential. -/
example : ¬ pennies.HasFIP := fun h =>
  let ⟨s, hs⟩ := h.exists_isPureNash
  pennies_not_isPureNash s hs

example : ¬ ∃ Φ, pennies.IsGeneralizedOrdinalPotential Φ := fun ⟨_, hΦ⟩ =>
  let ⟨s, hs⟩ := hΦ.exists_isPureNash
  pennies_not_isPureNash s hs

/-- The uniform mixed strategies of matching pennies. -/
noncomputable def penniesUniform : Convexity.StdSimplex ℝ (Fin 2 → Bool) :=
  productDist (p := fun _ _ => 1 / 2) (fun _ _ => by norm_num)
    (fun _ => by rw [Fintype.sum_bool]; norm_num)

/-- Uniform mixing is a coarse correlated equilibrium of matching pennies, which has no pure Nash
equilibrium. -/
theorem pennies_isCoarseCorrelatedEquilibrium_uniform :
    pennies.IsCoarseCorrelatedEquilibrium penniesUniform := by
  intro i a
  rw [penniesUniform, productDist_sum, productDist_sum,
    ← (piFinTwoEquiv fun _ => Bool).symm.sum_comp, ← (piFinTwoEquiv fun _ => Bool).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, productWeight, Fin.prod_univ_two,
    piFinTwoEquiv_symm_apply]
  fin_cases i <;> cases a <;> norm_num [pennies, Function.update, Fin.cons_zero, Fin.cons_one]

/-- A pure Nash equilibrium played in every round has no regret, and Proposition 3.1 recovers it
as a coarse correlated equilibrium of the time average. -/
example (T : ℕ) (hT : 0 < T) (i : Fin 2) (a : Bool) :
    (timeAverage (fun _ => Convexity.StdSimplex.single fun _ => true) T hT).weights.sum
        (fun s w => w * pd.cost i s)
      ≤ (timeAverage (fun _ => Convexity.StdSimplex.single fun _ => true) T hT).weights.sum
          (fun s w => w * pd.cost i (Function.update s i a)) + 0 / T := by
  refine CostGame.timeAverage_le_add (G := pd) hT (R := fun _ => 0) (fun j b => ?_) i a
  simp only [Convexity.StdSimplex.weights_single, Finsupp.sum_single_index, zero_mul, one_mul,
    add_zero]
  exact Finset.sum_le_sum fun _ _ => pd_isPureNash_defect j b

/-! ### Mixed Nash equilibria -/

/-- The uniform mixed strategies of matching pennies. -/
noncomputable def penniesHalf : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2

private theorem isMixedStrategy_penniesHalf (i : Fin 2) : IsMixedStrategy (penniesHalf i) :=
  isMixedStrategy_iff.2 ⟨fun _ => by norm_num [penniesHalf], by
    rw [Fintype.sum_bool]; norm_num [penniesHalf]⟩

/-- Against uniform mixing, every pure strategy of matching pennies costs `1/2` in expectation. -/
private theorem pennies_deviationCost_penniesHalf (i : Fin 2) (a : Bool) :
    pennies.deviationCost penniesHalf i a = 1 / 2 := by
  rw [CostGame.deviationCost_def, ← (piFinTwoEquiv fun _ => Bool).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, productWeight_def, Fin.prod_univ_two,
    piFinTwoEquiv_symm_apply]
  fin_cases i <;> cases a <;>
    norm_num [pennies, penniesHalf, Function.update, Fin.cons_zero, Fin.cons_one]

/-- Uniform mixing is a mixed Nash equilibrium of matching pennies. -/
theorem pennies_isMixedNash_penniesHalf : pennies.IsMixedNash penniesHalf := by
  refine ⟨isMixedStrategy_penniesHalf, fun i a => ?_⟩
  rw [← pennies.sum_mul_deviationCost_eq_expectedCost _ (isMixedStrategy_penniesHalf i).sum_eq_one]
  simp only [pennies_deviationCost_penniesHalf, Fintype.sum_bool, penniesHalf]
  norm_num

/-- Its product distribution is the coarse correlated equilibrium `penniesUniform`. -/
example : pennies.IsCoarseCorrelatedEquilibrium penniesUniform :=
  pennies_isMixedNash_penniesHalf.isCoarseCorrelatedEquilibrium

/-- Mixed deviations from uniform mixing gain nothing either. -/
example (i : Fin 2) (q : Bool → ℝ) (hq : IsMixedStrategy q) :
    pennies.expectedCost penniesHalf i ≤ pennies.expectedCost (Function.update penniesHalf i q) i :=
  pennies_isMixedNash_penniesHalf.expectedCost_le_update i hq

/-- Nash's theorem gives matching pennies a mixed Nash equilibrium. None of its mixed Nash
equilibria is made of point masses, since it has no pure Nash equilibrium. -/
example : (∃ p, pennies.IsMixedNash p) ∧
    ∀ s : Fin 2 → Bool, ¬ pennies.IsMixedNash fun i => Pi.single (s i) 1 :=
  ⟨pennies.exists_isMixedNash, fun s h =>
    pennies_not_isPureNash s ((pennies.isMixedNash_single_iff s).1 h)⟩

/-- In the Prisoner's Dilemma, point masses at mutual defection form a mixed Nash equilibrium, and
point masses at mutual cooperation do not. -/
example : pd.IsMixedNash (fun _ => Pi.single true 1) ∧
    ¬ pd.IsMixedNash (fun _ => Pi.single false 1) :=
  ⟨pd_isPureNash_defect.isMixedNash, fun h =>
    pd_not_isPureNash_cooperate ((pd.isMixedNash_single_iff fun _ => false).1 h)⟩

end CslibFrontierTests.GameTheory.Strategic
