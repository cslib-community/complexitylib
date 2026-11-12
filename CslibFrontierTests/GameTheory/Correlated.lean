/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.Strategic.Correlated
import CslibFrontierTests.GameTheory.Strategic

/-!
# Tests for correlated equilibria

The equilibrium concepts of [Roughgarden2013CS364A], Lecture 13, §3, are nested, and each
inclusion is strict:

* pure Nash ⊊ mixed Nash: matching pennies has no pure Nash equilibrium but has a mixed one
  (`CslibFrontierTests.GameTheory.Strategic`);
* mixed Nash ⊊ correlated: in the traffic-light game of Lecture 13, §3.4, the even mixture of the
  two pure Nash equilibria (stop, go) and (go, stop) is a correlated equilibrium but not a product
  distribution;
* correlated ⊊ coarse correlated: in Rock–Paper–Scissors, the uniform distribution on the six
  outcomes without a tie is a coarse correlated equilibrium, but a player recommended `a` gains by
  switching to the strategy that beats the strategy beating `a`.

The bridges from pure and mixed Nash equilibria to correlated equilibria are checked on the
Prisoner's Dilemma and matching pennies.
-/

namespace CslibFrontierTests.GameTheory.Correlated

open Cslib.GameTheory CslibFrontierTests.GameTheory.Strategic

/-! ### Bridges -/

/-- A pure Nash equilibrium is a correlated equilibrium as a point mass. -/
example : pd.IsCorrelatedEquilibrium (Convexity.StdSimplex.single fun _ => true) :=
  pd_isPureNash_defect.isCorrelatedEquilibrium

/-- The product distribution of the uniform mixed Nash equilibrium of matching pennies is a
correlated equilibrium, and hence the coarse correlated equilibrium `penniesUniform`. -/
example : pennies.IsCorrelatedEquilibrium
    (productDist (fun i => (pennies_isMixedNash_penniesHalf.1 i).nonneg)
      (fun i => (pennies_isMixedNash_penniesHalf.1 i).sum_eq_one)) :=
  pennies_isMixedNash_penniesHalf.isCorrelatedEquilibrium

/-- Correlated equilibria exist in every finite game. -/
example : ∃ σ, pennies.IsCorrelatedEquilibrium σ := pennies.exists_isCorrelatedEquilibrium

/-! ### The traffic light: a correlated equilibrium that is not a product distribution -/

/-- The traffic-light game of [Roughgarden2013CS364A], Lecture 13, §3.4, in cost form (negated
payoffs): `true` is "go" and `false` is "stop". Going against a stopped car pays `1`, and a
collision costs both drivers `5`. -/
def trafficCost (i : Fin 2) (s : Fin 2 → Bool) : ℝ :=
  match s 0, s 1 with
  | false, false => 0
  | false, true => if i = 0 then 0 else -1
  | true, false => if i = 0 then -1 else 0
  | true, true => 5

def traffic : CostGame (Fin 2) (fun _ => Bool) := ⟨trafficCost⟩

/-- The traffic light: (go, stop) and (stop, go) with probability `1/2` each. -/
noncomputable def trafficLight : Convexity.StdSimplex ℝ (Fin 2 → Bool) :=
  .duple ![true, false] ![false, true] (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)

private theorem trafficLight_sum (f : (Fin 2 → Bool) → ℝ) :
    trafficLight.weights.sum (fun s w => w * f s)
      = 1 / 2 * f ![true, false] + 1 / 2 * f ![false, true] := by
  rw [trafficLight, Convexity.StdSimplex.duple, Finsupp.sum_add_index' (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _), Finsupp.sum_single_index (zero_mul _),
    Finsupp.sum_single_index (zero_mul _)]

/-- Each driver follows its light: told to go, the other stops; told to stop, the other goes. -/
theorem traffic_isCorrelatedEquilibrium_trafficLight :
    traffic.IsCorrelatedEquilibrium trafficLight := by
  intro i δ
  rw [trafficLight_sum, trafficLight_sum]
  fin_cases i <;> cases hT : δ true <;> cases hF : δ false <;>
    norm_num [traffic, trafficCost, Function.update, hT, hF]

/-- The traffic light is not the product distribution of any pair of mixed strategies, so it is
not induced by a mixed Nash equilibrium. -/
theorem trafficLight_ne_productDist {p : Fin 2 → Bool → ℝ} (hp0 : ∀ i a, 0 ≤ p i a)
    (hp1 : ∀ i, ∑ a, p i a = 1) : productDist hp0 hp1 ≠ trafficLight := by
  intro h
  have hw : ∀ s, p 0 (s 0) * p 1 (s 1)
      = trafficLight.weights.sum (fun t w => w * if t = s then 1 else 0) := fun s => by
    rw [← h, productDist_sum]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      productWeight_def, Fin.prod_univ_two]
  have h1 : p 0 true * p 1 false = 1 / 2 := by
    have := hw ![true, false]
    rw [trafficLight_sum] at this
    norm_num [Matrix.vecCons_inj] at this
    linarith
  have h2 : p 0 false * p 1 true = 1 / 2 := by
    have := hw ![false, true]
    rw [trafficLight_sum] at this
    norm_num [Matrix.vecCons_inj] at this
    linarith
  have h3 : p 0 false = 0 ∨ p 1 false = 0 := by
    have := hw ![false, false]
    rw [trafficLight_sum] at this
    norm_num [Matrix.vecCons_inj] at this
    tauto
  rcases h3 with h0 | h0
  · rw [h0, zero_mul] at h2
    norm_num at h2
  · rw [h0, mul_zero] at h1
    norm_num at h1

/-! ### Rock–Paper–Scissors: a coarse correlated equilibrium that is not correlated -/

/-- Rock–Paper–Scissors in cost form, with strategies `Fin 3` and `a + 1` beating `a`: the winner
pays `-1`, the loser `1`, and a tie costs nothing. -/
def rps : CostGame (Fin 2) (fun _ => Fin 3) where
  cost i s := if s i = s (i + 1) + 1 then -1 else if s (i + 1) = s i + 1 then 1 else 0

/-- The uniform distribution on the six outcomes without a tie. -/
noncomputable def rpsNoTie : Convexity.StdSimplex ℝ (Fin 2 → Fin 3) where
  weights := Finsupp.equivFunOnFinite.symm fun s => if s 0 = s 1 then 0 else 1 / 6
  nonneg s := by
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_equivFunOnFinite_symm]
    split_ifs <;> norm_num
  total := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl, ← (piFinTwoEquiv fun _ => Fin 3).symm.sum_comp]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Fintype.sum_prod_type, Fin.sum_univ_three,
      piFinTwoEquiv_symm_apply]
    norm_num

private theorem rpsNoTie_sum (f : (Fin 2 → Fin 3) → ℝ) :
    rpsNoTie.weights.sum (fun s w => w * f s)
      = ∑ x : Fin 3 × Fin 3, (if x.1 = x.2 then 0 else 1 / 6) * f ![x.1, x.2] := by
  rw [Finsupp.sum_fintype _ _ fun _ => zero_mul _,
    ← (piFinTwoEquiv fun _ => Fin 3).symm.sum_comp]
  simp only [rpsNoTie, Finsupp.coe_equivFunOnFinite_symm, piFinTwoEquiv_symm_apply]
  rfl

/-- Against the uniform no-tie distribution, every fixed strategy breaks even on average. -/
theorem rps_isCoarseCorrelatedEquilibrium_rpsNoTie :
    rps.IsCoarseCorrelatedEquilibrium rpsNoTie := by
  intro i a
  rw [rpsNoTie_sum, rpsNoTie_sum]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three]
  fin_cases i <;> fin_cases a <;> norm_num [rps, Function.update]

/-- Switching from each recommendation `a` to `a + 2`, which beats `a + 1`, wins against the
recommended opponent strategies `a + 1` and `a + 2` on average. -/
theorem rps_not_isCorrelatedEquilibrium_rpsNoTie :
    ¬ rps.IsCorrelatedEquilibrium rpsNoTie := by
  intro h
  have h0 := h 0 fun a => a + 2
  rw [rpsNoTie_sum, rpsNoTie_sum] at h0
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three] at h0
  norm_num [rps, Function.update] at h0

/-- The strict hierarchy: mixed Nash ⊊ correlated ⊊ coarse correlated. -/
example : (traffic.IsCorrelatedEquilibrium trafficLight ∧
      ∀ (p : Fin 2 → Bool → ℝ) (h : traffic.IsMixedNash p),
        productDist (fun i => (h.1 i).nonneg) (fun i => (h.1 i).sum_eq_one) ≠ trafficLight) ∧
    rps.IsCoarseCorrelatedEquilibrium rpsNoTie ∧ ¬ rps.IsCorrelatedEquilibrium rpsNoTie :=
  ⟨⟨traffic_isCorrelatedEquilibrium_trafficLight, fun _ _ => trafficLight_ne_productDist _ _⟩,
    rps_isCoarseCorrelatedEquilibrium_rpsNoTie, rps_not_isCorrelatedEquilibrium_rpsNoTie⟩

end CslibFrontierTests.GameTheory.Correlated
