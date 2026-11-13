/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module

import CslibFrontier.Computability.Communication.Lifting.DangerousParameters
import CslibFrontier.Computability.Communication.Lifting.WitnessCounting
import CslibFrontier.Computability.Communication.Lifting.RatioWitness
import CslibFrontier.Computability.Communication.Lifting.DiscrepancyLifting
import CslibFrontier.Computability.Communication.Lifting.ParameterSpecialization
import CslibFrontier.Computability.Communication.Lifting.RareDanger
import CslibFrontier.Computability.Communication.Protocol.Alternating
import CslibFrontier.Computability.Communication.Lifting.SimulationTrace

/-! Finite counting, threshold rounding and executed-trace regression clients. -/

open Cslib.Communication.Lifting Cslib.Probability Finset

/-- Empty assignment plus two choices of coordinate, each with two alphabet values. -/
example : Fintype.card (ConditioningAssignment (univ : Finset (Fin 2)) 2 1) = 5 := by
  rw [card_conditioningAssignment]
  norm_num [sum_range_succ, Nat.choose]

/-- A threshold above the ambient dimension does not introduce fictitious assignments. -/
example : Fintype.card (ConditioningAssignment (univ : Finset (Fin 2)) 2 5) = 9 := by
  rw [card_conditioningAssignment]
  norm_num [sum_range_succ, Nat.choose]

/-- The ratio threshold pays its low-order mass while allowing larger parity witnesses. -/
example : ∃ t : ℕ, 1 ≤ t ∧ (2 : ℝ) ^ t ≤ 16 ∧ (64 : ℝ) ≤ 2 ^ (2 * t) := by
  simpa only [show (64 : ℝ) / 4 = 16 by norm_num] using
    exists_power_threshold_of_ratio (N := 2) (R := 64) (by norm_num) (by norm_num)

/-- The ambient subset estimate includes an empty coordinate set. -/
example : (#{S : Finset (Fin 0) | S.card < 1} + 1) ≤ 2 ^ 1 := by
  apply card_filter_card_lt_add_one_le_pow_of_card_le <;> simp

/-- A valid executed trace cannot query more than the ambient input dimension. -/
example {n m c q : ℕ} {g : Fin m → Fin m → Bool} {τ σ : ℝ}
    {F' : Finset (Fin n)} {X' Y' : Finset (Fin n → Fin m)}
    (h : DensityTrace g τ σ univ univ univ F' X' Y' c q) : q ≤ n := by
  have hf := h.card_free
  simp only [card_univ, Fintype.card_fin] at hf
  omega

/-- The multiplicative query bound needs no extra endpoint fixedness hypothesis. -/
example {n m c q : ℕ} {g : Fin m → Fin m → Bool} {τ σ : ℝ}
    {F' : Finset (Fin n)} {X' Y' : Finset (Fin n → Fin m)}
    (h : DensityTrace g τ σ univ univ univ F' X' Y' c q) (hm : 0 < m) (hτ : 0 < τ) :
    ((m : ℝ) / (2 * τ)) ^ q ≤ 8 ^ c := h.query_bound hm hτ

/-- Repeated Alice messages really need a dummy Bob message. -/
example : ¬ Cslib.Communication.Protocol.Alternates true
    (Cslib.Communication.Protocol.alice (fun x : Bool => x)
      (.alice (fun x => x) (.output false) (.output true))
      (.output true) : Cslib.Communication.Protocol Bool Bool Bool) := by
  simp [Cslib.Communication.Protocol.Alternates]

/-- Normalization supplies the invariant for the same repeated-speaker protocol. -/
example (p : Cslib.Communication.Protocol Bool Bool Bool) :
    Cslib.Communication.Protocol.Alternates true (p.alternate true) ∧
      (p.alternate true).depth ≤ 2 * p.depth ∧
      ∀ x y, (p.alternate true).run x y = p.run x y :=
  ⟨p.alternates_alternate true, p.depth_alternate_le true, p.run_alternate true⟩

/-- The explicit polynomial parameters pay a factor growing with the alphabet base per query. -/
example {B : ℝ} (hB : 2 ≤ B) : B ^ 31 ≤ B ^ 2048 / (2 * B ^ 2016) :=
  (polynomial_density_ratios hB).2.2.2

-- The concrete alphabet exponent must be permitted during type elaboration.
set_option exponentiation.threshold 2048 in
/-- A functional client of the relation-valued lifting theorem. -/
example {n B : ℕ} [NeZero B] (g : Fin (B ^ 2048) → Fin (B ^ 2048) → Bool)
    (f : (Fin n → Bool) → Bool) (hB : 2 ≤ B) (hn : 2 ≤ n) (hnB : n ≤ B)
    (hd : Cslib.Communication.discrepancy
      (PMF.uniformOfFintype (Fin (B ^ 2048) × Fin (B ^ 2048))) g ≤ ((B : ℝ) ^ 1024)⁻¹)
    (p : Cslib.Communication.Protocol
      (Fin n → Fin (B ^ 2048)) (Fin n → Fin (B ^ 2048)) Bool)
    (hp : ∀ x y, p.run x y = f (fun i => g (x i) (y i))) :
    ∃ t : Cslib.DecisionTree (Fin n) Bool, (∀ z, t.eval z = f z) ∧
      (B : ℝ) ^ (31 * t.depth) ≤ 8 ^ (2 * p.depth) :=
  exists_decisionTree_of_polynomial_discrepancy g hB hn hnB hd
    (fun z output => output = f z) p hp
