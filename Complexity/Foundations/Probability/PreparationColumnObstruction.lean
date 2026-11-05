/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyPreparationRanks

/-!
# A source-column obstruction to the auxiliary maximum profile

This original example distinguishes the weighted auxiliary maximum from actual incoming
preparation error. A stochastic reference sends all ordinary sources to one column; one
exceptional source splits equally between two columns. Deleting just that exceptional
row changes its auxiliary score by one. The source-column maximum consequently charges
all the ordinary reference entries, including when both incoming gates are closed.

Thus scalar own-entry error alone cannot pay this particular profile uniformly in width.
This does not give an estimator error lower bound. In particular, closing both gates makes
the actual preparation difference zero in the overloaded column. The smaller invariant
should retain the actual incoming-gate difference (or its actual rank difference) before
averaging, rather than the maximum auxiliary-score difference used in
`Matrix.preparationRankError`. Precisely, its column term should be
`atomPrep h ρ K f B T x y * |incomingGate I τ K Kc f A S T y -
incomingGate I τ K Kc f B S T y|`. An own-error payment still needs an integrated
bound for this term on successful completed children. Keeping the exact difference
removes the obstruction here; it does not by itself prove that bound.
No claim about exhaustive polynomial-bin execution follows
from the finite-bin execution test.

## Main definitions

* `Matrix.PreparationColumn.reference`: a stochastic reference with one split row.
* `Matrix.PreparationColumn.deleted`: the same table with the split row deleted.

## Main results

* `Matrix.PreparationColumn.profile_column`: the auxiliary maximum charges the whole column.
* `Matrix.PreparationColumn.closed_column`: the actual incoming preparations are both zero.
* `Matrix.PreparationColumn.profile_not_paid`: explicit width threshold for profile failure.
-/

public section
noncomputable section
namespace Matrix.PreparationColumn
open Finset Cslib
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A stochastic table: source `a` splits between distinct `a,b`; other sources go to `a`. -/
@[expose] def reference (a b : V) : Matrix V V ℝ :=
  fun x y => if x = a then (if y = a ∨ y = b then 1 / 2 else 0)
    else if y = a then 1 else 0

/-- Delete only the split row; every other entry is unchanged. -/
@[expose] def deleted (a b : V) : Matrix V V ℝ :=
  fun x y => if x = a then 0 else reference a b x y

/-- The canonical reference has nonnegative entries and every row has total mass one. -/
theorem reference_stochastic (a b : V) (hab : a ≠ b) :
    (∀ x y, 0 ≤ reference a b x y) ∧ (∀ x, ∑ y, reference a b x y = 1) := by
  constructor
  · intro x y
    unfold reference
    split_ifs <;> norm_num
  · intro x
    by_cases hx : x = a
    · subst x
      have he (y : V) : reference a b a y =
          (if y = a then (1 / 2 : ℝ) else 0) + (if y = b then 1 / 2 else 0) := by
        by_cases ha : y = a <;> by_cases hb : y = b <;> simp_all [reference]
      simp_rw [he]
      norm_num [sum_add_distrib]
    · simp [reference, hx]

omit [DecidableEq V] in
private theorem rank_zero (a b x : V) {K : ℕ} (hK : 2 < K)
    (A : Matrix V V ℝ) (hs : ∀ y, y ≠ a → y ≠ b → A x y = 0) :
    kthLargest K (univ : Finset V) (A x) = 0 := by
  classical
  apply le_antisymm _ kthLargest_nonneg
  apply not_lt.mp
  intro ht
  have hc := (lt_kthLargest_iff (by omega : 0 < K) (le_refl (0 : ℝ))).mp ht
  have hsub : ({y : V | 0 < A x y} : Finset V) ⊆ ({a, b} : Finset V) := by
    intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy
    by_contra hn
    have hn' : y ≠ a ∧ y ≠ b := by simpa using hn
    rw [hs y hn'.1 hn'.2] at hy
    exact lt_irrefl _ hy
  have hcard := (card_le_card hsub).trans (card_insert_le _ _)
  simp only [card_singleton] at hcard
  exact (not_le_of_gt hK) (hc.trans hcard)

/-- The row ranks vanish by two-entry support, even when the width exceeds the cap. -/
theorem row_ranks (a b x : V) {K : ℕ} (hK : 2 < K) :
    kthLargest K univ (fun y => deleted a b x y) = 0 ∧
      kthLargest K univ (fun y => reference a b x y) = 0 := by
  constructor
  · apply rank_zero a b x hK
    intro y ha hb
    simp [deleted, reference, ha, hb]
  · apply rank_zero a b x hK
    intro y ha hb
    simp [reference, ha, hb]

private theorem theta_small (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    HP.θ < 1 / 2 := by
  have h := HP.θ_lt_θ₂.trans HP.θ₂_lt
  norm_num at h
  linarith

/-- The exceptional source changes the actual polynomial auxiliary score by one. -/
theorem auxiliary_difference (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (a b : V) (hK : 2 < HP.K) :
    |auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 (deleted a b) univ a a -
      auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 (reference a b) univ a a| = 1 := by
  simp only [auxScore, div_one]
  rw [(row_ranks a b a hK).1, (row_ranks a b a hK).2]
  simp only [deleted, reference, ↓reduceIte, true_or]
  rw [polynomialAuxCutoff4_eq_zero_of_entry_le HP.θ_pos (by linarith [HP.θ_pos]),
    polynomialAuxCutoff4_eq_one HP.θ_pos (by linarith [theta_small HP])
      (by linarith [HP.θ_pos])]
  norm_num

/-- The actual auxiliary-score maximum at the overloaded column is one. -/
theorem auxiliary_maximum (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (a b : V) (hK : 2 < HP.K) :
    kthLargest 1 univ (fun z =>
      |auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 (deleted a b) univ z a -
        auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 (reference a b) univ z a|) = 1 := by
  apply le_antisymm
  · apply kthLargest_le zero_le_one
    intro z _
    exact abs_sub_le_of_nonneg_of_le
      (polynomialAuxCutoff4_nonneg _ _ _) (polynomialAuxCutoff4_le_one _ _ _)
      (polynomialAuxCutoff4_nonneg _ _ _) (polynomialAuxCutoff4_le_one _ _ _)
  · have h := abs_le_kthLargest_one univ (fun z =>
      auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 (deleted a b) univ z a -
        auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 (reference a b) univ z a)
      a (mem_univ _)
    rwa [auxiliary_difference HP a b hK] at h

/-- Every reference entry in the common column has preparation weight one. -/
theorem reference_preparation (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (a b x : V) (hK : 2 < HP.K) :
    atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1 (reference a b) univ x a = 1 := by
  simp only [atomPrep, rowGate, div_one]
  rw [(row_ranks a b x hK).2, HP.ρ_one 0 HP.η_pos.le, mul_one]
  apply polynomialPrepCutoff4_eq_one HP.θ_pos
  simp only [reference, true_or, ↓reduceIte]
  split_ifs <;> linarith [theta_small HP]

/-- The old source-column profile charges every row, regardless of the incoming cap.
Nonnegative entry/row coefficients can only add to this charge. -/
theorem profile_column (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (a b x : V) (hK : 2 < HP.K) (Kc : ℕ) {Lh Lρ Lτ : ℝ}
    (hh : 0 ≤ Lh) (hr : 0 ≤ Lρ) :
    Lτ ≤ preparationRankError (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
      (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K Kc 1 Lh Lρ Lτ
      (deleted a b) (reference a b) univ univ x a := by
  unfold preparationRankError
  rw [reference_preparation HP a b x hK, auxiliary_maximum HP a b hK]
  simp only [div_one, mul_one]
  have hg : 0 ≤ incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc 1
      (deleted a b) univ univ a := HP.incomingCutoff_nonneg _
  have hrow : 0 ≤ rowGate HP.ρ HP.K 1 (deleted a b) univ x := HP.ρ_nonneg _
  have hp : 0 ≤ polynomialPrepCutoff4 HP.θ (reference a b x a) :=
    polynomialPrepCutoff4_nonneg _ _
  have h1 : 0 ≤ Lh * |deleted a b x a - reference a b x a| *
      rowGate HP.ρ HP.K 1 (deleted a b) univ x *
      incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc 1
        (deleted a b) univ univ a := by positivity
  have hmax : 0 ≤ kthLargest 1 univ (fun w => |deleted a b x w - reference a b x w|) :=
    kthLargest_nonneg
  have h2 : 0 ≤ Lρ * polynomialPrepCutoff4 HP.θ (reference a b x a) *
      kthLargest 1 univ (fun w => |deleted a b x w - reference a b x w|) *
      incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc 1
        (deleted a b) univ univ a := by positivity
  linarith

/-- Once the ordinary incoming sources fill the cap, both actual preparations are zero
in that column. This is not an estimator error lower bound. -/
theorem closed_column (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (a b x : V) (hK : 2 < HP.K) {Kc : ℕ} (hKc : 0 < Kc)
    (hwidth : Kc < Fintype.card V) :
    correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc 1
      (deleted a b) (polynomialPrepCutoff4 HP.θ) HP.ρ univ univ x a = 0 ∧
    correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc 1
      (reference a b) (polynomialPrepCutoff4 HP.θ) HP.ρ univ univ x a = 0 := by
  have hτ : HP.τ₁ ≤ 1 := by rw [HP.τ₁_eq]; norm_num
  have hcard : Kc ≤ #((univ : Finset V).erase a) := by
    simp only [card_erase_of_mem (mem_univ _), card_univ]
    omega
  have he (z : V) (hz : z ∈ (univ : Finset V).erase a) : z ≠ a := (mem_erase.mp hz).1
  have hd (z : V) (hz : z ∈ (univ : Finset V).erase a) :
      auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 (deleted a b) univ z a = 1 := by
    simp only [auxScore, div_one]
    rw [(row_ranks a b z hK).1]
    simp only [deleted, reference, he z hz, ↓reduceIte]
    exact polynomialAuxCutoff4_eq_one HP.θ_pos (by linarith [theta_small HP])
      (by linarith [HP.θ_pos])
  have hb (z : V) (hz : z ∈ (univ : Finset V).erase a) :
      auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 (reference a b) univ z a = 1 := by
    simp only [auxScore, div_one]
    rw [(row_ranks a b z hK).2]
    simp only [reference, he z hz, ↓reduceIte]
    exact polynomialAuxCutoff4_eq_one HP.θ_pos (by linarith [theta_small HP])
      (by linarith [HP.θ_pos])
  have hgate (A : Matrix V V ℝ)
      (hA : ∀ z ∈ (univ : Finset V).erase a,
        auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 A univ z a = 1) :
      incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc 1 A
        univ univ a = 0 := by
    apply incomingGate_eq_zero hKc hτ (fun _ h => HP.incomingCutoff_zero h)
    apply hcard.trans
    apply card_le_card
    intro z hz
    exact mem_filter.mpr ⟨mem_univ _, by rw [hA z hz]⟩
  constructor <;> simp only [correctionPrep, hgate _ hd, hgate _ hb, mul_zero]

/-- Only two entries of one row contribute to the ordinary fourth-power error. -/
theorem own_error_sum (a b : V) (hab : a ≠ b) :
    ∑ x, ∑ y, |deleted a b x y - reference a b x y| ^ 4 = (1 / 8 : ℝ) := by
  have he (x y : V) : |deleted a b x y - reference a b x y| ^ 4 =
      if x = a then ((if y = a then (1 / 16 : ℝ) else 0) +
        (if y = b then 1 / 16 else 0)) else 0 := by
    by_cases hx : x = a <;> by_cases hy : y = a <;> by_cases hb : y = b <;>
      simp_all [deleted, reference] <;> norm_num
  simp_rw [he]
  norm_num [sum_add_distrib, sum_ite_irrel]

/-- A deterministic full-mask own error decreases inversely with width. -/
theorem own_error_moment (Ω : Type*) [Fintype Ω] [Nonempty Ω] (a b : V) (hab : a ≠ b) :
    rowNormPow 4 (Fintype.card V) 1 (fun (_ : Ω) (_ : V) => True)
      (fun _ _ => True) (fun _ x y => deleted a b x y - reference a b x y) =
      (Fintype.card V : ℝ)⁻¹ * (1 / 8) := by
  simp only [rowNormPow, mul_one, filter_true, Fintype.expect_const, own_error_sum a b hab]

/-- The old profile keeps a fixed positive moment while its own error tends to zero.
The incoming cap is arbitrary and can remain fixed below the growing width. -/
theorem profile_moment_lower (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (a b : V) (hK : 2 < HP.K) (Kc : ℕ) {Lh Lρ Lτ : ℝ}
    (hh : 0 ≤ Lh) (hr : 0 ≤ Lρ) (ht : 0 ≤ Lτ) :
    Lτ ^ 4 ≤ rowNormPow 4 (Fintype.card V) 1 (fun (_ : Ω) (_ : V) => True)
      (fun _ _ => True) (fun _ x y =>
        preparationRankError (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
          (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K Kc 1 Lh Lρ Lτ
          (deleted a b) (reference a b) univ univ x y) := by
  have : Nonempty V := ⟨a⟩
  simp only [rowNormPow, mul_one, filter_true, Fintype.expect_const]
  have hrow (x : V) : Lτ ^ 4 ≤ ∑ y,
      |preparationRankError (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
        (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K Kc 1 Lh Lρ Lτ
        (deleted a b) (reference a b) univ univ x y| ^ 4 := by
    apply (pow_le_pow_left₀ ht ((profile_column HP a b x hK Kc hh hr).trans
      (le_abs_self _)) 4).trans
    apply single_le_sum (f := fun y =>
      |preparationRankError (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
        (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K Kc 1 Lh Lρ Lτ
        (deleted a b) (reference a b) univ univ x y| ^ 4) (s := univ)
    · intro y _
      positivity
    · exact mem_univ a
  have hs := sum_le_sum (fun x (_hx : x ∈ (univ : Finset V)) => hrow x)
  simp only [sum_const, card_univ, nsmul_eq_mul] at hs
  have hc : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have h := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hc.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using h

/-- An explicit width threshold refutes payment of this auxiliary-maximum profile.
This concerns the profile only, even if both actual gates are closed. -/
theorem profile_not_paid (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (a b : V) (hab : a ≠ b) (hK : 2 < HP.K) (Kc : ℕ) {Lh Lρ Lτ D : ℝ}
    (hh : 0 ≤ Lh) (hr : 0 ≤ Lρ) (ht : 0 ≤ Lτ)
    (hwidth : D ^ 4 < 8 * Fintype.card V * Lτ ^ 4) :
    D ^ 4 * rowNormPow 4 (Fintype.card V) 1 (fun (_ : Ω) (_ : V) => True)
      (fun _ _ => True) (fun _ x y => deleted a b x y - reference a b x y) <
    rowNormPow 4 (Fintype.card V) 1 (fun (_ : Ω) (_ : V) => True)
      (fun _ _ => True) (fun _ x y =>
        preparationRankError (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
          (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K Kc 1 Lh Lρ Lτ
          (deleted a b) (reference a b) univ univ x y) := by
  have : Nonempty V := ⟨a⟩
  have hc : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  rw [own_error_moment Ω a b hab]
  apply lt_of_lt_of_le _ (profile_moment_lower Ω HP a b hK Kc hh hr ht)
  have h : D ^ 4 / (8 * Fintype.card V) < Lτ ^ 4 :=
    (div_lt_iff₀ (by positivity)).mpr (by nlinarith [hwidth])
  convert h using 1; ring

end Matrix.PreparationColumn
