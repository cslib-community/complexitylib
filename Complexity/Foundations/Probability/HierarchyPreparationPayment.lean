/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyPreparationGates

/-!
# Sparse payment of actual incoming preparation

These original finite estimates use the supports of the actual polynomial auxiliary
scores and preparations of both signed RAW tables. They do not transfer canonical
support to an approximate child. Row sparsity pays row-rank perturbations; incoming
column sparsity pays column-rank perturbations before averaging. Constants depend on
the fixed hierarchy ranks, with an explicit inverse terminal-rate fourth power.

The unrestricted `preparationGateError` can charge points outside both actual output
supports. The estimates here pay the actual preparation difference instead. Recursive
joint availability and the numerical precision salary remain separate obligations.

## Main results

* `auxiliary_row_support`, `preparation_row_support`, `preparation_column_support`:
  gate-enforced support bounds for each signed RAW table.
* `preparation_fourth_sum`, `preparation_row_moment`: finite and masked field-free payment.
* `Matrix.HierarchyParams.H4RankEnvironment.BudgetData.evaluate_preparation_paid_bias`:
  the literal successful PREP mean paid by its input child's ordinary own accuracy.
-/

public section
noncomputable section
namespace Matrix.FourthRootHierarchyParams
open Finset Cslib
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix

private theorem sub_support_card {V : Type*} (S : Finset V) (a b : V → ℝ)
    {K : ℕ} (ha : #{x ∈ S | a x ≠ 0} < K) (hb : #{x ∈ S | b x ≠ 0} < K) :
    #{x ∈ S | a x - b x ≠ 0} ≤ 2 * K := by
  have hs : {x ∈ S | a x - b x ≠ 0} ⊆
      {x ∈ S | a x ≠ 0} ∪ {x ∈ S | b x ≠ 0} := by
    intro x hx
    rcases mem_filter.mp hx with ⟨hx, hn⟩
    by_cases h : a x = 0
    · exact mem_union_right _ (mem_filter.mpr ⟨hx, fun h' => hn (by rw [h, h', sub_self])⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hx, h⟩)
  have hc := (card_le_card hs).trans (card_union_le _ _)
  omega

private theorem sparse_fourth_sum {V : Type*} (S : Finset V) (a : V → ℝ)
    {K : ℕ} {b : ℝ} (hb : 0 ≤ b) (hc : #{x ∈ S | a x ≠ 0} ≤ K)
    (h : ∀ x ∈ S, |a x| ≤ b) :
    ∑ x ∈ S, |a x| ^ 4 ≤ K * b ^ 4 := by
  have he : (∑ x ∈ S, |a x| ^ 4) = ∑ x ∈ S.filter (fun x => a x ≠ 0), |a x| ^ 4 := by
    symm
    rw [sum_filter]
    apply sum_congr rfl
    intro x _
    split_ifs with hx
    · rfl
    · simp [not_ne_iff.mp hx]
  rw [he]
  calc
    _ ≤ ∑ _x ∈ S.filter (fun x => a x ≠ 0), b ^ 4 :=
      sum_le_sum fun x hx => pow_le_pow_left₀ (abs_nonneg _) (h x (mem_filter.mp hx).1) 4
    _ = (#(S.filter (fun x => a x ≠ 0)) : ℝ) * b ^ 4 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (pow_nonneg hb 4)

variable (HP : FourthRootHierarchyParams 16 1 16 32 8)

/-- Auxiliary scores of an arbitrary signed RAW table have fewer than K nonzero
entries in a retained row: their rank closure lies below their entry threshold. -/
theorem auxiliary_row_support {V : Type*} (f : ℝ) (A : Matrix V V ℝ)
    (T : Finset V) (x : V) :
    #{y ∈ T | auxScore (polynomialAuxCutoff4 HP.θ) HP.K f A T x y ≠ 0} < HP.K := by
  have hK := NormalizedRow.rank_pos HP
  by_contra hn
  have hs : {y ∈ T | auxScore (polynomialAuxCutoff4 HP.θ) HP.K f A T x y ≠ 0} ⊆
      {y ∈ T | HP.θ / 8 < A x y / f} := by
    intro y hy
    refine mem_filter.mpr ⟨(mem_filter.mp hy).1, lt_of_not_ge ?_⟩
    intro he
    exact (mem_filter.mp hy).2 (polynomialAuxCutoff4_eq_zero_of_entry_le HP.θ_pos he)
  have hr : HP.θ / 8 < kthLargest HP.K T (fun y => A x y / f) :=
    (lt_kthLargest_iff hK (by linarith [HP.θ_pos])).mpr
      ((not_lt.mp hn).trans (card_le_card hs))
  have hz (y : V) : auxScore (polynomialAuxCutoff4 HP.θ) HP.K f A T x y = 0 :=
    polynomialAuxCutoff4_eq_zero_of_rank_ge HP.θ_pos (by linarith [HP.θ_pos])
  have he : {y ∈ T | auxScore (polynomialAuxCutoff4 HP.θ) HP.K f A T x y ≠ 0} = ∅ := by
    simp only [hz, ne_eq, not_true_eq_false, filter_false]
  rw [he, card_empty] at hn
  exact hn hK

/-- Actual incoming preparation has a sparse retained row, for each RAW table separately. -/
theorem preparation_row_support {V : Type*} (Kc : ℕ) (f : ℝ)
    (A : Matrix V V ℝ) (S T : Finset V) (x : V) :
    #{y ∈ T | correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f A
      (polynomialPrepCutoff4 HP.θ) HP.ρ S T x y ≠ 0} < HP.K := by
  apply lt_of_le_of_lt (card_le_card ?_)
    (card_filter_mul_rowGate_ne_zero_lt (a := f) (G := A) T x (NormalizedRow.rank_pos HP)
      (by linarith [HP.θ_pos] : 0 ≤ HP.θ / 2)
      (fun _ h => polynomialPrepCutoff4_eq_zero HP.θ_pos h)
      (show HP.η₂ ≤ HP.θ / 2 by
        linarith [HP.η₂_lt, HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_pos]) HP.ρ_zero)
  intro y hy
  exact mem_filter.mpr ⟨(mem_filter.mp hy).1, fun h =>
    (mem_filter.mp hy).2 (by simp only [correctionPrep, h, zero_mul])⟩

/-- The actual incoming gate enforces column sparsity on each signed RAW table.
No canonical-to-approximate support premise occurs. -/
theorem preparation_column_support {V : Type*} {Kc : ℕ} (hKc : 0 < Kc) (f : ℝ)
    (A : Matrix V V ℝ) (S T : Finset V) (y : V) :
    #{x ∈ S | correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f A
      (polynomialPrepCutoff4 HP.θ) HP.ρ S T x y ≠ 0} < Kc := by
  by_contra hn
  have hg : incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f A S T y = 0 := by
    apply incomingGate_eq_zero hKc (show HP.τ₁ ≤ 1 by rw [HP.τ₁_eq]; norm_num)
      (fun _ h => HP.incomingCutoff_zero h)
    apply (not_lt.mp hn).trans
    apply card_le_card
    intro x hx
    rcases mem_filter.mp hx with ⟨hx, hne⟩
    have he : polynomialPrepCutoff4 HP.θ (A x y / f) ≠ 0 := by
      intro he
      exact hne (by simp only [correctionPrep, he, zero_mul])
    have hr : HP.ρ (kthLargest HP.K T (fun w => A x w / f)) ≠ 0 := by
      intro hr
      exact hne (by simp only [correctionPrep, rowGate, hr, mul_zero, zero_mul])
    exact mem_filter.mpr ⟨hx, by rw [auxScore, HP.aux_full_on_prep_rho he hr]⟩
  have hz : {x ∈ S | correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
      HP.K Kc f A (polynomialPrepCutoff4 HP.θ) HP.ρ S T x y ≠ 0} = ∅ := by
    simp only [correctionPrep, hg, mul_zero, ne_eq, not_true_eq_false, filter_false]
  rw [hz, card_empty] at hn
  exact hn hKc

/-- Two sparse auxiliary supports pay the same-row rank error without a width factor. -/
theorem auxiliary_fourth_sum {V : Type*} {LI f : ℝ} (hLI : 0 ≤ LI) (hf : 0 < f)
    (hI : ∀ v q v' q', |polynomialAuxCutoff4 HP.θ v q - polynomialAuxCutoff4 HP.θ v' q'| ≤
      LI * (|v - v'| + |q - q'|))
    (A B : Matrix V V ℝ) (T : Finset V) (x : V) :
    ∑ y ∈ T, |auxScore (polynomialAuxCutoff4 HP.θ) HP.K f A T x y -
      auxScore (polynomialAuxCutoff4 HP.θ) HP.K f B T x y| ^ 4 ≤
      (2 * HP.K : ℝ) * (2 * LI / f) ^ 4 * ∑ y ∈ T, |A x y - B x y| ^ 4 := by
  let e := kthLargest 1 T (fun y => |A x y - B x y|)
  have he : 0 ≤ e := kthLargest_nonneg
  have hp := sparse_fourth_sum T
    (fun y => auxScore (polynomialAuxCutoff4 HP.θ) HP.K f A T x y -
      auxScore (polynomialAuxCutoff4 HP.θ) HP.K f B T x y)
    (b := (2 * LI / f) * e)
    (mul_nonneg (div_nonneg (by positivity) hf.le) he)
    (sub_support_card T _ _ (HP.auxiliary_row_support f A T x)
      (HP.auxiliary_row_support f B T x)) (fun y hy => ?_)
  · have hm := abs_kthLargest_pow_le_sum T (fun y => A x y - B x y) (by decide : 4 ≠ 0)
    rw [abs_of_nonneg he] at hm
    exact hp.trans (by
      rw [mul_pow, ← mul_assoc]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_left hm (by positivity))
  · apply (auxScore_stability hLI hI (NormalizedRow.rank_pos HP) hf A B T x y).trans
    have hm := abs_le_kthLargest_one T (fun y => A x y - B x y) y hy
    calc
      _ ≤ LI * (e + e) / f := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hm (le_refl e)) hLI) hf.le
      _ = _ := by ring

private theorem sparse_axes_fourth_sum {V : Type*} (S T : Finset V)
    (Z : Matrix V V ℝ) (R C : V → ℝ) (kr kc : ℕ)
    (hR : ∀ x, 0 ≤ R x) (hC : ∀ y, 0 ≤ C y)
    (hr : ∀ x ∈ S, #{y ∈ T | Z x y ≠ 0} ≤ kr)
    (hc : ∀ y ∈ T, #{x ∈ S | Z x y ≠ 0} ≤ kc)
    (hz : ∀ x ∈ S, ∀ y ∈ T, |Z x y| ≤ R x + C y) :
    ∑ x ∈ S, ∑ y ∈ T, |Z x y| ^ 4 ≤
      8 * ((kr : ℝ) * ∑ x ∈ S, R x ^ 4 + (kc : ℝ) * ∑ y ∈ T, C y ^ 4) := by
  let F := fun x y => Z x y ≠ 0
  have hpoint (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ T) :
      |Z x y| ^ 4 ≤ 8 * ((if F x y then R x ^ 4 else 0) +
        (if F x y then C y ^ 4 else 0)) := by
    by_cases h : F x y
    · simp only [h, ↓reduceIte]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hz x hx y hy) 4).trans
        (by convert add_pow_le (hR x) (hC y) 4 using 1; norm_num)
    · simp only [F, ne_eq, not_not] at h
      simp [F, h]
  have hrow (x : V) (hx : x ∈ S) :
      ∑ y ∈ T, (if F x y then R x ^ 4 else 0) ≤ kr * R x ^ 4 := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hr x hx) (by positivity)
  have hcol (y : V) (hy : y ∈ T) :
      ∑ x ∈ S, (if F x y then C y ^ 4 else 0) ≤ kc * C y ^ 4 := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc y hy) (by positivity)
  calc
    _ ≤ ∑ x ∈ S, ∑ y ∈ T, 8 * ((if F x y then R x ^ 4 else 0) +
        (if F x y then C y ^ 4 else 0)) :=
      sum_le_sum fun x hx => sum_le_sum fun y hy => hpoint x hx y hy
    _ = 8 * ((∑ x ∈ S, ∑ y ∈ T, if F x y then R x ^ 4 else 0) +
        ∑ y ∈ T, ∑ x ∈ S, if F x y then C y ^ 4 else 0) := by
      simp only [mul_add, mul_sum, sum_add_distrib]
      congr 1
      exact sum_comm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [mul_sum] using add_le_add (sum_le_sum hrow) (sum_le_sum hcol)

/-- Actual PREP error has no ambient-width loss. Both tables may be signed and
unbounded; only their own gate-enforced row and column supports are used. The two
rank sets, terminal rate, and entry units remain unchanged. -/
theorem preparation_fourth_sum :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (V : Type*) (Kc : ℕ), 0 < Kc →
    ∀ (f : ℝ), 0 < f → ∀ (A B : Matrix V V ℝ) (S T : Finset V),
    (∑ x ∈ S, ∑ y ∈ T,
      |correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f A
          (polynomialPrepCutoff4 HP.θ) HP.ρ S T x y -
        correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f B
          (polynomialPrepCutoff4 HP.θ) HP.ρ S T x y| ^ 4) ≤
      (L * (1 + Kc) / f) ^ 4 * ∑ x ∈ S, ∑ y ∈ T, |A x y - B x y| ^ 4 := by
  obtain ⟨Lh, Lρ, hh, hρ, hlh, hlρ⟩ :=
    HierarchyParams.H4RankEnvironment.NormalizedMoments.preparation_stability_constants HP
  obtain ⟨LI, hi, hI⟩ := HP.auxiliary_stability_constants
  obtain ⟨Lt, hLt⟩ := HP.incomingCutoff_root
  let Lτ : ℝ := 4 * Lt
  have ht : 0 ≤ Lτ := by dsimp only [Lτ]; positivity
  have hlτ : ∀ a b, |HP.incomingCutoff a - HP.incomingCutoff b| ≤ Lτ * |a - b| :=
    abs_sub_le_four_mul_root_lipschitz
      (fun z => ⟨HP.incomingCutoff_nonneg z, HP.incomingCutoff_le_one z⟩) hLt
  let L := 16 * (1 + (HP.K : ℝ)) * (1 + Lh + Lρ + Lτ * (2 * LI))
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro V Kc hKc f hf A B S T
  let E := fun x => kthLargest 1 T (fun y => |A x y - B x y|)
  let D := fun x y => auxScore (polynomialAuxCutoff4 HP.θ) HP.K f A T x y -
    auxScore (polynomialAuxCutoff4 HP.θ) HP.K f B T x y
  let Q := fun y => kthLargest 1 S (fun x => |D x y|)
  let Z := fun x y => correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f A
      (polynomialPrepCutoff4 HP.θ) HP.ρ S T x y -
    correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f B
      (polynomialPrepCutoff4 HP.θ) HP.ρ S T x y
  have he (x : V) : 0 ≤ E x := kthLargest_nonneg
  have hq (y : V) : 0 ≤ Q y := kthLargest_nonneg
  have hz (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ T) :
      |Z x y| ≤ ((Lh + Lρ) / f) * E x + Lτ * Q y := by
    have hp := DenseRowRecipe.atomPrep_stability
      (fun z => ⟨polynomialPrepCutoff4_nonneg _ z, polynomialPrepCutoff4_le_one _ z⟩)
      (fun z => ⟨HP.ρ_nonneg z, HP.ρ_le_one z⟩) hlh hlρ hρ
      (NormalizedRow.rank_pos HP) hf A B T x y
    have hg : |incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f A S T y -
        incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f B S T y| ≤
        Lτ * Q y := by
      exact (hlτ _ _).trans (mul_le_mul_of_nonneg_left
        (abs_kthLargest_sub_kthLargest_le hKc (hq y)
          (fun z hz => abs_le_kthLargest_one S (fun z => D z y) z hz)) ht)
    have hb0 : 0 ≤ atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K f B T x y :=
      mul_nonneg (polynomialPrepCutoff4_nonneg _ _) (HP.ρ_nonneg _)
    have hb1 : atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K f B T x y ≤ 1 :=
      (mul_le_of_le_one_right (polynomialPrepCutoff4_nonneg _ _) (HP.ρ_le_one _)).trans
        (polynomialPrepCutoff4_le_one _ _)
    have htri : |Z x y| ≤
        |atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K f A T x y -
          atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K f B T x y| +
        |incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f A S T y -
          incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f B S T y| := by
      dsimp only [Z]
      change |atomPrep _ _ _ _ _ _ _ _ * _ - atomPrep _ _ _ _ _ _ _ _ * _| ≤ _
      have hid (a b c d : ℝ) : a * c - b * d = (a - b) * c + b * (c - d) := by ring
      rw [hid]
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_mul, abs_of_nonneg hb0,
        abs_of_nonneg (show 0 ≤ incomingGate (polynomialAuxCutoff4 HP.θ)
          HP.incomingCutoff HP.K Kc f A S T y from HP.incomingCutoff_nonneg _)]
      exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (HP.incomingCutoff_le_one _))
        (mul_le_of_le_one_left (abs_nonneg _) hb1)
    apply htri.trans ((add_le_add hp hg).trans ?_)
    have hm := abs_le_kthLargest_one T (fun y => A x y - B x y) y hy
    calc
      _ ≤ (Lh * E x + Lρ * E x) / f + Lτ * Q y := by gcongr
      _ = _ := by ring
  have hsum := sparse_axes_fourth_sum S T Z
    (fun x => ((Lh + Lρ) / f) * E x) (fun y => Lτ * Q y) (2 * HP.K) (2 * Kc)
    (fun x => mul_nonneg (div_nonneg (add_nonneg hh hρ) hf.le) (he x))
    (fun y => mul_nonneg ht (hq y))
    (fun x _ => sub_support_card T _ _ (HP.preparation_row_support Kc f A S T x)
      (HP.preparation_row_support Kc f B S T x))
    (fun y _ => sub_support_card S _ _ (HP.preparation_column_support hKc f A S T y)
      (HP.preparation_column_support hKc f B S T y)) hz
  have her : ∑ x ∈ S, E x ^ 4 ≤ ∑ x ∈ S, ∑ y ∈ T, |A x y - B x y| ^ 4 := by
    apply sum_le_sum
    intro x _
    simpa only [abs_of_nonneg (kthLargest_nonneg (k := 1))] using
      abs_kthLargest_pow_le_sum T (fun y => A x y - B x y) (by decide : 4 ≠ 0)
  have hqc : ∑ y ∈ T, Q y ^ 4 ≤
      (2 * HP.K : ℝ) * (2 * LI / f) ^ 4 * ∑ x ∈ S, ∑ y ∈ T, |A x y - B x y| ^ 4 := by
    calc
      _ ≤ ∑ y ∈ T, ∑ x ∈ S, |D x y| ^ 4 := by
        apply sum_le_sum
        intro y _
        simpa only [abs_of_nonneg (kthLargest_nonneg (k := 1))] using
          abs_kthLargest_pow_le_sum S (fun x => D x y) (by decide : 4 ≠ 0)
      _ = ∑ x ∈ S, ∑ y ∈ T, |D x y| ^ 4 := sum_comm
      _ ≤ ∑ x ∈ S, (2 * HP.K : ℝ) * (2 * LI / f) ^ 4 *
          ∑ y ∈ T, |A x y - B x y| ^ 4 :=
        sum_le_sum fun x _ => HP.auxiliary_fourth_sum hi hf hI A B T x
      _ = _ := by rw [mul_sum]
  have hbound : (∑ x ∈ S, ∑ y ∈ T, |Z x y| ^ 4) ≤
      (16 * HP.K * (Lh + Lρ) ^ 4 + 32 * HP.K * Kc * Lτ ^ 4 * (2 * LI) ^ 4) /
        f ^ 4 * ∑ x ∈ S, ∑ y ∈ T, |A x y - B x y| ^ 4 := by
    apply hsum.trans
    simp only [mul_pow, ← mul_sum, Nat.cast_mul, Nat.cast_ofNat]
    have hh' := mul_le_mul_of_nonneg_left her
      (show 0 ≤ (2 * HP.K : ℝ) * ((Lh + Lρ) / f) ^ 4 by positivity)
    have hc' := mul_le_mul_of_nonneg_left hqc
      (show 0 ≤ (2 * Kc : ℝ) * Lτ ^ 4 by positivity)
    have hd := mul_le_mul_of_nonneg_left (add_le_add hh' hc') (by norm_num : (0 : ℝ) ≤ 8)
    convert hd using 1 <;> ring
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [div_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  -- A deliberately coarse fixed-rank coefficient avoids fourth roots of the ranks.
  have hk : 0 ≤ (HP.K : ℝ) := Nat.cast_nonneg _
  have hc : 0 ≤ (Kc : ℝ) := Nat.cast_nonneg _
  have ha : Lh + Lρ ≤ 1 + Lh + Lρ + Lτ * (2 * LI) := by
    linarith [mul_nonneg ht (show 0 ≤ 2 * LI by positivity)]
  have hb : Lτ * (2 * LI) ≤ 1 + Lh + Lρ + Lτ * (2 * LI) := by linarith
  have hpa := pow_le_pow_left₀ (add_nonneg hh hρ) ha 4
  have hpb := pow_le_pow_left₀ (mul_nonneg ht (by positivity)) hb 4
  have hmono := add_le_add (mul_le_mul_of_nonneg_left hpa (by positivity : 0 ≤ 16 * (HP.K : ℝ)))
    (mul_le_mul_of_nonneg_left hpb (by positivity : 0 ≤ 32 * (HP.K : ℝ) * Kc))
  rw [mul_pow] at hmono
  have hrank : 16 * (HP.K : ℝ) + 32 * HP.K * Kc ≤
      (16 * (1 + HP.K) * (1 + (Kc : ℝ))) ^ 4 := by
    let t : ℝ := (1 + HP.K) * (1 + (Kc : ℝ))
    have ht1 : 1 ≤ t := by dsimp only [t]; nlinarith [mul_nonneg hk hc]
    have hsmall : 16 * (HP.K : ℝ) + 32 * HP.K * Kc ≤ 32 * t := by
      dsimp only [t]; nlinarith
    have hp : t ≤ t ^ 4 := by
      simpa only [pow_one] using pow_le_pow_right₀ ht1 (by decide : 1 ≤ 4)
    apply hsmall.trans
    calc
      32 * t ≤ 32 * t ^ 4 := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ ≤ 16 ^ 4 * t ^ 4 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = _ := by dsimp only [t]; ring
  have hd := mul_le_mul_of_nonneg_right hrank
    (pow_nonneg (show 0 ≤ 1 + Lh + Lρ + Lτ * (2 * LI) by positivity) 4)
  calc
    _ = 16 * ↑HP.K * (Lh + Lρ) ^ 4 + 32 * ↑HP.K * ↑Kc * (Lτ ^ 4 * (2 * LI) ^ 4) := by ring
    _ ≤ _ := hmono
    _ ≤ _ := by
      convert hd using 1 <;> (try dsimp only [L]) <;> ring

/-- The finite sparse estimate commutes with the original correlated masks and
environment average. No seed independence or canonical support is required. -/
theorem preparation_row_moment :
    ∃ L : ℝ, 0 ≤ L ∧
    ∀ (Ω V : Type*) [Fintype Ω] [Fintype V]
      (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
      (Kc : ℕ), 0 < Kc → ∀ f : ℝ, 0 < f →
    ∀ (A B : Ω → Matrix V V ℝ) (N u : ℝ), 0 ≤ N * u →
    rowNormPow 4 N u X Y (fun σ x y =>
      correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f (A σ)
          (polynomialPrepCutoff4 HP.θ) HP.ρ {z | X σ z} {w | Y σ w} x y -
        correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f (B σ)
          (polynomialPrepCutoff4 HP.θ) HP.ρ {z | X σ z} {w | Y σ w} x y) ≤
      (L * (1 + Kc) / f) ^ 4 *
        rowNormPow 4 N u X Y (fun σ x y => A σ x y - B σ x y) := by
  obtain ⟨L, hL, h⟩ := HP.preparation_fourth_sum
  refine ⟨L, hL, ?_⟩
  intro Ω V instΩ instV X Y instX instY Kc hKc f hf A B N u hNu
  unfold rowNormPow
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, (L * (1 + Kc) / f) ^ 4 *
        ∑ x ∈ ({z | X σ z} : Finset V), ∑ y ∈ ({w | Y σ w} : Finset V),
          |A σ x y - B σ x y| ^ 4 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNu)
      exact expect_le_expect fun σ _ => h V Kc hKc f hf (A σ) (B σ) _ _
    _ = _ := by rw [← mul_expect]; ring

end Matrix.FourthRootHierarchyParams

namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
variable {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- Literal successful PREP is paid by its actual input child's own RAW accuracy.
The constant is fixed at HP before field, bins, requests or masks. At full terminal
rate it is field-free. The own-usage contract keeps usage equal to terminal; it does
not supply simultaneous recursive availability or the remaining precision salary. -/
theorem evaluate_preparation_paid_bias :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (P : ℕ) [Fact P.Prime] (B : BudgetData HP P)
      (M : ℕ) (pilot : Bool) (i : Fin HP.k)
      (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
    r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i) →
    0 < B.requestPrecision M r → B.childBudget M < M →
    r.usage = r.terminal → 0 ≤ r.source.rate → 0 < r.terminal.rate →
    ∀ (A W : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ),
    let q := { r with task := .row 0 (if pilot then .pilotInput i else .input i) }
    0 < B.requestPrecision (B.childBudget M) q →
    B.evaluate (B.childBudget M) q = some (.row A) →
    B.evaluate M r = some (.row W) →
    rowNormPow 4 P q.source.rate
      (fun σ x => q.source.retains (channels B.padding) σ x)
      (fun σ y => q.usage.retains (channels B.padding) σ y)
      (fun σ x y => A σ x y - B.canonicalPreparationInput pilot i r x y) ≤
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 →
    ∀ (s u : Fin 3) (_hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P)),
    r.source = gridChannel s ks ss → r.usage = gridChannel u ku su →
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    rowNormPow 4 P r.source.rate X U (fun _ x y => rowSliceMean X U W x y -
      rowSliceMean X U (B.incomingPreparation r
        (fun _ => B.canonicalPreparationInput pilot i r)) x y) ≤
      (L / r.terminal.rate) ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 := by
  obtain ⟨L, hL, hreg⟩ := HP.preparation_row_moment
  let Kc := ⌈4 * (1 + 32 * HP.R)⌉₊
  refine ⟨L * (1 + Kc), by positivity, ?_⟩
  intro P instP B M pilot i r hr hp hm hu hs hf A W q _hqp hA hW hih
    s u hsu ks ku ss su hsource husage
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let U := fun σ y => r.usage.retains (channels B.padding) σ y
  let C := fun _ : Environment P 3 => B.canonicalPreparationInput pilot i r
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := mul_nonneg (Nat.cast_nonneg _) hs
  have hmean : (fun (_ : Environment P 3) x y => rowSliceMean X U W x y -
      rowSliceMean X U (B.incomingPreparation r C) x y) =
      (fun _ => rowSliceMean X U (fun σ x y =>
        B.incomingPreparation r A σ x y - B.incomingPreparation r C σ x y)) := by
    funext σ x y
    rw [B.evaluate_preparation_mean M pilot i r hr hp hm A W hA hW
      s u hsu ks ku ss su hsource husage]
    simp only [rowSliceMean, expect_sub_distrib, X, U]
  change rowNormPow 4 P r.source.rate X U _ ≤ _
  rw [hmean]
  apply (rowNormPow_sliceMean_fourth_le hNu X U _).trans
  have hKc : 0 < Kc := Nat.ceil_pos.mpr (by linarith [HP.R_var])
  have h := hreg (Environment P 3) (ZMod P) X U Kc hKc r.terminal.rate hf A C
    P r.source.rate hNu
  have he := h.trans (mul_le_mul_of_nonneg_left hih
    (pow_nonneg (div_nonneg (mul_nonneg hL (by positivity)) hf.le) 4))
  simpa only [incomingPreparation, hu, X, U, C, Kc, q] using he

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
