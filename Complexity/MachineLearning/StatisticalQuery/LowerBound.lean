/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.MachineLearning.StatisticalQuery.Basic
import Complexity.Foundations.Geometry.Euclidean.Angle.Cap
import Complexity.Languages.Probabilistic.QueriesWith
import Complexity.Probability.PMF
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Lower bounds for statistical query learning

A concept class with many almost uncorrelated concepts cannot be learned from few statistical
queries of coarse tolerance [BlumEtAl1994]. Let `f i ∈ C` for `i ∈ κ`
have pairwise correlations `|corr D (f i) (f j)| ≤ γ` under `D`, and let `A` learn `C` under `D`
with tolerance `τ` and error `ε` using at most `q` queries, where `γ < τ ^ 2` and
`γ < (1 - 2 ε) ^ 2`. Then
`|κ| ≤ q (1 - γ) / (τ ^ 2 - γ) + (1 - γ) / ((1 - 2 ε) ^ 2 - γ)`
(`StatisticalQuery.LearnsStateless.card_le_of_abs_corr_le`).

The proof is the argument of [Szörényi][Szorenyi2009], as presented in
[Reyzin, Theorem 12][Reyzin2020]. Write a query as `φ (x, y) = g x + k x · (±1 value of y)`,
where `k` has `|k| ≤ 1`, and answer it by `E_D [g]`, which ignores the target. This answer is
within `τ` of the truth for every `f i` except those with `|E_D [k · f i]| > τ`, and by Bessel's
inequality for the almost orthogonal `f i` there are at most `(1 - γ) / (τ ^ 2 - γ)` of these
(`InnerProductGeometry.card_mul_sq_sub_le_of_le_abs_inner`, applied to the vectors
`√(D x) · f i x` of `ℝ^X`). Run `A` against these target-independent answers. Along the run it
makes at most `q` queries, and every `f i` outside the at most `q (1 - γ) / (τ ^ 2 - γ)`
exceptional ones for those queries sees only valid answers (`OracleComp.interpret_id_congr`).
Hence the single hypothesis `h` that `A` returns has error at most `ε`, that is correlation at
least `1 - 2 ε`, for each such `f i`, and by the same inequality at most
`(1 - γ) / ((1 - 2 ε) ^ 2 - γ)` concepts correlate that well with `h`.

The bound assumes only `LearnsStateless`, so it applies to every learner (`Learns.learnsStateless`)
and to queries with values in `[-1, 1]`, which include the predicates of [Kearns1998].
When only the one-sided bound `corr D (f i) (f j) ≤ γ` holds, the first term doubles
(`StatisticalQuery.LearnsStateless.card_le_of_corr_le`). Take `γ = 1 / d` for `d = |κ|`, so that
the statistical query dimension [Reyzin, Definition 11][Reyzin2020] is at least `d`. Requiring
accuracy `τ`, that is `1 - 2 ε ≥ τ`, as in [Reyzin, Theorem 12][Reyzin2020], gives
`d τ ^ 2 - 1 ≤ 2 q + 1`
(`StatisticalQuery.LearnsStateless.card_mul_sq_sub_one_le_two_mul_add_one`). For exact learning,
the special case `ε = 0`, this sharpens to Reyzin's query count `d τ ^ 2 - 1 ≤ 2 q`
(`StatisticalQuery.LearnsStateless.card_mul_sq_sub_one_le_two_mul`).

## Main results

* `Cslib.MachineLearning.StatisticalQuery.LearnsStateless.card_le_of_abs_corr_le`: the lower bound
  for pairwise almost uncorrelated concepts.
* `Cslib.MachineLearning.StatisticalQuery.LearnsStateless.card_le_of_corr_le`: the lower bound for
  concepts with one-sided correlation bounds.
* `Cslib.MachineLearning.StatisticalQuery.LearnsStateless.card_mul_sq_sub_one_le_two_mul_add_one`:
  the statistical query dimension bound for learning with accuracy `τ`.
* `Cslib.MachineLearning.StatisticalQuery.LearnsStateless.card_mul_sq_sub_one_le_two_mul`: the
  statistical query dimension bound for exact learning.

## References

* [A. Blum, M. Furst, J. Jackson, M. Kearns, Y. Mansour, S. Rudich, *Weakly learning DNF and
  characterizing statistical query learning using Fourier analysis*][BlumEtAl1994]
* [B. Szörényi, *Characterizing statistical query learning: simplified notions and
  proofs*][Szorenyi2009]
* [L. Reyzin, *Statistical queries and statistical algorithms: foundations and
  applications*][Reyzin2020]
* [M. Kearns, *Efficient noise-tolerant learning from statistical queries*][Kearns1998]
-/

public section

namespace Cslib.MachineLearning.StatisticalQuery

open Finset
open scoped RealInnerProductSpace

variable {X : Type} [Fintype X]

/-! ### Functions as vectors -/

/-- The function `u` as the vector `(√(D x) · u x)_x`, whose inner products are expectations
under `D`. -/
private noncomputable def emb (D : PMF X) (u : X → ℝ) : EuclideanSpace ℝ X :=
  WithLp.toLp 2 fun x => Real.sqrt (D x).toReal * u x

private theorem inner_emb (D : PMF X) (u v : X → ℝ) :
    ⟪emb D u, emb D v⟫ = ∑ x, (D x).toReal * (u x * v x) := by
  simp only [emb, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  refine sum_congr rfl fun x _ => ?_
  have h := Real.mul_self_sqrt (ENNReal.toReal_nonneg (a := D x))
  calc Real.sqrt (D x).toReal * v x * (Real.sqrt (D x).toReal * u x)
      = (Real.sqrt (D x).toReal * Real.sqrt (D x).toReal) * (u x * v x) := by ring
    _ = _ := by rw [h]

private theorem norm_emb_le (D : PMF X) (u : X → ℝ) (hu : ∀ x, |u x| ≤ 1) : ‖emb D u‖ ≤ 1 := by
  have hsq : ‖emb D u‖ ^ 2 ≤ 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_emb]
    calc ∑ x, (D x).toReal * (u x * u x) ≤ ∑ x, (D x).toReal * 1 :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
            (by nlinarith [abs_le.1 (hu x), abs_nonneg (u x), sq_abs (u x)]) ENNReal.toReal_nonneg
      _ = 1 := by simp only [mul_one, Cslib.Probability.PMF.sum_toReal]
  nlinarith [norm_nonneg (emb D u)]

private theorem norm_emb_signVal_le (D : PMF X) (f : X → Bool) :
    ‖emb D fun x => BitString.signVal (f x)‖ ≤ 1 :=
  norm_emb_le D _ fun x => (BitString.abs_signVal (f x)).le

private theorem inner_emb_corr (D : PMF X) (f g : X → Bool) :
    ⟪emb D (fun x => BitString.signVal (f x)), emb D (fun x => BitString.signVal (g x))⟫ =
      corr D f g := by
  rw [inner_emb]
  rfl

/-! ### Splitting a query -/

/-- The part `(φ (x, false) + φ (x, true)) / 2` of a query that ignores the label, averaged over
`D`. -/
private noncomputable def nullAnswer (D : PMF X) (φ : Query X) : ℝ :=
  ∑ x, (D x).toReal * ((φ x false + φ x true) / 2)

/-- The label-dependent half difference of a query. -/
private noncomputable def slope (φ : Query X) (x : X) : ℝ :=
  (φ x false - φ x true) / 2

/-- The correlation of the label-dependent part of a query with the target. -/
private noncomputable def bias (D : PMF X) (φ : Query X) (f : X → Bool) : ℝ :=
  ∑ x, (D x).toReal * (slope φ x * BitString.signVal (f x))

omit [Fintype X] in
private theorem abs_slope_le (φ : Query X) (x : X) : |slope φ x| ≤ 1 := by
  rw [slope, abs_div, abs_two, div_le_one two_pos]
  calc |φ x false - φ x true| ≤ |φ x false| + |φ x true| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (φ.abs_le_one x false) (φ.abs_le_one x true)
    _ = 2 := one_add_one_eq_two

private theorem expect_eq_nullAnswer_add_bias (D : PMF X) (f : X → Bool) (φ : Query X) :
    expect D f φ = nullAnswer D φ + bias D φ f := by
  simp only [expect, nullAnswer, bias, slope, ← sum_add_distrib, ← mul_add]
  refine sum_congr rfl fun x _ => ?_
  cases f x <;> simp only [BitString.signVal_false, BitString.signVal_true] <;> ring

private theorem inner_emb_bias (D : PMF X) (φ : Query X) (f : X → Bool) :
    ⟪emb D (fun x => BitString.signVal (f x)), emb D (slope φ)⟫ = bias D φ f := by
  rw [inner_emb]
  refine sum_congr rfl fun x _ => ?_
  ring

/-! ### The adversary argument -/

open Classical in
/-- The counting core: if each query has at most `b` concepts with bias above `τ`, and each
hypothesis correlates at least `1 - 2 ε` with at most `g` concepts, then there are at most
`q b + g` concepts. -/
private theorem card_le_of_bad_good {κ : Type} [Fintype κ] {D : PMF X}
    {C : PACLearning.ConceptClass X Bool} {f : κ → X → Bool} (hf : ∀ i, f i ∈ C)
    {A : Algorithm X} {q : ℕ} (hq : A.IsQueryBounded q) {τ ε : ℝ} (hτ : 0 ≤ τ)
    (hA : LearnsStateless A D C τ ε) {b g : ℝ}
    (hbad : ∀ φ : Query X, (#({i | τ < |bias D φ (f i)|} : Finset κ) : ℝ) ≤ b)
    (hgood : ∀ h : X → Bool, (#({i | 1 - 2 * ε ≤ corr D (f i) h} : Finset κ) : ℝ) ≤ g)
    (hb : 0 ≤ b) :
    (Fintype.card κ : ℝ) ≤ q * b + g := by
  set h₀ := run A (nullAnswer D) with hh₀
  set L := (OracleComp.queriesWith (nullAnswer D) A).toFinset with hL
  set B := L.biUnion fun φ => ({i | τ < |bias D φ (f i)|} : Finset κ) with hB
  set G := ({i | 1 - 2 * ε ≤ corr D (f i) h₀} : Finset κ) with hG
  -- Every concept outside `B` sees only valid answers, so `h₀` is a good hypothesis for it.
  have hcover : (univ : Finset κ) ⊆ B ∪ G := by
    intro i _
    by_cases hiB : i ∈ B
    · exact mem_union_left _ hiB
    refine mem_union_right _ (mem_filter.2 ⟨mem_univ _, ?_⟩)
    set answer : Query X → ℝ := fun φ =>
      if φ ∈ L then nullAnswer D φ else expect D (f i) φ with hanswer
    have hvalid : ∀ φ, |answer φ - expect D (f i) φ| ≤ τ := by
      intro φ
      by_cases hφ : φ ∈ L
      · have hnb : ¬ τ < |bias D φ (f i)| := fun hlt =>
          hiB (mem_biUnion.2 ⟨φ, hφ, mem_filter.2 ⟨mem_univ _, hlt⟩⟩)
        rw [hanswer]
        simp only [hφ, ite_true]
        rw [expect_eq_nullAnswer_add_bias, sub_add_cancel_left, abs_neg]
        exact not_lt.1 hnb
      · rw [hanswer]
        simp only [hφ, ite_false, sub_self, abs_zero]
        exact hτ
    have hrun : run A answer = h₀ :=
      (OracleComp.interpret_id_congr (nullAnswer D) answer A fun φ hφ => by
        rw [hanswer]
        simp only [List.mem_toFinset.2 hφ, ite_true, hL]).1
    have hdis := hA (f i) (hf i) answer hvalid
    rw [hrun] at hdis
    rw [corr_eq_one_sub_two_mul_disagreement]
    linarith
  have hBcard : (#B : ℝ) ≤ q * b := by
    calc (#B : ℝ) ≤ ∑ φ ∈ L, (#({i | τ < |bias D φ (f i)|} : Finset κ) : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ _φ ∈ L, b := sum_le_sum fun φ _ => hbad φ
      _ = #L * b := by rw [sum_const, nsmul_eq_mul]
      _ ≤ q * b := by
          refine mul_le_mul_of_nonneg_right ?_ hb
          have h1 := List.toFinset_card_le (OracleComp.queriesWith (nullAnswer D) A)
          have h2 := hq.length_queriesWith_le (nullAnswer D)
          exact_mod_cast h1.trans h2
  calc (Fintype.card κ : ℝ) = #(univ : Finset κ) := by rw [card_univ]
    _ ≤ #(B ∪ G) := by exact_mod_cast card_le_card hcover
    _ ≤ #B + #G := by exact_mod_cast card_union_le B G
    _ ≤ q * b + g := add_le_add hBcard (hgood h₀)

open Classical in
private theorem card_bad_le_of_abs {κ : Type} [Fintype κ] (D : PMF X) (f : κ → X → Bool)
    {τ γ : ℝ} (hτ : 0 ≤ τ) (hγ1 : γ ≤ 1) (hγτ : γ < τ ^ 2)
    (hcorr : ∀ i j, i ≠ j → |corr D (f i) (f j)| ≤ γ) (φ : Query X) :
    (#({i | τ < |bias D φ (f i)|} : Finset κ) : ℝ) ≤ (1 - γ) / (τ ^ 2 - γ) := by
  rw [le_div_iff₀ (sub_pos.2 hγτ)]
  refine InnerProductGeometry.card_mul_sq_sub_le_of_le_abs_inner (x := emb D (slope φ))
    (y := fun i => emb D fun x => BitString.signVal (f i x))
    (norm_emb_le D _ (abs_slope_le φ)) (fun i _ => norm_emb_signVal_le D (f i)) hτ hγ1
    (fun i hi => ?_) (fun i _ j _ hij => ?_)
  · rw [inner_emb_bias]
    exact (mem_filter.1 hi).2.le
  · rw [inner_emb_corr]
    exact hcorr i j hij

open Classical in
private theorem card_bad_le {κ : Type} [Fintype κ] (D : PMF X) (f : κ → X → Bool) {τ γ : ℝ}
    (hτ : 0 ≤ τ) (hγ1 : γ ≤ 1) (hγτ : γ < τ ^ 2)
    (hcorr : ∀ i j, i ≠ j → corr D (f i) (f j) ≤ γ) (φ : Query X) :
    (#({i | τ < |bias D φ (f i)|} : Finset κ) : ℝ) ≤ 2 * ((1 - γ) / (τ ^ 2 - γ)) := by
  have hpos : 0 < τ ^ 2 - γ := sub_pos.2 hγτ
  have hsplit : ({i | τ < |bias D φ (f i)|} : Finset κ) ⊆
      ({i | τ ≤ bias D φ (f i)} : Finset κ) ∪ ({i | τ ≤ -bias D φ (f i)} : Finset κ) := by
    intro i hi
    rcases lt_abs.1 (mem_filter.1 hi).2 with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, h.le⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, h.le⟩)
  have hyy : ∀ i ∈ (univ : Finset κ), ∀ j ∈ (univ : Finset κ), i ≠ j →
      ⟪emb D (fun x => BitString.signVal (f i x)),
        emb D (fun x => BitString.signVal (f j x))⟫ ≤ γ :=
    fun i _ j _ hij => by
      rw [inner_emb_corr]
      exact hcorr i j hij
  have hplus : (#({i | τ ≤ bias D φ (f i)} : Finset κ) : ℝ) * (τ ^ 2 - γ) ≤ 1 - γ :=
    InnerProductGeometry.card_mul_sq_sub_le_of_le_inner (x := emb D (slope φ))
      (y := fun i => emb D fun x => BitString.signVal (f i x))
      (norm_emb_le D _ (abs_slope_le φ)) (fun i _ => norm_emb_signVal_le D (f i)) hτ hγ1
      (fun i hi => by
        rw [inner_emb_bias]
        exact (mem_filter.1 hi).2)
      (fun i _ j _ hij => hyy i (mem_univ i) j (mem_univ j) hij)
  have hminus : (#({i | τ ≤ -bias D φ (f i)} : Finset κ) : ℝ) * (τ ^ 2 - γ) ≤ 1 - γ :=
    InnerProductGeometry.card_mul_sq_sub_le_of_le_inner (x := emb D fun x => -slope φ x)
      (y := fun i => emb D fun x => BitString.signVal (f i x))
      (norm_emb_le D _ fun x => by
        rw [abs_neg]
        exact abs_slope_le φ x)
      (fun i _ => norm_emb_signVal_le D (f i)) hτ hγ1
      (fun i hi => by
        have h := (mem_filter.1 hi).2
        rw [← inner_emb_bias, ← inner_neg_right] at h
        convert h using 2
        ext x
        simp only [emb, PiLp.neg_apply, mul_neg])
      (fun i _ j _ hij => hyy i (mem_univ i) j (mem_univ j) hij)
  have hu : (#({i | τ < |bias D φ (f i)|} : Finset κ) : ℝ) ≤
      #({i | τ ≤ bias D φ (f i)} : Finset κ) + #({i | τ ≤ -bias D φ (f i)} : Finset κ) := by
    exact_mod_cast (card_le_card hsplit).trans (card_union_le _ _)
  rw [two_mul]
  exact hu.trans (add_le_add ((le_div_iff₀ hpos).2 hplus) ((le_div_iff₀ hpos).2 hminus))

open Classical in
private theorem card_good_le {κ : Type} [Fintype κ] (D : PMF X) (f : κ → X → Bool) {ε γ : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (hγε : γ < (1 - 2 * ε) ^ 2)
    (hcorr : ∀ i j, i ≠ j → corr D (f i) (f j) ≤ γ) (h : X → Bool) :
    (#({i | 1 - 2 * ε ≤ corr D (f i) h} : Finset κ) : ℝ) ≤ (1 - γ) / ((1 - 2 * ε) ^ 2 - γ) := by
  have hβ0 : 0 ≤ 1 - 2 * ε := by linarith
  have hγ1 : γ ≤ 1 := hγε.le.trans (pow_le_one₀ hβ0 (by linarith))
  rw [le_div_iff₀ (sub_pos.2 hγε)]
  refine InnerProductGeometry.card_mul_sq_sub_le_of_le_inner
    (x := emb D fun x => BitString.signVal (h x))
    (y := fun i => emb D fun x => BitString.signVal (f i x))
    (norm_emb_signVal_le D h) (fun i _ => norm_emb_signVal_le D (f i)) hβ0 hγ1
    (fun i hi => ?_) (fun i _ j _ hij => ?_)
  · rw [inner_emb_corr]
    exact (mem_filter.1 hi).2
  · rw [inner_emb_corr]
    exact hcorr i j hij

/-! ### The lower bounds -/

/-- **Statistical query lower bound** [BlumEtAl1994]
[Szorenyi2009]. If the concepts `f i ∈ C`, `i ∈ κ`, have pairwise correlations of absolute value
at most `γ` under `D`, and `A` learns `C` under `D` with tolerance `τ ≥ 0` and error
`ε ∈ [0, 1/2]` using at most `q` queries, where `γ < τ ^ 2` and `γ < (1 - 2 ε) ^ 2`, then
`|κ| ≤ q (1 - γ) / (τ ^ 2 - γ) + (1 - γ) / ((1 - 2 ε) ^ 2 - γ)`. -/
theorem LearnsStateless.card_le_of_abs_corr_le {κ : Type} [Fintype κ] {D : PMF X}
    {C : PACLearning.ConceptClass X Bool} {A : Algorithm X} {τ ε : ℝ}
    (hA : LearnsStateless A D C τ ε) {q : ℕ} (hq : A.IsQueryBounded q)
    {f : κ → X → Bool} (hf : ∀ i, f i ∈ C) {γ : ℝ}
    (hcorr : ∀ i j, i ≠ j → |corr D (f i) (f j)| ≤ γ)
    (hτ : 0 ≤ τ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (hγτ : γ < τ ^ 2)
    (hγε : γ < (1 - 2 * ε) ^ 2) :
    (Fintype.card κ : ℝ) ≤ q * ((1 - γ) / (τ ^ 2 - γ)) + (1 - γ) / ((1 - 2 * ε) ^ 2 - γ) := by
  have hcorr' : ∀ i j, i ≠ j → corr D (f i) (f j) ≤ γ := fun i j hij =>
    (le_abs_self _).trans (hcorr i j hij)
  have hγ1 : γ ≤ 1 := hγε.le.trans (pow_le_one₀ (by linarith) (by linarith))
  exact card_le_of_bad_good hf hq hτ hA (card_bad_le_of_abs D f hτ hγ1 hγτ hcorr)
    (card_good_le D f hε0 hε hγε hcorr') (div_nonneg (by linarith) (sub_pos.2 hγτ).le)

/-- **Statistical query lower bound, one-sided correlations.** If the concepts `f i ∈ C`,
`i ∈ κ`, have pairwise correlations at most `γ` under `D`, and `A` learns `C` under `D` with
tolerance `τ ≥ 0` and error `ε ∈ [0, 1/2]` using at most `q` queries, where `γ < τ ^ 2` and
`γ < (1 - 2 ε) ^ 2`, then `|κ| ≤ 2 q (1 - γ) / (τ ^ 2 - γ) + (1 - γ) / ((1 - 2 ε) ^ 2 - γ)`. -/
theorem LearnsStateless.card_le_of_corr_le {κ : Type} [Fintype κ] {D : PMF X}
    {C : PACLearning.ConceptClass X Bool} {A : Algorithm X} {τ ε : ℝ}
    (hA : LearnsStateless A D C τ ε) {q : ℕ} (hq : A.IsQueryBounded q)
    {f : κ → X → Bool} (hf : ∀ i, f i ∈ C) {γ : ℝ}
    (hcorr : ∀ i j, i ≠ j → corr D (f i) (f j) ≤ γ)
    (hτ : 0 ≤ τ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (hγτ : γ < τ ^ 2)
    (hγε : γ < (1 - 2 * ε) ^ 2) :
    (Fintype.card κ : ℝ) ≤
      2 * q * ((1 - γ) / (τ ^ 2 - γ)) + (1 - γ) / ((1 - 2 * ε) ^ 2 - γ) := by
  have hγ1 : γ ≤ 1 := hγε.le.trans (pow_le_one₀ (by linarith) (by linarith))
  have h := card_le_of_bad_good hf hq hτ hA (card_bad_le D f hτ hγ1 hγτ hcorr)
    (card_good_le D f hε0 hε hγε hcorr)
    (mul_nonneg zero_le_two (div_nonneg (by linarith) (sub_pos.2 hγτ).le))
  calc (Fintype.card κ : ℝ) ≤ _ := h
    _ = _ := by ring

/-- **The statistical query dimension bound for exact learning**: the special case `ε = 0` of
[Reyzin, Theorem 12][Reyzin2020], which assumes only accuracy `τ`
(`LearnsStateless.card_mul_sq_sub_one_le_two_mul_add_one`). If `C` contains
`d ≥ 2` concepts with pairwise correlations at most `1 / d` under `D`, so that the statistical
query dimension of `C` under `D` is at least `d` [Reyzin, Definition 11][Reyzin2020], then a
learner learning `C` exactly under `D` from at most `q` queries of tolerance `τ ≥ 0` has
`d τ ^ 2 - 1 ≤ 2 q`, Reyzin's query count. -/
theorem LearnsStateless.card_mul_sq_sub_one_le_two_mul {κ : Type} [Fintype κ] {D : PMF X}
    {C : PACLearning.ConceptClass X Bool} {A : Algorithm X} {τ : ℝ}
    (hA : LearnsStateless A D C τ 0) {q : ℕ} (hq : A.IsQueryBounded q)
    {f : κ → X → Bool} (hf : ∀ i, f i ∈ C)
    (hcorr : ∀ i j, i ≠ j → corr D (f i) (f j) ≤ 1 / Fintype.card κ)
    (hκ : 2 ≤ Fintype.card κ) (hτ : 0 ≤ τ) :
    Fintype.card κ * τ ^ 2 - 1 ≤ 2 * q := by
  have hd2 : (2 : ℝ) ≤ Fintype.card κ := by exact_mod_cast hκ
  set d : ℝ := (Fintype.card κ : ℝ) with hd
  have hdpos : 0 < d := by linarith
  rcases le_or_gt (d * τ ^ 2) 1 with h1 | h1
  · have : (0 : ℝ) ≤ 2 * q := by positivity
    linarith
  have hγτ : 1 / d < τ ^ 2 := by
    rw [div_lt_iff₀ hdpos]
    linarith
  have hγ1 : 1 / d < 1 := by
    rw [div_lt_one hdpos]
    linarith
  have hγε : 1 / d < (1 - 2 * 0) ^ 2 := by
    rw [mul_zero, sub_zero, one_pow]
    exact hγ1
  have h := hA.card_le_of_corr_le hq hf hcorr hτ le_rfl (by norm_num) hγτ hγε
  rw [mul_zero, sub_zero, one_pow, div_self (sub_pos.2 hγ1).ne'] at h
  have hxmul : (1 - 1 / d) / (τ ^ 2 - 1 / d) * (τ ^ 2 - 1 / d) = 1 - 1 / d :=
    div_mul_cancel₀ _ (sub_pos.2 hγτ).ne'
  have h4 : (d - 1) * (τ ^ 2 - 1 / d) ≤ 2 * q * (1 - 1 / d) := by
    have := mul_le_mul_of_nonneg_right
      (show d - 1 ≤ 2 * q * ((1 - 1 / d) / (τ ^ 2 - 1 / d)) by linarith) (sub_pos.2 hγτ).le
    rw [mul_assoc (2 * (q : ℝ)), hxmul] at this
    exact this
  have h5 : (d - 1) * (d * τ ^ 2 - 1) ≤ (d - 1) * (2 * q) := by
    have e : (d - 1) * (τ ^ 2 - 1 / d) * d = (d - 1) * (d * τ ^ 2 - 1) := by
      field_simp
    have e' : 2 * q * (1 - 1 / d) * d = (d - 1) * (2 * q) := by
      field_simp
    rw [← e, ← e']
    exact mul_le_mul_of_nonneg_right h4 hdpos.le
  exact le_of_mul_le_mul_left h5 (by linarith)

/-- **The statistical query dimension bound for weak learning** [Reyzin, Theorem 12][Reyzin2020].
If `C` contains `d` concepts with pairwise correlations at most `1 / d` under `D`, and `A` learns
`C` under `D` from at most `q` queries of tolerance `τ ≥ 0` with accuracy `τ`, that is with error
`ε ≥ 0` where `1 - 2 ε ≥ τ`, so that every hypothesis has correlation at least `τ` with the
target, then `d τ ^ 2 - 1 ≤ 2 q + 1`. -/
theorem LearnsStateless.card_mul_sq_sub_one_le_two_mul_add_one {κ : Type} [Fintype κ]
    {D : PMF X} {C : PACLearning.ConceptClass X Bool} {A : Algorithm X} {τ ε : ℝ}
    (hA : LearnsStateless A D C τ ε) {q : ℕ} (hq : A.IsQueryBounded q)
    {f : κ → X → Bool} (hf : ∀ i, f i ∈ C)
    (hcorr : ∀ i j, i ≠ j → corr D (f i) (f j) ≤ 1 / Fintype.card κ)
    (hτ : 0 ≤ τ) (hε0 : 0 ≤ ε) (hετ : τ ≤ 1 - 2 * ε) :
    Fintype.card κ * τ ^ 2 - 1 ≤ 2 * q + 1 := by
  rcases le_or_gt ((Fintype.card κ : ℝ) * τ ^ 2) 1 with h1 | h1
  · have : (0 : ℝ) ≤ 2 * q + 1 := by positivity
    linarith
  have hd1 : (1 : ℝ) ≤ Fintype.card κ := by
    have hne : Fintype.card κ ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero, zero_mul] at h1
      linarith
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
  set d : ℝ := (Fintype.card κ : ℝ) with hd
  have hdpos : 0 < d := by linarith
  have hγτ : 1 / d < τ ^ 2 := by
    rw [div_lt_iff₀ hdpos]
    linarith
  have hττ : τ ^ 2 ≤ (1 - 2 * ε) ^ 2 := pow_le_pow_left₀ hτ hετ 2
  have hγε : 1 / d < (1 - 2 * ε) ^ 2 := hγτ.trans_le hττ
  have h := hA.card_le_of_corr_le hq hf hcorr hτ hε0 (by linarith) hγτ hγε
  have hnum : 0 ≤ 1 - 1 / d := by
    rw [sub_nonneg, div_le_one hdpos]
    exact hd1
  have hpos : 0 < τ ^ 2 - 1 / d := sub_pos.2 hγτ
  have h2 : (1 - 1 / d) / ((1 - 2 * ε) ^ 2 - 1 / d) ≤ (1 - 1 / d) / (τ ^ 2 - 1 / d) :=
    div_le_div_of_nonneg_left hnum hpos (by linarith)
  have h' : d ≤ (2 * q + 1) * ((1 - 1 / d) / (τ ^ 2 - 1 / d)) := by
    calc d ≤ _ := h
      _ ≤ 2 * q * ((1 - 1 / d) / (τ ^ 2 - 1 / d)) + (1 - 1 / d) / (τ ^ 2 - 1 / d) := by
        linarith
      _ = _ := by ring
  have h3 : d * (τ ^ 2 - 1 / d) ≤ (2 * q + 1) * (1 - 1 / d) := by
    calc d * (τ ^ 2 - 1 / d)
        ≤ (2 * q + 1) * ((1 - 1 / d) / (τ ^ 2 - 1 / d)) * (τ ^ 2 - 1 / d) :=
          mul_le_mul_of_nonneg_right h' hpos.le
      _ = _ := by rw [mul_assoc, div_mul_cancel₀ _ hpos.ne']
  have h4 : d * (τ ^ 2 - 1 / d) = d * τ ^ 2 - 1 := by
    field_simp
  have h5 : (2 * q + 1) * (1 - 1 / d) ≤ 2 * q + 1 := by
    have : 0 ≤ (2 * q + 1 : ℝ) * (1 / d) := by positivity
    nlinarith
  linarith

end Cslib.MachineLearning.StatisticalQuery
