/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.Monotone
public import Complexity.Foundations.LinearAlgebra.Matrix.Gram
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Spanning backbones for rounding

The linear-algebra and mass-counting steps of [XuGaoHu2027], Theorem 3.3,
PDF pp. 6–7. A spanning set of fully retained observations gives an actual
positive definite Gram matrix. General position is stated using independence
of every set of `d` design rows, not as an assumed rounding conclusion.
-/

public section

namespace Cslib.LeastSquares

open Matrix Submodule

variable {ι d : Type*} [Fintype d]

/-- General position: every `d` observations are linearly independent as design rows.
For simple regression with an intercept, this means distinct regressor values. -/
@[expose] def GeneralPosition (x : ι → d → ℝ) : Prop :=
  ∀ s : Finset ι, s.card = Fintype.card d → LinearIndependent ℝ (fun i : s => x i)

/-- General position makes every set of at least `d` fully retained observations a
positive definite backbone. No nonsingularity premise is supplied separately. -/
theorem GeneralPosition.gram_posDef (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (s : Finset ι) (hs : Fintype.card d ≤ s.card) :
    (∑ i ∈ s, vecMulVec (x i) (x i)).PosDef := by
  classical
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hs
  have hspan : span ℝ (Set.range fun i : t => x i) = ⊤ :=
    (hgp t ht).span_eq_top_of_card_eq_finrank' (by simpa using ht)
  apply posDef_sum_vecMulVec_of_span_eq_top
  apply top_unique
  rw [← hspan]
  apply span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨i, hts i.property, rfl⟩

open Classical in
/-- With at most `d` fractional coordinates and retained mass at least `2d`,
at least `d` observations have weight exactly one. This is a consequence of the
mass bounds, not an additional backbone hypothesis. -/
theorem card_fully_retained_ge (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, w i ∈ Set.Icc (0 : ℝ) 1)
    (hsparse : (s.filter fun i => 0 < w i ∧ w i < 1).card ≤ Fintype.card d)
    (hmass : 2 * (Fintype.card d : ℝ) ≤ ∑ i ∈ s, w i) :
    Fintype.card d ≤ (s.filter fun i => w i = 1).card := by
  classical
  have hle : (∑ i ∈ s, w i) ≤
      ((s.filter fun i => w i = 1).card : ℝ) +
        (s.filter fun i => 0 < w i ∧ w i < 1).card := by
    have hc (t : Finset ι) : (t.card : ℝ) = ∑ _i ∈ t, (1 : ℝ) := by simp
    rw [hc, hc]
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    by_cases h1 : w i = 1
    · simp [h1]
    · by_cases h0 : w i = 0
      · simp [h0]
      · have hf : 0 < w i ∧ w i < 1 :=
          ⟨lt_of_le_of_ne (hw i hi).1 (Ne.symm h0), lt_of_le_of_ne (hw i hi).2 h1⟩
        simp only [h1, hf, ite_false, zero_add]
        exact (hw i hi).2
  have hsparse' : ((s.filter fun i => 0 < w i ∧ w i < 1).card : ℝ) ≤ Fintype.card d :=
    Nat.cast_le.mpr hsparse
  apply (Nat.cast_le (α := ℝ)).mp
  linarith

open Classical in
/-- Sparse feasible weights in general position have the positive definite fixed
backbone needed for monotone rounding. Sparsification itself is not assumed to
have been established by this lemma. -/
theorem GeneralPosition.sparse_backbone (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, w i ∈ Set.Icc (0 : ℝ) 1)
    (hsparse : (s.filter fun i => 0 < w i ∧ w i < 1).card ≤ Fintype.card d)
    (hmass : 2 * (Fintype.card d : ℝ) ≤ ∑ i ∈ s, w i) :
    (∑ i ∈ s.filter (fun i => w i = 1), vecMulVec (x i) (x i)).PosDef := by
  exact hgp.gram_posDef x _ (card_fully_retained_ge s w hw hsparse hmass)

open Classical in
private theorem sum_fractional_split {E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Finset ι) (w u : ι → ℝ) (a : ι → E)
    (hw : ∀ i ∈ s, w i ∈ Set.Icc (0 : ℝ) 1)
    (hout : ∀ i ∈ s, ¬ (0 < w i ∧ w i < 1) → u i = w i) :
    (∑ i ∈ s, u i • a i) = (∑ i ∈ s.filter (fun i => w i = 1), a i) +
      ∑ i ∈ s.filter (fun i => 0 < w i ∧ w i < 1), u i • a i := by
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h1 : w i = 1
  · have hn : ¬ (0 < w i ∧ w i < 1) := by simp [h1]
    rw [hout i hi hn]
    simp [h1]
  · by_cases h0 : w i = 0
    · have hn : ¬ (0 < w i ∧ w i < 1) := by simp [h0]
      rw [hout i hi hn]
      simp [h0]
    · have hf : 0 < w i ∧ w i < 1 :=
        ⟨lt_of_le_of_ne (hw i hi).1 (Ne.symm h0), lt_of_le_of_ne (hw i hi).2 h1⟩
      simp [h1, hf]

open Classical in
private theorem weightedEstimate_fractional [DecidableEq d]
    (s : Finset ι) (x : ι → d → ℝ) (y w u : ι → ℝ)
    (hw : ∀ i ∈ s, w i ∈ Set.Icc (0 : ℝ) 1)
    (hout : ∀ i ∈ s, ¬ (0 < w i ∧ w i < 1) → u i = w i) :
    weightedEstimate 0 0 s x y u =
      weightedEstimate (∑ i ∈ s.filter (fun i => w i = 1), vecMulVec (x i) (x i))
        (∑ i ∈ s.filter (fun i => w i = 1), y i • x i)
        (s.filter fun i => 0 < w i ∧ w i < 1) x y u := by
  unfold weightedEstimate weightedGram weightedResponse
  simp only [zero_add, mul_smul]
  rw [sum_fractional_split s w u (fun i => vecMulVec (x i) (x i)) hw hout,
    sum_fractional_split s w u (fun i => y i • x i) hw hout]

open Classical in
/-- Round a sparse feasible design in general position, deriving its fixed backbone
from retained mass. The output is integral on the entire original index set and
loses strictly less than `d` retained mass. This assembles the rounding part of
Theorem 3.3 **after** Lemma 3.2; no sparsification or attainment claim is made. -/
theorem exists_round_sparse [DecidableEq d] (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (s : Finset ι) (y w : ι → ℝ) (e : d → ℝ) (hd : 0 < Fintype.card d)
    (hw : ∀ i ∈ s, w i ∈ Set.Icc (0 : ℝ) 1)
    (hsparse : (s.filter fun i => 0 < w i ∧ w i < 1).card ≤ Fintype.card d)
    (hmass : 2 * (Fintype.card d : ℝ) ≤ ∑ i ∈ s, w i) :
    ∃ u : ι → ℝ, (∀ i ∈ s, u i = 0 ∨ u i = 1) ∧
      (∀ i, i ∉ s → u i = w i) ∧
      e ⬝ᵥ weightedEstimate 0 0 s x y u ≤ e ⬝ᵥ weightedEstimate 0 0 s x y w ∧
      (∑ i ∈ s, w i) - (∑ i ∈ s, u i) < Fintype.card d ∧
      (weightedGram 0 s x u).PosDef := by
  classical
  let J := s.filter fun i => 0 < w i ∧ w i < 1
  obtain ⟨u, hu, hout, htarget, hloss⟩ := exists_round_weights_loss_lt
    (hgp.sparse_backbone x s w hw hsparse hmass)
    (∑ i ∈ s.filter (fun i => w i = 1), y i • x i) e J x y w hd hsparse
    (fun i hi => (Finset.mem_filter.mp hi).2)
  have hsame : ∀ i ∈ s, ¬ (0 < w i ∧ w i < 1) → u i = w i := by
    intro i hi hn
    exact hout i (by simp [J, hn])
  refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hf : 0 < w i ∧ w i < 1
    · exact hu i (Finset.mem_filter.mpr ⟨hi, hf⟩)
    · rw [hsame i hi hf]
      rcases eq_or_lt_of_le (hw i hi).1 with h0 | h0
      · exact Or.inl h0.symm
      · exact Or.inr (by by_contra h1; exact hf ⟨h0, lt_of_le_of_ne (hw i hi).2 h1⟩)
  · intro i hi
    exact hout i (fun h => hi (Finset.mem_filter.mp h).1)
  · rw [weightedEstimate_fractional s x y w u hw hsame,
      weightedEstimate_fractional s x y w w hw (fun _ _ _ => rfl)]
    exact htarget
  · have heq : (∑ i ∈ s, w i) - (∑ i ∈ s, u i) =
        (∑ i ∈ J, w i) - (∑ i ∈ J, u i) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Eq.symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hni
      rw [hout i hni, sub_self]
    rw [heq]
    exact hloss
  · unfold weightedGram
    rw [zero_add, sum_fractional_split s w u (fun i => vecMulVec (x i) (x i)) hw hsame]
    exact weightedGram_posDef (hgp.sparse_backbone x s w hw hsparse hmass) J x u
      (fun i hi => by rcases hu i hi with h | h <;> simp [h])

end Cslib.LeastSquares
