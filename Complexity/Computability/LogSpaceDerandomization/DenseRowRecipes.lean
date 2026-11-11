/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.LogSpaceDerandomization.CorrectionRowTasks
public import Complexity.Computability.LogSpaceDerandomization.HierarchyAtomCutoff
import Mathlib.Tactic.Linarith

/-!
# Bounded dense row recipes

Shared arbitrary-child recipes for global hierarchy access and signed residual clients.
The routed cutoff is [OpenAI2026LogSpace, Section 5.2, (5.9)], revision `7ef5c0cc`.
Top clipping includes routing; raw ranks are evaluated before scalar clipping.

## Main definitions

* `routedBinCutoff`: routing in atom units.
* `boundedRoutedBinCutoff`: clipped top bin and zero-extended fine bins.
* `CorrectionRowRecipe.residual`: signed raw residual on four completed children.
* `DenseRowRecipe.normalized`: raw row gate and clipped preparatory normalizer.
* `DenseBinRecipe`: scalar parameters shared by global bin constructors.
-/

public section

open Finset
open scoped BigOperators

namespace Matrix

/-- The bin in atom units, with destination routing included before the row normalization.
For an unrouted bin use the routing function constantly equal to one. -/
@[expose] noncomputable def routedBinCutoff (χ : ℝ → ℝ) (b : ℕ → ℝ) (i : ℕ)
    (route : ℝ → ℝ) (d : ℝ) : ℝ :=
  d * Cslib.binWeight χ b i (b i * d) * route (b i * d)

/-- Converting an atom-unit routed cutoff back to matrix units preserves the raw argument. -/
theorem mul_routedBinCutoff {χ route : ℝ → ℝ} {b : ℕ → ℝ} {i : ℕ}
    (hb : b i ≠ 0) (w : ℝ) :
    b i * routedBinCutoff χ b i route (w / b i) =
      w * Cslib.binWeight χ b i w * route w := by
  simp only [routedBinCutoff, mul_div_cancel₀ _ hb]
  field_simp

/-- Finite coverage of the true entry suffices; a zero entry needs no positive lower cutoff. -/
theorem sum_routedBinCutoff {χ route : ℝ → ℝ} {b : ℕ → ℝ} (n : ℕ)
    (hb : ∀ i, 0 < b i) (hχ : ∀ t, 1 ≤ t → χ t = 1) {w : ℝ}
    (hcover : w = 0 ∨ b n ≤ w) :
    ∑ i ∈ range (n + 1), b i * routedBinCutoff χ b i route (w / b i) = w * route w := by
  simp_rw [mul_routedBinCutoff (hb _).ne']
  rw [← sum_mul]
  congr 1
  rcases hcover with rfl | hw
  · simp
  · exact Cslib.sum_range_mul_binWeight hχ (hb n) hw

namespace CorrectionRowRecipe

/-- Signed raw residual, before any scalar saturation. The right child releases the source
and is evaluated at `z`. The negative and product-left corrections have separate
terminal/usage tuples. Direct and right children may be different estimates of the base. -/
@[expose] def residual {V : Type*} [Fintype V]
    (direct negative left right : Matrix V V ℝ) : Matrix V V ℝ :=
  fun x y => direct x y - negative x y + ∑ z, left x z * right z y

/-- Substitution of exact children recovers the existing matrix expression. -/
theorem residual_eq {V : Type*} [Fintype V] (C E : Matrix V V ℝ) :
    residual C E E C = C - E + E * C := by
  ext x y
  rfl

end CorrectionRowRecipe

/-- Bounded top bin, with the same clipped first entry used in its routing fraction.
Positive fine bins keep their original expression; negative inputs are extended by zero. -/
@[expose] noncomputable def boundedRoutedBinCutoff (χ : ℝ → ℝ) (b : ℕ → ℝ)
    (cap : ℝ) (i : ℕ) (route : ℝ → ℝ) (d : ℝ) : ℝ :=
  if i = 0 then routedBinCutoff χ b i route (min cap (max 0 d))
  else if d < 0 then 0 else routedBinCutoff χ b i route d

/-- The bounded expression preserves every nonnegative true input below the top cap. -/
theorem boundedRoutedBinCutoff_eq {χ : ℝ → ℝ} {b : ℕ → ℝ} {cap d : ℝ}
    (hd : 0 ≤ d) (hcap : d ≤ cap) (i : ℕ) (route : ℝ → ℝ) :
    boundedRoutedBinCutoff χ b cap i route d = routedBinCutoff χ b i route d := by
  simp [boundedRoutedBinCutoff, max_eq_right hd, min_eq_right hcap, not_lt.mpr hd]

/-- Negative estimates produce no bin value, including at the clipped top bin. -/
theorem boundedRoutedBinCutoff_of_neg {χ : ℝ → ℝ} {b : ℕ → ℝ} {cap d : ℝ}
    (hcap : 0 ≤ cap) (hd : d < 0) (i : ℕ) (route : ℝ → ℝ) :
    boundedRoutedBinCutoff χ b cap i route d = 0 := by
  by_cases hi : i = 0
  · simp [boundedRoutedBinCutoff, hi, max_eq_left hd.le, min_eq_right hcap,
      routedBinCutoff]
  · simp [boundedRoutedBinCutoff, hi, hd]

/-- Scalar top clipping and zero extension preserve the dense lower support threshold.
Consequently raw row-rank gates still bound support for arbitrary estimates. -/
theorem boundedRoutedBinCutoff_eq_zero {χ : ℝ → ℝ} {b : ℕ → ℝ} {cap d : ℝ}
    (hcap : 0 ≤ cap) (hχ0 : ∀ t, t ≤ 1 / 2 → χ t = 0)
    (hb : ∀ i, 0 < b i) (hanti : Antitone b) (hd : d ≤ 1 / 2)
    (i : ℕ) (route : ℝ → ℝ) : boundedRoutedBinCutoff χ b cap i route d = 0 := by
  by_cases hd0 : d < 0
  · exact boundedRoutedBinCutoff_of_neg hcap hd0 i route
  have hd0 := not_lt.mp hd0
  cases i with
  | zero =>
    have hc : min cap (max 0 d) ≤ 1 / 2 := by
      rw [max_eq_right hd0]
      exact (min_le_right _ _).trans hd
    simp [boundedRoutedBinCutoff, routedBinCutoff, Cslib.binWeight,
      mul_div_cancel_left₀ _ (hb 0).ne', hχ0 _ hc]
  | succ i =>
    have hu : b (i + 1) * d / b i ≤ 1 / 2 := by
      apply (div_le_iff₀ (hb i)).mpr
      calc
        b (i + 1) * d ≤ b (i + 1) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hd (hb _).le
        _ ≤ (1 / 2) * b i := by
          simpa only [mul_comm] using
            mul_le_mul_of_nonneg_right (hanti (Nat.le_succ i)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simp [boundedRoutedBinCutoff, not_lt.mpr hd0, routedBinCutoff, Cslib.binWeight,
      mul_div_cancel_left₀ _ (hb (i + 1)).ne', hχ0 _ hd, hχ0 _ hu]

/-- A true fine-bin nonzero value controls the atom-unit entry by the adjacent scale ratio. -/
theorem routedBinCutoff_succ_lt {χ : ℝ → ℝ} {b : ℕ → ℝ}
    (hχ0 : ∀ t, t ≤ 1 / 2 → χ t = 0) (hχ1 : ∀ t, 1 ≤ t → χ t = 1)
    (hb : ∀ i, 0 < b i) (hanti : Antitone b) {i : ℕ} {route : ℝ → ℝ} {d : ℝ}
    (h : routedBinCutoff χ b (i + 1) route d ≠ 0) : d < b i / b (i + 1) := by
  have hw : Cslib.binWeight χ b (i + 1) (b (i + 1) * d) ≠ 0 := by
    intro hw
    exact h (by simp [routedBinCutoff, hw])
  have hu := (Cslib.binWeight_succ_ne_zero hχ0 hχ1 hb hanti hw).2
  exact (lt_div_iff₀ (hb _)).mpr (by simpa only [mul_comm] using hu)

/-- Fixed finite range for arbitrary estimated inputs. The top cap and fine scale ratio are
separate bounds; no clipping is applied to a fine bin's routing argument. -/
theorem boundedRoutedBinCutoff_mem_Icc {χ : ℝ → ℝ} {b : ℕ → ℝ} {cap B : ℝ}
    (hcap : 0 ≤ cap) (hB : 0 ≤ B) (hcapB : cap ≤ B)
    (hχ : Monotone χ) (hχ0 : ∀ t, t ≤ 1 / 2 → χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχrange : ∀ t, χ t ∈ Set.Icc 0 1)
    (hb : ∀ i, 0 < b i) (hanti : Antitone b)
    (hratio : ∀ i, b i / b (i + 1) ≤ B)
    (route : ℝ → ℝ) (hr : ∀ w, route w ∈ Set.Icc 0 1) (i : ℕ) (d : ℝ) :
    boundedRoutedBinCutoff χ b cap i route d ∈ Set.Icc 0 B := by
  have hzero : χ 0 = 0 := hχ0 _ (by norm_num)
  have bound (j : ℕ) (v : ℝ) (hv : 0 ≤ v) (hvB : v ≤ B) :
      routedBinCutoff χ b j route v ∈ Set.Icc 0 B := by
    have hw1 : Cslib.binWeight χ b j (b j * v) ≤ 1 := by
      cases j with
      | zero => exact (hχrange _).2
      | succ j =>
        simp only [Cslib.binWeight]
        linarith [(hχrange (b (j + 1) * v / b (j + 1))).2,
          (hχrange (b (j + 1) * v / b j)).1]
    have hw0' := Cslib.binWeight_nonneg hχ hzero hb hanti (k := j)
      (mul_nonneg (hb j).le hv)
    have hp0 := mul_nonneg hv hw0'
    exact ⟨mul_nonneg hp0 (hr _).1,
      (mul_le_of_le_one_right hp0 (hr _).2).trans
        ((mul_le_of_le_one_right hv hw1).trans hvB)⟩
  cases i with
  | zero =>
    simp only [boundedRoutedBinCutoff, ↓reduceIte]
    exact bound 0 _ (le_min hcap (le_max_left _ _)) ((min_le_left _ _).trans hcapB)
  | succ i =>
    by_cases hd : d < 0
    · simp [boundedRoutedBinCutoff, hd, hB]
    · simp only [boundedRoutedBinCutoff, Nat.succ_ne_zero, ↓reduceIte, hd]
      by_cases hz : routedBinCutoff χ b (i + 1) route d = 0
      · simpa only [hz, Set.mem_Icc] using And.intro le_rfl hB
      · exact bound _ _ (not_lt.mp hd)
          ((routedBinCutoff_succ_lt hχ0 hχ1 hb hanti hz).le.trans (hratio i))

namespace DenseRowRecipe

variable {V Γ Ω : Type*} [Fintype V] [Fintype Γ] [Fintype Ω]

/-- Dense preparation on the full raw row, before scalar clipping or access filtering. -/
@[expose] noncomputable def preparation (h ρ : ℝ → ℝ) (K : ℕ) (b : ℝ)
    (Y : Ω → V → Prop) [∀ s v, Decidable (Y s v)]
    (raw : Matrix V V ℝ) (s : Ω) : Matrix V V ℝ :=
  atomPrep h ρ K b raw {w | Y s w}

/-- Normalization of arbitrary children. Preparation is averaged on its own source/usage
slice, including inherited suffixes, without an importance factor. -/
@[expose] noncomputable def normalized (k ρ : ℝ → ℝ) (K : ℕ) (b : ℝ)
    (X : Γ → V → Prop) (Y Yt : Ω → V → Prop)
    [∀ s v, Decidable (X s v)] [∀ s v, Decidable (Y s v)] [∀ s v, Decidable (Yt s v)]
    (raw : Matrix V V ℝ) (prep : Γ × Ω → Matrix V V ℝ)
    (σ : Γ × Ω) (x y : V) : ℝ :=
  if Yt σ.2 y then k (raw x y / b) * rowGate ρ K b raw {w | Y σ.2 w} x /
    max (1 / 2) (min 1 (CorrectionRowRecipe.normalizer X Yt prep x y)) else 0

/-- Every arbitrary preparatory estimate gives the same fixed output range. -/
theorem normalized_mem_Icc (k ρ : ℝ → ℝ) (K : ℕ) (b : ℝ)
    (X : Γ → V → Prop) (Y Yt : Ω → V → Prop)
    [∀ s v, Decidable (X s v)] [∀ s v, Decidable (Y s v)] [∀ s v, Decidable (Yt s v)]
    {B : ℝ} (hB : 0 ≤ B) (hk : ∀ d, k d ∈ Set.Icc 0 B)
    (hρ : ∀ r, ρ r ∈ Set.Icc 0 1)
    (raw : Matrix V V ℝ) (prep : Γ × Ω → Matrix V V ℝ)
    (σ : Γ × Ω) (x y : V) : normalized k ρ K b X Y Yt raw prep σ x y ∈ Set.Icc 0 (2 * B) := by
  have hc : (1 / 2 : ℝ) ≤ max (1 / 2)
      (min 1 (CorrectionRowRecipe.normalizer X Yt prep x y)) := le_max_left _ _
  have hc0 : 0 < max (1 / 2)
      (min 1 (CorrectionRowRecipe.normalizer X Yt prep x y)) := by linarith
  unfold normalized
  split_ifs
  · have hn : 0 ≤ k (raw x y / b) * rowGate ρ K b raw {w | Y σ.2 w} x :=
      mul_nonneg (hk _).1 (hρ _).1
    refine ⟨div_nonneg hn hc0.le, (div_le_iff₀ hc0).mpr ?_⟩
    calc
      _ ≤ k (raw x y / b) := mul_le_of_le_one_right (hk _).1 (hρ _).2
      _ ≤ B := (hk _).2
      _ ≤ _ := by nlinarith
  · exact ⟨le_rfl, mul_nonneg (by norm_num) hB⟩

/-- Output support is controlled by ranks on the original raw matrix, independent of the
preparatory child. This is a support statement, not an access enumeration algorithm. -/
theorem card_filter_normalized_ne_zero_lt (k ρ : ℝ → ℝ) (K : ℕ) (b : ℝ)
    (X : Γ → V → Prop) (Y Yt : Ω → V → Prop)
    [∀ s v, Decidable (X s v)] [∀ s v, Decidable (Y s v)] [∀ s v, Decidable (Yt s v)]
    (hsub : ∀ s y, Yt s y → Y s y) (hK : 0 < K) {e g : ℝ}
    (he : 0 ≤ e) (hk : ∀ d, d ≤ e → k d = 0) (hg : g ≤ e)
    (hρ : ∀ r, g ≤ r → ρ r = 0)
    (raw : Matrix V V ℝ) (prep : Γ × Ω → Matrix V V ℝ) (σ : Γ × Ω) (x : V) :
    #{y | normalized k ρ K b X Y Yt raw prep σ x y ≠ 0} < K := by
  refine lt_of_le_of_lt (card_le_card fun y hy => ?_)
    (card_filter_mul_rowGate_ne_zero_lt (G := raw) (a := b)
      {w | Y σ.2 w} x hK he hk hg hρ)
  simp only [mem_filter, mem_univ, true_and] at hy
  unfold normalized at hy
  split_ifs at hy with ht
  · exact mem_filter.mpr ⟨by simpa using hsub _ _ ht,
      fun hz => hy (by rw [hz, zero_div])⟩
  · exact (hy rfl).elim

/-- Exact preparation loses its source dependence after the source slice is fixed. -/
theorem normalized_eq_denseAtom (k h ρ : ℝ → ℝ) (K : ℕ) (b : ℝ)
    (X : Γ → V → Prop) (Y Yt : Ω → V → Prop)
    [∀ s v, Decidable (X s v)] [∀ s v, Decidable (Y s v)] [∀ s v, Decidable (Yt s v)]
    (raw : Matrix V V ℝ) (σ : Γ × Ω) (x y : V)
    (hx : ({s | X s x} : Finset Γ).Nonempty) :
    normalized k ρ K b X Y Yt raw (fun σ => preparation h ρ K b Y raw σ.2) σ x y =
      denseAtom Y Yt k h ρ K b raw σ.2 x y := by
  have hm : CorrectionRowRecipe.normalizer X Yt
      (fun σ => preparation h ρ K b Y raw σ.2) x y = atomNormalizer Y Yt h ρ K b raw x y := by
    rw [CorrectionRowRecipe.normalizer, expect_product]
    simp only [preparation, atomNormalizer]
    exact expect_const hx _
  simp only [normalized, hm, denseAtom]

end DenseRowRecipe
/-- Scalar parameters of a dense bin. Channel predicates remain invocation arguments. -/
structure DenseBinRecipe where
  /-- Bin switch. -/
  χ : ℝ → ℝ
  /-- Positive scales are required by the true-mean lemmas, not by evaluation. -/
  scales : ℕ → ℝ
  /-- Cap on the top-bin scalar argument. -/
  cap : ℝ
  /-- Routing fraction evaluated before normalization. -/
  route : ℝ → ℝ
  /-- Preparation support function. -/
  h : ℝ → ℝ
  /-- Raw row-rank gate. -/
  ρ : ℝ → ℝ
  /-- Padded row rank. -/
  K : ℕ

end Matrix
