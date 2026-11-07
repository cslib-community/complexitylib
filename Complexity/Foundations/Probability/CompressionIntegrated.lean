/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.DecoderSharp
public import Complexity.Foundations.Analysis.RowCompression.FourthMoment
public import Complexity.Foundations.Probability.HeavyCountRarity

/-!
# Integrated compression errors for supported decoders

The same environment carries masks, raw prefixes and overflow events. A decoder's range
and postcompression rank support convert sharp pointwise truth comparisons to fourth moments.
False first overflows are paid at the already-added raw prefix j+1. Heavy-event tails remain
explicit budgets, so rarity must be applied to deterministic conditional means separately.
This extracts the shared proof of the normalized-atom client without assuming independence.
-/

public section
universe u v
namespace Cslib.RowCompression
open Finset Cslib Matrix Cslib.RowCompression
open scoped BigOperators

variable (H : ℝ → ℝ → ℝ → ℝ) (K : ℕ) (R : ℝ) (hR : 0 ≤ R)
  (hsupport : ∀ {ι : Type u} (S : Finset ι) (a : State ι),
    #{y ∈ S | H (a.row y 0) (a.row y 1) (firstRank S K a.defaultValue a.row) ≠ 0} < K)
  (hrange : ∀ d v r, 0 ≤ H d v r ^ (4⁻¹ : ℝ) ∧ H d v r ^ (4⁻¹ : ℝ) ≤ R)
include hR hsupport hrange


omit hR hrange in
open Classical in
/-- The root error has support below 2K, independently of row width and defaults. -/
lemma sum_rootError_four {ι : Type u} (S : Finset ι) (a b : State ι)
    {E : ℝ} (_hE : 0 ≤ E) (h : ∀ y ∈ S, |stateRootError H S K a b y| ≤ E) :
    ∑ y ∈ S, |stateRootError H S K a b y| ^ 4 ≤
      2 * (K : ℝ) * E ^ 4 := by
  let T := {y ∈ S | H (a.row y 0) (a.row y 1)
      (firstRank S K a.defaultValue a.row) ≠
    0} ∪
    {y ∈ S | H (b.row y 0) (b.row y 1) (firstRank S
      K b.defaultValue b.row) ≠ 0}
  have hT : T ⊆ S := union_subset (filter_subset _ _) (filter_subset _ _)
  have hc : T.card ≤ 2 * K := (card_union_le _ _).trans (by
    have ha := hsupport S a
    have hb := hsupport S b
    omega)
  calc
    _ = ∑ y ∈ T, |stateRootError H S K a b y| ^
      4 := by
      symm
      apply sum_subset hT
      intro y hy hyt
      have ha : H (a.row y 0) (a.row y 1) (firstRank
        S K a.defaultValue a.row) = 0 :=
        by
        by_contra hz
        exact hyt (mem_union_left _ (mem_filter.mpr ⟨hy, hz⟩))
      have hb : H (b.row y 0) (b.row y 1) (firstRank
        S K b.defaultValue b.row) = 0 :=
        by
        by_contra hz
        exact hyt (mem_union_right _ (mem_filter.mpr ⟨hy, hz⟩))
      simp only [stateRootError, ha, hb, Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0), sub_self,
        abs_zero, zero_pow (by decide : 4 ≠ 0)]
    _ ≤ ∑ _y ∈ T, E ^ 4 := sum_le_sum fun y hy => pow_le_pow_left₀ (abs_nonneg _) (h y (hT hy)) 4
    _ = (T.card : ℝ) * E ^ 4 := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)

omit hR hsupport in
open Classical in
lemma rootError_range {ι : Type u} (S : Finset ι) (a b : State ι) (y : ι) :
    |stateRootError H S K a b y| ≤ R
      := by
  have ha := hrange (a.row y 0) (a.row y 1) (firstRank S K a.defaultValue a.row)
  have hb := hrange (b.row y 0) (b.row y 1) (firstRank S K b.defaultValue b.row)
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
end Cslib.RowCompression
namespace Cslib.RowCompression

open Finset Cslib Cslib.RowCompression Cslib.Probability
open scoped BigOperators

variable (H : ℝ → ℝ → ℝ → ℝ) (K : ℕ) (R : ℝ) (hR : 0 ≤ R)
  (hsupport : ∀ {ι : Type u} (S : Finset ι) (a : State ι),
    #{y ∈ S | H (a.row y 0) (a.row y 1) (firstRank S K a.defaultValue a.row) ≠ 0} < K)
  (hrange : ∀ d v r, 0 ≤ H d v r ^ (4⁻¹ : ℝ) ∧ H d v r ^ (4⁻¹ : ℝ) ≤ R)
include hR hsupport hrange

variable {ι : Type u}
open Classical in
private theorem sum_stateRootError_pow_four_le_of_false {η : ℝ}
    {S : Finset ι} {n : ℕ → ℕ} (_hK : 0 < K)
    {Δ : ℕ → ι → Fin 2 → ℝ} {a : State ι} {truth : ι → Fin 2 → ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (ha : a.defaultValue = 0)
    (m j : ℕ) (hj : j < m) (hn : 0 < n j)
    (hover : IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ a j)
    (hfirst : ∀ y ∈ S, 0 ≤ truth y 0)
    (hsecond : ∀ y ∈ S, truth y 0 ≤ dyadicFloor η m j / 4 → truth y 1 = 0)
    (hheavy : 2 * #{y ∈ S | dyadicFloor η m j / 4 < truth y 0} < n j)
    (b : State ι) :
    ∑ y ∈ S, |stateRootError H S K b ⟨0, truth⟩
      y| ^ 4 ≤
      (64 * (K : ℝ) * R ^ 4 / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
        ∑ y ∈ S, |clippedError (truth y 0) (truth y 1)
          (uncompressedRow Δ a.row (j + 1) y)| ^ 4 := by
  have hcharge := one_le_sum_clippedError_pow_of_firstOverflow_dyadic hη hη1 ha
    m j hj hn hover hfirst hsecond hheavy 4
  have he (y : ι) : |clippedError (truth y 0) (truth y 1)
      (uncompressedRow Δ a.row (j + 1) y)| =
      clippedError (truth y 0) (truth y 1) (uncompressedRow Δ a.row (j + 1) y) :=
    abs_of_nonneg (clippedError_nonneg _ _ _)
  calc
    _ ≤ 2 * (K : ℝ) * R ^ 4 := sum_rootError_four H K hsupport S _ _ hR (fun y _ =>
      rootError_range H K R hrange S _ _ y)
    _ = (2 * (K : ℝ) * R ^ 4) * 1 := by ring
    _ ≤ (2 * (K : ℝ) * R ^ 4) * ((2 : ℝ) ^ (4 + 1) /
        ((n j : ℝ) * dyadicFloor η m j ^ 4) *
          ∑ y ∈ S, clippedError (truth y 0) (truth y 1)
            (uncompressedRow Δ a.row (j + 1) y) ^ 4) :=
      mul_le_mul_of_nonneg_left hcharge (by positivity)
    _ = _ := by simp only [he]; norm_num; ring

variable {Ω : Type v} {V : Type u} [Fintype Ω] [Fintype V]

open Classical in
/-- The supported decoder outputs on a specified false-first-overflow event are paid
for by the raw-prefix moment at `j + 1`. Every random quantity may share the environment. -/
theorem rowNormPow_falseFirstOverflow_le {η N u : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (n : ℕ → ℕ) (hK : 0 < K) (m j : ℕ) (hj : j < m) (hn : 0 < n j)
    (Δ : Ω → V → ℕ → V → Fin 2 → ℝ) (a : Ω → V → State V)
    (truth : Ω → V → V → Fin 2 → ℝ)
    (ha : ∀ σ x, X σ x → (a σ x).defaultValue = 0)
    (hfirst : ∀ σ x y, X σ x → Y σ y → 0 ≤ truth σ x y 0)
    (hsecond : ∀ σ x y, X σ x → Y σ y →
      truth σ x y 0 ≤ dyadicFloor η m j / 4 → truth σ x y 1 = 0) :
    let S := fun σ => ({y | Y σ y} : Finset V)
    let b := fun σ x => iterate (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) (a σ x) m
    let F := fun σ x => IsFirstOverflow (S σ) n (fun _ => K)
      (dyadicFloor η m) (Δ σ x) (a σ x) j ∧
        ¬ heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ
    rowNormPow 4 N u X Y (fun σ x y =>
      if F σ x then stateRootError H (S σ) K (b
        σ x) ⟨0, truth σ x⟩ y else 0) ≤
      (64 * (K : ℝ) * R ^ 4 / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
        rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
          (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)) := by
  classical
  dsimp only
  unfold rowNormPow
  have hc : 0 ≤ 64 * (K : ℝ) * R ^ 4 / ((n j : ℝ) * dyadicFloor η m j ^ 4) := by
    positivity
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
        (64 * (K : ℝ) * R ^ 4 / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
          ∑ y ∈ ({y | Y σ y} : Finset V),
            |clippedError (truth σ x y 0) (truth σ x y 1)
              (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)| ^ 4 := by
      refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.mpr hNu)
      refine sum_le_sum fun x hx => ?_
      have hx' := (mem_filter.mp hx).2
      dsimp only
      split_ifs with hF
      · apply sum_stateRootError_pow_four_le_of_false H K R hR hsupport hrange hK hη hη1 (ha
        σ x hx')
          m j hj hn hF.1
        · intro y hy
          exact hfirst σ x y hx' (mem_filter.mp hy).2
        · intro y hy
          exact hsecond σ x y hx' (mem_filter.mp hy).2
        · simpa only [heavyCountEvent, filter_filter] using Nat.lt_of_not_ge hF.2
      · simp only [abs_zero, zero_pow (by decide : (4 : ℕ) ≠ 0), sum_const_zero]
        exact mul_nonneg hc (sum_nonneg fun _ _ => by positivity)
    _ = _ := by simp only [← mul_sum, ← mul_expect]; ring

open Classical in
/-- **The false-type contribution to final decoder error.** Taking the union of the
possible false first overflows gives the sum of their raw-prefix charges. Both sides use the
same `RootMetric` normalization, and no independence or final-output error premise is required. -/
theorem rowNormPow_falseFirstOverflowBefore_le {η N u : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (n : ℕ → ℕ) (hK : 0 < K) (m : ℕ) (hn : ∀ j < m, 0 < n j)
    (Δ : Ω → V → ℕ → V → Fin 2 → ℝ) (a : Ω → V → State V)
    (truth : Ω → V → V → Fin 2 → ℝ)
    (ha : ∀ σ x, X σ x → (a σ x).defaultValue = 0)
    (hfirst : ∀ σ x y, X σ x → Y σ y → 0 ≤ truth σ x y 0)
    (hsecond : ∀ j < m, ∀ σ x y, X σ x → Y σ y →
      truth σ x y 0 ≤ dyadicFloor η m j / 4 → truth σ x y 1 = 0) :
    let S := fun σ => ({y | Y σ y} : Finset V)
    let b := fun σ x => iterate (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) (a σ x) m
    let F := fun j σ x => IsFirstOverflow (S σ) n (fun _ => K)
      (dyadicFloor η m) (Δ σ x) (a σ x) j ∧
        ¬ heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ
    rowNormPow 4 N u X Y (fun σ x y =>
      if ∃ j < m, F j σ x then stateRootError H (S
        σ) K (b σ x) ⟨0, truth σ x⟩ y
        else 0) ≤
      ∑ j ∈ range m, (64 * (K : ℝ) * R ^ 4 / ((n j : ℝ) * dyadicFloor η m j ^ 4))
 *
        rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
          (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)) := by
  classical
  let S := fun σ => ({y | Y σ y} : Finset V)
  let b := fun σ x => iterate (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) (a σ x) m
  let F := fun j σ x => IsFirstOverflow (S σ) n (fun _ => K)
    (dyadicFloor η m) (Δ σ x) (a σ x) j ∧
      ¬ heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ
  let D := fun σ x y => stateRootError H (S σ) K
    (b σ x) ⟨0, truth σ x⟩ y
  change rowNormPow 4 N u X Y (fun σ x y => if ∃ j < m, F j σ x then D σ x y else 0) ≤ _
  have hgroup (j : ℕ) (hj : j ∈ range m) :
      rowNormPow 4 N u X Y (fun σ x y => if F j σ x then D σ x y else 0) ≤
        (64 * (K : ℝ) * R ^ 4 / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
          rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
            (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)) :=
    rowNormPow_falseFirstOverflow_le H K R hR hsupport hrange hη hη1 hNu X Y n hK m j
      (mem_range.mp hj) (hn j (mem_range.mp hj)) Δ a truth ha hfirst (hsecond j (mem_range.mp hj))
  refine le_trans ?_ (sum_le_sum hgroup)
  have hpoint (σ : Ω) (x y : V) :
      |if ∃ j < m, F j σ x then D σ x y else 0| ^ 4 ≤
        ∑ j ∈ range m, |if F j σ x then D σ x y else 0| ^ 4 := by
    by_cases hF : ∃ j < m, F j σ x
    · obtain ⟨j, hj, hjF⟩ := hF
      have hsome : ∃ i < m, F i σ x := ⟨j, hj, hjF⟩
      have hsingle := single_le_sum (s := range m)
        (f := fun i => |if F i σ x then D σ x y else 0| ^ 4)
        (fun _ _ => by positivity) (mem_range.mpr hj)
      simpa only [hsome, hjF, ↓reduceIte] using hsingle
    · simp only [hF, ↓reduceIte, abs_zero, zero_pow (by decide : (4 : ℕ) ≠ 0)]
      exact sum_nonneg fun _ _ => by positivity
  have hswap (σ : Ω) :
      (∑ x ∈ ({x | X σ x} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V),
        ∑ j ∈ range m, |if F j σ x then D σ x y else 0| ^ 4) =
      ∑ j ∈ range m, ∑ x ∈ ({x | X σ x} : Finset V),
        ∑ y ∈ ({y | Y σ y} : Finset V), |if F j σ x then D σ x y else 0| ^ 4 := by
    simp_rw [sum_comm (s := ({y | Y σ y} : Finset V)) (t := range m)]
    rw [sum_comm]
  unfold rowNormPow
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
        ∑ y ∈ ({y | Y σ y} : Finset V), ∑ j ∈ range m,
          |if F j σ x then D σ x y else 0| ^ 4 := by
      refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.mpr hNu)
      exact sum_le_sum fun x _ => sum_le_sum fun y _ => hpoint σ x y
    _ = _ := by simp only [hswap, expect_sum_comm, mul_sum]

end Cslib.RowCompression
namespace Cslib.RowCompression
open Finset Cslib Cslib.RowCompression Cslib.Probability
open scoped BigOperators

variable (H : ℝ → ℝ → ℝ → ℝ) (K : ℕ) (R : ℝ) (hR : 0 ≤ R)
  (hsupport : ∀ {ι : Type u} (S : Finset ι) (a : State ι),
    #{y ∈ S | H (a.row y 0) (a.row y 1) (firstRank S K a.defaultValue a.row) ≠ 0} < K)
  (hrange : ∀ d v r, 0 ≤ H d v r ^ (4⁻¹ : ℝ) ∧ H d v r ^ (4⁻¹ : ℝ) ≤ R)
include hR hsupport hrange

omit hR hsupport hrange in
open Classical in
private theorem add_add_pow_four_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a + b + c) ^ 4 ≤ 64 * (a ^ 4 + b ^ 4 + c ^ 4) := by
  have h := add_pow_le ha hb 4
  have h' := add_pow_le (add_nonneg ha hb) hc 4
  norm_num at h h'
  nlinarith [pow_nonneg hc 4]

open Classical in
/-- The actual final output is bounded by weighted prefix, no-overflow final and true-overflow
budgets, plus the existing false-overflow raw-prefix charge. The masks and all errors may be
correlated. No final-output error premise or factor counting endpoints or groups is introduced. -/
theorem compression_rowNormPow_le {scale η C A : ℝ}
    (hK : 0 < K) (hη : 0 < η) (hη1 : η ≤ 1) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hbound :
    ∀ {ι : Type u} (S : Finset ι) (n : ℕ → ℕ)
        (Δ : ℕ → ι → Fin 2 → ℝ) (raw truth : ι → Fin 2 → ℝ)
        (m : ℕ) (heavy : ℕ → Prop),
        (∀ y ∈ S, 0 ≤ truth y 0) →
        (∀ y ∈ S, |truth y 1| ≤ scale / 2) →
        (∀ i < m, K ≤ n i) → ∀ (ε : ℕ → ℝ),
        (∀ i < m, 0 ≤ ε i) →
        (∀ i < m, ∀ y ∈ S,
          clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i) →
        ∀ εfinal : ℝ, 0 ≤ εfinal →
        (∀ y ∈ S,
          clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw m y) ≤ εfinal) →
        (¬ ∃ j < m, IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ j ∧ ¬heavy j) →
        ∀ y ∈ S,
        |stateRootError H S K
          (iterate S n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ m) ⟨0, truth⟩ y| ≤
          A * (∑ i ∈ range m, dyadicFloor η m i * ε i) +
          C * (if ∀ i < m, stepThreshold S n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ i ≤
            dyadicFloor η m i then εfinal else 0) + C * (∑ j ∈ range m,
            if IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ ⟨0, raw⟩ j ∧ heavy j then
              ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i else 0)) :
      ∀ {Ω : Type v} {V : Type u} [Fintype Ω] [Fintype V]
        (N u : ℝ), 0 ≤ N * u → ∀ (X Y : Ω → V → Prop)
        [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
        (n : ℕ → ℕ) (m : ℕ), (∀ i < m, K ≤ n i) →
        ∀ (Δ : Ω → V → ℕ → V → Fin 2 → ℝ) (raw : Ω → V → V → Fin 2 → ℝ)
        (truth : Ω → V → V → Fin 2 → ℝ),
        (∀ σ x y, X σ x → Y σ y → 0 ≤ truth σ x y 0) →
        (∀ σ x y, X σ x → Y σ y → |truth σ x y 1| ≤ scale / 2) →
        (∀ j < m, ∀ σ x y, X σ x → Y σ y →
          truth σ x y 0 ≤ dyadicFloor η m j / 4 → truth σ x y 1 = 0) →
        ∀ (ε : ℕ → Ω → V → ℝ) (εfinal : Ω → V → ℝ),
        (∀ i < m, ∀ σ x, X σ x → 0 ≤ ε i σ x) →
        (∀ σ x, X σ x → 0 ≤ εfinal σ x) →
        (∀ i < m, ∀ σ x y, X σ x → Y σ y →
          clippedError (truth σ x y 0) (truth σ x y 1)
            (uncompressedRow (Δ σ x) (raw σ x) (i + 1) y) ≤ ε i σ x) →
        (∀ σ x y, X σ x → Y σ y →
          clippedError (truth σ x y 0) (truth σ x y 1)
            (uncompressedRow (Δ σ x) (raw σ x) m y) ≤ εfinal σ x) →
        let S := fun σ => ({y | Y σ y} : Finset V)
        let actual := fun σ x => iterate (S σ) n (fun _ => K)
          (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ m
        let Pre := fun σ x => ∑ i ∈ range m, dyadicFloor η m i * ε i σ x
        let No := fun σ x => if ∀ i < m,
          stepThreshold (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ i ≤
            dyadicFloor η m i then εfinal σ x else 0
        let Tail := fun σ x => ∑ j ∈ range m,
          if IsFirstOverflow (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ j ∧
            heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ then
              ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x else 0
        rowNormPow 4 N u X Y (fun σ x y =>
          stateRootError H (S σ) K (actual σ x)
            ⟨0, truth σ x⟩ y) ≤
          128 * (K : ℝ) * (A ^ 4 * vertexNormPow 4 N u X Pre +
            C ^ 4 * vertexNormPow 4 N u X No + C ^ 4 * vertexNormPow 4 N u X Tail) +
          ∑ j ∈ range m, (64 * (K : ℝ) * R ^ 4 / ((n j : ℝ) * dyadicFloor η m j ^
            4)) *
            rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
              (uncompressedRow (Δ σ x) (raw σ x) (j + 1) y)) := by
  classical
  intro Ω V _ _ N u hNu X Y _ _ n m hcapacity Δ raw truth hfirst hsecond
    hvanish ε εfinal hε hεfinal herr herrfinal
  dsimp only
  let S := fun σ => ({y | Y σ y} : Finset V)
  let actual := fun σ x => iterate (S σ) n (fun _ => K)
    (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ m
  let D := fun σ x y => stateRootError H (S σ) K
    (actual σ x) ⟨0, truth σ x⟩ y
  let heavy := fun j σ x =>
    heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ
  let F := fun σ x => ∃ j < m,
    IsFirstOverflow (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ j ∧ ¬heavy j σ x
  let Pre := fun σ x => ∑ i ∈ range m, dyadicFloor η m i * ε i σ x
  let No := fun σ x => if ∀ i < m,
      stepThreshold (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ i ≤
        dyadicFloor η m i then εfinal σ x else 0
  let Tail := fun σ x => ∑ j ∈ range m,
    if IsFirstOverflow (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ j ∧
      heavy j σ x then ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x else 0
  have hpre0 (σ : Ω) (x : V) (hx : X σ x) : 0 ≤ Pre σ x :=
    sum_nonneg fun i hi => mul_nonneg (dyadicFloor_nonneg hη.le _ _) (hε i (mem_range.mp hi) σ x hx)
  have hno0 (σ : Ω) (x : V) (hx : X σ x) : 0 ≤ No σ x := by
    dsimp only [No]
    split_ifs
    · exact hεfinal σ x hx
    · exact le_rfl
  have htail0 (σ : Ω) (x : V) (hx : X σ x) : 0 ≤ Tail σ x := by
    refine sum_nonneg fun j _ => ?_
    split_ifs
    · exact sum_nonneg fun i hi => mul_nonneg (by positivity) (hε i (mem_Ico.mp hi).2 σ x hx)
    · exact le_rfl
  have hrow (σ : Ω) (x : V) (hx : X σ x) :
      (∑ y ∈ S σ, |D σ x y| ^ 4) ≤
        128 * (K : ℝ) * (A ^ 4 * |Pre σ x| ^ 4 + C ^ 4 * |No σ x| ^ 4 +
          C ^ 4 * |Tail σ x| ^ 4) +
        ∑ y ∈ S σ, |if F σ x then D σ x y else 0| ^ 4 := by
    have hb0 : 0 ≤ 128 * (K : ℝ) * (A ^ 4 * |Pre σ x| ^ 4 + C ^ 4 * |No σ x| ^ 4 +
        C ^ 4 * |Tail σ x| ^ 4) := by positivity
    by_cases hf : F σ x
    · simp only [hf, ↓reduceIte]
      linarith
    · have hlocal : ∀ y ∈ S σ, |D σ x y| ≤
          A * Pre σ x + C * No σ x + C * Tail σ x :=
        hbound (S σ) n (Δ σ x) (raw σ x) (truth σ x) m (fun j => heavy j σ x) (fun y hy => hfirst
          σ x y hx (mem_filter.mp hy).2)
          (fun y hy => hsecond σ x y hx (mem_filter.mp hy).2) hcapacity
          (fun i => ε i σ x) (fun i hi => hε i hi σ x hx)
          (fun i hi y hy => herr i hi σ x y hx (mem_filter.mp hy).2)
          (εfinal σ x) (hεfinal σ x hx)
          (fun y hy => herrfinal σ x y hx (mem_filter.mp hy).2) hf
      have hs := sum_rootError_four H K hsupport (S σ)
        (actual σ x) ⟨0, truth σ x⟩ (add_nonneg (add_nonneg (mul_nonneg hA (hpre0 σ x hx))
          (mul_nonneg hC (hno0 σ x hx))) (mul_nonneg hC (htail0 σ x hx))) hlocal
      have hp := add_add_pow_four_le (mul_nonneg hA (hpre0 σ x hx))
        (mul_nonneg hC (hno0 σ x hx)) (mul_nonneg hC (htail0 σ x hx))
      have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * (K : ℝ) by positivity)
      simp only [abs_of_nonneg (hpre0 σ x hx), abs_of_nonneg (hno0 σ x hx),
        abs_of_nonneg (htail0 σ x hx), hf, ↓reduceIte, abs_zero,
        zero_pow (by decide : (4 : ℕ) ≠ 0), sum_const_zero, add_zero]
      exact hs.trans (by nlinarith only [hh])
  have hintegrated : rowNormPow 4 N u X Y D ≤
      128 * (K : ℝ) * (A ^ 4 * vertexNormPow 4 N u X Pre +
        C ^ 4 * vertexNormPow 4 N u X No + C ^ 4 * vertexNormPow 4 N u X Tail) +
      rowNormPow 4 N u X Y (fun σ x y => if F σ x then D σ x y else 0) := by
    unfold rowNormPow vertexNormPow
    calc
      _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
          (128 * (K : ℝ) * (A ^ 4 * |Pre σ x| ^ 4 + C ^ 4 * |No σ x| ^ 4 +
            C ^ 4 * |Tail σ x| ^ 4) +
            ∑ y ∈ ({y | Y σ y} : Finset V), |if F σ x then D σ x y else 0| ^ 4) := by
        refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.mpr hNu)
        exact sum_le_sum fun x hx => hrow σ x (mem_filter.mp hx).2
      _ = _ := by
        simp only [sum_add_distrib, ← mul_sum, expect_add_distrib, ← mul_expect]
        ring
  have hfalse := rowNormPow_falseFirstOverflowBefore_le H K R hR hsupport hrange hη hη1 hNu X Y n
    hK m
    (fun i hi => hK.trans_le (hcapacity i hi)) Δ (fun σ x => ⟨0, raw σ
      x⟩) truth (by intros; rfl) hfirst hvanish
  exact hintegrated.trans (add_le_add_right hfalse _)

end Cslib.RowCompression
