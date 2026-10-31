/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.SourceRelease
import Complexity.Foundations.Analysis.RootError
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Coupled product errors and source release

For four nonnegative tables on one environment, compare the concrete products
`P σ x y = ∑ z ∈ Z σ, F σ x z * B σ z y` and `P'` built from `F'`, `B'`.
Splitting each product through `F' * B` charges the left error against the row support of `B`
and the right error against the incoming support of `F'`. The latter changes source rate from
`u` to `f` and has the exact normalization cost `f / u`.

The root-metric estimate uses the homogeneous-loss mixture inequality and scalar product-root
comparison. Its explicit conservative constant is `2 ^ (2 * (s - 1)) * s ^ s`, or `16384` at
`s = 4`. All four tables may depend on the same environment. The right error is a common table
at `(z, y)`, with no additional old-source argument.

This is the product and source-domain part of the proof of [OpenAI2026LogSpace, Lemma 7.3].
The coarse/fine terminal scale comparisons and conditional-mean estimates remain separate.
No final-estimator or machine-space contract is assumed.

## Main results

* `Cslib.rootDistPow_mul_le`: a coupled product-table estimate with row and incoming caps.
* `Matrix.correctionAtom_denseAtom_rootDistPow_le`: the actual atom specialization, deriving
  both support caps from the incoming and row gates.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  proof of Lemma 7.3, September 23, 2026 revision `7ef5c0cc` (preprint, not peer reviewed).
-/

public section

open Finset
open scoped BigOperators

namespace Cslib

private theorem root_mul_sub_pow_le {s : ℕ} (hs : s ≠ 0) {a a' b b' : ℝ}
    (ha : 0 ≤ a) (ha' : 0 ≤ a') (hb : 0 ≤ b) (hb' : 0 ≤ b') :
    |(a * b) ^ (s⁻¹ : ℝ) - (a' * b') ^ (s⁻¹ : ℝ)| ^ s ≤
      2 ^ (s - 1) * (b * |a ^ (s⁻¹ : ℝ) - a' ^ (s⁻¹ : ℝ)| ^ s +
        a' * |b ^ (s⁻¹ : ℝ) - b' ^ (s⁻¹ : ℝ)| ^ s) := by
  have heq : (a * b) ^ (s⁻¹ : ℝ) - (a' * b') ^ (s⁻¹ : ℝ) =
      (a ^ (s⁻¹ : ℝ) - a' ^ (s⁻¹ : ℝ)) * b ^ (s⁻¹ : ℝ) +
        a' ^ (s⁻¹ : ℝ) * (b ^ (s⁻¹ : ℝ) - b' ^ (s⁻¹ : ℝ)) := by
    rw [Real.mul_rpow ha hb, Real.mul_rpow ha' hb']
    ring
  have habs : |(a * b) ^ (s⁻¹ : ℝ) - (a' * b') ^ (s⁻¹ : ℝ)| ≤
      |a ^ (s⁻¹ : ℝ) - a' ^ (s⁻¹ : ℝ)| * b ^ (s⁻¹ : ℝ) +
        a' ^ (s⁻¹ : ℝ) * |b ^ (s⁻¹ : ℝ) - b' ^ (s⁻¹ : ℝ)| := by
    rw [heq]
    refine (abs_add_le _ _).trans_eq ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hb _),
      abs_of_nonneg (Real.rpow_nonneg ha' _)]
  refine (pow_le_pow_left₀ (abs_nonneg _) habs s).trans ?_
  refine (add_pow_le (by positivity) (by positivity) s).trans_eq ?_
  rw [mul_pow, mul_pow, Real.rpow_inv_natCast_pow hb hs, Real.rpow_inv_natCast_pow ha' hs]
  ring

private theorem root_sum_mul_sub_pow_le {α : Type*} (T : Finset α) {s : ℕ} (hs : s ≠ 0)
    {a a' b b' : α → ℝ} (ha : ∀ z ∈ T, 0 ≤ a z) (ha' : ∀ z ∈ T, 0 ≤ a' z)
    (hb : ∀ z ∈ T, 0 ≤ b z) (hb' : ∀ z ∈ T, 0 ≤ b' z) :
    |(∑ z ∈ T, a z * b z) ^ (s⁻¹ : ℝ) - (∑ z ∈ T, a' z * b' z) ^ (s⁻¹ : ℝ)| ^ s ≤
      (2 ^ (2 * (s - 1)) * (s : ℝ) ^ s) *
        ∑ z ∈ T, (b z * |a z ^ (s⁻¹ : ℝ) - a' z ^ (s⁻¹ : ℝ)| ^ s +
          a' z * |b z ^ (s⁻¹ : ℝ) - b' z ^ (s⁻¹ : ℝ)| ^ s) := by
  have hsum := homogeneousLoss_sum_le T hs (w := fun _ => 1)
    (F := fun z => a z * b z) (F' := fun z => a' z * b' z) (fun _ _ => zero_le_one)
    (fun z hz => mul_nonneg (ha z hz) (hb z hz))
    (fun z hz => mul_nonneg (ha' z hz) (hb' z hz))
  simp only [one_mul] at hsum
  calc
    _ ≤ 2 ^ (s - 1) * homogeneousLoss s (∑ z ∈ T, a z * b z) (∑ z ∈ T, a' z * b' z) :=
      rpow_inv_sub_pow_le_homogeneousLoss hs
        (sum_nonneg fun z hz => mul_nonneg (ha z hz) (hb z hz))
        (sum_nonneg fun z hz => mul_nonneg (ha' z hz) (hb' z hz))
    _ ≤ 2 ^ (s - 1) * ∑ z ∈ T, homogeneousLoss s (a z * b z) (a' z * b' z) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 2 ^ (s - 1) * ∑ z ∈ T, (s : ℝ) ^ s *
        (2 ^ (s - 1) * (b z * |a z ^ (s⁻¹ : ℝ) - a' z ^ (s⁻¹ : ℝ)| ^ s +
          a' z * |b z ^ (s⁻¹ : ℝ) - b' z ^ (s⁻¹ : ℝ)| ^ s)) := by
      refine mul_le_mul_of_nonneg_left (sum_le_sum fun z hz => ?_) (by positivity)
      exact (homogeneousLoss_le_rpow_inv_sub_pow hs (mul_nonneg (ha z hz) (hb z hz))
        (mul_nonneg (ha' z hz) (hb' z hz))).trans
        (mul_le_mul_of_nonneg_left (root_mul_sub_pow_le hs (ha z hz) (ha' z hz)
          (hb z hz) (hb' z hz)) (by positivity))
    _ = _ := by
      simp only [← mul_sum]
      rw [show 2 * (s - 1) = (s - 1) + (s - 1) by omega, pow_add]
      ring

private theorem sum_le_mul_of_card_support_le {α : Type*} (T : Finset α) {v : α → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hv : ∀ z, v z ≤ C) {K : ℕ} (hK : #{z ∈ T | v z ≠ 0} ≤ K) :
    ∑ z ∈ T, v z ≤ K * C := by
  classical
  have hsum : ∑ z ∈ T, v z = ∑ z ∈ T with v z ≠ 0, v z := by
    rw [sum_filter]
    refine sum_congr rfl fun z _ => ?_
    split_ifs with hz
    · rfl
    · exact not_ne_iff.mp hz
  rw [hsum]
  calc
    _ ≤ ∑ z ∈ T with v z ≠ 0, C := sum_le_sum fun z _ => hv z
    _ = (#{z ∈ T | v z ≠ 0} : ℝ) * C := by rw [sum_const, nsmul_eq_mul]
    _ ≤ K * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hK) hC

variable {Ω V : Type*} [Fintype Ω] [Fintype V]
  {s : ℕ} {N u f : ℝ} {X Z Y : Ω → V → Prop}
  [∀ σ x, Decidable (X σ x)] [∀ σ z, Decidable (Z σ z)] [∀ σ y, Decidable (Y σ y)]

/-- **Coupled product errors with source release**. The true or estimated tables may share
all their randomness. Only `B` needs the row cap and bound `CB`, and only `F'` needs the incoming
cap and bound `CF`, because the scalar comparison splits through `F' * B`.
The source normalization in the right error is exactly `f / u`. -/
theorem rootDistPow_mul_le (hs : s ≠ 0) (hN : 0 < N) (hu : 0 < u) (hf : 0 < f)
    {F F' B B' : Ω → V → V → ℝ}
    (hF : ∀ σ x z, 0 ≤ F σ x z) (hF' : ∀ σ x z, 0 ≤ F' σ x z)
    (hB : ∀ σ z y, 0 ≤ B σ z y) (hB' : ∀ σ z y, 0 ≤ B' σ z y)
    {CF CB : ℝ} (hCF : 0 ≤ CF) (hCB : 0 ≤ CB)
    (hFbound : ∀ σ x z, F' σ x z ≤ CF) (hBbound : ∀ σ z y, B σ z y ≤ CB)
    {Kr Kc : ℕ} (hrow : ∀ σ z, Z σ z → #{y ∈ ({y | Y σ y} : Finset V) | B σ z y ≠ 0} ≤ Kr)
    (hcol : ∀ σ z, Z σ z → #{x ∈ ({x | X σ x} : Finset V) | F' σ x z ≠ 0} ≤ Kc) :
    rootDistPow s N u X Y (fun σ x y => ∑ z ∈ ({z | Z σ z} : Finset V), F σ x z * B σ z y)
        (fun σ x y => ∑ z ∈ ({z | Z σ z} : Finset V), F' σ x z * B' σ z y) ≤
      (2 ^ (2 * (s - 1)) * (s : ℝ) ^ s) *
        (CB * Kr * rootDistPow s N u X Z F F' +
          CF * Kc * (f / u) * rootDistPow s N f Z Y B B') := by
  classical
  let eF : Ω → V → V → ℝ := fun σ x z => |F σ x z ^ (s⁻¹ : ℝ) - F' σ x z ^ (s⁻¹ : ℝ)| ^ s
  let eB : Ω → V → V → ℝ := fun σ z y => |B σ z y ^ (s⁻¹ : ℝ) - B' σ z y ^ (s⁻¹ : ℝ)| ^ s
  have heF : ∀ σ x z, 0 ≤ eF σ x z := fun _ _ _ => by dsimp [eF]; positivity
  have heB : ∀ σ z y, 0 ≤ eB σ z y := fun _ _ _ => by dsimp [eB]; positivity
  have hleft : (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
      ∑ z ∈ ({z | Z σ z} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V), B σ z y * eF σ x z ≤
      CB * Kr * rootDistPow s N u X Z F F' := by
    calc
      _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
          ∑ z ∈ ({z | Z σ z} : Finset V), ((Kr : ℝ) * CB) * eF σ x z := by
        refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (by positivity)
        refine sum_le_sum fun x _ => sum_le_sum fun z hz => ?_
        rw [← sum_mul]
        exact mul_le_mul_of_nonneg_right
          (sum_le_mul_of_card_support_le _ hCB (hBbound σ z) (hrow σ z (by simpa using hz)))
          (heF σ x z)
      _ = _ := by
        simp only [rootDistPow, rowNormPow, eF, ← mul_sum, ← mul_expect]
        ring
  have hright : (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
      ∑ z ∈ ({z | Z σ z} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V), F' σ x z * eB σ z y ≤
      CF * Kc * (f / u) * rootDistPow s N f Z Y B B' := by
    have hpoint : ∀ σ x,
        ∑ z ∈ ({z | Z σ z} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V), F' σ x z * eB σ z y ≤
          CF * ∑ z ∈ ({z | Z σ z} : Finset V) with F' σ x z ≠ 0,
            ∑ y ∈ ({y | Y σ y} : Finset V), eB σ z y := by
      intro σ x
      conv_rhs => rw [mul_sum, sum_filter]
      refine sum_le_sum fun z _ => ?_
      by_cases hz : F' σ x z = 0
      · simp [hz]
      · simp only [hz, ne_eq, not_false_eq_true, ↓reduceIte]
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_right (hFbound σ x z) (sum_nonneg fun y _ => heB σ z y)
    have hrelease : (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
        ∑ z ∈ ({z | Z σ z} : Finset V) with F' σ x z ≠ 0,
          ∑ y ∈ ({y | Y σ y} : Finset V), eB σ z y ≤
        Kc * (f / u) * rootDistPow s N f Z Y B B' := by
      exact sourceRelease_le_rowNormPow hN hu hf (fun σ x z => F' σ x z ≠ 0) hcol
        (fun σ z y => B σ z y ^ (s⁻¹ : ℝ) - B' σ z y ^ (s⁻¹ : ℝ))
    calc
      _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
          CF * ∑ z ∈ ({z | Z σ z} : Finset V) with F' σ x z ≠ 0,
            ∑ y ∈ ({y | Y σ y} : Finset V), eB σ z y := by
        exact mul_le_mul_of_nonneg_left
          (expect_le_expect fun σ _ => sum_le_sum fun x _ => hpoint σ x) (by positivity)
      _ = CF * ((N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
          ∑ z ∈ ({z | Z σ z} : Finset V) with F' σ x z ≠ 0,
            ∑ y ∈ ({y | Y σ y} : Finset V), eB σ z y) := by
        simp only [← mul_sum, ← mul_expect]
        ring
      _ ≤ CF * (Kc * (f / u) * rootDistPow s N f Z Y B B') :=
        mul_le_mul_of_nonneg_left hrelease hCF
      _ = _ := by ring
  have hswap : ∀ σ x,
      ∑ y ∈ ({y | Y σ y} : Finset V), ∑ z ∈ ({z | Z σ z} : Finset V),
        (B σ z y * eF σ x z + F' σ x z * eB σ z y) =
      (∑ z ∈ ({z | Z σ z} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V), B σ z y * eF σ x z) +
        ∑ z ∈ ({z | Z σ z} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V), F' σ x z * eB σ z y := by
    intro σ x
    rw [sum_comm]
    simp only [sum_add_distrib]
  rw [rootDistPow, rowNormPow]
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V),
        (2 ^ (2 * (s - 1)) * (s : ℝ) ^ s) *
          ∑ z ∈ ({z | Z σ z} : Finset V), (B σ z y * eF σ x z + F' σ x z * eB σ z y) := by
      refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (by positivity)
      refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
      exact root_sum_mul_sub_pow_le _ hs (fun z _ => hF σ x z) (fun z _ => hF' σ x z)
        (fun z _ => hB σ z y) (fun z _ => hB' σ z y)
    _ = (2 ^ (2 * (s - 1)) * (s : ℝ) ^ s) *
        (((N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V), ∑ z ∈ ({z | Z σ z} : Finset V),
          ∑ y ∈ ({y | Y σ y} : Finset V), B σ z y * eF σ x z) +
          ((N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V), ∑ z ∈ ({z | Z σ z} : Finset V),
            ∑ y ∈ ({y | Y σ y} : Finset V), F' σ x z * eB σ z y)) := by
      simp only [← mul_sum, ← mul_expect]
      simp_rw [hswap]
      simp only [sum_add_distrib, expect_add_distrib, ← mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hleft hright) (by positivity)

end Cslib

namespace Matrix

variable {Ω V ι κ υ : Type*} [Fintype Ω] [Fintype V] [Fintype ι] [Fintype κ] [Fintype υ]
  {s KF Kc KB : ℕ} {N u f b : ℝ} {I : ℝ → ℝ → ℝ} {τ Q hF ρF k hB ρB : ℝ → ℝ}
  {X : ι → V → Prop} {Z Zt : κ → V → Prop} {Y Yt : υ → V → Prop}
  [∀ t x, Decidable (X t x)] [∀ t z, Decidable (Z t z)] [∀ t z, Decidable (Zt t z)]
  [∀ t y, Decidable (Y t y)] [∀ t y, Decidable (Yt t y)]

private theorem nonneg_correctionAtom {G : Matrix V V ℝ} {g₀ : V → ℝ}
    (hQ0 : ∀ v, 0 ≤ Q v) (hρ0 : ∀ r, 0 ≤ ρF r) (hτ0 : ∀ r, 0 ≤ τ r)
    (hg₀ : ∀ z, 0 ≤ g₀ z) (d : ι × κ) (x z : V) :
    0 ≤ correctionAtom I τ KF Kc f G X Z Zt Q hF ρF g₀ d x z := by
  rw [correctionAtom]
  split_ifs
  · refine mul_nonneg (div_nonneg (mul_nonneg (hQ0 _) (mul_nonneg (hρ0 _) (hτ0 _))) ?_)
      (hg₀ z)
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_max_left _ _)
  · exact le_rfl

private theorem nonneg_denseAtom {H : Matrix V V ℝ}
    (hk0 : ∀ v, 0 ≤ k v) (hρ0 : ∀ r, 0 ≤ ρB r) (t : υ) (z y : V) :
    0 ≤ denseAtom Y Yt k hB ρB KB b H t z y := by
  rw [denseAtom]
  split_ifs
  · refine div_nonneg (mul_nonneg (hk0 _) (hρ0 _)) ?_
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_max_left _ _)
  · exact le_rfl

/-- **Product errors for actual correction and dense atoms**. The matrices, multipliers, and
both seed maps may depend on one shared environment. The bounded cutoffs give `CF = 2 * AF`
and `CB = 2 * AB`; the actual incoming and row gates give caps `Kc` and `KB`.

The intermediate source normalization changes from `u` to the correction scale `f`, with exact
factor `f / u`. This theorem does not change the terminal scale `b` or take conditional means. -/
theorem correctionAtom_denseAtom_rootDistPow_le
    (drawF : Ω → ι × κ) (drawB : Ω → υ)
    (G G' H H' : Ω → Matrix V V ℝ) (g g' : Ω → V → ℝ)
    (hs : s ≠ 0) (hN : 0 < N) (hu : 0 < u) (hf : 0 < f)
    (hQ0 : ∀ v, 0 ≤ Q v) (hk0 : ∀ v, 0 ≤ k v)
    (hρF0 : ∀ r, 0 ≤ ρF r) (hρF1 : ∀ r, ρF r ≤ 1)
    (hτ0 : ∀ r, 0 ≤ τ r) (hτ1 : ∀ r, τ r ≤ 1)
    (hρB0 : ∀ r, 0 ≤ ρB r) (hρB1 : ∀ r, ρB r ≤ 1)
    (hg0 : ∀ σ z, 0 ≤ g σ z) (hg'0 : ∀ σ z, 0 ≤ g' σ z) (hg'1 : ∀ σ z, g' σ z ≤ 1)
    {AF AB : ℝ} (hAF : 0 ≤ AF) (hAB : 0 ≤ AB)
    (hQbound : ∀ σ x z, Q (G' σ x z / f) ≤ AF)
    (hkbound : ∀ σ z y, k (H σ z y / b) ≤ AB)
    (hKc : 0 < Kc) (hIQ : ∀ v r, Q v ≠ 0 → ρF r ≠ 0 → I v r = 1)
    {gF : ℝ} (hgF : gF ≤ 1) (hτclose : ∀ r, gF ≤ r → τ r = 0)
    (hYt : ∀ t y, Yt t y → Y t y) (hKB : 0 < KB)
    {eB gB : ℝ} (heB : 0 ≤ eB) (hkzero : ∀ v, v ≤ eB → k v = 0)
    (hgB : gB ≤ eB) (hρBclose : ∀ r, gB ≤ r → ρB r = 0) :
    let F := fun σ => correctionAtom I τ KF Kc f (G σ) X Z Zt Q hF ρF (g σ) (drawF σ)
    let F' := fun σ => correctionAtom I τ KF Kc f (G' σ) X Z Zt Q hF ρF (g' σ) (drawF σ)
    let B := fun σ => denseAtom Y Yt k hB ρB KB b (H σ) (drawB σ)
    let B' := fun σ => denseAtom Y Yt k hB ρB KB b (H' σ) (drawB σ)
    Cslib.rootDistPow s N u (fun σ x => X (drawF σ).1 x) (fun σ y => Yt (drawB σ) y)
        (fun σ x y => ∑ z ∈ ({z | Zt (drawF σ).2 z} : Finset V), F σ x z * B σ z y)
        (fun σ x y => ∑ z ∈ ({z | Zt (drawF σ).2 z} : Finset V), F' σ x z * B' σ z y) ≤
      (2 ^ (2 * (s - 1)) * (s : ℝ) ^ s) *
        ((2 * AB) * KB * Cslib.rootDistPow s N u (fun σ x => X (drawF σ).1 x)
            (fun σ z => Zt (drawF σ).2 z) F F' +
          (2 * AF) * Kc * (f / u) * Cslib.rootDistPow s N f (fun σ z => Zt (drawF σ).2 z)
            (fun σ y => Yt (drawB σ) y) B B') := by
  classical
  dsimp only
  refine Cslib.rootDistPow_mul_le hs hN hu hf
    (fun σ => nonneg_correctionAtom hQ0 hρF0 hτ0 (hg0 σ) (drawF σ))
    (fun σ => nonneg_correctionAtom hQ0 hρF0 hτ0 (hg'0 σ) (drawF σ))
    (fun σ => nonneg_denseAtom hk0 hρB0 (drawB σ))
    (fun σ => nonneg_denseAtom hk0 hρB0 (drawB σ))
    (by positivity) (by positivity) ?_ ?_ ?_ ?_
  · intro σ x z
    calc
      _ ≤ |correctionAtom I τ KF Kc f (G' σ) X Z Zt Q hF ρF (g' σ) (drawF σ) x z| :=
        le_abs_self _
      _ ≤ 2 * |Q (G' σ x z / f)| * |g' σ z| := abs_correctionAtom_le hρF0 hρF1 hτ0 hτ1 _ _ _
      _ = 2 * Q (G' σ x z / f) * g' σ z := by
        rw [abs_of_nonneg (hQ0 _), abs_of_nonneg (hg'0 _ _)]
      _ ≤ (2 * AF) * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left (hQbound σ x z) (by norm_num)) (hg'1 σ z) (hg'0 σ z)
        (by positivity)
      _ = _ := mul_one _
  · intro σ z y
    calc
      _ ≤ |denseAtom Y Yt k hB ρB KB b (H σ) (drawB σ) z y| := le_abs_self _
      _ ≤ 2 * |k (H σ z y / b)| := abs_denseAtom_le hρB0 hρB1 _ _ _
      _ = 2 * k (H σ z y / b) := by rw [abs_of_nonneg (hk0 _)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hkbound σ z y) (by norm_num)
  · intro σ z _
    refine (card_le_card ?_).trans
      (card_filter_denseAtom_ne_zero_lt (h := hB) (a := b) (G := H σ)
        hYt hKB heB hkzero hgB hρBclose (drawB σ) z).le
    intro y hy
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2⟩
  · intro σ z _
    exact (card_filter_correctionAtom_col_ne_zero_lt hKc hIQ hgF hτclose (drawF σ) z).le

end Matrix
