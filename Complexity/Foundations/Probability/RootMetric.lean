/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Foundations.Analysis.RootError
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Integrated norms and root metrics of random tables

The estimators of the OpenAI preprint compare random row tables and vertex arrays by integrated
`s`-th power norms over a shared environment `σ` [OpenAI2026LogSpace, Section 5.6]. Let `σ` range
uniformly over a finite type `Ω`, let `X` and `Y` be channels (`X σ x` means that `x` is retained
on the draw `σ`), and fix a normalization `N` and a nominal rate `u`. For a random table
`Z : Ω → V → V → ℝ` and a random vertex array `v : Ω → V → ℝ`,

* `‖Z‖^s_{u,a;s} = (N u)⁻¹ 𝔼_σ ∑_{X σ x} ∑_{Y σ y} |Z σ x y|^s` (`Cslib.rowNormPow`, (5.19));
* `d_{u,a}(H, H')^s = ‖H^{1/s} - H'^{1/s}‖^s_{u,a;s}` (`Cslib.rootDistPow`, (5.19));
* `‖v‖^s_{u;s} = (N u)⁻¹ 𝔼_σ ∑_{X σ x} |v σ x|^s` (`Cslib.vertexNormPow`, (5.20)).

Here the channel `Y` plays the role of the preprint's `Y_a`, and values outside the retained sets
are ignored, which is the preprint's convention of extending them by zero. We work with the
`s`-th powers of the norms throughout, as every estimate of the preprint does.

The ordinary norm of a difference of bounded nonnegative tables is controlled by their root
distance (`Cslib.rowNormPow_sub_le_rootDistPow`, from (5.21)). A table with bounded values and
fewer than `K` nonzero entries per retained row has norm at most `K B^s ‖1‖^s_{u;s}`
(`Cslib.rowNormPow_le_of_card_le`). This is the uniform bound of [OpenAI2026LogSpace, Section 5.6].

## Main definitions

* `Cslib.rowNormPow`, `Cslib.rootDistPow`, `Cslib.vertexNormPow`.

## Main results

* `Cslib.rowNormPow_nonneg`, `Cslib.vertexNormPow_nonneg`, `Cslib.rootDistPow_comm`,
  `Cslib.rootDistPow_self`: basic properties.
* `Cslib.rowNormPow_le_mul`: comparison of norms from a pointwise comparison.
* `Cslib.rowNormPow_sub_le_rootDistPow`: ordinary error is controlled by root error.
* `Cslib.rowNormPow_le_of_card_le`: the uniform bound for bounded sparse tables.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 5.6, (5.19)–(5.21) (preprint, not peer reviewed)
-/

public section

open Finset
open scoped BigOperators

namespace Cslib

variable {Ω V : Type*} [Fintype Ω] [Fintype V]

section Definitions

variable (s : ℕ) (N u : ℝ) (X Y : Ω → V → Prop) [∀ σ v, Decidable (X σ v)]
  [∀ σ v, Decidable (Y σ v)]

/-- The `s`-th power `‖Z‖^s_{u,a;s}` of the integrated row norm of a random table
[OpenAI2026LogSpace, (5.19)]. -/
@[expose] noncomputable def rowNormPow (Z : Ω → V → V → ℝ) : ℝ :=
  (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V), |Z σ x y| ^ s

/-- The `s`-th power `d_{u,a}(H, H')^s` of the root distance of two random tables
[OpenAI2026LogSpace, (5.19)]. -/
noncomputable def rootDistPow (H H' : Ω → V → V → ℝ) : ℝ :=
  rowNormPow s N u X Y fun σ x y => H σ x y ^ (s⁻¹ : ℝ) - H' σ x y ^ (s⁻¹ : ℝ)

/-- The `s`-th power `‖v‖^s_{u;s}` of the integrated norm of a random vertex array
[OpenAI2026LogSpace, (5.20)]. -/
@[expose] noncomputable def vertexNormPow (v : Ω → V → ℝ) : ℝ :=
  (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V), |v σ x| ^ s

end Definitions

variable {s : ℕ} {N u : ℝ} {X Y : Ω → V → Prop} [∀ σ v, Decidable (X σ v)]
  [∀ σ v, Decidable (Y σ v)]

theorem rowNormPow_nonneg (hNu : 0 ≤ N * u) (Z : Ω → V → V → ℝ) : 0 ≤ rowNormPow s N u X Y Z := by
  unfold rowNormPow; positivity

theorem vertexNormPow_nonneg (hNu : 0 ≤ N * u) (v : Ω → V → ℝ) :
    0 ≤ vertexNormPow s N u X v := by
  unfold vertexNormPow; positivity

theorem rootDistPow_comm (H H' : Ω → V → V → ℝ) :
    rootDistPow s N u X Y H H' = rootDistPow s N u X Y H' H := by
  simp only [rootDistPow, rowNormPow, abs_sub_comm]

@[simp]
theorem rootDistPow_self (hs : s ≠ 0) (H : Ω → V → V → ℝ) : rootDistPow s N u X Y H H = 0 := by
  simp [rootDistPow, rowNormPow, hs]

/-- A pointwise comparison of `s`-th powers on the retained pairs gives a comparison of the
norms. -/
theorem rowNormPow_le_mul (hNu : 0 ≤ N * u) {c : ℝ} {Z Z' : Ω → V → V → ℝ}
    (h : ∀ σ x y, X σ x → Y σ y → |Z σ x y| ^ s ≤ c * |Z' σ x y| ^ s) :
    rowNormPow s N u X Y Z ≤ c * rowNormPow s N u X Y Z' := by
  unfold rowNormPow
  calc (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V),
        |Z σ x y| ^ s
      ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V),
        c * |Z' σ x y| ^ s := by
        refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.2 hNu)
        refine sum_le_sum fun x hx => sum_le_sum fun y hy => ?_
        simp only [mem_filter, mem_univ, true_and] at hx hy
        exact h σ x y hx hy
    _ = _ := by simp only [← mul_sum, ← mul_expect]; ring

/-- **Ordinary error is controlled by root error** [OpenAI2026LogSpace, (5.21)], integrated: for
tables with values in `[0, C]` on the retained pairs,
`‖H - H'‖^s ≤ (s C^{(s-1)/s})^s d(H, H')^s`. -/
theorem rowNormPow_sub_le_rootDistPow (hs : s ≠ 0) (hNu : 0 ≤ N * u) {C : ℝ}
    {H H' : Ω → V → V → ℝ}
    (hH : ∀ σ x y, X σ x → Y σ y → 0 ≤ H σ x y ∧ H σ x y ≤ C)
    (hH' : ∀ σ x y, X σ x → Y σ y → 0 ≤ H' σ x y ∧ H' σ x y ≤ C) :
    rowNormPow s N u X Y (fun σ x y => H σ x y - H' σ x y) ≤
      (s * C ^ (((s : ℝ) - 1) / s)) ^ s * rootDistPow s N u X Y H H' := by
  refine rowNormPow_le_mul hNu fun σ x y hx hy => ?_
  obtain ⟨h0, h1⟩ := hH σ x y hx hy
  obtain ⟨h0', h1'⟩ := hH' σ x y hx hy
  have hk : 0 ≤ (s : ℝ) * C ^ (((s : ℝ) - 1) / s) :=
    mul_nonneg (Nat.cast_nonneg s) (Real.rpow_nonneg (h0.trans h1) _)
  rw [← mul_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub_le_mul_abs_rpow_inv_sub hs h0 h0' h1 h1') s

/-- **The uniform bound** [OpenAI2026LogSpace, Section 5.6]. A table with values bounded by `B`
and at most `K` nonzero entries in each retained row has `‖Z‖^s ≤ K B^s ‖1‖^s`. -/
theorem rowNormPow_le_of_card_le (hs : s ≠ 0) (hNu : 0 ≤ N * u) {B : ℝ} (hB0 : 0 ≤ B) {K : ℕ}
    {Z : Ω → V → V → ℝ} (hB : ∀ σ x y, |Z σ x y| ≤ B)
    (hK : ∀ σ x, X σ x → #{y ∈ ({y | Y σ y} : Finset V) | Z σ x y ≠ 0} ≤ K) :
    rowNormPow s N u X Y Z ≤ K * B ^ s * vertexNormPow s N u X fun _ _ => 1 := by
  unfold rowNormPow vertexNormPow
  have hrow : ∀ σ, ∀ x ∈ ({x | X σ x} : Finset V),
      ∑ y ∈ ({y | Y σ y} : Finset V), |Z σ x y| ^ s ≤ K * B ^ s := fun σ x hx => by
    simp only [mem_filter, mem_univ, true_and] at hx
    rw [← sum_filter_of_ne (p := fun y => Z σ x y ≠ 0) fun y _ h hy =>
      h (by rw [hy, abs_zero, zero_pow hs])]
    calc ∑ y ∈ ({y | Y σ y} : Finset V) with Z σ x y ≠ 0, |Z σ x y| ^ s
        ≤ ∑ y ∈ ({y | Y σ y} : Finset V) with Z σ x y ≠ 0, B ^ s :=
          sum_le_sum fun y _ => pow_le_pow_left₀ (abs_nonneg _) (hB σ x y) s
      _ ≤ K * B ^ s := by
          rw [sum_const, nsmul_eq_mul]
          gcongr
          exact_mod_cast hK σ x hx
  calc (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V),
        |Z σ x y| ^ s
      ≤ (N * u)⁻¹ * 𝔼 σ, (#({x | X σ x} : Finset V) : ℝ) * (K * B ^ s) := by
        refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.2 hNu)
        rw [← nsmul_eq_mul, ← sum_const]
        exact sum_le_sum (hrow σ)
    _ = _ := by
        rw [← expect_mul]
        simp only [abs_one, one_pow, sum_const, nsmul_eq_mul, mul_one]
        ring

end Cslib
