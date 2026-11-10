/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/Order/BigOperators/Expect.lean`)

public import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# The Paley–Zygmund inequality and reasonable random variables

A nonnegative function `f` on a finite type, with values in an ordered field, exceeds a fraction
`θ` of its uniform average on a set of density at least `(1 - θ) ^ 2 (𝔼 f) ^ 2 / 𝔼 f ^ 2`: this is
the **Paley–Zygmund inequality** (`Fintype.sq_one_sub_mul_expect_le_dens_mul_expect_sq`), the
"second moment method" of [O'Donnell, Section 9.1][ODonnell2014]. Its case `θ = 0` is the second
moment method `Fintype.sq_expect_le_dens_mul_expect_sq`.

A real random variable `X` is `B`-*reasonable* when `𝔼 X ^ 4 ≤ B (𝔼 X ^ 2) ^ 2`
[O'Donnell, Definition 9.1][ODonnell2014]. We do not introduce a predicate for it: the results
below take the inequality as a hypothesis, for a function on a finite type under the uniform
distribution. Reasonable random variables satisfy a tail bound better than Chebyshev's
(`Fintype.pow_four_mul_dens_le_of_expect_pow_four_le`, [O'Donnell, Proposition 9.3][ODonnell2014])
and, by Paley–Zygmund, an anticoncentration bound
(`Fintype.sq_one_sub_sq_le_mul_dens_of_expect_pow_four_le`,
[O'Donnell, Proposition 9.4][ODonnell2014]). A function taking each of its values with probability
at least `λ` is `1 / λ`-reasonable (`Fintype.mul_expect_pow_four_le_of_le_dens`,
[O'Donnell, Proposition 9.5][ODonnell2014]). Paley–Zygmund and Proposition 9.5 hold in any ordered
field; Propositions 9.3 and 9.4 are stated over `ℝ`, since they normalise by `‖X‖₂ = √(𝔼 X ^ 2)`.

## Main results

* `Fintype.sq_one_sub_mul_expect_le_dens_mul_expect_sq`: the Paley–Zygmund inequality.
* `Fintype.pow_four_mul_dens_le_of_expect_pow_four_le`: `Pr[|X| ≥ t ‖X‖₂] ≤ B / t ^ 4`.
* `Fintype.sq_one_sub_sq_le_mul_dens_of_expect_pow_four_le`:
  `Pr[|X| > t ‖X‖₂] ≥ (1 - t ^ 2) ^ 2 / B` for `t ∈ [0, 1]`.
* `Fintype.mul_expect_pow_four_le_of_le_dens`: minimum probability `λ` gives `1 / λ`-reasonable.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open Finset
open scoped BigOperators

namespace Fintype

variable {ι : Type*} [Fintype ι] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **The Paley–Zygmund inequality** for a uniform average: if `f` is nonnegative and
`0 ≤ θ ≤ 1`, then `((1 - θ) 𝔼 f) ^ 2 ≤ Pr[f > θ 𝔼 f] · 𝔼 f ^ 2`
[O'Donnell, Section 9.1][ODonnell2014]. -/
theorem sq_one_sub_mul_expect_le_dens_mul_expect_sq {f : ι → 𝕜} (hf : ∀ i, 0 ≤ f i) {θ : 𝕜}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    ((1 - θ) * 𝔼 i, f i) ^ 2 ≤ (dens {i | θ * 𝔼 j, f j < f i} : 𝕜) * 𝔼 i, f i ^ 2 := by
  classical
  set μ := 𝔼 j, f j with hμ
  have hμ0 : 0 ≤ μ := expect_nonneg fun i _ => hf i
  set E : ι → 𝕜 := fun i => if θ * μ < f i then 1 else 0 with hE
  -- `μ ≤ θ μ + 𝔼 E f`, splitting the mean at the threshold `θ μ`
  have hsplit : μ ≤ θ * μ + 𝔼 i, E i * f i := by
    cases isEmpty_or_nonempty ι with
    | inl h => simp [hμ, Finset.univ_eq_empty]
    | inr h =>
      have hpt (i : ι) : f i ≤ θ * μ + E i * f i := by
        simp only [hE]
        split_ifs with hi
        · linarith [mul_nonneg hθ₀ hμ0]
        · push Not at hi
          linarith
      calc μ = 𝔼 i, f i := rfl
        _ ≤ 𝔼 i, (θ * μ + E i * f i) := expect_le_expect fun i _ => hpt i
        _ = θ * μ + 𝔼 i, E i * f i := by rw [expect_add_distrib, Fintype.expect_const]
  have hlow : 0 ≤ (1 - θ) * μ := mul_nonneg (by linarith) hμ0
  have hle : (1 - θ) * μ ≤ 𝔼 i, E i * f i := by linarith
  have hcs := expect_mul_sq_le_sq_mul_sq univ E f
  have hE2 : 𝔼 i, E i ^ 2 = (dens {i | θ * μ < f i} : 𝕜) := Fintype.expect_boole_sq _
  rw [hE2] at hcs
  calc ((1 - θ) * μ) ^ 2 ≤ (𝔼 i, E i * f i) ^ 2 := pow_le_pow_left₀ hlow hle 2
    _ ≤ _ := hcs

/-- **Reasonable random variables have light tails**: if `𝔼 f ^ 4 ≤ B (𝔼 f ^ 2) ^ 2` and
`f ≢ 0`, then `Pr[|f| ≥ t ‖f‖₂] ≤ B / t ^ 4` for `t ≥ 0`, in the form
`t ^ 4 Pr[|f| ≥ t ‖f‖₂] ≤ B` [O'Donnell, Proposition 9.3][ODonnell2014]. -/
theorem pow_four_mul_dens_le_of_expect_pow_four_le {f : ι → ℝ} {B : ℝ}
    (hB : 𝔼 i, f i ^ 4 ≤ B * (𝔼 i, f i ^ 2) ^ 2) (hf : 0 < 𝔼 i, f i ^ 2) {t : ℝ} (ht : 0 ≤ t) :
    t ^ 4 * (dens {i | t * √(𝔼 j, f j ^ 2) ≤ |f i|} : ℝ) ≤ B := by
  classical
  set m := 𝔼 j, f j ^ 2 with hm
  have hmk := Fintype.mul_dens_filter_le_expect (f := fun i => f i ^ 4)
    (fun i => by positivity) (t ^ 4 * m ^ 2)
  have hsub : ({i | t * √m ≤ |f i|} : Finset ι) ⊆ ({i | t ^ 4 * m ^ 2 ≤ f i ^ 4} : Finset ι) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    have h4 := pow_le_pow_left₀ (mul_nonneg ht (Real.sqrt_nonneg _)) hi 4
    rwa [mul_pow, show √m ^ 4 = (√m ^ 2) ^ 2 by ring, Real.sq_sqrt hf.le,
      show |f i| ^ 4 = (|f i| ^ 2) ^ 2 by ring, sq_abs, ← pow_mul] at h4
  have hd : (dens ({i | t * √m ≤ |f i|} : Finset ι) : ℝ) ≤
      (dens ({i | t ^ 4 * m ^ 2 ≤ f i ^ 4} : Finset ι) : ℝ) := by
    exact_mod_cast dens_le_dens hsub
  refine le_of_mul_le_mul_right ?_ (pow_pos hf 2)
  calc t ^ 4 * (dens {i | t * √m ≤ |f i|} : ℝ) * m ^ 2
      ≤ t ^ 4 * m ^ 2 * (dens {i | t ^ 4 * m ^ 2 ≤ f i ^ 4} : ℝ) := by
        rw [mul_right_comm]; exact mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ 𝔼 i, f i ^ 4 := hmk
    _ ≤ B * m ^ 2 := hB

/-- **Reasonable random variables are anticoncentrated**: if `𝔼 f ^ 4 ≤ B (𝔼 f ^ 2) ^ 2` and
`f ≢ 0`, then `Pr[|f| > t ‖f‖₂] ≥ (1 - t ^ 2) ^ 2 / B` for `t ∈ [0, 1]`, in the form
`(1 - t ^ 2) ^ 2 ≤ B Pr[|f| > t ‖f‖₂]` [O'Donnell, Proposition 9.4][ODonnell2014]. The proof
applies Paley–Zygmund to `f ^ 2`. -/
theorem sq_one_sub_sq_le_mul_dens_of_expect_pow_four_le {f : ι → ℝ} {B : ℝ}
    (hB : 𝔼 i, f i ^ 4 ≤ B * (𝔼 i, f i ^ 2) ^ 2) (hf : 0 < 𝔼 i, f i ^ 2) {t : ℝ} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    (1 - t ^ 2) ^ 2 ≤ B * (dens {i | t * √(𝔼 j, f j ^ 2) < |f i|} : ℝ) := by
  classical
  set m := 𝔼 j, f j ^ 2 with hm
  have hpz := sq_one_sub_mul_expect_le_dens_mul_expect_sq (f := fun i => f i ^ 2)
    (fun i => sq_nonneg _) (θ := t ^ 2) (sq_nonneg t) (by nlinarith)
  rw [← hm] at hpz
  have hset : ({i | t ^ 2 * m < f i ^ 2} : Finset ι) = ({i | t * √m < |f i|} : Finset ι) := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    rw [← sq_lt_sq₀ (mul_nonneg ht₀ (Real.sqrt_nonneg _)) (abs_nonneg _), sq_abs, mul_pow,
      Real.sq_sqrt hf.le]
  have h44 : 𝔼 i, (f i ^ 2) ^ 2 = 𝔼 i, f i ^ 4 := expect_congr rfl fun i _ => by ring
  rw [hset, h44] at hpz
  refine le_of_mul_le_mul_right ?_ (pow_pos hf 2)
  calc (1 - t ^ 2) ^ 2 * m ^ 2 = ((1 - t ^ 2) * m) ^ 2 := by ring
    _ ≤ _ := hpz
    _ ≤ (dens {i | t * √m < |f i|} : ℝ) * (B * m ^ 2) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    _ = _ := by ring

/-- **A random variable with no rare values is reasonable**: if `f` takes each of its values with
probability at least `l`, then `l 𝔼 f ^ 4 ≤ (𝔼 f ^ 2) ^ 2`, so `f` is `1 / l`-reasonable when
`l > 0` [O'Donnell, Proposition 9.5][ODonnell2014]. -/
theorem mul_expect_pow_four_le_of_le_dens {f : ι → 𝕜} {l : 𝕜}
    (hl : ∀ i, l ≤ (dens {j | f j = f i} : 𝕜)) :
    l * 𝔼 i, f i ^ 4 ≤ (𝔼 i, f i ^ 2) ^ 2 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => simp [Finset.univ_eq_empty]
  | inr h =>
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image univ (fun i => f i ^ 2) univ_nonempty
    set M := f i₀ ^ 2
    have hm0 : 0 ≤ 𝔼 i, f i ^ 2 := expect_nonneg fun i _ => sq_nonneg _
    -- `𝔼 f ^ 4 ≤ M 𝔼 f ^ 2`, where `M = ‖f‖_∞ ^ 2`
    have h4 : 𝔼 i, f i ^ 4 ≤ M * 𝔼 i, f i ^ 2 := by
      rw [mul_expect]
      exact expect_le_expect fun i _ => by
        rw [show f i ^ 4 = f i ^ 2 * f i ^ 2 by ring]
        exact mul_le_mul_of_nonneg_right (hi₀ i (mem_univ _)) (sq_nonneg _)
    -- `l M ≤ 𝔼 f ^ 2`, since `f ^ 2 = M` with probability at least `l`
    have hlM : l * M ≤ 𝔼 i, f i ^ 2 := by
      have hmk := Fintype.mul_dens_filter_le_expect (f := fun i => f i ^ 2)
        (fun i => sq_nonneg _) M
      have hsub : ({j | f j = f i₀} : Finset ι) ⊆ ({i | M ≤ f i ^ 2} : Finset ι) := by
        intro j hj
        simp only [mem_filter, mem_univ, true_and] at hj ⊢
        rw [hj]
      have hd : (dens ({j | f j = f i₀} : Finset ι) : 𝕜) ≤ (dens {i | M ≤ f i ^ 2} : 𝕜) := by
        exact_mod_cast dens_le_dens hsub
      calc l * M ≤ (dens {j | f j = f i₀} : 𝕜) * M :=
            mul_le_mul_of_nonneg_right (hl i₀) (sq_nonneg _)
        _ ≤ (dens {i | M ≤ f i ^ 2} : 𝕜) * M := mul_le_mul_of_nonneg_right hd (sq_nonneg _)
        _ = M * (dens {i | M ≤ f i ^ 2} : 𝕜) := mul_comm _ _
        _ ≤ _ := hmk
    by_cases hl0 : l ≤ 0
    · have : 0 ≤ 𝔼 i, f i ^ 4 := expect_nonneg fun i _ => by positivity
      nlinarith
    · push Not at hl0
      calc l * 𝔼 i, f i ^ 4 ≤ l * (M * 𝔼 i, f i ^ 2) := mul_le_mul_of_nonneg_left h4 hl0.le
        _ = (l * M) * 𝔼 i, f i ^ 2 := by ring
        _ ≤ (𝔼 i, f i ^ 2) * 𝔼 i, f i ^ 2 := mul_le_mul_of_nonneg_right hlM hm0
        _ = _ := by ring

end Fintype
