/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Bonami
public import Complexity.Foundations.Data.Finset.PaleyZygmund

/-!
# Low-degree functions are anticoncentrated

A real function `f` of degree at most `k` on the cube is `9 ^ k`-reasonable by the Bonami Lemma
(`BitString.expect_pow_four_le`), and so is `f - 𝔼 f`. Paley–Zygmund for reasonable random
variables (`Fintype.sq_one_sub_sq_le_mul_dens_of_expect_pow_four_le`) then shows that a nonconstant
low-degree function is not concentrated around its mean: with `μ = 𝔼 f` and `σ ^ 2 = Var f`,
`Pr[|f - μ| > t σ] ≥ (1 - t ^ 2) ^ 2 / 9 ^ k` for `t ∈ [0, 1]`
(`BitString.sq_one_sub_sq_div_nine_pow_le_dens_lt_abs_sub`), in particular
`Pr[|f - μ| > σ / 2] ≥ 9 ^ (1 - k) / 16` (`BitString.nine_div_sixteen_div_nine_pow_le_dens`)
[O'Donnell, Theorem 9.7][ODonnell2014]. The variance is written `𝔼 (f - 𝔼 f) ^ 2`, and
`0 < Var f` says that `f` is nonconstant.

## Main results

* `Cslib.BitString.sq_one_sub_sq_div_nine_pow_le_dens_lt_abs_sub`:
  `Pr[|f - μ| > t σ] ≥ (1 - t ^ 2) ^ 2 / 9 ^ k` for `f` of degree at most `k`.
* `Cslib.BitString.nine_div_sixteen_div_nine_pow_le_dens`: the case `t = 1 / 2`, Theorem 9.7.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Low-degree functions are anticoncentrated**: if `f` has degree at most `k` and positive
variance `σ ^ 2 = 𝔼 (f - μ) ^ 2`, where `μ = 𝔼 f`, then
`Pr[|f - μ| > t σ] ≥ (1 - t ^ 2) ^ 2 / 9 ^ k` for every `t ∈ [0, 1]`. This is the proof of
[O'Donnell, Theorem 9.7][ODonnell2014] for a general threshold `t`: `f - μ` is `9 ^ k`-reasonable
by the Bonami Lemma, and Paley–Zygmund applies. -/
theorem sq_one_sub_sq_div_nine_pow_le_dens_lt_abs_sub {k : ℕ} {f : (ι → Bool) → ℝ}
    (hf : f ∈ lowDegree ℝ ι k) (hV : 0 < 𝔼 x, (f x - 𝔼 y, f y) ^ 2) {t : ℝ} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    (1 - t ^ 2) ^ 2 / 9 ^ k ≤
      (dens {x | t * √(𝔼 z, (f z - 𝔼 y, f y) ^ 2) < |f x - 𝔼 y, f y|} : ℝ) := by
  have hg : (fun x => f x - 𝔼 y, f y) ∈ lowDegree ℝ ι k :=
    Submodule.sub_mem _ hf (const_mem_lowDegree k _)
  rw [div_le_iff₀ (by positivity), mul_comm]
  exact Fintype.sq_one_sub_sq_le_mul_dens_of_expect_pow_four_le (expect_pow_four_le hg) hV ht₀ ht₁

/-- **Theorem 9.7**: a nonconstant function `f` of degree at most `k` deviates from its mean `μ`
by more than half its standard deviation `σ` with probability at least `9 ^ (1 - k) / 16`,
written `9 / 16 / 9 ^ k` [O'Donnell, Theorem 9.7][ODonnell2014]. -/
theorem nine_div_sixteen_div_nine_pow_le_dens {k : ℕ} {f : (ι → Bool) → ℝ}
    (hf : f ∈ lowDegree ℝ ι k) (hV : 0 < 𝔼 x, (f x - 𝔼 y, f y) ^ 2) :
    9 / 16 / 9 ^ k ≤
      (dens {x | √(𝔼 z, (f z - 𝔼 y, f y) ^ 2) / 2 < |f x - 𝔼 y, f y|} : ℝ) := by
  have h := sq_one_sub_sq_div_nine_pow_le_dens_lt_abs_sub hf hV (t := 1 / 2) (by norm_num)
    (by norm_num)
  simp only [one_div_mul_eq_div] at h
  calc (9 / 16 / 9 ^ k : ℝ) = (1 - (1 / 2) ^ 2) ^ 2 / 9 ^ k := by norm_num
    _ ≤ _ := h

end Cslib.BitString
