/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, near `Mathlib/LinearAlgebra/Reflection.lean`)

public import Complexity.Init
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Two reflections rotate a plane

Let `a` and `e` span a plane in a module over `ℝ` or `ℂ`, and write `v(φ) = cos φ • a + sin φ • e`
for the vector at angle `φ` from `a` towards `e`. Suppose a linear map `R_a` negates `a` and fixes
`e`, and a linear map `R_b` negates `b = v(π/2 - γ)` and fixes the vector `v(-γ)` orthogonal to it.
Then `R_b R_a` maps `v(φ)` to `-v(φ - 2γ)`
(`Cslib.LinearAlgebra.reflection_comp_reflection`), so `T` rounds map `v(φ)` to
`(-1)^T v(φ - 2Tγ)` (`Cslib.LinearAlgebra.iterate_reflection_comp_reflection`). The hypotheses
mention only the plane, so they can be checked one vector at a time in a larger space; no inner
product is assumed. Mathlib's `Module.reflection_mul_reflection_pow_apply` computes the powers of a
product of two `Module.reflection`s through Chebyshev polynomials; it is not used here because
`R_a` and `R_b` are arbitrary linear maps, constrained only on the plane.

This is the geometry of Grover's algorithm, as Shi uses it to rotate a state that is almost
orthogonal to `a` onto a chosen real direction [Shi][Shi2003], §4.2 (proof of Lemma 4.5, Figure 1).
There `a = 0̂`, `e = 1̂` and `b = 1̃`, and `R_a` is `Λ̄(σ_z)`, Shi's reflection along `1̂`. Shi's
reflection along `1̃` is `R = T_θ^{⊗k} (-Λ̄(σ_z)) T_θ^{⊗k}`, which fixes `1̃`. The map `R_b` here
negates `1̃` instead: it is `T_θ^{⊗k} Λ̄(σ_z) T_θ^{⊗k} = -R`. Hence Shi's Grover iterate is
`(R Λ̄(σ_z))^T = (-1)^T (R_b R_a)^T`, which maps `v(φ)` to `v(φ - 2Tγ)`; the sign `(-1)^T` comes
from negating `b` here rather than fixing it.

## Main results

* `Cslib.LinearAlgebra.reflection_comp_reflection`: one round of two reflections.
* `Cslib.LinearAlgebra.iterate_reflection_comp_reflection`: `T` rounds.

## References

* [Y. Shi, *Both Toffoli and Controlled-NOT need little help to do universal quantum
  computation*][Shi2003], §4.2 (arXiv:quant-ph/0205115v2)
-/

public section

namespace Cslib.LinearAlgebra

variable {K E : Type*} [RCLike K] [AddCommGroup E] [Module K E]

/-- **Two reflections rotate a plane.** Let `Ra` negate `a` and fix `e`, and let `Rb` negate
`sin γ • a + cos γ • e` and fix `cos γ • a - sin γ • e`. Then `Rb ∘ Ra` maps the vector at angle `φ`
from `a` towards `e` to minus the vector at angle `φ - 2γ`. -/
theorem reflection_comp_reflection (Ra Rb : E →ₗ[K] E) {a e : E} {γ : ℝ}
    (ha : Ra a = -a) (he : Ra e = e)
    (hb : Rb ((Real.sin γ : K) • a + (Real.cos γ : K) • e) =
      -((Real.sin γ : K) • a + (Real.cos γ : K) • e))
    (hb' : Rb ((Real.cos γ : K) • a - (Real.sin γ : K) • e) =
      (Real.cos γ : K) • a - (Real.sin γ : K) • e) (φ : ℝ) :
    Rb (Ra ((Real.cos φ : K) • a + (Real.sin φ : K) • e)) =
      -((Real.cos (φ - 2 * γ) : K) • a + (Real.sin (φ - 2 * γ) : K) • e) := by
  have hsc : (Real.sin γ : K) ^ 2 + (Real.cos γ : K) ^ 2 = 1 := by
    rw [← RCLike.ofReal_pow, ← RCLike.ofReal_pow, ← RCLike.ofReal_add,
      Real.sin_sq_add_cos_sq, RCLike.ofReal_one]
  have hea : (Real.sin γ : K) • ((Real.sin γ : K) • a + (Real.cos γ : K) • e) +
      (Real.cos γ : K) • ((Real.cos γ : K) • a - (Real.sin γ : K) • e) = a := by
    linear_combination (norm := module) hsc • a
  have hee : (Real.cos γ : K) • ((Real.sin γ : K) • a + (Real.cos γ : K) • e) -
      (Real.sin γ : K) • ((Real.cos γ : K) • a - (Real.sin γ : K) • e) = e := by
    linear_combination (norm := module) hsc • e
  have hRa : Rb a = -((Real.sin γ : K) • ((Real.sin γ : K) • a + (Real.cos γ : K) • e)) +
      (Real.cos γ : K) • ((Real.cos γ : K) • a - (Real.sin γ : K) • e) := by
    conv_lhs => rw [← hea]
    rw [map_add, map_smul, map_smul, hb, hb', smul_neg]
  have hRe : Rb e = -((Real.cos γ : K) • ((Real.sin γ : K) • a + (Real.cos γ : K) • e)) -
      (Real.sin γ : K) • ((Real.cos γ : K) • a - (Real.sin γ : K) • e) := by
    conv_lhs => rw [← hee]
    rw [map_sub, map_smul, map_smul, hb, hb', smul_neg]
  rw [map_add, map_smul, map_smul, ha, he, map_add, map_smul, map_smul, map_neg, hRa, hRe,
    Real.cos_sub, Real.sin_sub, Real.cos_two_mul, Real.sin_two_mul]
  push_cast
  linear_combination (norm := module) hsc • ((Real.cos φ : K) • a + (Real.sin φ : K) • e)

/-- **Iterated reflections rotate a plane**, the geometry of Grover's algorithm: `T` rounds of
`Rb ∘ Ra` move the vector at angle `φ` to `(-1) ^ T` times the vector at angle `φ - 2Tγ`. -/
theorem iterate_reflection_comp_reflection (Ra Rb : E →ₗ[K] E) {a e : E} {γ : ℝ}
    (ha : Ra a = -a) (he : Ra e = e)
    (hb : Rb ((Real.sin γ : K) • a + (Real.cos γ : K) • e) =
      -((Real.sin γ : K) • a + (Real.cos γ : K) • e))
    (hb' : Rb ((Real.cos γ : K) • a - (Real.sin γ : K) • e) =
      (Real.cos γ : K) • a - (Real.sin γ : K) • e) (T : ℕ) (φ : ℝ) :
    (fun v => Rb (Ra v))^[T] ((Real.cos φ : K) • a + (Real.sin φ : K) • e) =
      (-1 : K) ^ T • ((Real.cos (φ - 2 * T * γ) : K) • a +
        (Real.sin (φ - 2 * T * γ) : K) • e) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hφ : φ - 2 * T * γ - 2 * γ = φ - 2 * ((T + 1 : ℕ) : ℝ) * γ := by
      push_cast
      ring
    rw [Function.iterate_succ_apply', ih, map_smul, map_smul,
      reflection_comp_reflection Ra Rb ha he hb hb', hφ, pow_succ, mul_neg_one, neg_smul,
      smul_neg]

end Cslib.LinearAlgebra
