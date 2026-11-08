/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Basic
public import Complexity.Foundations.Data.BitString.ZModTwo
public import Mathlib.Algebra.QuadraticAlgebra.Basic
import Complexity.Probability.PMF.Uniform

/-!
# Exact fair-bit sampling in the four-element field

Mathlib's `QuadraticAlgebra (ZMod 2) 1 1` represents the field with generator satisfying
`θ² = 1 + θ`. Its two coordinates are independent bits. The sampler draws those two bits
and returns the corresponding element of the existing quadratic algebra; no new field carrier
or arithmetic is defined here. This is one fixed field, not a growing extension-field family.

## Main definitions

* `Cslib.F4.equivBits`: the two Boolean coordinates of the quadratic algebra.
* `Cslib.F4.sample`: two independent fair bits interpreted in that field.

## Main results

* `Cslib.F4.card`: the field has four elements.
* `Cslib.F4.eval_sample`: the sampler is exactly uniform.
-/

public section

namespace Cslib.F4

open Probability

/-- Boolean coordinates in the basis `1, θ`, where `θ² = 1 + θ`. -/
@[expose] def equivBits : QuadraticAlgebra (ZMod 2) 1 1 ≃ Bool × Bool :=
  (QuadraticAlgebra.equivProd 1 1).trans
    (Equiv.prodCongr BitString.bitEquiv.toEquiv BitString.bitEquiv.toEquiv)

instance instFintype : Fintype (QuadraticAlgebra (ZMod 2) 1 1) :=
  Fintype.ofEquiv (Bool × Bool) equivBits.symm

/-- The polynomial `X² + X + 1` has no root over the two-element field, enabling Mathlib's
existing field instance for this quadratic algebra. -/
instance instFactNoRoot : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) := ⟨by decide⟩

/-- The quadratic algebra over two bits has exactly four elements. -/
theorem card : Fintype.card (QuadraticAlgebra (ZMod 2) 1 1) = 4 :=
  (Fintype.card_congr equivBits).trans (by decide)

/-- Sample the real and imaginary coordinates using two independent fair bits. -/
@[expose] noncomputable def sample : ProbComp (QuadraticAlgebra (ZMod 2) 1 1) := do
  let re ← ProbComp.uniform Bool
  let im ← ProbComp.uniform Bool
  return equivBits.symm (re, im)

/-- The two-fair-bit program has the exact uniform field distribution. -/
theorem eval_sample : ProbComp.eval sample =
    PMF.uniformOfFintype (QuadraticAlgebra (ZMod 2) 1 1) := by
  rw [sample, ProbComp.eval_bind]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform]
  rw [← Probability.PMF.uniformOfFintype_map_equiv equivBits.symm,
    ← Probability.PMF.uniformOfFintype_prod, PMF.map_bind]
  simp only [PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind]

end Cslib.F4
