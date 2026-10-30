/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Basic
public import Mathlib.Analysis.Real.Sqrt
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.GroupWithZero.Units.Equiv

/-!
# The affine-plane expander

Over a finite field `K`, join `(a, b)` to `(c, a * c - b)` for each label `c`. The reverse
label is `a`, so the rotation is an ordinary arithmetic expression. No graph search or choice
is used. This is the affine-plane construction of [Reingold, Vadhan and Wigderson,
Section 5.1][ReingoldVadhanWigderson2002], with a different involutive edge labelling.

Its two-step walk is the uniform average plus `1 / |K|` times the difference between a
function and its row average. Self-adjointness then bounds the spectral expansion by
`sqrt (1 / |K|)`, without an eigenvalue calculation.

## Main definitions

* `Cslib.RotationMap.affinePlaneRot`: the arithmetic rotation program.
* `Cslib.RotationMap.affinePlane`: a `|K|`-regular graph on `K × K`.

## Main results

* `Cslib.RotationMap.walk_affinePlane_twice`: the exact two-step averaging law.
* `Cslib.RotationMap.spectralExpansion_affinePlane_le`: spectral expansion at most
  `sqrt (1 / |K|)`.

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable (K : Type*) [Field K]

/-- The arithmetic program underlying the affine-plane rotation. -/
def affinePlaneRot (p : (K × K) × K) : (K × K) × K :=
  ((p.2, p.1.1 * p.2 - p.1.2), p.1.1)

/-- The affine-plane graph: `(a, b)` is adjacent to `(c, d)` when `a * c = b + d`.
The edge to first coordinate `c` has label `c`, and its reverse has label `a`. -/
@[reducible]
def affinePlane : RotationMap (K × K) K where
  rot := affinePlaneRot K
  rot_involutive p := by
    rcases p with ⟨⟨a, b⟩, c⟩
    dsimp only [affinePlaneRot]
    congr 2
    ring

/-- The rotation of the affine-plane graph is given directly by field arithmetic. -/
@[simp]
theorem rot_affinePlane (a b c : K) :
    (affinePlane K).rot ((a, b), c) = ((c, a * c - b), a) := rfl

variable [Fintype K]

/-- One step averages over the points on the corresponding affine line. -/
theorem walk_affinePlane (f : K × K → ℝ) (a b : K) :
    (affinePlane K).walk f (a, b) = 𝔼 c, f (c, a * c - b) := rfl

/-- Two affine-plane steps give the uniform mean plus the row-centered value divided by `|K|`.
-/
theorem walk_affinePlane_twice (f : K × K → ℝ) (a b : K) :
    (affinePlane K).walk ((affinePlane K).walk f) (a, b) =
      (𝔼 p, f p) + (f (a, b) - 𝔼 y, f (a, y)) / Fintype.card K := by
  classical
  simp only [walk_affinePlane]
  rw [expect_comm]
  have hrow (d : K) : (𝔼 c, f (d, c * d - (a * c - b))) =
      (𝔼 y, f (d, y)) + if d = a then f (a, b) - 𝔼 y, f (a, y) else 0 := by
    by_cases h : d = a
    · subst d
      simp [show ∀ c : K, c * a - (a * c - b) = b by intro c; ring]
    · simp only [h, ite_false, add_zero]
      refine Fintype.expect_equiv
        ((Equiv.mulRight₀ (d - a) (sub_ne_zero.mpr h)).trans (Equiv.addRight b)) _ _ ?_
      intro c
      congr 2
      change c * d - (a * c - b) = c * (d - a) + b
      ring
  simp only [hrow, expect_add_distrib]
  rw [← Fintype.expect_prod_type, Fintype.expect_ite_eq']
  simp [NNRat.smul_def, div_eq_mul_inv, mul_comm]

/-- The affine-plane graph has spectral expansion at most `sqrt (1 / |K|)`. -/
theorem spectralExpansion_affinePlane_le :
    (affinePlane K).spectralExpansion ≤ Real.sqrt (1 / Fintype.card K) := by
  apply spectralExpansion_le (Real.sqrt_nonneg _)
  intro f hf
  rw [Real.sq_sqrt (by positivity)]
  have hrow : (𝔼 p : K × K, f p * (𝔼 y, f (p.1, y))) =
      𝔼 a, (𝔼 y, f (a, y)) ^ 2 := by
    rw [Fintype.expect_prod_type]
    apply expect_congr rfl
    intro a _
    dsimp only
    rw [← expect_mul]
    ring
  have hself := (affinePlane K).expect_mul_walk_comm f ((affinePlane K).walk f)
  have heq : (𝔼 p, ((affinePlane K).walk f p) ^ 2) =
      ((𝔼 p, f p ^ 2) - 𝔼 a, (𝔼 y, f (a, y)) ^ 2) / Fintype.card K := by
    calc
      _ = 𝔼 p, f p * (affinePlane K).walk ((affinePlane K).walk f) p := by
        simpa only [pow_two] using hself.symm
      _ = 𝔼 p, (f p ^ 2 - f p * (𝔼 y, f (p.1, y))) / Fintype.card K := by
        apply expect_congr rfl
        rintro ⟨a, b⟩ _
        rw [walk_affinePlane_twice, hf, zero_add]
        ring
      _ = _ := by rw [← expect_div, expect_sub_distrib, hrow]
  rw [heq, one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right
    (sub_le_self _ (expect_nonneg fun a _ => sq_nonneg _)) (Nat.cast_nonneg _)

end Cslib.RotationMap
