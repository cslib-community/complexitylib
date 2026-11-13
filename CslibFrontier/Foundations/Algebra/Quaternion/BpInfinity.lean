/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.QuaternionBasis

/-!
# The `B_{p,∞}` quaternion presentation

For a rational parameter `p`, `BpInfinity p` is the quaternion algebra over `ℚ` with standard
basis `1, i, j, k` satisfying

`i² = -1`, `j² = -p`, and `ij = k = -ji`.

When `p` is a positive prime, this is the algebra denoted `B_{p,∞}` in the SQIsign specification.
The name records the source's intended algebra; this module establishes the displayed presentation
and positive-definite reduced norm, but does not prove the local ramification classification.

## Main definitions

* `Cslib.BpInfinity`: the rational quaternion algebra with parameters `-1` and `-p`.
* `Cslib.BpInfinity.i`, `Cslib.BpInfinity.j`, `Cslib.BpInfinity.k`: its standard generators.
* `Cslib.BpInfinity.reducedNorm`: the reduced norm `q * star q`, viewed in `ℚ`.
* `Cslib.BpInfinity.reducedTrace`: the reduced trace `q + star q`, viewed in `ℚ`.

## Main results

* `Cslib.BpInfinity.i_mul_i`, `Cslib.BpInfinity.j_mul_j`,
  `Cslib.BpInfinity.i_mul_j`, `Cslib.BpInfinity.j_mul_i`: the defining relations.
* `Cslib.BpInfinity.reducedNorm_mk`: the coordinate formula
  `x² + y² + p (z² + t²)`.
* `Cslib.BpInfinity.reducedNorm_pos`: positive definiteness when `p > 0`.

## References

* [SQIsign v3.0 specification](https://csrc.nist.gov/csrc/media/Projects/pqc-dig-sig/documents/sqisign_specification.pdf),
  Facts 12–13 (pp. 9–10), Section 2.2.1 (pp. 10–11), and Algorithms 4.38–4.40 (p. 32).
-/

public section

namespace Cslib

open scoped Quaternion

/-- The rational quaternion algebra with `i² = -1` and `j² = -p`.

For a positive prime `p`, this is the algebra denoted `B_{p,∞}` in the SQIsign specification.
The ramification classification is not part of this definition. -/
abbrev BpInfinity (p : ℚ) := ℍ[ℚ, -1, -p]

namespace BpInfinity

private def sourceBasis (p : ℚ) :
    QuaternionAlgebra.Basis (BpInfinity p) (-1) 0 (-p) :=
  QuaternionAlgebra.Basis.self ℚ

/-- The standard generator `i` of `B_{p,∞}`. -/
def i (p : ℚ) : BpInfinity p := (sourceBasis p).i

/-- The standard generator `j` of `B_{p,∞}`. -/
def j (p : ℚ) : BpInfinity p := (sourceBasis p).j

/-- The standard generator `k = i * j` of `B_{p,∞}`. -/
def k (p : ℚ) : BpInfinity p := (sourceBasis p).k

@[simp]
theorem i_mul_i (p : ℚ) : i p * i p = (-1 : BpInfinity p) := by
  simp only [i, sourceBasis, QuaternionAlgebra.Basis.i_mul_i]
  simp

@[simp]
theorem j_mul_j (p : ℚ) : j p * j p = (-p : BpInfinity p) := by
  simp only [j, sourceBasis, QuaternionAlgebra.Basis.j_mul_j]
  simp [Algebra.smul_def]

@[simp]
theorem i_mul_j (p : ℚ) : i p * j p = k p := by
  exact (sourceBasis p).i_mul_j

@[simp]
theorem j_mul_i (p : ℚ) : j p * i p = -k p := by
  simpa only [j, i, k, sourceBasis, zero_smul, zero_sub] using (sourceBasis p).j_mul_i

/-- Conjugation in `B_{p,∞}` negates the three imaginary coordinates. -/
theorem star_mk (p x y z t : ℚ) :
    star (QuaternionAlgebra.mk x y z t : BpInfinity p) =
      QuaternionAlgebra.mk x (-y) (-z) (-t) := by
  rw [QuaternionAlgebra.star_mk]
  simp

/-- The reduced norm of `q`, namely the scalar `q * star q`. -/
def reducedNorm {p : ℚ} (q : BpInfinity p) : ℚ := (q * star q).re

/-- Multiplication by the conjugate is the scalar reduced norm. -/
theorem mul_star_eq_reducedNorm {p : ℚ} (q : BpInfinity p) :
    q * star q = (reducedNorm q : BpInfinity p) := by
  rw [QuaternionAlgebra.mul_star_eq_coe]
  rfl

/-- Multiplication by the conjugate on the left gives the same reduced norm. -/
theorem star_mul_eq_reducedNorm {p : ℚ} (q : BpInfinity p) :
    star q * q = (reducedNorm q : BpInfinity p) := by
  rw [star_comm_self]
  exact mul_star_eq_reducedNorm q

/-- The coordinate formula for the reduced norm. -/
@[simp]
theorem reducedNorm_mk (p x y z t : ℚ) :
    reducedNorm (QuaternionAlgebra.mk x y z t : BpInfinity p) =
      x ^ 2 + y ^ 2 + p * (z ^ 2 + t ^ 2) := by
  simp only [reducedNorm, star_mk, QuaternionAlgebra.mk_mul_mk]
  ring

/-- The reduced trace of `q`, namely the scalar `q + star q`. -/
def reducedTrace {p : ℚ} (q : BpInfinity p) : ℚ := (q + star q).re

/-- Addition to the conjugate is the scalar reduced trace. -/
theorem add_star_eq_reducedTrace {p : ℚ} (q : BpInfinity p) :
    q + star q = (reducedTrace q : BpInfinity p) := by
  rcases q with ⟨x, y, z, t⟩
  ext <;> simp [reducedTrace]

/-- The coordinate formula for the reduced trace. -/
@[simp]
theorem reducedTrace_mk (p x y z t : ℚ) :
    reducedTrace (QuaternionAlgebra.mk x y z t : BpInfinity p) = 2 * x := by
  simp only [reducedTrace, star_mk]
  change x + x = 2 * x
  ring

/-- The reduced norm is positive definite when `p` is positive. -/
theorem reducedNorm_pos {p : ℚ} (hp : 0 < p) {q : BpInfinity p} (hq : q ≠ 0) :
    0 < reducedNorm q := by
  rcases q with ⟨x, y, z, t⟩
  rw [reducedNorm_mk]
  have hxyzt : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0 := by
    by_contra h
    push Not at h
    apply hq
    ext <;> simp [h]
  rcases hxyzt with hx | hy | hz | ht
  · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg y, sq_nonneg z, sq_nonneg t]
  · nlinarith [sq_nonneg x, sq_pos_of_ne_zero hy, sq_nonneg z, sq_nonneg t]
  · nlinarith [sq_nonneg x, sq_nonneg y, sq_pos_of_ne_zero hz, sq_nonneg t]
  · nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_pos_of_ne_zero ht]

end BpInfinity

end Cslib
