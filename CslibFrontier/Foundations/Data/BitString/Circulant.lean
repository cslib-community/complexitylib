/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.LinearAlgebra.Matrix.Circulant

/-!
# Cyclic convolution of bit strings

Mathlib represents cyclic convolution as a circulant matrix-vector product. Over the Boolean ring,
this operation is commutative and associative. The results below expose those generator-level laws
directly, complementing Mathlib's matrix product laws.

## Main results

* `Cslib.BitString.circulant_mulVec_comm`: binary cyclic convolution is commutative.
* `Cslib.BitString.circulant_mulVec_assoc`: binary cyclic convolution is associative.
-/

public section

namespace Cslib.BitString

open Matrix

/-- Binary cyclic convolution is commutative. -/
theorem circulant_mulVec_comm {n : ℕ} (x y : BitString n) :
    circulant x *ᵥ y = circulant y *ᵥ x := by
  apply Fin.circulant_injective n
  simpa only [Fin.circulant_mul] using Fin.circulant_mul_comm x y

/-- Binary cyclic convolution is associative. -/
theorem circulant_mulVec_assoc {n : ℕ} (x y z : BitString n) :
    circulant (circulant x *ᵥ y) *ᵥ z = circulant x *ᵥ (circulant y *ᵥ z) := by
  simp only [← Fin.circulant_mul, mulVec_mulVec]

end Cslib.BitString
