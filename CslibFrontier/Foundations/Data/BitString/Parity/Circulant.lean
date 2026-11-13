/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Parity
public import Mathlib.LinearAlgebra.Matrix.Circulant
import CslibFrontier.Foundations.LinearAlgebra.Matrix.GroupCirculant.Eigenvalues
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Parity of binary cyclic convolution

The parity of a circulant matrix-vector product is the product of the two input parities.
This is the trivial-character case of the existing circulant eigenvalue multiplication law.

## Main results

* `Cslib.BitString.parity_circulant_mulVec`: cyclic convolution multiplies parities.
-/

public section

namespace Cslib.BitString

open Matrix

/-- Cyclic convolution over the Boolean ring multiplies the parities of its factors. -/
theorem parity_circulant_mulVec {n : ℕ} [NeZero n] (x y : BitString n) :
    parity n (Matrix.circulant x *ᵥ y) = (parity n x && parity n y) := by
  simpa [parity, parityOn_eq_sum, Bool.mul_eq_and] using
    Matrix.circulantEigenvalue_mulVec x y (0 : AddChar (Fin n) Bool)

end Cslib.BitString
