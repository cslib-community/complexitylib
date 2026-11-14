/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: candidate
import CslibFrontier.Computability.Circuit.Arithmetic.Determinant

/-! # A degree obstruction to the draft's circuit-to-determinant claim

Arora–Barak's 2007-01-08 web draft, Theorem 14.7, printed p. 258/PDF p. 274, says that
an arbitrary size-u circuit projects to a determinant on u+2 variables. Even interpreting
u+2 as the matrix dimension, this fails: four squarings compute a polynomial of degree 16,
while a determinant of dimension at most 6 has degree at most 6. Existing circuit and
projection theorems supply this check; it does not test a corrected formula statement.
-/

open Cslib.Circuits Cslib.Circuits.Arithmetic

example {K : Type*} [CommRing K] [Nontrivial K] :
    ∃ c : Circuit (arithSignature K) 1 1,
      c.size ≤ 4 ∧ c.polynomial 0 = (powTwoPowFamily K).poly 4 ∧
        ¬ IsProjection (c.polynomial 0) (genericMatrix K (c.size + 2)).det := by
  obtain ⟨c, hc, hs⟩ := exists_circuit_pow_two_pow (K := K) 4
  refine ⟨c, hs, hc, ?_⟩
  rintro ⟨ρ, hρ⟩
  have hd := totalDegree_projection_le ρ (genericMatrix K (c.size + 2)).det
  have ht := totalDegree_det_genericMatrix_le (K := K) (c.size + 2)
  rw [hρ, hc] at hd
  have hd' : 16 ≤ (genericMatrix K (c.size + 2)).det.totalDegree := by
    simpa [powTwoPowFamily, MvPolynomial.totalDegree_X_pow] using hd
  omega
