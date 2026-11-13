/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.Module
import CslibFrontier.Crypto.Computational.SIS.Polynomial

/-! Checked quotient interpretation over integers and composite moduli, including sign wraparound,
characteristic two, dimension one, and the Module-SIS client. -/

namespace CslibFrontierTests.Crypto.NegacyclicPolynomial

open Cslib Cslib.Crypto Negacyclic Polynomial
open scoped _root_.Matrix

local instance : Fact (1 < 6) := ⟨by decide⟩

example : negacyclicEquiv (by decide : 2 ≠ 0) (ofCoeffs ![0, 1] : Negacyclic ℤ 2) =
    AdjoinRoot.root ((X : ℤ[X]) ^ 2 + 1) := by
  simp [negacyclicEquiv_apply, Fin.sum_univ_two]

/-- Wrapping `X * X` introduces a minus sign in degree two. -/
example :
    negacyclicEquiv (by decide : 2 ≠ 0) (ofCoeffs ![0, 1] : Negacyclic ℤ 2) *
      negacyclicEquiv (by decide : 2 ≠ 0) (ofCoeffs ![0, 1]) =
    negacyclicEquiv (by decide : 2 ≠ 0) (ofCoeffs ![-1, 0]) := by
  rw [← map_mul]
  congr 1
  decide

/-- Composite coefficients need not form a field. -/
example :
    negacyclicEquiv (by decide : 2 ≠ 0) (ofCoeffs ![0, 1] : Negacyclic (ZMod 6) 2) *
      negacyclicEquiv (by decide : 2 ≠ 0) (ofCoeffs ![0, 1]) =
    negacyclicEquiv (by decide : 2 ≠ 0) (ofCoeffs ![5, 0]) := by
  rw [← map_mul]
  congr 1
  decide

/-- Equality reflection detects the sign, so the interpretation is not a cyclic quotient. -/
example :
    negacyclicEquiv (by decide : 2 ≠ 0) (ofCoeffs ![-1, 0] : Negacyclic (ZMod 6) 2) ≠
      negacyclicEquiv (by decide : 2 ≠ 0) (ofCoeffs ![1, 0]) := by
  rw [Ne, (negacyclicEquiv _).injective.eq_iff]
  decide

/-- In characteristic two the two signs coincide, as they must. -/
example :
    negacyclicEquiv (by decide : 2 ≠ 0) (ofCoeffs ![0, 1] : Negacyclic (ZMod 2) 2) *
      negacyclicEquiv (by decide : 2 ≠ 0) (ofCoeffs ![0, 1]) =
    negacyclicEquiv (by decide : 2 ≠ 0) (ofCoeffs ![1, 0]) := by
  rw [← map_mul]
  congr 1
  decide

example :
    negacyclicEquiv (by decide : 1 ≠ 0) (ofCoeffs ![2] : Negacyclic ℤ 1) *
      negacyclicEquiv (by decide : 1 ≠ 0) (ofCoeffs ![3]) =
    negacyclicEquiv (by decide : 1 ≠ 0) (ofCoeffs ![6]) := by
  rw [← map_mul]
  congr 1
  decide

/-- A coefficient Module-SIS zero equation is exactly its quotient-ring zero equation. -/
example {d k n : ℕ} (hn : n ≠ 0)
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod 6))
    (z : Fin k → Fin n → ZMod 6) :
    moduleSISMap A z = 0 ↔
      A.map (negacyclicEquiv hn ∘ ofCoeffs) *ᵥ (negacyclicEquiv hn ∘ ofCoeffs ∘ z) = 0 := by
  rw [moduleSISMap_eq_zero_iff, ← Matrix.map_map, ← negacyclicEquiv_mulVec]
  simp only [funext_iff, Function.comp_apply, Pi.zero_apply, EmbeddingLike.map_eq_zero_iff]

end CslibFrontierTests.Crypto.NegacyclicPolynomial
