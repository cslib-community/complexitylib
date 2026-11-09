/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.Polynomial

/-! Checked quotient interpretation over integers and composite moduli, including sign wraparound,
characteristic two, dimension one, and the Module-SIS client. -/

namespace CslibFrontierTests.Crypto.NegacyclicPolynomial

open Cslib.Crypto Polynomial
open scoped Matrix

local instance : Fact (1 < 6) := ⟨by decide⟩

example : negacyclicEquiv (by decide : 2 ≠ 0) (![0, 1] : Fin 2 → ℤ) =
    AdjoinRoot.root ((X : ℤ[X]) ^ 2 + 1) := by
  simp [negacyclicEquiv_apply, Fin.sum_univ_two]

/-- Wrapping `X * X` introduces a minus sign in degree two. -/
example :
    negacyclicEquiv (by decide : 2 ≠ 0) (![0, 1] : Fin 2 → ℤ) *
      negacyclicEquiv (by decide : 2 ≠ 0) ![0, 1] =
    negacyclicEquiv (by decide : 2 ≠ 0) ![-1, 0] := by
  rw [← negacyclicEquiv_mul]
  congr 1
  decide

/-- Composite coefficients need not form a field. -/
example :
    negacyclicEquiv (by decide : 2 ≠ 0) (![0, 1] : Fin 2 → ZMod 6) *
      negacyclicEquiv (by decide : 2 ≠ 0) ![0, 1] =
    negacyclicEquiv (by decide : 2 ≠ 0) ![5, 0] := by
  rw [← negacyclicEquiv_mul]
  congr 1
  decide

/-- Equality reflection detects the sign, so the interpretation is not a cyclic quotient. -/
example :
    negacyclicEquiv (by decide : 2 ≠ 0) (![-1, 0] : Fin 2 → ZMod 6) ≠
      negacyclicEquiv (by decide : 2 ≠ 0) ![1, 0] := by
  intro h
  have := (negacyclicEquiv (R := ZMod 6) (by decide : 2 ≠ 0)).injective h
  exact (by decide : (![-1, 0] : Fin 2 → ZMod 6) ≠ ![1, 0]) this

/-- In characteristic two the two signs coincide, as they must. -/
example :
    negacyclicEquiv (by decide : 2 ≠ 0) (![0, 1] : Fin 2 → ZMod 2) *
      negacyclicEquiv (by decide : 2 ≠ 0) ![0, 1] =
    negacyclicEquiv (by decide : 2 ≠ 0) ![1, 0] := by
  rw [← negacyclicEquiv_mul]
  congr 1
  decide

example :
    negacyclicEquiv (by decide : 1 ≠ 0) (![2] : Fin 1 → ℤ) *
      negacyclicEquiv (by decide : 1 ≠ 0) ![3] =
    negacyclicEquiv (by decide : 1 ≠ 0) ![6] := by
  rw [← negacyclicEquiv_mul]
  congr 1
  decide

/-- A coefficient Module-SIS zero equation is exactly its quotient-ring zero equation. -/
example {d k n : ℕ} (hn : n ≠ 0)
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod 6))
    (z : Fin k → Fin n → ZMod 6) :
    moduleSISMap A z = 0 ↔
      (Matrix.of fun i j => negacyclicEquiv hn (A i j)) *ᵥ
        (fun j => negacyclicEquiv hn (z j)) = 0 := by
  simp only [funext_iff, Pi.zero_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
    ← negacyclicEquiv_moduleSISMap, LinearEquiv.map_eq_zero_iff]


end CslibFrontierTests.Crypto.NegacyclicPolynomial
