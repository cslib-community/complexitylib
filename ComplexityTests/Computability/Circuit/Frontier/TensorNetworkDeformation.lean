/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Deformation

/-!
# Tests for deformed contractions and the Cauchy kernel

A one-edge network deformed along a `1 × 1` matrix, checked by hand against the expansion of
`F(W)`, and the Cauchy kernel of a packet with one slot, `C(T) = T (T + 1)`.
-/

@[expose] public section

namespace ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.Deformation

open Cslib.Circuits.Frontier Polynomial

/-- A row vertex `0` and a column vertex `1` joined by one edge, with tensors `A = (1, 2)` and
`B = (3, 5)` on its bit. -/
def oneEdge : TensorNetwork ℤ Bool (Fin 2) (Fin 1) where
  src _ := 0
  tgt _ := 1
  tensor v x := if v = 0 then (if x 0 then 2 else 1) else (if x 0 then 5 else 3)
  tensor_congr v x y h := by rw [h 0 (by fin_cases v <;> simp)]

/-- The rows: vertex `0`. -/
def side (v : Fin 2) : Bool := v = 0

/-- By hand, `F(w) = A₀B₀ + A₀B₁ (1 - w) + A₁B₁ w`; at `w = 2` this is `3 - 5 + 20 = 18`. -/
example : oneEdge.deformedContraction side (fun _ _ => 2) = 18 := by decide

/-- At `w = 1` it is the contraction `A₀B₀ + A₁B₁ = 13`. -/
example : oneEdge.deformedContraction side 1 = 13 ∧ oneEdge.contraction = 13 := by decide

/-- Contraction commutes with reduction modulo `8`: `13 ≡ 5`. -/
example : (oneEdge.map (Int.castRingHom (ZMod 8))).contraction = 5 := by
  rw [TensorNetwork.contraction_map]
  decide

/-- With one slot the grid is `{-1, 0}`, `C'(0) = 1`, and the kernel at `-1` is `T`, whose value
at `T = 1` is `1`; the kernel at `0` is `T + 1`. -/
example : (cauchyKernel 1 (-1)).eval 1 = 1 ∧ (cauchyKernel 1 0).eval 1 = 2 := by
  have hS : cauchyGrid 1 = {-1, 0} := by decide
  have h0 : ({-1, 0} : Finset ℤ).erase 0 = {-1} := by decide
  have h1 : ({-1, 0} : Finset ℤ).erase (-1) = {0} := by decide
  simp only [cauchyKernel, hS, h0, h1, eval_mul, eval_C, Lagrange.eval_nodal,
    Finset.prod_singleton]
  norm_num

end ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.Deformation
