/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.PolyTime.LinearAlgebra.ExchangeReplacement
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Concrete tests for polynomial-time auxiliary exchange matrices and replacement rows

Computational, specification-bridge, and `fun_prop` synthesis tests on `(Q = 2, r = 2, A₀ = 1,
R = 2, D = 16)`, `D_cap < D` truncation, and degenerate `(Q = 0, R = 0, r = 0)` boundaries.
-/

namespace Cslib.ExchangeReplacementPolyTimeTests

open Cslib.LinearAlgebra Finset Polynomial Turing.MultiTapeTM

private def dotSparse (row : List ℤ) (ξ : List (ℕ × ℤ)) : ℤ :=
  (ξ.map fun p => row.getD p.1 0 * p.2).sum
private def evalRowSparse (Q r A₀ R u_idx : ℕ) (t : ℤ) (ξ : List (ℕ × ℤ)) : ℤ :=
  (ξ.map fun p => evalCoeffList t (auxReplacementRowCoeffsIdx Q r A₀ R u_idx p.1) * p.2).sum

/-! ### Mixed-radix `AuxLabel` encoding/decoding and `commonDenom` on `(Q = 2, r = 2, D = 16)` -/
example : decodeAuxDigits 2 2 12 = ([0, 0], [1, 1]) ∧
    decodeAuxDigits 2 2 5 = ([1, 0], [1, 0]) ∧ commonDenom 2 2 = 2 ∧ commonDenom 3 4 = 36 ∧
    ((List.range 16).all fun idx =>
      decide (encodeAuxDigits 2 (decodeAuxDigits 2 2 idx) = idx)) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Executable `{0, 1, -1}` measurement matrix `C^B` and `D_cap` truncation -/
example : (auxMeasurementRows 2 2 1 2).length = 9 ∧
    ((auxMeasurementRows 2 2 1 2).all fun row =>
      decide (row.length = 16) && row.all fun c => decide (c = -1 ∨ c = 0 ∨ c = 1)) = true ∧
    auxMeasurementRowsBounded 16 2 2 1 2 = auxMeasurementRows 2 2 1 2 ∧
    ((auxMeasurementRowsBounded 5 2 2 1 2).all fun row => decide (row.length = 5)) = true ∧
    decide (auxMeasurementRowsBounded 5 2 2 1 2 ≠ auxMeasurementRows 2 2 1 2) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Cleared replacement rows: table shape, degree `≤ 1`, and `T = 0` identity restoration -/
example : (auxReplacementTable 2 2 1 2).length = 16 ∧
    ((auxReplacementTable 2 2 1 2).all fun row =>
      decide (row.length = 16) && row.all fun p => decide (p.length = 2)) = true ∧
    ((List.range 16).all fun u => (List.range 16).all fun y =>
      decide (evalCoeffList 0 (((auxReplacementTable 2 2 1 2).getD u []).getD y []) =
        if u = y then (commonDenom 2 2 : ℤ) else 0)) = true :=
  ⟨rfl, rfl, rfl⟩

/-! ### Restricted kernel vanishing at `T = 1, 2` on `auxGroup s g` (Lemma 4.3) -/
example :
    let cases : List (ℕ × ℕ × List (ℕ × ℤ)) :=
      [(0, 0, [(2, -1), (6, -1), (8, 1), (12, 1)]), (0, 1, [(3, -1), (7, -1), (9, 1), (13, 1)]),
       (1, 0, [(1, -1), (4, 1), (9, -1), (12, 1)]), (1, 1, [(3, -1), (6, 1), (11, -1), (14, 1)])]
    (cases.all fun (s, g, ξ) =>
      (ξ.all fun (y_idx, _) => decide ((decodeAuxDigits 2 2 y_idx).1.getD s 0 = g)) &&
        ((auxMeasurementRows 2 2 1 2).all fun row => decide (dotSparse row ξ = 0)) &&
        ((List.range 16).all fun u_idx =>
          decide ((decodeAuxDigits 2 2 u_idx).2.getD s 0 = g ∨
            evalRowSparse 2 2 1 2 u_idx ((s : ℤ) + 1) ξ = 0))) = true ∧
      ((auxMeasurementRows 2 2 1 2).all fun row => decide (dotSparse row [(0, 1)] = 0)) = false :=
  ⟨rfl, rfl⟩

/-! ### Degenerate boundary cases (`Q = 0`, `R = 0`, `r = 0`) -/
example : auxMeasurementRows 0 2 0 1 = [] ∧ auxReplacementTable 0 2 0 1 = [[[1]]] ∧
    auxReplacementRowCoeffsIdx 2 2 0 0 0 0 = [2] ∧
    auxMeasurementRows 2 0 1 2 = [] ∧ auxReplacementTable 2 0 1 2 = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Bridges to `auxReplacementRowScaledInt`, `Polynomial.coeffNorm1`, and Lemma 4.6 row bound -/
example :
    let u₀ : AuxLabel 2 2 := decodeAuxLabel (by decide) 12
    let y₀ : AuxLabel 2 2 := decodeAuxLabel (by decide) 6
    Cslib.IsTableShape #(measurementIndices 2 2 1 2) 16 (auxMeasurementRows 2 2 1 2) ∧
      (auxReplacementRowScaledInt 2 2 1 2 u₀ y₀).coeff 1 =
        (auxReplacementRowCoeffs 2 2 1 2 u₀ y₀).getD 1 0 ∧
      (auxReplacementRowScaledInt 2 2 1 2 u₀ y₀).coeffNorm1 =
        ((auxReplacementRowCoeffs 2 2 1 2 u₀ y₀).map Int.natAbs).sum ∧
      (∑ y : AuxLabel 2 2, ((auxReplacementRowCoeffs 2 2 1 2 u₀ y).map Int.natAbs).sum) ≤
        commonDenom 2 2 * (1 + (1 + 2 ^ 2) * 2 * (4 * 2) ^ (2 - 1)) :=
  ⟨isTableShape_auxMeasurementRows 2 2 1 2, (getD_auxReplacementRowCoeffs 2 2 1 2 _ _ 1).symm,
   (sum_natAbs_auxReplacementRowCoeffs_eq_coeffNorm1 2 2 1 2 _ _).symm,
   sum_row_natAbs_auxReplacementRowCoeffs_le (by decide) (by omega) _⟩

/-! ### Compositional `fun_prop` synthesis for plain `ComputableInPolyTime` -/
example : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) =>
    encodeAuxDigits (p.2.1 + 2) (decodeAuxDigits (p.1 + 1) (p.2.1 + 2) p.2.2) +
      commonDenom (p.1 + 1) (p.1 + 2)) (encPair encUnary (encPair encNat encNat)) encNat := by
  fun_prop
example : ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) =>
    (auxMeasurementRowsBounded (p.1.1 + 1) p.1.2 (p.2.1 + 2) p.2.2.1 (p.2.2.2 + 1),
     auxReplacementTableBounded (p.1.1 + 1) p.1.2 (p.2.1 + 2) p.2.2.1 (p.2.2.2 + 1)))
    (encPair (encPair encUnary encUnary) (encPair encUnary (encPair encUnary encUnary)))
    (encPair (encList (encList encIntBin)) (encList (encList (encList encIntBin)))) := by
  fun_prop
example : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
    auxReplacementRowCoeffsIdx p.1.1 p.2.1 p.1.2.1 p.1.2.2 p.2.2.1 p.2.2.2)
    (encPair (encPair encUnary (encPair encUnary encUnary))
      (encPair encNat (encPair encNat encNat))) (encList encIntBin) := by
  fun_prop
example : True := by
  fail_if_success
    have : ComputableInPolyTime (fun n : ℕ => commonDenom n n) encNat encNat := by fun_prop
  trivial

end Cslib.ExchangeReplacementPolyTimeTests
