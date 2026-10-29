/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import Complexity.Computability.PolyTime.LinearAlgebra.BooleanMeasurements

-- Regression tests intentionally export no declarations.
set_option linter.privateModule false

open Cslib Cslib.GenericRAM Cslib.LinearAlgebra.BooleanMeasurements Turing.MultiTapeTM
open scoped BigOperators

private abbrev Context := List (List ℤ) × List ℤ

private def representative (p : Context × ℕ) : Option (List Bool) :=
  search Prod.fst Prod.snd p

private def contextEncoding : Context ↪ List Bool :=
  encPair (encList (encList encIntBin)) (encList encIntBin)

-- Signed coefficients, padding/truncation/ragged rows, retained runtime context, first-match
-- order, zero-row/zero-column regimes, target-length mismatch, and unrestricted representatives.
example :
    (evalBoolRow [-3, 2, 2] [true, false, true] = -1 ∧
      evalBoolMatrix [[2, -3, 2], [-1, 0, 4]] [true, true, true] = [1, 3] ∧
      (evalBoolRow [5] [] = 0 ∧ evalBoolRow [-3, 2] [true] = -3) ∧
      evalBoolRow [2, -3] [true, true, true] = -1 ∧
      evalBoolMatrix [[], [3, -2], [5]] [true] = [0, 3, 5]) ∧
    (representative (([[1, 0]], [1]), 2) = some [true, false] ∧
      representative (([[0, 1]], [1]), 2) = some [false, true] ∧
      representative (([[1, 0]], [0]), 2) = some [false, false]) ∧
    (representative (([[1, 1]], [1]), 2) = some [true, false] ∧
      representative (([[1, 1]], [3]), 2) = none ∧
      representative (([[2, -3, 2], [-1, 0, 4]], [-1, -1]), 3) = some [true, true, false]) ∧
    ((representative (([], []), 0) = some [] ∧
        representative (([], []), 2) = some [false, false]) ∧
      (representative (([[], []], [0, 0]), 0) = some [] ∧
        representative (([[], []], [0, 1]), 0) = none)) ∧
    ((representative (([[1, 1]], []), 2) = none ∧
        representative (([], [0]), 2) = none) ∧
      representative (([[], [3, -2], [5]], [0, 3, 5]), 1) = some [true]) ∧
    (representative (([[0, 1]], [0]), 2) = some [false, false] ∧
      evalBoolMatrix [[0, 1]] [true, false] = [0] ∧
      ([false, false] : List Bool).headD false = false) := by
  decide

-- A concrete successful native search gives the actual finite system of integer equations.
example : ∃ y : List Bool,
    representative (([[2, -3, 2], [-1, 0, 4]], [1, 3]), 3) = some y ∧ y.length = 3 ∧
      ∀ i : Fin 2, (∑ j : Fin 3,
        rowEntry [[2, -3, 2], [-1, 0, 4]] i j * BitString.bitVal ℤ (y.getD j false)) =
          ([1, 3] : List ℤ).getD i 0 := by
  let M : List (List ℤ) := [[2, -3, 2], [-1, 0, 4]]
  let y := [true, true, true]
  have hf : search Prod.fst Prod.snd ((M, [1, 3]), 3) = some y := by decide
  have hs := search_some Prod.fst Prod.snd ((M, [1, 3]), 3) hf
  refine ⟨y, hf, hs.1, fun i => ?_⟩
  rw [← evalBoolMatrix_getD_eq_sum (M := M) (by simp [IsTableShape, M]) y i, hs.2]

-- The finite-cube completeness statement rules out an unrealizable target.
example : ∀ y : BitString 2, evalBoolMatrix [[1, 1]] (List.ofFn y) ≠ [3] := by
  exact (search_eq_none_iff_cube Prod.fst Prod.snd (([[1, 1]], [3]), 2)).mp (by decide)

private theorem matrixProjection :
    ComputableInPolyTime (Prod.fst : Context → List (List ℤ)) contextEncoding
      (encList (encList encIntBin)) :=
  ComputableInPolyTime.fst (encList (encList encIntBin)) (encList encIntBin)

private theorem targetProjection :
    ComputableInPolyTime (Prod.snd : Context → List ℤ) contextEncoding (encList encIntBin) :=
  ComputableInPolyTime.snd (encList (encList encIntBin)) (encList encIntBin)

-- Compose real runtime projections with evaluation, equality testing, and both codecs.
private noncomputable def nativeRepresentative :
    NativeCertificate representative (encPair contextEncoding encUnary) (encOption encBits) :=
  searchCertificate matrixProjection targetProjection

-- Native certificate computability, polynomial space/time bounds, `ComputableInO`, and raw-bit
-- result encoding length.
example :
    IsComputable representative (encPair contextEncoding encUnary) (encOption encBits) ∧
    PolyBounded (fun p => (encPair contextEncoding encUnary p).length)
      nativeRepresentative.space ∧
    (∃ overhead : Context × ℕ → ℕ,
      PolyBounded (fun p => (encPair contextEncoding encUnary p).length) overhead ∧
      ∀ p, nativeRepresentative.time p = (2 ^ p.2 + 1) * overhead p) ∧
    (∃ overhead workspace : Context × ℕ → ℕ,
      PolyBounded (fun p => (encPair contextEncoding encUnary p).length) overhead ∧
      PolyBounded (fun p => (encPair contextEncoding encUnary p).length) workspace ∧
      ComputableInO representative (encPair contextEncoding encUnary) (encOption encBits)
        (fun p => (2 ^ p.2 + 1) * overhead p) workspace) ∧
    ((encOption encBits (representative (([[1, 1]], [1]), 2))).length = 3 ∧
      (encOption (encList encBool) (representative (([[1, 1]], [1]), 2))).length = 7) :=
  ⟨nativeRepresentative.isComputable,
   polyBounded_searchCertificate_space matrixProjection targetProjection,
   exists_polyBounded_searchCertificate_time matrixProjection targetProjection,
   exists_computableInO_search matrixProjection targetProjection,
   by decide⟩
