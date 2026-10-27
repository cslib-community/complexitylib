/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module

public import Complexity.Computability.PolyTime.CNF.GreedyParitySearch

public section

open Finset Cslib.BitString Cslib.GenericRAM Cslib.Logic.PL Cslib.Logic.PL.CNF Turing.MultiTapeTM

namespace ComplexityTests.CNFGreedyParitySearch

-- Boundary regimes: P = 0 yields 1 empty candidate and an all-false row; m = 0 and n = 0 are total.
theorem boundary_empty_tuple : candidateTupleCount 5 0 = 1 := rfl
example : decodeTestTuple 5 0 0 = [] := rfl
example : materializeTestRow 5 (decodeTestTuple 5 0 0) = [false, false, false, false, false] := rfl
example : selectBestTestRow List.length 3 0 [] = [false, false, false] := by decide
example : candidateTupleCount 0 2 = 0 := by decide
example : decodeTestTuple 0 2 99 = [(0, false), (0, false)] := by decide
example : materializeTestRow 0 [(0, true), (1, true)] = [] := rfl
example : selectBestTestRow (fun _ => 7) 0 2 [] = [] := by decide
example : greedyParityRows (fun _ => 0) 0 3 2 [[true, false, true]] = [[true, false, true]] := rfl

-- Base-2m codec via Cslib.Radix.digit and Nat.ofDigits: round-trips and full range bijection.
example : encodeTestTuple 3 [(2, true), (0, false), (1, true)] = 113 := by decide
example : decodeTestTuple 3 3 113 = [(2, true), (0, false), (1, true)] := by decide
example : ((List.range (candidateTupleCount 2 2)).map fun j =>
    encodeTestTuple 2 (decodeTestTuple 2 2 j)) = List.range 16 := by decide

-- Mod-2 cancellation in materializeTestRow: repeated clause index 0 cancels, dropping weight to 1.
example : materializeTestRow 3 [(0, true), (2, true), (0, true), (1, false)] =
    [false, false, true] := rfl
example : (materializeTestRow 3 [(0, true), (2, true), (0, true), (1, false)]).count true = 1 := by
  decide

-- Out-of-range clause indices ≥ m are ignored cleanly without overflow.
example : materializeTestRow 2 [(0, true), (5, true)] = [true, false] := by decide

-- Concrete bridge between materializeTestRow and Cslib.BitString.testRow on Fin 3.
example : let γ : Fin 3 → Fin 3 × Bool := ![(0, true), (2, true), (0, true)]
    materializeTestRow 3 (List.ofFn fun r => ((γ r).1.val, (γ r).2)) = List.ofFn (testRow γ) ∧
      List.ofFn (testRow γ) = [false, false, true] := by decide

-- Enumeration-order tie-breaking: j = 1 ([true, false]) and j = 3 ([false, true]) tie at count 2;
-- selectBestTestRow must pick the earlier index j = 1 rather than j = 3.
private def tieCount : List (List Bool) → ℕ
  | [[true, false]] | [[false, true]] => 2
  | _ => 5
example : decodeTestTuple 2 1 1 = [(0, true)] ∧ decodeTestTuple 2 1 3 = [(1, true)] := by decide
example : selectBestTestRow tieCount 2 1 [] = [true, false] := by decide

-- Concrete 2-variable CNF φ = x₀ ∧ x₁: executable list-based common-zero counter on all 4 inputs.
private def twoVarViolations : List (List Bool) :=
  [[true, true], [true, false], [false, true], [false, false]]
private def rowPassesList (row v : List Bool) : Bool :=
  !((List.zipWith (· && ·) row v).foldl xor false)
private def twoVarCountSys (rows : List (List Bool)) : ℕ :=
  (twoVarViolations.filter fun v => rows.all fun r => rowPassesList r v).length

example : twoVarCountSys [] = 4 := by decide
example : twoVarCountSys (greedyParityRows twoVarCountSys 2 2 2 []) = 1 := by decide
example : (greedyParityRows twoVarCountSys 2 2 2 []).length = 6 := by decide
example : (greedyParityRows twoVarCountSys 2 2 2 []).all
    (fun r => decide (r.length = 2 ∧ r.count true ≤ 2)) = true := by decide

-- Nonvacuous instantiation of numPassing_greedyParityRows_fin on twoVarAnd : CNF (Fin 2).
private def twoVarAnd : CNF (Fin 2) := [[(0, true)], [(1, true)]]
private theorem twoVarAnd_init_bound (σ : Fin 2 → Bool)
    (_ : PassesTests twoVarAnd.violations ([].map (ofList twoVarAnd.length)) σ)
    (heval : twoVarAnd.eval σ = false) :
    twoVarAnd.length ≤ 2 * weight (twoVarAnd.violations σ) := by
  have hne : twoVarAnd.violations σ ≠ 0 := fun h0 =>
    Bool.false_ne_true (heval.symm.trans ((CNF.violations_eq_zero_iff _ _).mp h0))
  have hw : weight (twoVarAnd.violations σ) ≠ 0 := by
    rw [weight_eq_hammingNorm, ne_eq, hammingNorm_eq_zero]; exact hne
  change 2 ≤ 2 * weight (twoVarAnd.violations σ); omega

example :
    let countSys := fun rows : List (List Bool) =>
      numPassing twoVarAnd.violations (rows.map (ofList twoVarAnd.length))
    let finalRows := greedyParityRows countSys 2 twoVarAnd.length 2 []
    countSys finalRows = #{σ : Fin 2 → Bool | twoVarAnd.eval σ = true} ∧
      #{σ : Fin 2 → Bool |
        PassesTests twoVarAnd.violations (finalRows.map (ofList twoVarAnd.length)) σ ∧
          twoVarAnd.eval σ = false} = 0 :=
  numPassing_greedyParityRows_fin twoVarAnd (by omega) (by omega) []
    (fun _ h => nomatch h) twoVarAnd_init_bound

-- Capacity-guarded Theorem 2.2 counter returning 999 if rows.length > 6 or any row has weight > 2.
private def guardedTwoVarCount (rows : List (List Bool)) : ℕ :=
  if rows.length ≤ 6 ∧ rows.all (fun r => decide (r.count true ≤ 2)) then
    numPassing twoVarAnd.violations (rows.map (ofList twoVarAnd.length))
  else 999
example : guardedTwoVarCount (List.replicate 7 [false, false]) = 999 := by decide
example : guardedTwoVarCount [[true, true, true]] = 999 := by decide
example :
    guardedTwoVarCount (greedyParityRows guardedTwoVarCount (Fintype.card (Fin 2))
      twoVarAnd.length 2 []) = #{σ : Fin 2 → Bool | twoVarAnd.eval σ = true} := by
  refine countSys_greedyParityRows_eq_card_sat twoVarAnd (by decide) (by omega)
    (fun _ h => nomatch h) (fun rows _ hlen hwt => ?_) twoVarAnd_init_bound
  have hlen' : rows.length ≤ 6 := by simpa only [List.length_nil, Fintype.card_fin] using hlen
  have hall : rows.all (fun r => decide (r.count true ≤ 2)) = true :=
    List.all_eq_true.mpr fun r hr => decide_eq_true ((hwt r hr).elim (fun h => nomatch h) id)
  simp only [guardedTwoVarCount, hlen', hall, and_self, ↓reduceIte]

-- Compositional fun_prop check for candidate decoding + mod-2 row materialization.
example : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × ℕ => materializeTestRow p.1.1 (decodeTestTuple p.1.1 p.1.2 p.2))
    (encPair (encPair encUnary encUnary) encNat) encBits := by fun_prop

-- Concrete NativeCertificate instantiation for ComputableInO and ComputableInPolySpace bounds.
private noncomputable def zeroCountCert :
    NativeCertificate (fun _ : List (List Bool) => 0) (encList encBits) encNat :=
  NativeCertificate.const 0

example : ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
    ComputableInO
      (fun a : ℕ × ℕ × List (List Bool) => selectBestTestRow (fun _ => 0) a.1 a.2.1 a.2.2)
      encSelectBestIn encBits
      (fun a => (candidateTupleCount a.1 a.2.1 + 1) *
        (poly (encSelectBestIn a).length + ((encList encBits a.2.2).length + (2 * a.1 + 1))))
      (fun a => poly (encSelectBestIn a).length) := by
  refine computableInO_selectBestTestRow zeroCountCert .self
    (fun a => (encList encBits a.2.2).length + (2 * a.1 + 1)) fun a j _ => ?_
  change (encList encBits (a.2.2 ++ [materializeTestRow a.1 (decodeTestTuple a.1 a.2.1 j)])).length
    ≤ _
  simp only [encList_append, List.length_append, encList_cons, encList_nil, List.append_nil,
    length_frame, encBits_apply, length_materializeTestRow]; omega

example : ComputableInPolySpace (fun a : ℕ × ℕ × ℕ × List (List Bool) =>
      greedyParityRows (fun _ => 0) a.1 a.2.1 a.2.2.1 a.2.2.2) encGreedyIn (encList encBits) :=
  computableInPolySpace_greedyParityRows zeroCountCert .self

end ComplexityTests.CNFGreedyParitySearch
