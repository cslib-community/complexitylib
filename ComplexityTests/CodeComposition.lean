/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.CodeComposition
import Complexity.Computability.Circuit.Boolean.CarrySave
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-! Tests of shared-input code append, including original input references, shifted gate
references, repeated outputs, zero-input constants and empty circuits. -/

namespace ComplexityTests.CodeComposition

open Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableInPolyTime

private def left : List (Op × List ℕ) × List ℕ := ([(.not, [0])], [2])

private def right : List (Op × List ℕ) × List ℕ :=
  ([(.not, [1]), (.and, [0, 2])], [3, 1, 3])

-- Original inputs 0 and 1 retain their references; right's gate 2 shifts to gate 3.
example : appendCode 2 left right =
    ([(.not, [0]), (.not, [1]), (.and, [0, 3])], [2, 4, 1, 4]) := by decide

example : (appendCode 2 left right).2.map
    (evalOutput [true, false] (appendCode 2 left right).1) = [false, true, false, true] := by decide

-- Two zero-input constant circuits still have disjoint gate namespaces.
example : appendCode 0 ([(.const true, [])], [0]) ([(.const false, [])], [0]) =
    ([(.const true, []), (.const false, [])], [0, 1]) := by decide

-- A zero-gate projection circuit can be appended without changing live inputs.
example : appendCode 2 ([], [1, 0]) right =
    ([(.not, [1]), (.and, [0, 2])], [1, 0, 3, 1, 3]) := by decide

example : appendCode 0 ([], []) ([], []) = ([], []) := by decide

/-- The constructor handles arbitrary raw codes and a binary input count uniformly. -/
theorem constructor_polynomialTime :
    ComputableInPolyTime
      (fun p : ℕ × (List (Op × List ℕ) × List ℕ) × (List (Op × List ℕ) × List ℕ) =>
        appendCode p.1 p.2.1 p.2.2)
      (encPair encNat (encPair encCode encCode)) encCode := by
  fun_prop

/-- The typed correspondence and resource theorem apply at zero dimensions. -/
example (c d : Circuit signature 0 0) :
    appendCode 0 c.code d.code = (c.append d).code ∧
      (appendCode 0 c.code d.code).1.length = c.size + d.size :=
  ⟨appendCode_code c d, by
    rw [length_appendCode, Circuit.length_code_fst, Circuit.length_code_fst]⟩

-- Every block has one gate, including repeated copies and different output lists.
example : bundleCode 2 1 [left, ([(.and, [0, 1])], [0, 2]), left] =
    ([(.not, [0]), (.and, [0, 1]), (.not, [0])], [2, 0, 3, 4]) := by decide

example : bundleCode 2 1 [left, ([(.and, [0, 1])], [0, 2]), left] =
    [left, ([(.and, [0, 1])], [0, 2]), left].foldl (appendCode 2) ([], []) := by
  apply bundleCode_eq_foldl_appendCode
  decide

example : bundleCode 0 0 [([], []), ([], [])] = ([], []) := by decide

-- Different gate counts, with zero-gate wiring between the two nonempty blocks.
example : appendCodes 2 [left, ([], [1, 0, 1]), right] =
    ([(.not, [0]), (.not, [1]), (.and, [0, 3])], [2, 1, 0, 1, 4, 1, 4]) := by decide

example : (appendCodes 2 [left, ([], [1, 0, 1]), right]).2.map
    (evalOutput [true, false] (appendCodes 2 [left, ([], [1, 0, 1]), right]).1) =
      [false, false, true, false, true, false, true] := by decide

example : appendCodes 0 [] = ([], []) := rfl

example : appendCodes 0 [([], []), ([(.const true, [])], [0, 0]),
    ([(.const false, []), (.not, [0])], [1])] =
      ([(.const true, []), (.const false, []), (.not, [1])], [0, 0, 2]) := by decide

-- Invalid references are relocated as binary data, including indices far beyond the gate list.
example : appendCodes 2 [left, ([(.not, [2 ^ 80])], [2 ^ 80, 0])] =
    ([(.not, [0]), (.not, [2 ^ 80 + 1])], [2, 2 ^ 80 + 1, 0]) := by decide

-- Malformed blocks need not evaluate independently: a missing earlier output can refer to a
-- later block after concatenation. The semantic theorem intentionally uses typed circuits.
example : (appendCodes 0 [([], [0]), ([(.const true, [])], [0])]).2.map
    (evalOutput [] (appendCodes 0 [([], [0]), ([(.const true, [])], [0])]).1) =
      [true, true] := by decide

example : [evalOutput [] [] 0, evalOutput [] [(.const true, [])] 0] =
    [false, true] := by decide

/-- Varying-size construction is certified uniformly on all raw codes and binary input counts. -/
theorem varying_bundler_polynomialTime :
    ComputableInPolyTime
      (fun p : ℕ × List (List (Op × List ℕ) × List ℕ) => appendCodes p.1 p.2)
      (encPair encNat (encList encCode)) encCode := by fun_prop

-- The carry-save carry outputs have different gate counts: no common block size applies.
example : (csaCarryFormula 2 0).toCircuit.size = 1 ∧
    (csaCarryFormula 2 1).toCircuit.size = 5 := by decide

/-- The existing carry-save circuit is assembled without padding its unequal carry-bit blocks. -/
example (w : ℕ) :
    appendCode (w + (w + w))
      (appendCodes (w + (w + w)) (List.ofFn fun i => (csaSumFormula w i).toCircuit.code))
      (appendCodes (w + (w + w)) (List.ofFn fun i => (csaCarryFormula w i).toCircuit.code)) =
        (csa3to2 w).code := by
  rw [appendCodes_code, appendCodes_code, appendCode_code]
  rfl

/-- The bundler has no block-size or well-formedness promise in its runtime certificate. -/
theorem bundler_polynomialTime :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List (List (Op × List ℕ) × List ℕ) =>
        bundleCode p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encNat) (encList encCode)) encCode := by
  fun_prop

/-- At zero outputs, fixed-size bundling and varying-size concatenation agree on the empty code. -/
example (cs : Fin 0 → Circuit signature 0 1) :
    bundleCode 0 0 (List.ofFn (fun j => (cs j).code)) =
      appendCodes 0 (List.ofFn (fun j => (cs j).code)) ∧
    (Circuit.pi cs).code = ([], []) := by
  rw [bundleCode_code cs 0 (fun j => j.elim0), appendCodes_code cs]
  exact ⟨rfl, rfl⟩

/-- Bundling two 1-gateinverter blocks on 2 shared inputs yields a 2-output circuit of size 2. -/
example :
    let cs : Fin 2 → Circuit signature 2 1 :=
      ![(Formula.input 0).not.toCircuit, (Formula.input 1).not.toCircuit]
    ∃ c : Circuit signature 2 2,
      bundleCode 2 1 (List.ofFn (fun j => (cs j).code)) = c.code ∧
        c.size = 2 ∧
        c.eval interpretation ![true, false] = ![false, true] := by
  intro cs
  have hsize : ∀ j, (cs j).size = 1 := by decide
  obtain ⟨c, hcode, heval⟩ := exists_circuit_bundleCode cs 1 hsize
  refine ⟨c, hcode, ?_, ?_⟩
  · rw [← Circuit.length_code_fst, ← hcode, length_bundleCode]
    · rfl
    · intro code hmem
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hmem
      exact (Circuit.length_code_fst _).trans (hsize j)
  · funext j
    rw [heval]
    fin_cases j <;> decide

/-- info: 'Cslib.Circuits.Boolean.bundleCode_eq_foldl_appendCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.bundleCode_eq_foldl_appendCode

end ComplexityTests.CodeComposition
