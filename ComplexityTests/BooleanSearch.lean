/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import Complexity.Computability.GenericRAM.Native.BooleanSearch
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

-- Regression tests intentionally export no declarations.
set_option linter.privateModule false

open Cslib.GenericRAM Cslib.GenericRAM.BooleanSearch Turing.MultiTapeTM

-- The empty cube contains one word, which can either pass or fail the test.
example : run (fun _ : Unit × List Bool => true) ((), 0) = some [] := by decide
example : run (fun _ : Unit × List Bool => false) ((), 0) = none := by decide
example : run (fun _ : Unit × List Bool => false) ((), 3) = none := by decide

-- First match in the existing little-endian order; later matches cannot replace it.
example : run (fun _ : Unit × List Bool => true) ((), 3) = some [false, false, false] := by
  decide
example : run (fun p : Unit × List Bool => p.2.headD false) ((), 2) =
    some [true, false] := by decide
example : (runPrefix (fun p : Unit × List Bool => p.2.headD false) ((), 2) 4).2.2.2 =
    some [true, false] := by decide

-- A one-row measurement selecting the first coordinate, with the desired value in context.
private def measurementTest (p : Bool × List Bool) : Bool := p.2.headD false == p.1

example : run measurementTest (false, 2) = some [false, false] ∧
    run measurementTest (true, 2) = some [true, false] := by decide
example : run measurementTest (true, 0) = none := by decide

-- Measurements are checked without the later fixed-bit constraint x₀ = true.
-- The unrestricted representative may fail that constraint although its fiber contains a word
-- satisfying it (the second scan uses that word).
private def secondCoordinate (p : Bool × List Bool) : Bool := p.2[1]?.getD false == p.1

example : run secondCoordinate (false, 2) = some [false, false] ∧
    secondCoordinate (false, [true, false]) = true ∧
    ([false, false] : List Bool).headD false = false := by decide

-- Width and context persist, including the completed index and terminal prefix.
example : runPrefix measurementTest (true, 2) 4 =
    (4, (2, (true, some [true, false]))) := by decide

-- The complete state includes framing, context, binary index and unary dimension.
example : (encPair encNat (encPair encUnary (encPair encBool (encOption (encList encBool))))
    (runPrefix measurementTest (true, 2) 4)).length ≤ 22 := by
  exact length_prefix_le measurementTest (true, 2) 4 (by decide)

private theorem measurementTest_polyTime :
    ComputableInPolyTime measurementTest (encPair encBool (encList encBool)) encBool := by
  have hword := ComputableInPolyTime.snd encBool (encList encBool)
  have hctx := ComputableInPolyTime.fst encBool (encList encBool)
  exact ((ComputableInPolyTime.headD false).comp hword).beq hctx

private noncomputable def measurementCertificate :
    NativeCertificate measurementTest (encPair encBool (encList encBool)) encBool :=
  NativeCertificate.ofPolyTime measurementTest_polyTime

-- An actual test machine is composed with the decoder and captured search step.
example : (stepCertificate measurementCertificate).IsPolynomial :=
  stepCertificate_isPolynomial _ (NativeCertificate.ofPolyTime_isPolynomial _)

-- The full search has traversal-proportional time and polynomial workspace on this test.
example : ∃ overhead workspace : Bool × ℕ → ℕ,
    PolyBounded (fun p => (encPair encBool encUnary p).length) overhead ∧
    PolyBounded (fun p => (encPair encBool encUnary p).length) workspace ∧
    ComputableInO (run measurementTest) (encPair encBool encUnary)
      (encOption (encList encBool)) (fun p => (2 ^ p.2 + 1) * overhead p) workspace :=
  exists_computableInO measurementCertificate (NativeCertificate.ofPolyTime_isPolynomial _)

-- A fixed native search machine handles both runtime dimensions and both measurement targets.
example : IsComputable (run measurementTest) (encPair encBool encUnary)
    (encOption (encList encBool)) := (certificate measurementCertificate).isComputable

-- The semantic and native clients agree on a concrete successful search.
example : ∃ word, run measurementTest (true, 2) = some word ∧
    word.length = 2 ∧ measurementTest (true, word) = true := by
  refine ⟨[true, false], by decide, ?_⟩
  exact run_some measurementTest (true, 2) (by decide)
