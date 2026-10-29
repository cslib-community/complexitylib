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

-- A one-row measurement selecting the first coordinate, with the desired value in context.
private def measurementTest (p : Bool × List Bool) : Bool := p.2.headD false == p.1

-- Measurements are checked without the later fixed-bit constraint x₀ = true.
-- The unrestricted representative may fail that constraint although its fiber contains a word
-- satisfying it (the second scan uses that word).
private def secondCoordinate (p : Bool × List Bool) : Bool := p.2[1]?.getD false == p.1

-- Empty cube, first-match order, context-dependent measurement tests, unrestricted second
-- coordinate, and prefix state/length bounds.
example :
    (run (fun _ : Unit × List Bool => true) ((), 0) = some [] ∧
      run (fun _ : Unit × List Bool => false) ((), 0) = none ∧
      run (fun _ : Unit × List Bool => false) ((), 3) = none) ∧
    (run (fun _ : Unit × List Bool => true) ((), 3) = some [false, false, false] ∧
      run (fun p : Unit × List Bool => p.2.headD false) ((), 2) = some [true, false] ∧
      (runPrefix (fun p : Unit × List Bool => p.2.headD false) ((), 2) 4).2.2.2 =
        some [true, false]) ∧
    ((run measurementTest (false, 2) = some [false, false] ∧
        run measurementTest (true, 2) = some [true, false]) ∧
      run measurementTest (true, 0) = none) ∧
    (run secondCoordinate (false, 2) = some [false, false] ∧
      secondCoordinate (false, [true, false]) = true ∧
      ([false, false] : List Bool).headD false = false) ∧
    runPrefix measurementTest (true, 2) 4 = (4, (2, (true, some [true, false]))) ∧
    (encPair encNat (encPair encUnary (encPair encBool (encOption (encList encBool))))
      (runPrefix measurementTest (true, 2) 4)).length ≤ 22 :=
  ⟨by decide, by decide, by decide, by decide, by decide,
   length_prefix_le measurementTest (true, 2) 4 (by decide)⟩

private theorem measurementTest_polyTime :
    ComputableInPolyTime measurementTest (encPair encBool (encList encBool)) encBool := by
  have hword := ComputableInPolyTime.snd encBool (encList encBool)
  have hctx := ComputableInPolyTime.fst encBool (encList encBool)
  exact ((ComputableInPolyTime.headD false).comp hword).beq hctx

private noncomputable def measurementCertificate :
    NativeCertificate measurementTest (encPair encBool (encList encBool)) encBool :=
  NativeCertificate.ofPolyTime measurementTest_polyTime

-- Step-certificate polynomiality, `ComputableInO` search bound, native computability, and
-- concrete `run_some` witness.
example :
    (stepCertificate measurementCertificate).IsPolynomial ∧
    (∃ overhead workspace : Bool × ℕ → ℕ,
      PolyBounded (fun p => (encPair encBool encUnary p).length) overhead ∧
      PolyBounded (fun p => (encPair encBool encUnary p).length) workspace ∧
      ComputableInO (run measurementTest) (encPair encBool encUnary)
        (encOption (encList encBool)) (fun p => (2 ^ p.2 + 1) * overhead p) workspace) ∧
    IsComputable (run measurementTest) (encPair encBool encUnary) (encOption (encList encBool)) ∧
    (∃ word, run measurementTest (true, 2) = some word ∧
      word.length = 2 ∧ measurementTest (true, word) = true) :=
  ⟨stepCertificate_isPolynomial _ (NativeCertificate.ofPolyTime_isPolynomial _),
   exists_computableInO measurementCertificate (NativeCertificate.ofPolyTime_isPolynomial _),
   (certificate measurementCertificate).isComputable,
   ⟨[true, false], by decide, run_some measurementTest (true, 2) (by decide)⟩⟩
