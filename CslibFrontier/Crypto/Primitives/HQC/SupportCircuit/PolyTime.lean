/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit
public import CslibFrontier.Computability.Circuit.Boolean.Modular.Multiply.PolyTime
public import CslibFrontier.Computability.Circuit.Boolean.WordConstant.PolyTime
import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native generation of the support candidate circuit

Raw code construction uses existing sequential and parallel composition, including every
constant, widened multiplier input, output selector and addition gate.

## Main definitions

* `Cslib.Crypto.HQC.candidateCode`: total native code generation for a candidate.

## Main results

* `Cslib.Crypto.HQC.candidateCode_eq_code`: exact agreement with the typed circuit.
* `Cslib.Crypto.HQC.computableInPolyTime_candidateCircuit`: generation from unary parameters.

These are original compiler certificates for the existing candidate formula. They do not charge
an offline compiler as attack execution or assert a static generator-description size.
-/

public section

namespace Cslib.Crypto.HQC

open Circuits Circuits.Boolean Turing.MultiTapeTM ComputableInPolyTime

/-- Emit all gates and output references of the concrete candidate circuit. -/
@[expose] def candidateCode (width bits n offset : ℕ) : List (Op × List ℕ) × List ℕ :=
  compCode width (carryLookaheadAdd bits).code
    (appendCode width
      (compCode width ([], (List.range bits).map (width + ·))
        (compCode width (Modular.multiply (width + bits)).code
          (appendCode width
            (appendCode width ([], List.range width) (wordConstCode width bits 0))
            (wordConstCode width (width + bits) (n - offset)))))
      (wordConstCode width bits offset))

/-- The emitted raw instructions agree exactly, including zero widths and invalid intervals. -/
theorem candidateCode_eq_code (width bits n offset : ℕ) :
    candidateCode width bits n offset = (candidateCircuit width bits n offset).code := by
  have hh : (Circuit.wiring signature (Fin.natAdd width : Fin bits → Fin (width + bits))).code =
      ([], (List.range bits).map (width + ·)) := Circuit.code_wiring_eq_map fun _ => rfl
  have hi : (Circuit.id signature width).code = ([], List.range width) :=
    Circuit.code_wiring_id
  rw [candidateCode, ← hh, ← hi]
  simp only [wordConstCode_eq_bits, Nat.zero_testBit, appendCode_code, compCode_code]
  rfl

/-- Native uniform generation of the complete candidate circuit from unary parameters.
The separate gate bound is `size_candidateCircuit_le`. -/
@[fun_prop] theorem computableInPolyTime_candidateCircuit {α : Type} {enc : α ↪ List Bool}
    {width bits n offset : α → ℕ} (hw : ComputableInPolyTime width enc encUnary)
    (hb : ComputableInPolyTime bits enc encUnary) (hn : ComputableInPolyTime n enc encUnary)
    (ho : ComputableInPolyTime offset enc encUnary) :
    ComputableInPolyTime (fun a => (candidateCircuit (width a) (bits a) (n a) (offset a)).code)
      enc encCode := by
  have hw' := unary_to_binary.comp hw
  have hwide : ComputableInPolyTime (fun a => width a + bits a) enc encUnary := by fun_prop
  have hid : ComputableInPolyTime (fun a => ([], List.range (width a))) enc encCode := by
    have h := unary_to_binary.map.comp (range.comp hw)
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using
      (const (encOut := encList encGate) []).prod h
  have hhigh : ComputableInPolyTime
      (fun a => ([], (List.range (bits a)).map (width a + ·))) enc encCode := by
    have hi : ComputableInPolyTime (fun p : α × ℕ => width p.1 + p.2)
        (encPair enc encUnary) encNat := unary_to_binary.comp (by fun_prop)
    exact (const (encOut := encList encGate) []).prod (mapWithInput (range.comp hb) hi)
  have hdiff : ComputableInPolyTime (fun a => n a - offset a) enc encNat :=
    unary_to_binary.comp (by fun_prop)
  have h := computableInPolyTime_compCode hw'
    (computableInPolyTime_carryLookaheadAdd.comp hb)
    (computableInPolyTime_appendCode hw'
      (computableInPolyTime_compCode hw' hhigh
        (computableInPolyTime_compCode hw' (Modular.computableInPolyTime_multiply.comp hwide)
          (computableInPolyTime_appendCode hw'
            (computableInPolyTime_appendCode hw' hid
              (computableInPolyTime_wordConstCode hw' hb (const 0)))
            (computableInPolyTime_wordConstCode hw' hwide hdiff))))
      (computableInPolyTime_wordConstCode hw' hb (unary_to_binary.comp ho)))
  change ComputableInPolyTime (fun a => candidateCode (width a) (bits a) (n a) (offset a))
    enc encCode at h
  simpa only [candidateCode_eq_code] using h

end Cslib.Crypto.HQC
