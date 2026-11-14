/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WordConstant
public import CslibFrontier.Computability.Circuit.Boolean.CodeComposition
public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native generation of Boolean constant words

The generator emits the existing two-gate constant circuit and each output's binary wire
reference. The numeral is binary encoded and the requested output width is unary encoded.

## Main definitions

* `Cslib.Circuits.Boolean.wordConstCode`: total raw constant-word circuit code.

## Main results

* `Cslib.Circuits.Boolean.wordConstCode_eq_bits`: exact code, including truncated numerals.
* `Cslib.Circuits.Boolean.wordConstCode_eq`: agreement for a bounded numeral.
* `Cslib.Circuits.Boolean.computableInPolyTime_wordConstCode`: native generation of the full code.

Extracted from the threshold generator with the circuit and encoding unchanged. Oversized
numerals generate their low bits.
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM ComputableInPolyTime

/-- The two constant gates and their selected output wires for a binary numeral. -/
@[expose] def wordConstCode (n w q : ℕ) : List (Op × List ℕ) × List ℕ :=
  ([(.const false, []), (.const true, [])],
    (List.range w).map (fun i => if q.testBit i then n + 1 else n))

/-- The total raw code selects the numeral's low bits, including an oversized numeral. -/
theorem wordConstCode_eq_bits (n w q : ℕ) :
    wordConstCode n w q = (wordConstCircuit n (fun i : Fin w => q.testBit i.val)).code := by
  have hw (i : Fin w) :
      ((wordConstCircuit n (fun i : Fin w => q.testBit i.val)).outputs i).toNat =
        if q.testBit i.val then n + 1 else n := by
    dsimp only [wordConstCircuit, Circuit.comp, Circuit.wiring, Function.comp_apply,
      Program.appendedWire]
    split_ifs <;> rfl
  apply Prod.ext
  · rfl
  · apply List.ext_getElem (by simp [wordConstCode, Circuit.code])
    intro i hi hj
    simp only [wordConstCode, List.getElem_map, List.getElem_range, Circuit.code,
      List.getElem_ofFn, hw]

/-- The raw numeral code is exactly the typed constant-word circuit. -/
theorem wordConstCode_eq (n w : ℕ) (q : Fin (2 ^ w)) :
    wordConstCode n w q.val = (wordConstCircuit n ((BitString.equivFin w).symm q)).code := by
  rw [wordConstCode_eq_bits]
  apply congrArg (fun b : BitString w => (wordConstCircuit n b).code)
  funext i
  exact (BitString.equivFin_symm_apply q i).symm

/-- Native generation charges every output reference, from unary width and a binary numeral. -/
theorem computableInPolyTime_wordConstCode {α : Type} {enc : α ↪ List Bool}
    {n w q : α → ℕ} (hn : ComputableInPolyTime n enc encNat)
    (hw : ComputableInPolyTime w enc encUnary) (hq : ComputableInPolyTime q enc encNat) :
    ComputableInPolyTime (fun a => wordConstCode (n a) (w a) (q a)) enc encCode := by
  have hi : ComputableInPolyTime
      (fun p : α × ℕ => if (q p.1).testBit p.2 then n p.1 + 1 else n p.1)
      (encPair enc encUnary) encNat := by
    have hn' := (hn.comp (fst enc encUnary)).tidy
    have hq' := (hq.comp (fst enc encUnary)).tidy
    have hi' := (snd enc encUnary).tidy
    have ht := ComputableTidilyInPolyTime.binary_testBit hq' hi'
    exact .of_tidy (ht.cond
      (ComputableTidilyInPolyTime.binary_add.comp
        (hn'.prod (ComputableTidilyInPolyTime.const 1))) hn')
  exact (const (encOut := encList encGate) [(Op.const false, []), (Op.const true, [])]).prod
    (mapWithInput (range.comp hw) hi)

end Cslib.Circuits.Boolean
