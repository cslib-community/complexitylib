/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.CarrySave.Reduce
import all Complexity.Computability.Circuit.Boolean.CarrySave.Reduce
public import Complexity.Computability.Circuit.Boolean.CarrySave.PolyTime
public import Complexity.Computability.Circuit.Boolean.CarryLookahead.PolyTime
public import Complexity.Computability.Circuit.Boolean.BalancedCode
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native generation of carry-save reductions

The generator preserves the complete half-split reducer, its zero fallback and the final adder.
Input counts and references are binary, word widths unary, and all supplied leaf code is charged.

## Main definitions

* `Cslib.Circuits.Boolean.pairWithZeroCode`, `Cslib.Circuits.Boolean.sumPairsCode`: raw code
  generators for `pairWithZero` and `sumPairs`.

## Main results

* `Cslib.Circuits.Boolean.sumPairsCode_eq_code`: exact reduction and final-adder code.
* `Cslib.Circuits.Boolean.computableInPolyTime_sumPairsCode`: uniform native generation.
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM ComputableTidilyInPolyTime

local notation "Code" => List (Op × List ℕ) × List ℕ

/-- One shared false gate with a complete repeated-output word. -/
private def falseWordCode (n w : ℕ) : Code := ([(.const false, [])], List.replicate w n)

private theorem falseWordCode_eq (n w : ℕ) :
    falseWordCode n w =
      ((Circuit.wiring signature (fun _ : Fin w => (0 : Fin 1))).comp
        (Circuit.oneGate (n := n) (.const false) Fin.elim0)).code := by
  apply Prod.ext
  · rfl
  change List.replicate w n = List.ofFn (fun _ : Fin w => n)
  simp

/-- Add the shared zero word to any supplied raw leaf code. -/
def pairWithZeroCode (n w : ℕ) (C : Code) : Code :=
  appendCode n C (falseWordCode n w)

/-- Exact carry-save representation of the original leaf. -/
theorem pairWithZeroCode_eq_code {n w : ℕ} (C : Circuit signature n w) :
    pairWithZeroCode n w C.code = (pairWithZero C).code := by
  rw [pairWithZeroCode, falseWordCode_eq, appendCode_code]
  rfl

/-- Generate the entire balanced sum and final carry-lookahead adder. -/
def sumPairsCode (n w : ℕ) (leaves : List Code) : Code :=
  compCode n (carryLookaheadAdd w).code
    (balancedCode n (csa4to2 w).code (falseWordCode n (w + w)) leaves)

/-- The raw generator preserves every original gate, fallback and output selector. -/
theorem sumPairsCode_eq_code {n w : ℕ} (cs : List (Circuit signature n (w + w))) :
    sumPairsCode n w (cs.map Circuit.code) = (sumPairs n w cs).code := by
  rw [sumPairsCode, falseWordCode_eq, balancedCode_eq_code, compCode_code]
  rfl

/-- Shared zero words are generated in time polynomial in unary output width and binary arity. -/
private theorem computableTidilyInPolyTime_falseWordCode
    {α : Type} {enc : α ↪ List Bool} {n w : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encNat)
    (hw : ComputableTidilyInPolyTime w enc encUnary) :
    ComputableTidilyInPolyTime (fun a => falseWordCode (n a) (w a)) enc encCode := by
  exact (const (encMid := encList encGate) [(Op.const false, [])]).prod
    (replicate hw hn)

/-- Pair generation charges all supplied leaf code. -/
@[fun_prop] theorem computableInPolyTime_pairWithZeroCode
    {α : Type} {enc : α ↪ List Bool} {n w : α → ℕ} {C : α → Code}
    (hn : ComputableInPolyTime n enc encNat)
    (hw : ComputableInPolyTime w enc encUnary)
    (hC : ComputableInPolyTime C enc encCode) :
    ComputableInPolyTime (fun a => pairWithZeroCode (n a) (w a) (C a)) enc encCode := by
  have hn := hn.tidy
  have hw := hw.tidy
  have hC := hC.tidy
  apply ComputableInPolyTime.of_tidy
  unfold pairWithZeroCode
  exact (computableInPolyTime_appendCode (.of_tidy hn) (.of_tidy hC)
    (.of_tidy (computableTidilyInPolyTime_falseWordCode hn hw))).tidy

/-- The native generator charges the complete leaf list and both reduction stages. -/
@[fun_prop] theorem computableInPolyTime_sumPairsCode
    {α : Type} {enc : α ↪ List Bool} {n w : α → ℕ} {cs : α → List Code}
    (hn : ComputableInPolyTime n enc encNat)
    (hw : ComputableInPolyTime w enc encUnary)
    (hcs : ComputableInPolyTime cs enc (encList encCode)) :
    ComputableInPolyTime (fun a => sumPairsCode (n a) (w a) (cs a)) enc encCode := by
  have hn := hn.tidy
  have hw := hw.tidy
  have hcs := hcs.tidy
  apply ComputableInPolyTime.of_tidy
  unfold sumPairsCode
  exact (computableInPolyTime_compCode (.of_tidy hn)
    (.of_tidy (computableInPolyTime_carryLookaheadAdd.tidy.comp hw))
    (computableInPolyTime_balancedCode (.of_tidy hn)
      (.of_tidy (computableInPolyTime_csa4to2.tidy.comp hw))
      (.of_tidy (computableTidilyInPolyTime_falseWordCode hn (by fun_prop))) (.of_tidy hcs))).tidy

end Cslib.Circuits.Boolean
