/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Modular.PartialProduct
import all Complexity.Computability.Circuit.Boolean.Modular.PartialProduct
public import Complexity.Computability.Circuit.Boolean.CodeTemplate
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native partial-product generation

The complete shifted word is generated from unary width and shift. Every emitted gate and binary
wire is charged. Out-of-range raw shifts have total behavior; the exact circuit theorem uses a
valid shift.

## Main definitions

* `Cslib.Circuits.Boolean.Modular.partialProductCode`: raw circuit code for a shifted partial
  product.

## Main results

* `Cslib.Circuits.Boolean.Modular.partialProductCode_eq_code`: exact typed-circuit agreement.
* `Cslib.Circuits.Boolean.Modular.computableInPolyTime_partialProductCode`: native generation.
-/

public section

namespace Cslib.Circuits.Boolean.Modular

open Turing.MultiTapeTM ComputableTidilyInPolyTime

variable {w : ℕ}

/-- Code for one retained product digit or its zero fallback. -/
private def partialProductBitCode (w i j : ℕ) : List (Op × List ℕ) × List ℕ :=
  if i ≤ j then formulaCode (w + w)
    ((Formula.input (n := 2) 0).and (.input 1)) ![j - i, w + i]
  else ([(.const false, [])], [w + w])

/-- Generate all retained shifted product digits, including the zero lower positions. -/
def partialProductCode (w i : ℕ) : List (Op × List ℕ) × List ℕ :=
  appendCodes (w + w) ((List.range w).map (partialProductBitCode w i))

private theorem partialProductBitCode_eq (i j : Fin w) :
    partialProductBitCode w i.val j.val = (partialProductBit w i j).toCircuit.code := by
  by_cases h : i.val ≤ j.val
  · let wires : Fin 2 → Fin (w + w) :=
      ![Fin.castAdd w ⟨j.val - i.val, by omega⟩, Fin.natAdd w i]
    have he : (fun k => (wires k).val) = ![j.val - i.val, w + i.val] := by
      funext k
      fin_cases k <;> rfl
    have ht := formulaCode_eq_code ((Formula.input (n := 2) 0).and (.input 1)) wires
    rw [he] at ht
    have hf : (((Formula.input (n := 2) 0).and (.input 1)).rename wires) =
        partialProductBit w i j := by
      simp only [partialProductBit, h, ↓reduceDIte, Formula.rename, Formula.and,
        Formula.gate_bind]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hf] at ht
    simpa only [partialProductBitCode, h, ↓reduceIte] using ht
  · simp only [partialProductBitCode, partialProductBit, h, ↓reduceIte, ↓reduceDIte]
    rfl

/-- Native generation retains exactly the existing parallel partial-product circuit. -/
theorem partialProductCode_eq_code (i : Fin w) :
    partialProductCode w i.val = (partialProduct w i).code := by
  have he : (List.range w).map (partialProductBitCode w i.val) =
      List.ofFn (fun j : Fin w => (partialProductBit w i j).toCircuit.code) := by
    apply List.ext_getElem (by simp)
    intro j hj hj'
    simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
      partialProductBitCode_eq i ⟨j, by simpa using hj⟩
  rw [partialProductCode, he, appendCodes_code]
  rfl

/-- The full raw partial-product code is generated uniformly in unary width and shift. -/
theorem computableInPolyTime_partialProductCode :
    ComputableInPolyTime (fun p : ℕ × ℕ => partialProductCode p.1 p.2)
      (encPair encUnary encUnary) encCode := by
  apply ComputableInPolyTime.of_tidy
  have hw : ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.1)
      (encPair (encPair encUnary encUnary) encUnary) encNat := by fun_prop
  have hi : ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.2)
      (encPair (encPair encUnary encUnary) encUnary) encNat := by fun_prop
  have hj : ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.2)
      (encPair (encPair encUnary encUnary) encUnary) encNat := by fun_prop
  have ht : ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℕ =>
      formulaCode (p.1.1 + p.1.1)
        ((Formula.input (n := 2) 0).and (.input 1)) ![p.2 - p.1.2, p.1.1 + p.1.2])
      (encPair (encPair encUnary encUnary) encUnary) encCode := by
    apply ComputableInPolyTime.tidy
    apply computableInPolyTime_formulaCode _ (.of_tidy (by fun_prop))
    intro k
    apply ComputableInPolyTime.of_tidy
    fin_cases k
    · change ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.2 - p.1.2) _ encNat
      fun_prop
    · change ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.1 + p.1.2) _ encNat
      fun_prop
  have hb : ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => partialProductBitCode p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encUnary) encCode := by
    unfold partialProductBitCode
    fun_prop
  exact (computableInPolyTime_appendCodes (.of_tidy (by fun_prop))
    (.of_tidy (mapWith hb id' (range.comp (fst _ _))))).tidy

end Cslib.Circuits.Boolean.Modular
