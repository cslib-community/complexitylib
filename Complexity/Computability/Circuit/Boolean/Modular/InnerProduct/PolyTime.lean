/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Modular.InnerProduct
import all Complexity.Computability.Circuit.Boolean.Modular.InnerProduct
public import Complexity.Computability.Circuit.Boolean.Modular.Multiply.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native modular inner-product generation

Unary array count and word width generate all block selectors, complete product circuits and the
balanced sum. Binary wire numbers and every generated code list are charged.

## Main definitions

* `Cslib.Circuits.Boolean.Modular.innerProductCode`: raw circuit code for the modular inner product.

## Main results

* `Cslib.Circuits.Boolean.Modular.innerProductCode_eq_code`: exact raw and typed code agreement.
* `Cslib.Circuits.Boolean.Modular.computableInPolyTime_innerProduct`: native generation.
-/

public section

namespace Cslib.Circuits.Boolean.Modular

open Turing.MultiTapeTM ComputableInPolyTime

local notation "Code" => List (Op × List ℕ) × List ℕ

/-- Raw input selectors for the corresponding block of two complete word arrays. -/
private def innerProductInputsCode (k w j : ℕ) : Code :=
  ([], (List.range w).map (fun i => j * w + i) ++
    (List.range w).map (fun i => k * w + (j * w + i)))

private theorem innerProductInputsCode_eq {k w : ℕ} (j : Fin k) :
    innerProductInputsCode k w j.val =
      (Circuit.wiring signature (innerProductInputs k w j)).code := by
  apply Prod.ext
  · rfl
  change _ = List.ofFn (fun i => (innerProductInputs k w j i).val)
  rw [List.ofFn_add]
  have hl : (fun i : Fin w => (innerProductInputs k w j (Fin.castAdd w i)).val) =
      (fun i : Fin w => j.val * w + i.val) := by
    funext i
    simp only [innerProductInputs, Fin.addCases_left, Fin.val_castAdd]
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  have hr : (fun i : Fin w => (innerProductInputs k w j (Fin.natAdd w i)).val) =
      (fun i : Fin w => k * w + (j.val * w + i.val)) := by
    funext i
    simp only [innerProductInputs, Fin.addCases_right, Fin.val_natAdd]
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  change _ ++ _ = List.ofFn (fun i : Fin w =>
      (innerProductInputs k w j (Fin.castAdd w i)).val) ++ _
  rw [hl, hr]
  congr 1 <;> apply List.ext_getElem (by simp) <;> intro i hi hi' <;> simp

/-- Generate every product and its zero carry-save companion before the complete sum. -/
def innerProductCode (k w : ℕ) : Code :=
  sumPairsCode (k * w + k * w) w ((List.range k).map fun j =>
    pairWithZeroCode (k * w + k * w) w
      (compCode (k * w + k * w) (multiplyCode w) (innerProductInputsCode k w j)))

/-- Gate-for-gate agreement includes empty arrays and zero-width words. -/
theorem innerProductCode_eq_code (k w : ℕ) :
    innerProductCode k w = (innerProduct k w).code := by
  have he : (List.range k).map (fun j => pairWithZeroCode (k * w + k * w) w
      (compCode (k * w + k * w) (multiplyCode w) (innerProductInputsCode k w j))) =
      (List.ofFn fun j : Fin k => pairWithZero (innerProductTerm k w j)).map Circuit.code := by
    rw [List.map_ofFn]
    apply List.ext_getElem (by simp)
    intro j hj hj'
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [multiplyCode_eq_code, innerProductInputsCode_eq ⟨j, by simpa using hj⟩,
      compCode_code, pairWithZeroCode_eq_code]
    rfl
  rw [innerProductCode, he, sumPairsCode_eq_code]
  rfl

/-- The full constructor is uniform in unary count and width. -/
@[fun_prop] theorem computableInPolyTime_innerProduct :
    ComputableInPolyTime (fun p : ℕ × ℕ => (innerProduct p.1 p.2).code)
      (encPair encUnary encUnary) encCode := by
  have hw : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.2)
      (encPair (encPair encUnary encUnary) encUnary) encUnary := by fun_prop
  have hwire : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.2 * p.1.1.2 + p.2)
      (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encNat :=
    unary_to_binary.comp (by fun_prop)
  have hwire' : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.1.1 * p.1.1.2 +
        (p.1.2 * p.1.1.2 + p.2))
      (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encNat :=
    unary_to_binary.comp (by fun_prop)
  have hin : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => innerProductInputsCode p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encUnary) encCode :=
    (const (encOut := encList encGate) []).prod
      (listAppend' (mapWithInput (range.comp hw) hwire)
        (mapWithInput (range.comp hw) hwire'))
  have hmul : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => multiplyCode p.1.2)
      (encPair (encPair encUnary encUnary) encUnary) encCode := by
    simpa only [multiplyCode_eq_code, Function.comp_def] using
      computableInPolyTime_multiply.comp hw
  have hn_leaf : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => p.1.1 * p.1.2 + p.1.1 * p.1.2)
      (encPair (encPair encUnary encUnary) encUnary) encNat :=
    unary_to_binary.comp (by fun_prop)
  have hleaf : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => pairWithZeroCode (p.1.1 * p.1.2 + p.1.1 * p.1.2)
        p.1.2 (compCode (p.1.1 * p.1.2 + p.1.1 * p.1.2)
          (multiplyCode p.1.2) (innerProductInputsCode p.1.1 p.1.2 p.2)))
      (encPair (encPair encUnary encUnary) encUnary) encCode :=
    computableInPolyTime_pairWithZeroCode hn_leaf hw
      (computableInPolyTime_compCode hn_leaf hmul hin)
  suffices ComputableInPolyTime (fun p : ℕ × ℕ => innerProductCode p.1 p.2)
      (encPair encUnary encUnary) encCode by
    simpa only [← innerProductCode_eq_code] using this
  unfold innerProductCode
  exact computableInPolyTime_sumPairsCode (by fun_prop) (snd _ _)
    (mapWithInput (by fun_prop) hleaf)

end Cslib.Circuits.Boolean.Modular
