/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Modular.Subtract
import all Complexity.Computability.Circuit.Boolean.Modular.Subtract
public import Complexity.Computability.Circuit.Boolean.CarryLookahead.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native modular subtraction generation

The complete complement-plus-carry construction is generated from unary width. All circuit gates,
wire references and output selectors are charged.

## Main definitions

* `Cslib.Circuits.Boolean.Modular.subtractCode`: raw circuit code for modular subtraction.

## Main results

* `Cslib.Circuits.Boolean.Modular.subtractCode_eq_code`: exact generated code.
* `Cslib.Circuits.Boolean.Modular.computableInPolyTime_subtract`: native constructor.
-/

public section

namespace Cslib.Circuits.Boolean.Modular

open Turing.MultiTapeTM ComputableInPolyTime

local notation "Code" => List (Op × List ℕ) × List ℕ

private def notCode (w i : ℕ) : Code :=
  formulaCode (w + w) (Formula.input (n := 1) 0).not (fun _ => w + i)

private theorem notCode_eq {w : ℕ} (i : Fin w) :
    notCode w i.val = (Formula.input (Fin.natAdd w i)).not.toCircuit.code := by
  have h := formulaCode_eq_code (Formula.input (n := 1) 0).not
    (fun _ => Fin.natAdd w i)
  exact h

private theorem firstCode_eq (w : ℕ) :
    ([], List.range w) = (Circuit.wiring signature (Fin.castAdd w : Fin w → Fin (w + w))).code := by
  simpa using (Circuit.code_wiring_eq_map (σ := signature)
    (f := (Fin.castAdd w : Fin w → Fin (w + w))) (g := id) fun _ => rfl).symm

private theorem outputCode_eq (w : ℕ) :
    ([], List.range w) =
      (Circuit.wiring signature (fun i : Fin w => i.castSucc)).code := by
  simpa using (Circuit.code_wiring_eq_map (σ := signature)
    (f := fun i : Fin w => i.castSucc) (g := id) fun _ => rfl).symm

private def inputsCode (w : ℕ) : Code :=
  appendCode (w + w)
    (appendCode (w + w) ([], List.range w)
      (appendCodes (w + w) ((List.range w).map (notCode w))))
    ([(.const true, [])], [w + w])

private theorem inputsCode_eq (w : ℕ) : inputsCode w = (subtractInputs w).code := by
  have he : (List.range w).map (notCode w) =
      List.ofFn (fun i : Fin w => (Formula.input (Fin.natAdd w i)).not.toCircuit.code) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
      notCode_eq ⟨i, by simpa using hi⟩
  have ht : ([(Op.const true, [])], [w + w]) =
      (Circuit.oneGate (σ := signature) (n := w + w) (.const true) Fin.elim0).code := rfl
  rw [inputsCode, he, firstCode_eq, ht, appendCodes_code, appendCode_code, appendCode_code]
  rfl

/-- Generate the full modular subtractor, including the shared carry and discarded carry-out. -/
def subtractCode (w : ℕ) : Code :=
  private_decl% (compCode (w + w) ([], List.range w)
    (compCode (w + w) (carryLookahead w).code (inputsCode w)))

/-- Raw generation preserves the complete typed subtractor. -/
theorem subtractCode_eq_code (w : ℕ) : subtractCode w = (subtract w).code := by
  change compCode (w + w) ([], List.range w)
    (compCode (w + w) (carryLookahead w).code (inputsCode w)) = _
  rw [inputsCode_eq, outputCode_eq, compCode_code, compCode_code]
  rfl

/-- Full generation is polynomial-time in unary width, including binary gate and output indices. -/
@[fun_prop] theorem computableInPolyTime_subtract :
    ComputableInPolyTime (fun w => (subtract w).code) encUnary encCode := by
  have hn : ComputableInPolyTime (fun w : ℕ => w + w) encUnary encNat :=
    unary_to_binary.comp (by fun_prop)
  have hr : ComputableInPolyTime (fun w : ℕ => ([], List.range w)) encUnary encCode := by
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using
      (const (encOut := encList encGate) []).prod (unary_to_binary.map.comp range)
  have hnot : ComputableInPolyTime (fun p : ℕ × ℕ => notCode p.1 p.2)
      (encPair encUnary encUnary) encCode := by
    apply computableInPolyTime_formulaCode _ (unary_to_binary.comp (by fun_prop))
    intro i
    change ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + p.2) _ encNat
    exact unary_to_binary.comp (by fun_prop)
  have ht : ComputableInPolyTime (fun w : ℕ => ([(Op.const true, [])], [w + w]))
      encUnary encCode := (const _).prod (hn.cons' (const []))
  have hi := computableInPolyTime_appendCode hn
    (computableInPolyTime_appendCode hn hr
      (computableInPolyTime_appendCodes hn (mapWithInput range hnot))) ht
  have h := computableInPolyTime_compCode hn hr
    (computableInPolyTime_compCode hn computableInPolyTime_carryLookahead hi)
  simp_rw [← subtractCode_eq_code]
  change ComputableInPolyTime (fun w => compCode (w + w) ([], List.range w)
    (compCode (w + w) (carryLookahead w).code (inputsCode w))) encUnary encCode
  simpa only [inputsCode, Function.comp_def, List.map_id_fun', id_eq] using h

end Cslib.Circuits.Boolean.Modular
