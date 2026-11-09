/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Comparison
public import CslibFrontier.Computability.Circuit.Boolean.CodeTemplate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Tactic.FinCases

/-!
# Native generation of the multiplexer

A fixed four-input formula template generates each bit of the multiplexer `muxCircuit w`, and
`appendCodes` and `compCode` assemble them with the shared negation of the control bit, exactly as
in `muxCircuit` (`muxCode_code`). The width is unary and all emitted references are binary
(`computableInPolyTime_muxCode`).

## Main definitions

* `Cslib.Circuits.Boolean.muxTemplate`: the formula of one multiplexer bit.
* `Cslib.Circuits.Boolean.muxCode`: raw code generation for the multiplexer.

## Main results

* `Cslib.Circuits.Boolean.muxCode_code`: exact agreement with `muxCircuit`.
* `Cslib.Circuits.Boolean.computableInPolyTime_muxCode`: uniform native constructor.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- The formula `(x₀ ∧ x₁) ∨ (x₂ ∧ x₃)`, instantiated by `muxBit`. -/
def muxTemplate : Formula signature 4 :=
  ((Formula.input 0).and (.input 1)).or ((Formula.input 2).and (.input 3))

/-- The code of bit `i` of the multiplexer on words of `w` bits. -/
def muxBitCode (w i : ℕ) : List (Op × List ℕ) × List ℕ :=
  formulaCode (1 + (w + w) + 1) muxTemplate ![0, 1 + i, 1 + (w + w), 1 + (w + i)]

private theorem muxBitCode_eq (w : ℕ) (i : Fin w) :
    muxBitCode w i.val = (muxBit i).toCircuit.code := by
  let wires : Fin 4 → Fin (1 + (w + w) + 1) :=
    ![Fin.castAdd 1 (Fin.castAdd (w + w) 0), Fin.castAdd 1 (Fin.natAdd 1 (Fin.castAdd w i)),
      Fin.natAdd (1 + (w + w)) 0, Fin.castAdd 1 (Fin.natAdd 1 (Fin.natAdd w i))]
  have hw : (fun j => (wires j).val) = ![0, 1 + i.val, 1 + (w + w), 1 + (w + i.val)] := by
    funext j
    fin_cases j <;> simp [wires, Nat.add_comm]
  have h := formulaCode_eq_code muxTemplate wires
  rw [hw] at h
  exact h

/-- The code of the multiplexer `muxCircuit w`: the negation of the control bit, then one formula
block per bit. -/
def muxCode (w : ℕ) : List (Op × List ℕ) × List ℕ :=
  compCode (1 + (w + w)) (appendCodes (1 + (w + w) + 1) ((List.range w).map (muxBitCode w)))
    (appendCode (1 + (w + w)) ([], List.range (1 + (w + w))) ([(.not, [0])], [1 + (w + w)]))

theorem muxCode_code (w : ℕ) : muxCode w = (muxCircuit w).code := by
  have hbits : (List.range w).map (muxBitCode w) =
      List.ofFn (fun i : Fin w => (muxBit i).toCircuit.code) :=
    List.ext_getElem (by simp) fun i hi _ => by
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      exact muxBitCode_eq w ⟨i, by simpa using hi⟩
  rw [muxCode, hbits, appendCodes_code, ← Circuit.code_wiring_id (σ := signature),
    show ([(Op.not, [0])], [1 + (w + w)]) = (Circuit.oneGate (σ := signature) Op.not
      fun _ => Fin.castAdd (w + w) (0 : Fin 1)).code from rfl, appendCode_code, compCode_code]
  rfl

open Turing.MultiTapeTM ComputableInPolyTime

/-- The multiplexer on words of `w` bits has a polynomial-time generator in unary `w`. -/
theorem computableInPolyTime_muxCode : ComputableInPolyTime muxCode encUnary encCode := by
  have hw := unary_to_binary
  have hn : ComputableInPolyTime (fun w : ℕ => 1 + (w + w)) encUnary encNat := by fun_prop
  have hn1 : ComputableInPolyTime (fun w : ℕ => 1 + (w + w) + 1) encUnary encNat := by fun_prop
  have hbit : ComputableInPolyTime (fun p : ℕ × ℕ => muxBitCode p.1 p.2)
      (encPair encUnary encUnary) encCode := by
    have hw' := unary_to_binary.comp (fst encUnary encUnary)
    have hi := unary_to_binary.comp (snd encUnary encUnary)
    apply computableInPolyTime_formulaCode _ (by fun_prop)
    intro j
    fin_cases j
    · exact const 0
    · change ComputableInPolyTime (fun p : ℕ × ℕ => 1 + p.2) _ encNat
      fun_prop
    · change ComputableInPolyTime (fun p : ℕ × ℕ => 1 + (p.1 + p.1)) _ encNat
      fun_prop
    · change ComputableInPolyTime (fun p : ℕ × ℕ => 1 + (p.1 + p.2)) _ encNat
      fun_prop
  have hid : ComputableInPolyTime (fun w : ℕ => (([] : List (Op × List ℕ)),
      List.range (1 + (w + w)))) encUnary encCode := by
    have hr := unary_to_binary.map.comp
      (range.comp (show ComputableInPolyTime (fun w : ℕ => 1 + (w + w))
        encUnary encUnary from by fun_prop))
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using (const []).prod hr
  have hnot : ComputableInPolyTime (fun w : ℕ => ([(Op.not, [0])], [1 + (w + w)]))
      encUnary encCode :=
    (const _).prod (hn.cons' (const []))
  exact computableInPolyTime_compCode hn
    (computableInPolyTime_appendCodes hn1 (mapWithInput range hbit))
    (computableInPolyTime_appendCode hn hid hnot)

end Cslib.Circuits.Boolean
