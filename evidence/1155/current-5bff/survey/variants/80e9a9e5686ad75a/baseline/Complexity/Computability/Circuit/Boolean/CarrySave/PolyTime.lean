/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.CarrySave
public import Complexity.Computability.Circuit.Boolean.CodeTemplate
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native generation of carry-save circuits

Fixed three-input formula templates generate each sum and carry bit. The lowest carry bit is a
constant, so the carry blocks have different gate counts. `appendCodes` assembles their actual
codes without padding. Composition then generates the existing four-to-two reducer.

The width is unary, and all emitted gate and output references are binary. These certificates
charge the full code and hold uniformly at every width, including zero.

## Main definitions

* `Cslib.Circuits.Boolean.csaSumCode`, `Cslib.Circuits.Boolean.csaCarryCode`: raw code templates
  for sum and carry bits.
* `Cslib.Circuits.Boolean.csa3to2Code`: raw code generation for the three-to-two reducer.
* `Cslib.Circuits.Boolean.csa4to2Code`: raw code generation for the four-to-two reducer.

## Main results

* `Cslib.Circuits.Boolean.csa3to2Code_eq_code`,
  `Cslib.Circuits.Boolean.csa4to2Code_eq_code`: exact agreement with the existing circuits.
* `Cslib.Circuits.Boolean.computableInPolyTime_csa3to2`,
  `Cslib.Circuits.Boolean.computableInPolyTime_csa4to2`: uniform native constructors.

## References

The underlying carry-save circuits are formalized in `Boolean.CarrySave`, following
[Chandra, Stockmeyer and Vishkin][ChandraStockmeyerVishkin1984] and
[Vollmer, Chapter 1][Vollmer1999].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM ComputableTidilyInPolyTime

private def sumTemplate : Formula signature 3 :=
  ((Formula.input 0).xor (.input 1)).xor (.input 2)

/-- The sum-bit formula instantiated at three raw input references. -/
def csaSumCode (w i : ℕ) : List (Op × List ℕ) × List ℕ :=
  formulaCode (w + (w + w)) (((Formula.input (n := 3) 0).xor (.input 1)).xor (.input 2))
    ![i, w + i, w + (w + i)]

/-- A carry-bit formula, including the constant lowest carry and total raw-index behavior. -/
def csaCarryCode (w i : ℕ) : List (Op × List ℕ) × List ℕ :=
  if 0 < i then
    formulaCode (w + (w + w)) (maj3Formula (0 : Fin 3) 1 2)
      ![i - 1, w + (i - 1), w + (w + (i - 1))]
  else ([(.const false, [])], [w + (w + w)])

private theorem csaSumCode_eq (w : ℕ) (i : Fin w) :
    csaSumCode w i.val = (csaSumFormula w i).toCircuit.code := by
  let wires : Fin 3 → Fin (w + (w + w)) :=
    ![Fin.castAdd (w + w) i, Fin.natAdd w (Fin.castAdd w i), Fin.natAdd w (Fin.natAdd w i)]
  have hw : (fun j => (wires j).val) = ![i.val, w + i.val, w + (w + i.val)] := by
    funext j
    fin_cases j <;> simp [wires, Nat.add_comm]
  have h := formulaCode_eq_code sumTemplate wires
  rw [hw] at h
  exact h

private theorem csaCarryCode_eq (w : ℕ) (i : Fin w) :
    csaCarryCode w i.val = (csaCarryFormula w i).toCircuit.code := by
  by_cases hi : 0 < i.val
  · let j : Fin w := ⟨i.val - 1, by omega⟩
    let wires : Fin 3 → Fin (w + (w + w)) :=
      ![Fin.castAdd (w + w) j, Fin.natAdd w (Fin.castAdd w j), Fin.natAdd w (Fin.natAdd w j)]
    have hw : (fun k => (wires k).val) =
        ![i.val - 1, w + (i.val - 1), w + (w + (i.val - 1))] := by
      funext k
      fin_cases k <;> simp [wires, j, Nat.add_comm]
    have h := formulaCode_eq_code (maj3Formula (0 : Fin 3) 1 2) wires
    rw [hw] at h
    simp only [csaCarryCode, csaCarryFormula, hi, ↓reduceIte, ↓reduceDIte]
    exact h
  · simp only [csaCarryCode, csaCarryFormula, hi, ↓reduceIte, ↓reduceDIte]
    rfl

/-- Generate the full three-to-two carry-save circuit code from its width. -/
def csa3to2Code (w : ℕ) : List (Op × List ℕ) × List ℕ :=
  appendCode (w + (w + w))
    (appendCodes (w + (w + w)) ((List.range w).map (csaSumCode w)))
    (appendCodes (w + (w + w)) ((List.range w).map (csaCarryCode w)))

/-- Generation preserves the exact existing circuit, including its unequal carry-bit blocks. -/
theorem csa3to2Code_eq_code (w : ℕ) : csa3to2Code w = (csa3to2 w).code := by
  have hs : (List.range w).map (csaSumCode w) =
      List.ofFn (fun i : Fin w => (csaSumFormula w i).toCircuit.code) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
      csaSumCode_eq w ⟨i, by simpa using hi⟩
  have hc : (List.range w).map (csaCarryCode w) =
      List.ofFn (fun i : Fin w => (csaCarryFormula w i).toCircuit.code) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
      csaCarryCode_eq w ⟨i, by simpa using hi⟩
  rw [csa3to2Code, hs, hc, appendCodes_code, appendCodes_code, appendCode_code]
  rfl

/-- The actual three-to-two reducer has a uniform native generator on unary widths. -/
@[fun_prop] theorem computableInPolyTime_csa3to2 :
    ComputableInPolyTime (fun w => (csa3to2 w).code) encUnary encCode := by
  refine .of_tidy ?_
  have hw : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1)
      (encPair encUnary encUnary) encNat := unary_to_binary.comp (fst _ _)
  have hi : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.2)
      (encPair encUnary encUnary) encNat := unary_to_binary.comp (snd _ _)
  have hs : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => csaSumCode p.1 p.2)
      (encPair encUnary encUnary) encCode := by
    apply ComputableInPolyTime.tidy
    apply computableInPolyTime_formulaCode _ (.of_tidy (by fun_prop))
    intro j
    apply ComputableInPolyTime.of_tidy
    fin_cases j
    · exact hi
    · change ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 + p.2) _ encNat
      fun_prop
    · change ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 + (p.1 + p.2)) _ encNat
      fun_prop
  have hm : ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ => formulaCode (p.1 + (p.1 + p.1)) (maj3Formula (0 : Fin 3) 1 2)
        ![p.2 - 1, p.1 + (p.2 - 1), p.1 + (p.1 + (p.2 - 1))])
      (encPair encUnary encUnary) encCode := by
    apply ComputableInPolyTime.tidy
    apply computableInPolyTime_formulaCode _ (.of_tidy (by fun_prop))
    intro j
    apply ComputableInPolyTime.of_tidy
    fin_cases j
    · change ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.2 - 1) _ encNat
      fun_prop
    · change ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 + (p.2 - 1)) _ encNat
      fun_prop
    · change ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 + (p.1 + (p.2 - 1))) _ encNat
      fun_prop
  have hc : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => csaCarryCode p.1 p.2)
      (encPair encUnary encUnary) encCode := by
    unfold csaCarryCode
    fun_prop
  have hw' := unary_to_binary
  have hn : ComputableTidilyInPolyTime (fun w : ℕ => w + (w + w)) encUnary encNat := by fun_prop
  have h := (computableInPolyTime_appendCode (.of_tidy hn)
    (computableInPolyTime_appendCodes (.of_tidy hn) (.of_tidy (mapWith hs id' range)))
    (computableInPolyTime_appendCodes (.of_tidy hn) (.of_tidy (mapWith hc id' range)))).tidy
  simpa only [← csa3to2Code_eq_code, csa3to2Code] using h

private theorem csa4to2FirstIn_val (w : ℕ) (i : Fin (w + (w + w))) :
    (csa4to2FirstIn w i).val = i.val := by
  induction i using Fin.addCases with
  | left i => simp [csa4to2FirstIn]
  | right i =>
    induction i using Fin.addCases with
    | left i => simp [csa4to2FirstIn, Nat.add_comm]
    | right i => simp [csa4to2FirstIn, -Fin.natAdd_eq_addNat, Nat.add_assoc]

private theorem code_csa4to2FirstIn (w : ℕ) :
    (Circuit.wiring signature (csa4to2FirstIn w)).code = ([], List.range (w + (w + w))) := by
  simpa using Circuit.code_wiring_eq_map (σ := signature) (g := id) (csa4to2FirstIn_val w)

private theorem code_csa4to2LastIn (w : ℕ) :
    (Circuit.wiring signature
      (Fin.natAdd (w + w) ∘ Fin.natAdd w : Fin w → Fin ((w + w) + (w + w)))).code =
      ([], (List.range w).map (fun i => (w + w) + (w + i))) :=
  Circuit.code_wiring_eq_map fun i => by simp [Nat.add_comm]

/-- Generate the existing two-layer carry-save reducer, including all input wiring. -/
def csa4to2Code (w : ℕ) : List (Op × List ℕ) × List ℕ :=
  compCode ((w + w) + (w + w)) (csa3to2Code w)
    (appendCode ((w + w) + (w + w))
      ([], (List.range w).map (fun i => (w + w) + (w + i)))
      (compCode ((w + w) + (w + w)) (csa3to2Code w) ([], List.range (w + (w + w)))))

/-- The generated code is exactly the existing four-to-two circuit's code. -/
theorem csa4to2Code_eq_code (w : ℕ) : csa4to2Code w = (csa4to2 w).code := by
  rw [csa4to2Code, csa3to2Code_eq_code, ← code_csa4to2FirstIn, ← code_csa4to2LastIn,
    compCode_code, appendCode_code, compCode_code]
  rfl

/-- The actual four-to-two reducer has a uniform native generator on unary widths. -/
@[fun_prop] theorem computableInPolyTime_csa4to2 :
    ComputableInPolyTime (fun w => (csa4to2 w).code) encUnary encCode := by
  refine .of_tidy ?_
  have hw := unary_to_binary
  have hn : ComputableTidilyInPolyTime
      (fun w : ℕ => (w + w) + (w + w)) encUnary encNat := by fun_prop
  have hfirst : ComputableTidilyInPolyTime
      (fun w : ℕ => ([], List.range (w + (w + w)))) encUnary encCode := by
    have hr := unary_to_binary.map.comp
      (range.comp (show ComputableTidilyInPolyTime (fun w : ℕ => w + (w + w))
        encUnary encUnary from by fun_prop))
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using (const []).prod hr
  have hlast : ComputableTidilyInPolyTime
      (fun w : ℕ => ([], (List.range w).map (fun i => (w + w) + (w + i))))
      encUnary encCode := by
    have hw' := unary_to_binary.comp (fst encUnary encUnary)
    have hi := unary_to_binary.comp (snd encUnary encUnary)
    exact (const []).prod (mapWithInput range (show ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ => (p.1 + p.1) + (p.1 + p.2)) (encPair encUnary encUnary) encNat
      from by fun_prop))
  have h3 : ComputableTidilyInPolyTime csa3to2Code encUnary encCode := by
    simpa only [← csa3to2Code_eq_code] using computableInPolyTime_csa3to2.tidy
  have h := (computableInPolyTime_compCode (.of_tidy hn) (.of_tidy h3)
    (computableInPolyTime_appendCode (.of_tidy hn) (.of_tidy hlast)
      (computableInPolyTime_compCode (.of_tidy hn) (.of_tidy h3) (.of_tidy hfirst)))).tidy
  simpa only [← csa4to2Code_eq_code, csa4to2Code] using h

end Cslib.Circuits.Boolean
