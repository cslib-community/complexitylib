/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.DecryptionCircuit
import all Complexity.Crypto.Computational.Homomorphic.GSW.DecryptionCircuit
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Circuit.Boolean.Modular.InnerProduct.PolyTime
public import Complexity.Computability.Circuit.Boolean.Modular.Subtract.PolyTime
public import Complexity.Computability.Circuit.Boolean.Layered.Compile.PolyTime
public import Complexity.Crypto.Computational.Homomorphic.Circuit.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native generation of complete GSW decryption circuits

Unary dimension and word width generate the full code of the actual raw-input decryptor, without
an assumed generator or runtime certificate. All matrix selectors and arithmetic circuits are
charged, even on inputs outside key-generation or encryption support.

## Main results

* `Cslib.Crypto.Homomorphic.GSW.DecryptionCircuit.code_eq_code`: exact generated code.
* `Cslib.Crypto.Homomorphic.GSW.DecryptionCircuit.computableInPolyTime_code`: public generator.
-/

public section

namespace Cslib.Crypto.Homomorphic.GSW.DecryptionCircuit

open Circuits Circuits.Boolean
open Turing.MultiTapeTM ComputableTidilyInPolyTime

local notation "Code" => List (Op × List ℕ) × List ℕ

private def rowCode (n w : ℕ) : Code :=
  ([], (List.range w).map fun i => n * w + (w - 1) * ((n + 1) * w) + i)

private theorem rowCode_eq (n w : ℕ) (hw : 0 < w) :
    rowCode n w = (Circuit.wiring signature (rowInputs n w hw 0)).code := by
  symm
  exact Circuit.code_wiring_eq_map fun i => by
    simp [rowInputs, selectedRow, finProdFinEquiv, Nat.mul_comm, Nat.add_comm,
      Nat.add_left_comm]

private def productInputsCode (n w : ℕ) : Code :=
  ([], List.range (n * w) ++ (List.range (n * w)).map
    (fun i => n * w + (w - 1) * ((n + 1) * w) + (w + i)))

private theorem tail_val (n w : ℕ) (hw : 0 < w) (i : Fin (n * w)) :
    (rowInputs n w hw (finProdFinEquiv.symm i).1.succ
      (finProdFinEquiv.symm i).2).val =
      n * w + (w - 1) * ((n + 1) * w) + (w + i.val) := by
  have he := congrArg Fin.val (finProdFinEquiv.apply_symm_apply i)
  simp only [finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_mk] at he
  simp only [rowInputs, selectedRow, Fin.val_natAdd, finProdFinEquiv, Equiv.coe_fn_mk,
    Fin.val_zero, Fin.val_succ]
  nlinarith [he]

private theorem productInputsCode_eq (n w : ℕ) (hw : 0 < w) :
    productInputsCode n w = (Circuit.wiring signature (productInputs n w hw)).code := by
  apply Prod.ext
  · rfl
  change _ = List.ofFn (fun i => (productInputs n w hw i).val)
  rw [List.ofFn_add]
  have hl : (fun i : Fin (n * w) =>
      (productInputs n w hw (Fin.castAdd (n * w) i)).val) = (fun i => i.val) := by
    funext i
    simp only [productInputs, Fin.append_left, Fin.val_castAdd]
  have hr : (fun i : Fin (n * w) =>
      (productInputs n w hw (Fin.natAdd (n * w) i)).val) =
      (fun i => n * w + (w - 1) * ((n + 1) * w) + (w + i.val)) := by
    funext i
    simp only [productInputs, Fin.append_right]
    exact tail_val n w hw i
  change _ ++ _ = List.ofFn (fun i : Fin (n * w) =>
      (productInputs n w hw (Fin.castAdd (n * w) i)).val) ++ _
  rw [hl, hr]
  congr 1 <;> apply List.ext_getElem (by simp) <;> intro i hi hi' <;> simp

private def decoderCode (w : ℕ) : Code :=
  if w = 0 then ([(.const false, [])], [w])
  else if w = 1 then ([], [0])
  else formulaCode w ((Formula.input (n := 2) 0).xor (.input 1)) ![w - 1, w - 2]

private theorem decoderCode_eq (w : ℕ) : decoderCode w = (decodeWord w).code := by
  by_cases h₀ : w = 0
  · subst w
    rfl
  · by_cases h₁ : w = 1
    · subst w
      rfl
    · let wires : Fin 2 → Fin w := ![⟨w - 1, by omega⟩, ⟨w - 2, by omega⟩]
      have he : (fun i => (wires i).val) = ![w - 1, w - 2] := by
        funext i
        fin_cases i <;> rfl
      have ht := formulaCode_eq_code ((Formula.input (n := 2) 0).xor (.input 1)) wires
      rw [he] at ht
      have hf : (((Formula.input (n := 2) 0).xor (.input 1)).rename wires) =
          (Formula.input ⟨w - 1, by omega⟩).xor (.input ⟨w - 2, by omega⟩) := by
        simp only [Formula.rename, Formula.xor, Formula.and, Formula.or, Formula.not,
          Formula.gate_bind]
        congr 1
        funext i
        fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ',
          Formula.gate_bind]
        all_goals
          congr 1
          funext j
          fin_cases j <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ',
            Formula.gate_bind, Formula.input_bind, wires]
        all_goals congr 1
        all_goals
          funext k
          fin_cases k
          simp only [Matrix.cons_val_zero', Formula.input_bind, Matrix.cons_val_zero,
            Matrix.cons_val_one]
      rw [hf] at ht
      simpa only [decoderCode, decodeWord, h₀, h₁, ↓reduceIte, ↓reduceDIte] using ht

/-- Generate the full selected-row GSW decryptor, including width-zero fallback behavior. -/
def code (n w : ℕ) : Code :=
  private_decl% (if w = 0 then ([(.const false, [])], [inputWidth n w])
  else compCode (inputWidth n w) (decoderCode w)
    (compCode (inputWidth n w) (Modular.subtractCode w)
      (appendCode (inputWidth n w) (rowCode n w)
        (compCode (inputWidth n w) (Modular.innerProductCode n w)
          (productInputsCode n w)))))

/-- The native constructor returns every gate and designated output of the actual circuit. -/
theorem code_eq_code (n w : ℕ) : code n w = (circuit n w).code := by
  by_cases hw : 0 < w
  · change (if w = 0 then _ else _) = _
    rw [ite_eq_right (by omega : w ≠ 0), decoderCode_eq, Modular.subtractCode_eq_code,
      rowCode_eq n w hw, Modular.innerProductCode_eq_code, productInputsCode_eq n w hw,
      compCode_code, appendCode_code, compCode_code, compCode_code]
    rw [circuit, dite_eq_left hw]
    rfl
  · have hz : w = 0 := by omega
    subst w
    rfl

private theorem native_rowCode :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => rowCode p.1 p.2)
      (encPair encUnary encUnary) encCode := by
  have hwire : ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℕ =>
      p.1.1 * p.1.2 + (p.1.2 - 1) * ((p.1.1 + 1) * p.1.2) + p.2)
      (encPair (encPair encUnary encUnary) encUnary) encNat := by fun_prop
  exact (const (encMid := encList encGate) []).prod
    (mapWith hwire id' (range.comp (snd _ _)))

private theorem native_productInputsCode :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => productInputsCode p.1 p.2)
      (encPair encUnary encUnary) encCode := by
  have hlen : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 * p.2)
      (encPair encUnary encUnary) encUnary := by fun_prop
  have hwire : ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℕ =>
      p.1.1 * p.1.2 + (p.1.2 - 1) * ((p.1.1 + 1) * p.1.2) + (p.1.2 + p.2))
      (encPair (encPair encUnary encUnary) encUnary) encNat := by fun_prop
  have hr : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => List.range (p.1 * p.2))
      (encPair encUnary encUnary) (encList encNat) := by
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using
      unary_to_binary.map.comp (range.comp hlen)
  exact (const (encMid := encList encGate) []).prod
    (listAppend' hr (mapWith hwire id' (range.comp hlen)))

private theorem native_decoderCode :
    ComputableTidilyInPolyTime decoderCode encUnary encCode := by
  have hw : ComputableTidilyInPolyTime (fun w : ℕ => w) encUnary encNat := unary_to_binary
  have ht : ComputableTidilyInPolyTime (fun w : ℕ =>
      formulaCode w ((Formula.input (n := 2) 0).xor (.input 1)) ![w - 1, w - 2])
      encUnary encCode := by
    apply ComputableInPolyTime.tidy
    apply computableInPolyTime_formulaCode _ (.of_tidy hw)
    intro i
    apply ComputableInPolyTime.of_tidy
    fin_cases i
    · change ComputableTidilyInPolyTime (fun w : ℕ => w - 1) _ encNat
      fun_prop
    · change ComputableTidilyInPolyTime (fun w : ℕ => w - 2) _ encNat
      fun_prop
  unfold decoderCode
  fun_prop

private theorem native_code :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => code p.1 p.2)
      (encPair encUnary encUnary) encCode := by
  have hn : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => inputWidth p.1 p.2)
      (encPair encUnary encUnary) encNat := by fun_prop
  have hi : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => Modular.innerProductCode p.1 p.2)
      (encPair encUnary encUnary) encCode := by
    simpa only [Modular.innerProductCode_eq_code] using
      Modular.computableInPolyTime_innerProduct.tidy
  have hs : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => Modular.subtractCode p.2)
      (encPair encUnary encUnary) encCode := by
    simpa only [Modular.subtractCode_eq_code, Function.comp_def] using
      Modular.computableInPolyTime_subtract.tidy.comp (snd _ _)
  have hd := native_decoderCode.comp (snd encUnary encUnary)
  have hbody := (computableInPolyTime_compCode (.of_tidy hn) (.of_tidy hd)
    (computableInPolyTime_compCode (.of_tidy hn) (.of_tidy hs)
      (computableInPolyTime_appendCode (.of_tidy hn) (.of_tidy native_rowCode)
        (computableInPolyTime_compCode (.of_tidy hn) (.of_tidy hi) (.of_tidy
          native_productInputsCode))))).tidy
  change ComputableTidilyInPolyTime (fun p : ℕ × ℕ =>
    if p.2 = 0 then ([(Op.const false, [])], [inputWidth p.1 p.2])
    else compCode (inputWidth p.1 p.2) (decoderCode p.2)
      (compCode (inputWidth p.1 p.2) (Modular.subtractCode p.2)
        (appendCode (inputWidth p.1 p.2) (rowCode p.1 p.2)
          (compCode (inputWidth p.1 p.2) (Modular.innerProductCode p.1 p.2)
            (productInputsCode p.1 p.2))))) _ _
  fun_prop

/-- One native polynomial-time algorithm generates the full decryptor from unary parameters. -/
theorem computableInPolyTime_code :
    ComputableInPolyTime (fun p : ℕ × ℕ => code p.1 p.2)
      (encPair encUnary encUnary) encCode := native_code.computableInPolyTime

private theorem native_circuit :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ =>
      (⟨inputWidth p.1 p.2, circuit p.1 p.2⟩ : Σ m, Circuit signature m 1))
      (encPair encUnary encUnary) (encCircuit 1) := by
  have hn : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => inputWidth p.1 p.2)
      (encPair encUnary encUnary) encUnary := by fun_prop
  exact (hn.prod native_code).of_enc_eq (fun p => by
    simp only [encCircuit_apply, code_eq_code])

/-- Generate the actual circuit together with its unary input arity in native polynomial time. -/
theorem computableInPolyTime_circuit :
    ComputableInPolyTime (fun p : ℕ × ℕ =>
      (⟨inputWidth p.1 p.2, circuit p.1 p.2⟩ : Σ m, Circuit signature m 1))
      (encPair encUnary encUnary) (encCircuit 1) := native_circuit.computableInPolyTime

/-- Generate the complete layered NAND augmentation, including its schedule and selectors. -/
theorem computableInPolyTime_layeredAugment :
    ComputableInPolyTime (fun p : ℕ × ℕ =>
      Layered.compile (inputWidth p.1 p.2 + inputWidth p.1 p.2)
        (augmentNand (circuit p.1 p.2)).code)
      (encPair encUnary encUnary) Layered.encCompiled := by
  have ha := computableInPolyTime_augmentNand.tidy.comp native_circuit
  have hview : ComputableTidilyInPolyTime
      (fun D : Σ m, Circuit signature m 1 => (D.1, D.2.code))
      (encCircuit 1) (encPair encUnary encCode) := .of_eq fun _ => rfl
  have hv := hview.comp ha
  exact (Layered.computableInPolyTime_compile (.of_tidy hv.fst') (.of_tidy hv.snd'))

end Cslib.Crypto.Homomorphic.GSW.DecryptionCircuit
