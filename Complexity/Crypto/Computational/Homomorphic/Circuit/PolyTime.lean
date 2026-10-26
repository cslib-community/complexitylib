/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Circuit
public import Complexity.Computability.Circuit.Boolean.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Circuit.Boolean.CodeComposition
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Polynomial-time generation of NAND-augmented circuits

The concrete augmentation transformer duplicates the encoded circuit, relocates its two input
blocks, and connects their outputs to the fixed two-gate NAND circuit. Existing code composition
certificates account for every binary wire lookup and relocation and the complete emitted code.
The circuit encoding records its input count in unary and its wire indices in binary.

## Main results

* `Cslib.Crypto.Homomorphic.computableInPolyTime_augmentNand`: uniform polynomial-time
  construction of the actual NAND augmentation.

## References

* [C. Gentry, *Fully Homomorphic Encryption Using Ideal Lattices*, Section 2][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic

open Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableTidilyInPolyTime

private theorem code_wiring_left (n : ℕ) :
    (Circuit.wiring signature (Fin.castAdd n : Fin n → Fin (n + n))).code =
      ([], List.range n) := by
  simpa using Circuit.code_wiring_eq_map (σ := signature)
    (f := (Fin.castAdd n : Fin n → Fin (n + n))) (g := id) fun _ => rfl

private theorem code_wiring_right (n : ℕ) :
    (Circuit.wiring signature (Fin.natAdd n : Fin n → Fin (n + n))).code =
      ([], (List.range n).map (fun i => n + i)) :=
  Circuit.code_wiring_eq_map fun _ => rfl

private def augmentCode (n : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  compCode (n + n) nandCircuit.code (appendCode (n + n)
    (compCode (n + n) code ([], List.range n))
    (compCode (n + n) code ([], (List.range n).map (fun i => n + i))))

private theorem code_augmentNand {n : ℕ} (D : Circuit signature n 1) :
    (augmentNand D).code = augmentCode n D.code := by
  unfold augmentNand Circuit.parallel
  rw [← compCode_code, ← appendCode_code, ← compCode_code, ← compCode_code,
    code_wiring_left, code_wiring_right]
  rfl

attribute [local fun_prop] ComputableInPolyTime.tidy in
private theorem computableTidilyInPolyTime_augmentCode {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {code : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hcode : ComputableTidilyInPolyTime code enc encCode) :
    ComputableTidilyInPolyTime (fun a => augmentCode (n a) (code a)) enc encCode := by
  have hnBinary := unary_to_binary.comp hn
  have hindices : ComputableTidilyInPolyTime (fun a => List.range (n a))
      enc (encList encNat) := by
    simpa only [Function.comp_def, List.map_id'] using
      unary_to_binary.map.comp (range.comp hn)
  have hleft : ComputableTidilyInPolyTime (fun a => ([], List.range (n a)))
      enc encCode := (const []).prod hindices
  have hright : ComputableTidilyInPolyTime
      (fun a => ([], (List.range (n a)).map (fun i => n a + i))) enc encCode := by
    apply ComputableTidilyInPolyTime.prod (const [])
    apply mapWithInput hindices
    fun_prop
  unfold augmentCode
  apply ComputableInPolyTime.tidy
  apply computableInPolyTime_compCode (.of_tidy (by fun_prop)) (.of_tidy (const _))
  apply computableInPolyTime_appendCode (.of_tidy (by fun_prop))
  · exact computableInPolyTime_compCode (.of_tidy (by fun_prop)) (.of_tidy hcode) (.of_tidy hleft)
  · exact computableInPolyTime_compCode (.of_tidy (by fun_prop)) (.of_tidy hcode) (.of_tidy hright)

/-- Generate the concrete NAND augmentation in uniform polynomial time. The input arity and
all gates, wire indices and output references are read and written through `encCircuit 1`. -/
@[fun_prop] theorem computableInPolyTime_augmentNand :
    ComputableInPolyTime
      (fun D : Σ n, Circuit signature n 1 => ⟨D.1 + D.1, augmentNand D.2⟩)
      (encCircuit 1) (encCircuit 1) := by
  refine .of_tidy ?_
  have hview : ComputableTidilyInPolyTime
      (fun D : Σ n, Circuit signature n 1 => (D.1, D.2.code))
      (encCircuit 1) (encPair encUnary encCode) := .of_eq fun _ => rfl
  have hn := hview.fst'
  have hcode := computableTidilyInPolyTime_augmentCode hn hview.snd'
  have hcount : ComputableTidilyInPolyTime (fun D : Σ n, Circuit signature n 1 => D.1 + D.1)
      (encCircuit 1) encUnary := by fun_prop
  exact (hcount.prod hcode).of_enc_eq (fun D => by
    simp only [encCircuit_apply, code_augmentNand])

end Cslib.Crypto.Homomorphic
