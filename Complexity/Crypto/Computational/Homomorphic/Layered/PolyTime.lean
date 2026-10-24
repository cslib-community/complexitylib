/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Layered
public import Complexity.Crypto.Computational.Homomorphic.Efficiency
public import Complexity.Computability.Circuit.Boolean.Layered.PolyTime
import Complexity.Computability.Probabilistic.Adaptive
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.GetD
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Uniform polynomial-time evaluation of encrypted layers

The actual evaluator has one uniform polynomial clock for the full encoded public input.
Binary wire lookups are bounded before unary conversion. Every node's output is truncated at
the generated decryption circuit's unary input arity, which bounds state growth even on malformed
keys, links, ciphertexts and node references. Correctness, fixed widths and secrecy assumptions
are not used in these runtime certificates.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_evaluateNode`: evaluate one node and truncate its output.
* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_evaluateLayer`: traverse a complete layer.
* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_evaluateLayerStep`: advance the public loop state.
* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_evaluateLayers`: execute the complete public loop.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Circuits Probability Turing.MultiTapeTM

variable {E : Scheme} {secretWidth ciphertextWidth : ℕ → ℕ}
  (D : DecryptionCircuits E secretWidth ciphertextWidth)
  (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => E.encrypt p.1 p.2.1 p.2.2))
  (hevaluate : IsPPTOn
    (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
    encBits (fun p => E.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
  (hD : ComputableTidilyInPolyTime
    (fun n => (⟨_, D.circuit n⟩ : Σ m, Circuit Boolean.signature m 1))
    encUnary (Boolean.encCircuit 1))
  {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {pk : α → List Bool}
  {encryptedKey inputs : α → List (List Bool)} {node : α → Boolean.Layered.Node}
  {layer : α → List Boolean.Layered.Node}

include hD in
private theorem computableTidilyInPolyTime_decryptionArity :
    ComputableTidilyInPolyTime (fun n => secretWidth n + ciphertextWidth n) encUnary encUnary := by
  have hview : ComputableTidilyInPolyTime
      (fun C : Σ m, Circuit Boolean.signature m 1 => (C.1, C.2.code))
      (Boolean.encCircuit 1) (encPair encUnary Boolean.encCode) := .of_eq fun _ => rfl
  exact (hview.comp hD).fst'

include hencrypt hevaluate hD in
/-- Execute the actual node program, including binary lookups and unconditional truncation. -/
@[fun_prop]
theorem isPPTOn_evaluateNode
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hpk : ComputableTidilyInPolyTime pk input encBits)
    (hek : ComputableTidilyInPolyTime encryptedKey input (encList encBits))
    (hinputs : ComputableTidilyInPolyTime inputs input (encList encBits))
    (hnode : ComputableTidilyInPolyTime node input Boolean.Layered.encNode) :
    IsPPTOn input encBits
      (fun a => evaluateNode D (n a) (pk a) (encryptedKey a) (inputs a) (node a)) := by
  have hcode := Boolean.Layered.computableInPolyTime_nodeCode.tidy.comp hnode
  have hfirst : ComputableTidilyInPolyTime
      (fun a => (inputs a).getD (node a).code.2.1 []) input encBits :=
    ComputableTidilyInPolyTime.listGetD_binary (encA := encBits) [] hinputs (by fun_prop)
  have hsecond : ComputableTidilyInPolyTime
      (fun a => (inputs a).getD (node a).code.2.2 []) input encBits :=
    ComputableTidilyInPolyTime.listGetD_binary (encA := encBits) [] hinputs (by fun_prop)
  have hraw : IsPPTOn input encBits (fun a =>
      if (node a).code.1.1 then
        if (node a).code.1.2 then
          refreshNand D (n a) (pk a) (encryptedKey a)
            ((inputs a).getD (node a).code.2.1 []) ((inputs a).getD (node a).code.2.2 [])
        else refresh D (n a) (pk a) (encryptedKey a) ((inputs a).getD (node a).code.2.1 [])
      else E.encrypt (n a) (pk a) (node a).code.1.2) := by
    apply IsPPTOn.cond hcode.fst'.fst'
    · apply IsPPTOn.cond hcode.fst'.snd'
      · exact isPPTOn_refreshNand hencrypt hevaluate D hD hn hpk hek hfirst hsecond
      · exact isPPTOn_refresh hencrypt hevaluate D hD hn hpk hek hfirst
    · exact hencrypt.preprocess (.of_tidy (hn.prod (hpk.prod hcode.fst'.snd')))
  have hcap := (computableTidilyInPolyTime_decryptionArity D hD).comp hn
  have hbounded := hraw.map_with (f := fun a ciphertext =>
    ciphertext.take (secretWidth (n a) + ciphertextWidth (n a)))
    (.of_tidy (ComputableTidilyInPolyTime.bitsTake.comp
      ((ComputableTidilyInPolyTime.snd input encBits).prod
        (hcap.comp (ComputableTidilyInPolyTime.fst input encBits)))))
  apply hbounded.congr
  intro a
  cases node a <;> rfl

include hencrypt hevaluate hD in
/-- Evaluate every node of a computed layer, charging the entire input and output lists. -/
@[fun_prop]
theorem isPPTOn_evaluateLayer
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hpk : ComputableTidilyInPolyTime pk input encBits)
    (hek : ComputableTidilyInPolyTime encryptedKey input (encList encBits))
    (hinputs : ComputableTidilyInPolyTime inputs input (encList encBits))
    (hlayer : ComputableTidilyInPolyTime layer input (encList Boolean.Layered.encNode)) :
    IsPPTOn input (encList encBits)
      (fun a => evaluateLayer D (n a) (pk a) (encryptedKey a) (inputs a) (layer a)) := by
  apply IsPPTOn.mapMWith (element := Boolean.Layered.encNode)
  · apply isPPTOn_evaluateNode D hencrypt hevaluate hD <;> fun_prop
  · exact hlayer

variable {publicKeys : α → List (List Bool)} {encryptedKeys : α → List (List (List Bool))}
  {layers : α → List (List Boolean.Layered.Node)} {state : α → ℕ × List (List Bool)}

include hencrypt hevaluate hD in
/-- Read the next public key, encrypted link and layer with a unary loop index, then advance it. -/
@[fun_prop]
theorem isPPTOn_evaluateLayerStep
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hpks : ComputableTidilyInPolyTime publicKeys input (encList encBits))
    (heks : ComputableTidilyInPolyTime encryptedKeys input (encList (encList encBits)))
    (hlayers : ComputableTidilyInPolyTime layers input
      (encList (encList Boolean.Layered.encNode)))
    (hstate : ComputableTidilyInPolyTime state input (encPair encUnary (encList encBits))) :
    IsPPTOn input (encPair encUnary (encList encBits))
      (fun a =>
        evaluateLayerStep D (n a) (publicKeys a) (encryptedKeys a) (layers a) (state a)) := by
  have hpk := (ComputableTidilyInPolyTime.listGetD (encA := encBits) []).comp
    (hpks.prod hstate.fst')
  have hek := (ComputableTidilyInPolyTime.listGetD (encA := encList encBits) []).comp
    (heks.prod hstate.fst')
  have hlayer := (ComputableTidilyInPolyTime.listGetD
    (encA := encList Boolean.Layered.encNode) []).comp (hlayers.prod hstate.fst')
  exact (isPPTOn_evaluateLayer D hencrypt hevaluate hD hn hpk hek hstate.snd' hlayer).pair
    (show ComputableTidilyInPolyTime (fun a => (state a).1 + 1) input encUnary by fun_prop)

include hencrypt hevaluate hD in
/-- Evaluate all layers with a strict polynomial clock in their full public encoding. The state
bound covers malformed keys and references, without `Scheme.Correct`, `FixedWidth` or input
validity premises. Secret keys are not arguments to the algorithm. -/
@[fun_prop]
theorem isPPTOn_evaluateLayers
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hpks : ComputableTidilyInPolyTime publicKeys input (encList encBits))
    (heks : ComputableTidilyInPolyTime encryptedKeys input (encList (encList encBits)))
    (hinputs : ComputableTidilyInPolyTime inputs input (encList encBits))
    (hlayers : ComputableTidilyInPolyTime layers input
      (encList (encList Boolean.Layered.encNode))) :
    IsPPTOn input (encList encBits)
      (fun a => evaluateLayers D (n a) (publicKeys a) (encryptedKeys a) (inputs a) (layers a)) := by
  have hcap := (computableTidilyInPolyTime_decryptionArity D hD).comp hn
  have hencoded : ComputableTidilyInPolyTime
      (fun a => (encList (encList Boolean.Layered.encNode) (layers a)).length)
      input encUnary := (ComputableTidilyInPolyTime.length (encL := encBits) encBool).comp
        hlayers.encoded
  let growth (a : α) := 2 + (encList (encList Boolean.Layered.encNode) (layers a)).length *
    (2 * (secretWidth (n a) + ciphertextWidth (n a)) + 1)
  have hgrowth : ComputableTidilyInPolyTime growth input encUnary := by
    dsimp only [growth]
    fun_prop
  have hstep : IsPPTOn (encPair input (encPair encUnary (encList encBits)))
      (encPair encUnary (encList encBits))
      (fun p : α × (ℕ × List (List Bool)) =>
        evaluateLayerStep D (n p.1) (publicKeys p.1) (encryptedKeys p.1) (layers p.1) p.2) := by
    apply isPPTOn_evaluateLayerStep D hencrypt hevaluate hD <;> fun_prop
  have hloop := IsPPTOn.iterateWith_of_bounded_growth
    (stateEncoding := encPair encUnary (encList encBits))
    (step := fun a => evaluateLayerStep D (n a) (publicKeys a) (encryptedKeys a) (layers a))
    ((ComputableTidilyInPolyTime.length (encList Boolean.Layered.encNode)).comp hlayers)
    ((ComputableTidilyInPolyTime.const 0).prod hinputs) hstep hgrowth.polyBounded
    (fun a state next hnext => ?_)
  · exact hloop.map (ComputableTidilyInPolyTime.snd encUnary (encList encBits))
  rw [evaluateLayerStep, ProbComp.eval_map, PMF.mem_support_map_iff] at hnext
  obtain ⟨outputs, houtputs, rfl⟩ := hnext
  have hbounds := evaluateLayer_bounds D (n a) ((publicKeys a).getD state.1 [])
    ((encryptedKeys a).getD state.1 []) state.2 ((layers a).getD state.1 []) outputs houtputs
  have hrow : (encList encBits outputs).length ≤
      ((layers a).getD state.1 []).length *
        (2 * (secretWidth (n a) + ciphertextWidth (n a)) + 1) := by
    rw [length_encList]
    calc
      (outputs.map fun ciphertext => 2 * (encBits ciphertext).length + 1).sum ≤
          (outputs.map fun _ => 2 * (secretWidth (n a) + ciphertextWidth (n a)) + 1).sum :=
        List.sum_le_sum fun ciphertext hc => by
          have := hbounds.2 ciphertext hc
          simp only [encBits_apply]
          omega
      _ = ((layers a).getD state.1 []).length *
          (2 * (secretWidth (n a) + ciphertextWidth (n a)) + 1) := by simp [hbounds.1]
  have hlayer : ((layers a).getD state.1 []).length ≤
      (encList (encList Boolean.Layered.encNode) (layers a)).length := by
    by_cases hi : state.1 < (layers a).length
    · rw [List.getD_eq_getElem _ _ hi]
      exact (length_le_length_encList Boolean.Layered.encNode _).trans
        (length_le_encList_of_mem (encList Boolean.Layered.encNode) (List.getElem_mem hi))
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
      exact Nat.zero_le _
  have houtput := hrow.trans (Nat.mul_le_mul_right
    (2 * (secretWidth (n a) + ciphertextWidth (n a)) + 1) hlayer)
  simp only [length_encPair, encUnary_apply, List.length_replicate]
  dsimp only [growth]
  omega

end Cslib.Crypto.Homomorphic.Scheme
