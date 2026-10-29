/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Layered.Compile.Correctness
public import Complexity.Crypto.Computational.Homomorphic.Layered.Correctness

/-!
# Homomorphic evaluation of ordinary Boolean circuits

Compile the shared De Morgan circuit, execute its layers, and select the designated outputs
without another key transition. There are twice the circuit's designated-output depth many
transitions. Unused gates do not increase this count, and depth-zero wiring uses the input key.

The final key here depends on actual circuit depth. `Homomorphic.Leveled.Basic` constructs a
depth-budgeted scheme, and `Homomorphic.Leveled.Correctness` proves normalization to a common
final key. Security reductions remain separate obligations.

## Main definitions

* `Cslib.Crypto.Homomorphic.Scheme.evaluateCircuit`: the actual compiler and encrypted evaluator.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.encryptedWires_evaluateCircuit`: evaluation along any valid
  supported key list, including repeated keys and inputs from previous evaluations.
* `Cslib.Crypto.Homomorphic.Scheme.encryptedWires_evaluateCircuit_of_generatedChain`: every
  supported execution evaluates the original circuit and retains the base ciphertext width.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Circuits Circuits.Boolean

variable {E : Scheme} {secretWidth ciphertextWidth : ℕ → ℕ}
  (D : DecryptionCircuits E secretWidth ciphertextWidth)

/-- Compile and evaluate raw circuit code, then select its outputs with no further key change.
The algorithm is total on raw codes; semantic correctness is for typed circuit codes. -/
def evaluateCircuit (n : ℕ) (publicKeys : List (List Bool))
    (encryptedKeys : List (List (List Bool))) (inputs : List (List Bool))
    (inputCount : ℕ) (code : List (Op × List ℕ) × List ℕ) : ProbComp (List (List Bool)) :=
  let compiled := Layered.compile inputCount code
  (fun row => compiled.2.map (row.getD · [])) <$>
    evaluateLayers D n publicKeys encryptedKeys inputs compiled.1

/-- Every supported evaluation preserves the ordered plaintext vector and exact ciphertext
width. Keys and encrypted links may repeat; inputs need only have the right width and
decryption, so outputs of previous evaluations are permitted. -/
theorem encryptedWires_evaluateCircuit (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Bootstrappable D)
    (n : ℕ) (keys : List (List Bool × List Bool)) (links : List (List (List Bool)))
    {inputCount outputCount : ℕ} (c : Circuit signature inputCount outputCount)
    (hcount : keys.length = 2 * c.depth + 1)
    (hkeys : ∀ key ∈ keys, key ∈ (ProbComp.eval (E.keyGen n)).support)
    (hlinks : E.ValidLinks n keys links)
    (x : Fin inputCount → Bool) (inputs : List (List Bool))
    (hinputs : E.EncryptedWires ciphertextWidth n (keys.getD 0 ([], [])).2
      (List.ofFn x) inputs)
    (outputs : List (List Bool))
    (houtputs : outputs ∈ (ProbComp.eval
      (evaluateCircuit D n (keys.tail.map Prod.fst) links inputs inputCount c.code)).support) :
    E.EncryptedWires ciphertextWidth n (keys.getD (2 * c.depth) ([], [])).2
      (List.ofFn (c.eval interpretation x)) outputs := by
  rw [evaluateCircuit, ProbComp.eval_map, PMF.mem_support_map_iff] at houtputs
  obtain ⟨row, hrow, rfl⟩ := houtputs
  have h := encryptedWires_evaluateLayers D hE hwidth hD n keys links
    (Layered.compile inputCount c.code).1 (by simpa only [Layered.length_compile] using hcount.ge)
    hkeys hlinks (List.ofFn x) inputs hinputs
    (by simpa only [List.length_ofFn] using Layered.wellFormed_compile c) row hrow
  have hselected := h.select (outputs := (Layered.compile inputCount c.code).2) (by
    simpa only [Layered.length_eval, List.length_ofFn] using Layered.outputs_valid_compile c)
  simpa only [Layered.select_eval_compile, Layered.length_compile] using hselected

/-- Every supported evaluation of an ordinary circuit decrypts to its ordered output vector.
The generated chain uses two key transitions per original depth, and no transition for output
selection. Input ciphertexts are fresh under the first key; the final widths are unchanged. -/
theorem encryptedWires_evaluateCircuit_of_generatedChain (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Bootstrappable D)
    (n : ℕ) (keys : List (List Bool × List Bool)) (links : List (List (List Bool)))
    {inputCount outputCount : ℕ} (c : Circuit signature inputCount outputCount)
    (hchain : (keys, links) ∈ (ProbComp.eval (E.generateKeyChain n (2 * c.depth))).support)
    (x : Fin inputCount → Bool) (inputs : List (List Bool))
    (hinputs : E.FreshInputs n (keys.getD 0 ([], [])).1 (List.ofFn x) inputs)
    (outputs : List (List Bool))
    (houtputs : outputs ∈ (ProbComp.eval
      (evaluateCircuit D n (keys.tail.map Prod.fst) links inputs inputCount c.code)).support) :
    E.EncryptedWires ciphertextWidth n (keys.getD (2 * c.depth) ([], [])).2
      (List.ofFn (c.eval interpretation x)) outputs := by
  obtain ⟨hcount, hkeys, hlinks⟩ :=
    (E.mem_support_generateKeyChain_iff n (2 * c.depth) keys links).1 hchain
  exact encryptedWires_evaluateCircuit D hE hwidth hD n keys links c hcount hkeys hlinks x
    inputs (hinputs.encryptedWires hE hwidth
      (E.key_mem_support_of_generatedChain hchain (Nat.zero_le _))) outputs houtputs

end Cslib.Crypto.Homomorphic.Scheme
