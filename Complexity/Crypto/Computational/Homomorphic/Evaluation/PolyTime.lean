/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Evaluation
public import Complexity.Computability.Circuit.Boolean.Layered.Compile.PolyTime
public import Complexity.Crypto.Computational.Homomorphic.Layered.PolyTime
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time encrypted evaluation of ordinary circuits

The native certificate composes the actual compiler, layered evaluator, and output selection.
It includes the complete circuit code and handles malformed references and keys. It requires
efficient base encryption, base evaluation, and the decryption-circuit generator; correctness
and security assumptions play no role in this runtime statement.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_evaluateCircuit`: strict polynomial-time evaluation
  of raw Boolean circuit code, uniformly across its input and output arities.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Circuits Probability Turing.MultiTapeTM

variable {E : Scheme} {secretWidth ciphertextWidth : ℕ → ℕ}

/-- Compile, evaluate, and select outputs in native polynomial time. The compiler computes its
own depth table; there is no supplied runtime, depth, validity, or correctness certificate. -/
@[fun_prop]
theorem isPPTOn_evaluateCircuit (D : DecryptionCircuits E secretWidth ciphertextWidth)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => E.encrypt p.1 p.2.1 p.2.2))
    (hevaluate : IsPPTOn
      (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
      encBits (fun p => E.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hD : ComputableInPolyTime
      (fun n => (⟨_, D.circuit n⟩ : Σ m, Circuit Boolean.signature m 1))
      encUnary (Boolean.encCircuit 1))
    {α : Type} {input : α ↪ List Bool} {n inputCount : α → ℕ}
    {publicKeys inputs : α → List (List Bool)}
    {encryptedKeys : α → List (List (List Bool))}
    {code : α → List (Boolean.Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hpks : ComputableInPolyTime publicKeys input (encList encBits))
    (heks : ComputableInPolyTime encryptedKeys input (encList (encList encBits)))
    (hinputs : ComputableInPolyTime inputs input (encList encBits))
    (hcount : ComputableInPolyTime inputCount input encUnary)
    (hcode : ComputableInPolyTime code input Boolean.encCode) :
    IsPPTOn input (encList encBits)
      (fun a => evaluateCircuit D (n a) (publicKeys a) (encryptedKeys a) (inputs a)
        (inputCount a) (code a)) := by
  have hcompiled := Boolean.Layered.computableInPolyTime_compile hcount hcode
  apply (isPPTOn_evaluateLayers D hencrypt hevaluate hD hn hpks heks hinputs
    hcompiled.fst').map_with
  apply ComputableInPolyTime.mapWithInput
    (hcompiled.snd'.comp (ComputableInPolyTime.fst _ _))
  exact ComputableInPolyTime.listGetD_binary [] (by fun_prop) (by fun_prop)

end Cslib.Crypto.Homomorphic.Scheme
