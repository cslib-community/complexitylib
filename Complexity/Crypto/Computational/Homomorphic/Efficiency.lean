/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Refresh
public import Complexity.Crypto.Computational.Homomorphic.Circuit.PolyTime
public import Complexity.Computability.Probabilistic.Traverse
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Uniform polynomial-time homomorphic refresh

Strict PPT encryption and evaluation, together with a uniform polynomial-time generator for
actual decryption circuits, suffice to implement refresh and NAND refresh in strict PPT.
The certificates charge the full encodings of the public key, encrypted secret key, ciphertexts,
and generated circuits. In particular, the NAND augmentation is constructed by a certified
code transformation rather than supplied as an independently assumed efficient operation.

These are computation certificates for Gentry's refresh construction [Gentry2009, Section 2].
They do not establish security or a leveled evaluator. Correctness and fixed output width have
separate hypotheses and are proved in `Homomorphic.Refresh`.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_encryptBits`: encrypt a computed list of bits.
* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_refresh`: uniform strict PPT refresh.
* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_refreshNand`: uniform strict PPT NAND refresh.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Circuits Probability Turing.MultiTapeTM

variable {E : Scheme}
  (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => E.encrypt p.1 p.2.1 p.2.2))
  (hevaluate : IsPPTOn
    (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
    encBits (fun p => E.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
  {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {pk bits : α → List Bool}

include hencrypt

/-- Encrypt all bits of an efficiently computed word, charging repeated copies of the key. -/
@[fun_prop]
theorem isPPTOn_encryptBits
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hbits : ComputableInPolyTime bits input encBits) :
    IsPPTOn input (encList encBits) (fun a => E.encryptBits (n a) (pk a) (bits a)) := by
  have hpairs : ComputableInPolyTime (fun a => (bits a).map fun b => (a, b))
      input (encList (encPair input encBool)) :=
    ComputableInPolyTime.mapWithInput (ComputableInPolyTime.bitsToList.comp hbits) .id'
  have hstep : IsPPTOn (encPair input encBool) encBits
      (fun p : α × Bool => E.encrypt (n p.1) (pk p.1) p.2) :=
    hencrypt.preprocess
      ((hn.comp (ComputableInPolyTime.fst _ _)).prod
        ((hpk.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _)))
  apply (hstep.mapM.preprocess hpairs).congr
  intro a
  simp only [Scheme.encryptBits, List.mapM_map, Function.comp_def]

variable {secretWidth ciphertextWidth : ℕ → ℕ}
  (D : DecryptionCircuits E secretWidth ciphertextWidth)
  (hD : ComputableInPolyTime
    (fun n => (⟨_, D.circuit n⟩ : Σ m, Circuit Boolean.signature m 1))
    encUnary (Boolean.encCircuit 1))
  {encryptedKey : α → List (List Bool)} {first second : α → List Bool}

include hevaluate hD

/-- Refresh is strict PPT from the base algorithm certificates and uniform decryption-circuit
construction. No refresh algorithm or refresh runtime bound is assumed. -/
@[fun_prop]
theorem isPPTOn_refresh
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hek : ComputableInPolyTime encryptedKey input (encList encBits))
    (hc : ComputableInPolyTime bits input encBits) :
    IsPPTOn input encBits (fun a => refresh D (n a) (pk a) (encryptedKey a) (bits a)) := by
  apply (isPPTOn_encryptBits hencrypt hn hpk hc).bind_with
  have hparameter := hn.comp (ComputableInPolyTime.fst input (encList encBits))
  have hcircuit := hD.comp hparameter
  exact hevaluate.preprocess
    (hparameter.prod ((hpk.comp (ComputableInPolyTime.fst _ _)).prod
      (hcircuit.prod (by fun_prop))))

/-- NAND refresh is strict PPT. The certificate constructs the augmented circuit and charges
both bit-encryption traversals and both copies of the encrypted secret key. -/
@[fun_prop]
theorem isPPTOn_refreshNand
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hek : ComputableInPolyTime encryptedKey input (encList encBits))
    (hfirst : ComputableInPolyTime first input encBits)
    (hsecond : ComputableInPolyTime second input encBits) :
    IsPPTOn input encBits
      (fun a => refreshNand D (n a) (pk a) (encryptedKey a) (first a) (second a)) := by
  apply (isPPTOn_encryptBits hencrypt hn hpk hfirst).bind_with
  have hsecond' : IsPPTOn (encPair input (encList encBits)) (encList encBits)
      (fun p : α × List (List Bool) => E.encryptBits (n p.1) (pk p.1) (second p.1)) :=
    (isPPTOn_encryptBits hencrypt hn hpk hsecond).preprocess (ComputableInPolyTime.fst _ _)
  apply hsecond'.bind_with
  have hparameter := hn.comp
    ((ComputableInPolyTime.fst (encPair input (encList encBits)) (encList encBits)).fst')
  have haug := (computableInPolyTime_augmentNand.comp hD).comp hparameter
  exact hevaluate.preprocess
    (hparameter.prod ((hpk.comp
      ((ComputableInPolyTime.fst _ _).fst')).prod (haug.prod (by fun_prop))))

end Cslib.Crypto.Homomorphic.Scheme
