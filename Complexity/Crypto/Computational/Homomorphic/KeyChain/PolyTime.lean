/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.KeyChain
public import Complexity.Crypto.Computational.Homomorphic.Efficiency
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Repeat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Uniform polynomial-time key-chain generation

The actual key-chain sampler from [Gentry2009, Section 2] is strict PPT when key generation and
bit encryption are uniformly strict PPT. Both the security parameter and the requested depth
are encoded in unary. The certificates charge every key, every secret-key bit encryption, and
the complete nested output encoding. They impose no correctness, fixed-width, or security
assumption.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_generateKeys`: sample all levels of keys.
* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_encryptKeyLinks`: encrypt adjacent secret-key links.
* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_generateKeyChain`: the complete sampler is strict PPT.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Probability Turing.MultiTapeTM

variable {E : Scheme}
  (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
  (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => E.encrypt p.1 p.2.1 p.2.2))
  {α : Type} {input : α ↪ List Bool} {n depth : α → ℕ}
  {keys : α → List (List Bool × List Bool)}

include hkeyGen in
/-- Generate an efficiently computed unary number of keys using bounded repetition. -/
@[fun_prop]
theorem isPPTOn_generateKeys
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hdepth : ComputableTidilyInPolyTime depth input encUnary) :
    IsPPTOn input (encList (encPair encBits encBits))
      (fun a => E.generateKeys (n a) (depth a)) := by
  exact (hkeyGen.preprocess (.of_tidy hn)).replicate (by fun_prop)

include hencrypt in
/-- Encrypt every adjacent secret-key link, including all copied public keys and key bits. -/
@[fun_prop]
theorem isPPTOn_encryptKeyLinks
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hkeys : ComputableTidilyInPolyTime keys input (encList (encPair encBits encBits))) :
    IsPPTOn input (encList (encList encBits))
      (fun a => E.encryptKeyLinks (n a) (keys a)) := by
  apply IsPPTOn.mapMWith
    (element := encPair (encPair encBits encBits) (encPair encBits encBits))
  · apply isPPTOn_encryptBits hencrypt <;> fun_prop
  · exact (ComputableTidilyInPolyTime.zip (encPair encBits encBits)
      (encPair encBits encBits)).comp
        (hkeys.prod ((ComputableTidilyInPolyTime.tail
          (encA := encPair encBits encBits)).comp hkeys))

include hkeyGen hencrypt in
/-- Generate the keys and their encrypted links with one uniform polynomial clock in the full
encoded input. No correctness or output-width premise is used to bound the sampled keys. -/
@[fun_prop]
theorem isPPTOn_generateKeyChain
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hdepth : ComputableTidilyInPolyTime depth input encUnary) :
    IsPPTOn input
      (encPair (encList (encPair encBits encBits)) (encList (encList encBits)))
      (fun a => E.generateKeyChain (n a) (depth a)) := by
  apply (isPPTOn_generateKeys hkeyGen hn hdepth).bind_with
  simpa only [bind_pure_comp] using (isPPTOn_encryptKeyLinks hencrypt
    (show ComputableTidilyInPolyTime
      (fun p : α × List (List Bool × List Bool) => n p.1)
      (encPair input (encList (encPair encBits encBits))) encUnary by fun_prop)
    (ComputableTidilyInPolyTime.snd _ _)).pair (ComputableTidilyInPolyTime.snd _ _)

end Cslib.Crypto.Homomorphic.Scheme
