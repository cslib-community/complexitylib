/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.KeyChain.Hybrid
public import Complexity.Crypto.Computational.Homomorphic.KeyChain.PolyTime
public import Complexity.Crypto.Computational.Homomorphic.BitEncryption.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Tactic.PPT

/-!
# Native runtime of encrypted-key chain hybrids

The actual hybrid samplers charge every public and private key supplied as input, every bit
encryption, and their full nested output. Counters are unary. These certificates require only
the native key-generation and encryption certificates, with no correctness, fixed-width or
security assumptions.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_encryptZeroKeyLinks`: encrypt zero words of the
  supplied secret keys' actual lengths.
* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_encryptKeyLinksHybrid`: sample the real prefix and
  zero suffix.
* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_publicKeyChainHybrid`: generate keys and return only
  the public keys and hybrid links.
* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_encryptKeyLinkHybrid`: refine the boundary link
  one bit at a time while sampling both surrounding link segments.
* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_spliceEncryptedKeyLink`: insert a supplied ciphertext
  into the boundary link while sampling the surrounding bits and links.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Probability Turing.MultiTapeTM

variable {E : Scheme}
  (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
  (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => E.encrypt p.1 p.2.1 p.2.2))
  {α : Type} {input : α ↪ List Bool} {n depth cut : α → ℕ}
  {keys : α → List (List Bool × List Bool)}

include hencrypt

/-- Encrypt every zero link, using the actual length of each supplied secret key. -/
@[fun_prop]
theorem isPPTOn_encryptZeroKeyLinks
    (hn : ComputableInPolyTime n input encUnary)
    (hkeys : ComputableInPolyTime keys input (encList (encPair encBits encBits))) :
    IsPPTOn input (encList (encList encBits))
      (fun a => E.encryptZeroKeyLinks (n a) (keys a)) := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hn
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hkeys
  apply IsPPTOn.mapMWith
    (element := encPair (encPair encBits encBits) (encPair encBits encBits))
  · apply isPPTOn_encryptBits hencrypt <;> fun_prop
  · exact (ComputableTidilyInPolyTime.zip (encPair encBits encBits)
      (encPair encBits encBits)).comp
        (hkeys.prod ((ComputableTidilyInPolyTime.tail
          (encA := encPair encBits encBits)).comp hkeys))

/-- Sample the actual real-prefix/zero-suffix hybrid for every unary boundary, including
boundaries beyond the supplied list. -/
@[fun_prop]
theorem isPPTOn_encryptKeyLinksHybrid
    (hn : ComputableInPolyTime n input encUnary)
    (hcut : ComputableInPolyTime cut input encUnary)
    (hkeys : ComputableInPolyTime keys input (encList (encPair encBits encBits))) :
    IsPPTOn input (encList (encList encBits))
      (fun a => E.encryptKeyLinksHybrid (n a) (cut a) (keys a)) := by
  have hn := hn.tidy
  have hcut := hcut.tidy
  have hkeys := hkeys.tidy
  have hfront := isPPTOn_encryptKeyLinks hencrypt (.of_tidy hn)
    (.of_tidy (show ComputableTidilyInPolyTime (fun a => (keys a).take (cut a + 1))
      input (encList (encPair encBits encBits)) by fun_prop))
  have hback := isPPTOn_encryptZeroKeyLinks hencrypt (.of_tidy hn)
    (.of_tidy (show ComputableTidilyInPolyTime (fun a => (keys a).drop (cut a))
      input (encList (encPair encBits encBits)) by fun_prop))
  unfold encryptKeyLinksHybrid
  ppt

include hkeyGen in
/-- Generate independent keys and hybrid links, charging the full public artifact. -/
@[fun_prop]
theorem isPPTOn_publicKeyChainHybrid
    (hn : ComputableInPolyTime n input encUnary)
    (hdepth : ComputableInPolyTime depth input encUnary)
    (hcut : ComputableInPolyTime cut input encUnary) :
    IsPPTOn input (encPair (encList encBits) (encList (encList encBits)))
      (fun a => E.publicKeyChainHybrid (n a) (depth a) (cut a)) := by
  have hn := hn.tidy
  have hdepth := hdepth.tidy
  have hcut := hcut.tidy
  apply (isPPTOn_generateKeys hkeyGen (.of_tidy hn) (.of_tidy hdepth)).bind_with
  have hlinks := isPPTOn_encryptKeyLinksHybrid hencrypt
    (.of_tidy (show ComputableTidilyInPolyTime
      (fun p : α × List (List Bool × List Bool) => n p.1)
      (encPair input (encList (encPair encBits encBits))) encUnary by fun_prop))
    (.of_tidy (show ComputableTidilyInPolyTime
      (fun p : α × List (List Bool × List Bool) => cut p.1)
      (encPair input (encList (encPair encBits encBits))) encUnary by fun_prop))
    (.of_tidy (ComputableTidilyInPolyTime.snd _ _))
  simpa only [bind_pure_comp] using hlinks.pair
    (show ComputableTidilyInPolyTime
      (fun p : α × List (List Bool × List Bool) => p.2.map Prod.fst)
      (encPair input (encList (encPair encBits encBits))) (encList encBits) by fun_prop)

/-- Refine one link's plaintext while sampling the real prefix and zero suffix. -/
@[fun_prop]
theorem isPPTOn_encryptKeyLinkHybrid
    {before after : α → List (List Bool × List Bool)}
    {predecessor next : α → List Bool × List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hbefore : ComputableInPolyTime before input (encList (encPair encBits encBits)))
    (hpredecessor : ComputableInPolyTime predecessor input (encPair encBits encBits))
    (hnext : ComputableInPolyTime next input (encPair encBits encBits))
    (hafter : ComputableInPolyTime after input (encList (encPair encBits encBits)))
    (hcut : ComputableInPolyTime cut input encUnary) :
    IsPPTOn input (encList (encList encBits))
      (fun a => E.encryptKeyLinkHybrid (n a) (before a) (predecessor a) (next a)
        (after a) (cut a)) := by
  have hn := hn.tidy
  have hbefore := hbefore.tidy
  have hpredecessor := hpredecessor.tidy
  have hnext := hnext.tidy
  have hafter := hafter.tidy
  have hcut := hcut.tidy
  have hfront := isPPTOn_encryptKeyLinks hencrypt (.of_tidy hn)
    (.of_tidy (show ComputableTidilyInPolyTime (fun a => before a ++ [predecessor a])
      input (encList (encPair encBits encBits)) by fun_prop))
  have hmiddle := isPPTOn_encryptBitsHybrid hencrypt (.of_tidy hn)
    (.of_tidy (show ComputableTidilyInPolyTime (fun a => (next a).1) input encBits by fun_prop))
    (.of_tidy (show ComputableTidilyInPolyTime (fun a => (predecessor a).2) input encBits by
      fun_prop)) (.of_tidy hcut)
  have hback := isPPTOn_encryptZeroKeyLinks hencrypt (.of_tidy hn)
    (.of_tidy (show ComputableTidilyInPolyTime (fun a => next a :: after a)
      input (encList (encPair encBits encBits)) by fun_prop))
  unfold encryptKeyLinkHybrid
  ppt

/-- Insert the full challenge ciphertext into the actual boundary-link simulation. -/
@[fun_prop]
theorem isPPTOn_spliceEncryptedKeyLink
    {before after : α → List (List Bool × List Bool)}
    {predecessor next : α → List Bool × List Bool} {challenge : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hbefore : ComputableInPolyTime before input (encList (encPair encBits encBits)))
    (hpredecessor : ComputableInPolyTime predecessor input (encPair encBits encBits))
    (hnext : ComputableInPolyTime next input (encPair encBits encBits))
    (hafter : ComputableInPolyTime after input (encList (encPair encBits encBits)))
    (hcut : ComputableInPolyTime cut input encUnary)
    (hchallenge : ComputableInPolyTime challenge input encBits) :
    IsPPTOn input (encList (encList encBits))
      (fun a => E.spliceEncryptedKeyLink (n a) (before a) (predecessor a) (next a)
        (after a) (cut a) (challenge a)) := by
  have hn := hn.tidy
  have hbefore := hbefore.tidy
  have hpredecessor := hpredecessor.tidy
  have hnext := hnext.tidy
  have hafter := hafter.tidy
  have hcut := hcut.tidy
  have hchallenge := hchallenge.tidy
  have hfront := isPPTOn_encryptKeyLinks hencrypt (.of_tidy hn)
    (.of_tidy (show ComputableTidilyInPolyTime (fun a => before a ++ [predecessor a])
      input (encList (encPair encBits encBits)) by fun_prop))
  have hmiddle := isPPTOn_spliceEncryptedBit hencrypt (.of_tidy hn)
    (.of_tidy (show ComputableTidilyInPolyTime (fun a => (next a).1) input encBits by fun_prop))
      (.of_tidy hcut)
    (.of_tidy (show ComputableTidilyInPolyTime (fun a => (predecessor a).2.drop (cut a + 1))
      input encBits by fun_prop)) (.of_tidy hchallenge)
  have hback := isPPTOn_encryptZeroKeyLinks hencrypt (.of_tidy hn)
    (.of_tidy (show ComputableTidilyInPolyTime (fun a => next a :: after a)
      input (encList (encPair encBits encBits)) by fun_prop))
  unfold spliceEncryptedKeyLink
  ppt

end Cslib.Crypto.Homomorphic.Scheme
