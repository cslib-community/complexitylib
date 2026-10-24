/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.KeyChain.Reduction
public import Complexity.Crypto.Computational.Homomorphic.KeyChain.Hybrid.PolyTime
public import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Computability.Probabilistic.Repeat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Tactic.PPT

/-!
# Native runtime of the encrypted-link reduction

The actual two-stage reduction is uniform strict PPT. Message selection charges every generated
key and the encoded saved context. Guessing charges total parsing on every saved word, the zero
replacement secret, all simulated encryptions and the complete public artifact passed to its
test. No security, correctness or fixed-width hypothesis is used in these runtime certificates.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_chooseLinkAt`: sample a complete reduction context.
* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_guessLink`: run the response on arbitrary saved words.
* `Cslib.Crypto.Homomorphic.Scheme.isPPT_linkAdversaryAt`: admissibility at efficient indices.
* `Cslib.Crypto.Homomorphic.Scheme.isPPT_linkAdversary`: admissibility of uniform dyadic selection.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Section 11.2][BonehShoup2023]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Probability Turing.MultiTapeTM

variable {E : Scheme}
  (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
  (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => E.encrypt p.1 p.2.1 p.2.2))
  {test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool}
  (htest : IsPPTOn
    (encPair encUnary (encPair (encList encBits) (encList (encList encBits)))) encBool
    (fun p => test p.1 p.2))
  {α : Type} {input : α ↪ List Bool}

include hkeyGen in
/-- Sample all known keys and encode the actual context, charging every saved secret bit. -/
@[fun_prop]
theorem isPPTOn_chooseLinkAt {n beforeCount afterCount bitIndex : α → ℕ}
    {challengePk : α → List Bool}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hbefore : ComputableTidilyInPolyTime beforeCount input encUnary)
    (hafter : ComputableTidilyInPolyTime afterCount input encUnary)
    (hindex : ComputableTidilyInPolyTime bitIndex input encUnary)
    (hpk : ComputableTidilyInPolyTime challengePk input encBits) :
    IsPPTOn input (encPair (encPair encBool encBool) encBits)
      (fun a => E.chooseLinkAt (n a) (beforeCount a) (afterCount a) (bitIndex a)
        (challengePk a)) := by
  have hkey := hkeyGen.preprocess (.of_tidy hn)
  have hfront := hkey.replicate hbefore
  have hback := hkey.replicate hafter
  unfold chooseLinkAt
  apply hfront.bind_with
  apply (hkey.preprocess (ComputableInPolyTime.fst _ _)).bind_with
  apply (hback.preprocess (ComputableInPolyTime.fst _ _).fst').bind_with
  have hstate : ComputableTidilyInPolyTime
      (fun p : ((α × List (List Bool × List Bool)) × (List Bool × List Bool)) ×
        List (List Bool × List Bool) =>
        (true, p.1.1.2, p.1.2, challengePk p.1.1.1, p.2, bitIndex p.1.1.1))
      (encPair (encPair (encPair input (encList (encPair encBits encBits)))
        (encPair encBits encBits)) (encList (encPair encBits encBits))) encLinkState := by
    unfold encLinkState
    fun_prop
  apply IsPPTOn.ite
  · fun_prop
  · apply ComputableTidilyInPolyTime.isPPTOn
    apply ComputableTidilyInPolyTime.prod
    · fun_prop
    · exact hstate.encoded
  · ppt

include hencrypt htest in
/-- The guessing stage is native strict PPT on every saved string, including malformed ones. -/
@[fun_prop]
theorem isPPTOn_guessLink {n : α → ℕ} {state challengeCiphertext : α → List Bool}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hstate : ComputableTidilyInPolyTime state input encBits)
    (hchallenge : ComputableTidilyInPolyTime challengeCiphertext input encBits) :
    IsPPTOn input encBool
      (fun a => E.guessLink test (n a) (state a) (challengeCiphertext a)) := by
  have hcontext := linkStateDecoder.computableTidilyInPolyTime.comp hstate
  dsimp only [encLinkState] at hcontext
  have hbefore := hcontext.snd'.fst'
  have hpredecessor := hcontext.snd'.snd'.fst'
  have hpk := hcontext.snd'.snd'.snd'.fst'
  have hafter := hcontext.snd'.snd'.snd'.snd'.fst'
  have hindex := hcontext.snd'.snd'.snd'.snd'.snd'
  have htarget := hpk.prod (ComputableTidilyInPolyTime.bitsReplicate false |>.comp
    (ComputableTidilyInPolyTime.length_bits.comp hpredecessor.snd'))
  have hlinks := isPPTOn_spliceEncryptedKeyLink hencrypt hn hbefore hpredecessor htarget
    hafter hindex hchallenge
  have hpublic : ComputableTidilyInPolyTime
      (fun a => ((linkStateDecoder.decode (state a)).2.1 ++
        (linkStateDecoder.decode (state a)).2.2.1 ::
        ((linkStateDecoder.decode (state a)).2.2.2.1,
          List.replicate (linkStateDecoder.decode (state a)).2.2.1.2.length false) ::
        (linkStateDecoder.decode (state a)).2.2.2.2.1).map Prod.fst)
      input (encList encBits) := by fun_prop
  unfold guessLink
  apply IsPPTOn.cond hcontext.fst'
  · apply hlinks.bind_with
    exact htest.preprocess (ComputableInPolyTime.of_tidy (show ComputableTidilyInPolyTime
      (fun p : α × List (List (List Bool)) => (n p.1,
        ((linkStateDecoder.decode (state p.1)).2.1 ++
          (linkStateDecoder.decode (state p.1)).2.2.1 ::
          ((linkStateDecoder.decode (state p.1)).2.2.2.1,
            List.replicate (linkStateDecoder.decode (state p.1)).2.2.1.2.length false) ::
          (linkStateDecoder.decode (state p.1)).2.2.2.2.1).map Prod.fst, p.2))
      (encPair input (encList (encList encBits)))
      (encPair encUnary (encPair (encList encBits) (encList (encList encBits)))) by
        exact (hn.comp (ComputableTidilyInPolyTime.fst _ _)).prod
          ((hpublic.comp (ComputableTidilyInPolyTime.fst _ _)).prod
            (ComputableTidilyInPolyTime.snd _ _))))
  · ppt

include hkeyGen hencrypt htest

/-- Efficient unary index families give one admissible chosen-message adversary. -/
theorem isPPT_linkAdversaryAt {beforeCount afterCount bitIndex : ℕ → ℕ}
    (hbefore : ComputableTidilyInPolyTime beforeCount encUnary encUnary)
    (hafter : ComputableTidilyInPolyTime afterCount encUnary encUnary)
    (hindex : ComputableTidilyInPolyTime bitIndex encUnary encUnary) :
    (E.linkAdversaryAt beforeCount afterCount bitIndex test).IsPPT := by
  constructor
  · change IsPPTOn (encPair encUnary encBits) (encPair (encPair encBool encBool) encBits)
      (fun p => E.chooseLinkAt p.1 (beforeCount p.1) (afterCount p.1) (bitIndex p.1) p.2)
    apply isPPTOn_chooseLinkAt hkeyGen <;> fun_prop
  · exact isPPTOn_guessLink hencrypt htest (by fun_prop) (by fun_prop) (by fun_prop)

/-- Uniform dyadic link and bit selection remains strict PPT, including rejected padding. -/
theorem isPPT_linkAdversary {depth capacity : ℕ → ℕ}
    (hdepth : ComputableTidilyInPolyTime depth encUnary encUnary)
    (hcapacity : ComputableTidilyInPolyTime capacity encUnary encUnary) :
    (E.linkAdversary depth capacity test).IsPPT := by
  constructor
  · change IsPPTOn (encPair encUnary encBits) (encPair (encPair encBool encBool) encBits)
      (fun p => (E.linkAdversary depth capacity test).choose p.1 p.2)
    have hchoose : IsPPTOn
        (encPair (encPair (encPair encUnary encBits) encUnary) encUnary)
        (encPair (encPair encBool encBool) encBits)
        (fun p : ((ℕ × List Bool) × ℕ) × ℕ => E.chooseLinkAt p.1.1.1
          (depth p.1.1.1 - p.1.2 - 1) p.1.2 p.2 p.1.1.2) := by
      apply isPPTOn_chooseLinkAt hkeyGen <;> fun_prop
    dsimp only [linkAdversary]
    ppt
  · exact isPPTOn_guessLink hencrypt htest (by fun_prop) (by fun_prop) (by fun_prop)

end Cslib.Crypto.Homomorphic.Scheme
