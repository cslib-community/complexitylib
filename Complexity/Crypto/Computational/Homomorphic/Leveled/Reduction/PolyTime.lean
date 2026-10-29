/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Leveled.Reduction
public import Complexity.Crypto.Computational.Homomorphic.KeyChain.Reduction.PolyTime
import Complexity.Computability.Probabilistic.Repeat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Tactic.PPT

/-!
# Native runtime of the leveled security reductions

The public-artifact test charges both adaptive adversary stages and the complete tagged
challenge. The zero-link adversary charges the generated key list, all zero-link encryptions,
public serialization and the adversary's saved state. `isPPT_leveledAdversary` certifies the
asymptotic runtime consequence of [Gentry2009, Section 2, Theorem 4, p. 171]: the unified
two-stage reduction is uniform strict PPT whenever the adversary, base scheme, depth and capacity
are (without proving the multiplicative `poly(ℓ, d)` runtime factor relative to the adversary).

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.isPPTOn_publicKeyGame`: native public-artifact postprocessing.
* `Cslib.Crypto.Homomorphic.Leveled.isPPT_zeroLinkAdversary`: native zero-link base-game
  admissibility.
* `Cslib.Crypto.Homomorphic.Leveled.isPPT_leveledAdversary`: native admissibility of the unified
  leveled reduction.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2, Theorem 4][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Probability Turing.MultiTapeTM

variable {E : Scheme}
  (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => E.encrypt p.1 p.2.1 p.2.2))
  {adversary : Encryption.Adversary} (hadversary : adversary.IsPPT)

include hencrypt hadversary

/-- Both stages of the adversary run after complete public-artifact serialization. -/
theorem isPPTOn_publicKeyGame (bit : Bool) :
    IsPPTOn (encPair encUnary encPublicKey) encBool
      (fun p => publicKeyGame E adversary bit p.1 p.2) := by
  let baseEncoding := encPair encUnary encPublicKey
  let choiceEncoding := encPair (encPair encBool encBool) encBits
  have hn := ComputableInPolyTime.fst encUnary encPublicKey
  have hartifact := ComputableInPolyTime.snd encUnary encPublicKey
  have hpublic := (ComputableInPolyTime.snd encUnary encPublicKey).encoding_comp
  have hchoose := hadversary.choose.on.preprocess (hn.prod hpublic)
  have hfirst := (ComputableInPolyTime.listGetD (encA := encBits) []).comp
    (hartifact.fst'.prod (ComputableInPolyTime.const 0))
  have hencryptArg : ComputableInPolyTime
      (fun p : (ℕ × (List (List Bool) × List (List (List Bool)))) ×
        ((Bool × Bool) × List Bool) =>
        (p.1.1, p.1.2.1.getD 0 [], if bit then p.2.1.2 else p.2.1.1))
      (encPair baseEncoding choiceEncoding) (encPair encUnary (encPair encBits encBool)) := by
    have houter := ComputableInPolyTime.fst baseEncoding choiceEncoding
    apply ComputableInPolyTime.prod (hn.comp houter)
    apply ComputableInPolyTime.prod (hfirst.comp houter)
    cases bit <;> dsimp only [baseEncoding, choiceEncoding, encPublicKey] <;> fun_prop
  have hcipher := hencrypt.preprocess hencryptArg
  have hguessArg : ComputableInPolyTime
      (fun p : ((ℕ × (List (List Bool) × List (List (List Bool)))) ×
        ((Bool × Bool) × List Bool)) × List Bool =>
        (p.1.1.1, p.1.2.2, false :: p.2)) (encPair (encPair baseEncoding choiceEncoding) encBits)
      (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [baseEncoding, choiceEncoding, encPublicKey]
    fun_prop
  have hlast := hadversary.guess.preprocess hguessArg
  have hbody := hcipher.bind_with
    (second := fun p ciphertext => adversary.guess p.1.1 p.2.2 (false :: ciphertext)) hlast
  simpa only [publicKeyGame, baseEncoding, choiceEncoding, Function.comp_def] using
    hchoose.bind_with (second := fun p choice => do
      let ciphertext ← E.encrypt p.1 (p.2.1.getD 0 [])
        (if bit then choice.1.2 else choice.1.1)
      adversary.guess p.1 choice.2 (false :: ciphertext)) hbody

/-- The all-zero simulation is strict PPT with the parameter, complete input public key and
saved state charged. The supported-width hypothesis is needed only for the semantic proof. -/
theorem isPPT_zeroLinkAdversary
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    {depth : ℕ → ℕ} (hdepth : ComputableInPolyTime depth encUnary encUnary) :
    (zeroLinkAdversary E depth adversary).IsPPT := by
  have hchoose := hadversary.choose
  have hguess := hadversary.guess
  constructor
  · change IsPPTOn (encPair encUnary encBits) (encPair (encPair encBool encBool) encBits)
      (fun p => (zeroLinkAdversary E depth adversary).choose p.1 p.2)
    dsimp only [zeroLinkAdversary]
    have hrest := (hkeyGen.preprocess
      (ComputableInPolyTime.fst encUnary encBits)).replicate
        (hdepth.comp (ComputableInPolyTime.fst encUnary encBits))
    apply hrest.bind_with
    have hlinks : IsPPTOn
        (encPair (encPair encUnary encBits) (encList (encPair encBits encBits)))
        (encList (encList encBits))
        (fun p => E.encryptZeroKeyLinks p.1.1 ((p.1.2, (p.2.headD ([], [])).2) :: p.2)) := by
      apply Scheme.isPPTOn_encryptZeroKeyLinks hencrypt <;> fun_prop
    apply hlinks.bind_with
    have hpublic : ComputableInPolyTime
        (fun p : ((ℕ × List Bool) × List (List Bool × List Bool)) ×
          List (List (List Bool)) => (p.1.1.2 :: p.1.2.map Prod.fst, p.2))
        (encPair (encPair (encPair encUnary encBits) (encList (encPair encBits encBits)))
          (encList (encList encBits))) encPublicKey := by
      unfold encPublicKey
      fun_prop
    exact hchoose.on.preprocess
      (((ComputableInPolyTime.fst _ _).fst'.fst').prod (hpublic.of_enc_eq fun _ => rfl))
  · change IsPPTOn (encPair encUnary (encPair encBits encBits)) encBool
      (fun p => adversary.guess p.1 p.2.1 (false :: p.2.2))
    ppt

omit hencrypt hadversary in
private theorem computableInPolyTime_tagLeveledChoice (first second : Bool) :
    ComputableInPolyTime (tagLeveledChoice first second)
      (encPair (encPair encBool encBool) encBits)
      (encPair (encPair encBool encBool) encBits) := by
  unfold tagLeveledChoice
  exact (ComputableInPolyTime.fst _ _).prod
    (ComputableInPolyTime.bitsCons (by fun_prop)
      (ComputableInPolyTime.bitsCons (by fun_prop)
        (ComputableInPolyTime.snd _ _)))

omit hencrypt hadversary in
private theorem computableInPolyTime_swapLeveledChoice :
    ComputableInPolyTime swapLeveledChoice
      (encPair (encPair encBool encBool) encBits)
      (encPair (encPair encBool encBool) encBits) := by
  unfold swapLeveledChoice
  fun_prop

/-- The unified leveled reduction is native strict PPT: its message selection charges both
selector coins, the dyadic index coins, and the selected sub-reduction (`zeroLinkAdversary` or
`E.linkAdversary`), while its guessing stage inspects the two prefix bits and charges the
forwarded saved state and challenge ciphertext. -/
theorem isPPT_leveledAdversary
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    {depth capacity : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary) :
    (leveledAdversary E depth capacity adversary).IsPPT := by
  have hzero := isPPT_zeroLinkAdversary hencrypt hadversary hkeyGen hdepth
  have hlinkFalse := Scheme.isPPT_linkAdversary hkeyGen hencrypt
    (isPPTOn_publicKeyGame hencrypt hadversary false) hdepth hcapacity
  have hlinkTrue := Scheme.isPPT_linkAdversary hkeyGen hencrypt
    (isPPTOn_publicKeyGame hencrypt hadversary true) hdepth hcapacity
  constructor
  · change IsPPTOn (encPair encUnary encBits) (encPair (encPair encBool encBool) encBits)
      (fun p => (leveledAdversary E depth capacity adversary).choose p.1 p.2)
    dsimp only [leveledAdversary]
    apply (isPPTOn_uniform_bool (input := encPair encUnary encBits)).bind_with
    apply (isPPTOn_uniform_bool
      (input := encPair (encPair encUnary encBits) encBool)).bind_with
    apply IsPPTOn.cond (by fun_prop)
    · apply IsPPTOn.cond (by fun_prop)
      · exact (ComputableInPolyTime.const rejectLeveledChoice).isPPTOn
      · apply (isPPTOn_sampleDyadicCoin
          (hdepth.comp (by fun_prop)) (by fun_prop)).bind_with
        apply (isPPTOn_sampleDyadicCoin
          (hcapacity.comp (by fun_prop)) (by fun_prop)).bind_with
        apply IsPPTOn.cond (by polytime)
        · apply IsPPTOn.cond (by polytime)
          · exact (hzero.choose.on.preprocess (by fun_prop)).map
              (computableInPolyTime_tagLeveledChoice true false)
          · exact (ComputableInPolyTime.const rejectLeveledChoice).isPPTOn
        · exact (ComputableInPolyTime.const rejectLeveledChoice).isPPTOn
    · apply IsPPTOn.cond (by fun_prop)
      · exact (hlinkTrue.choose.on.preprocess (by fun_prop)).map
          ((computableInPolyTime_tagLeveledChoice false true).comp
            computableInPolyTime_swapLeveledChoice)
      · exact (hlinkFalse.choose.on.preprocess (by fun_prop)).map
          (computableInPolyTime_tagLeveledChoice false false)
  · dsimp only [leveledAdversary]
    have hstate : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => p.2.1)
        (encPair encUnary (encPair encBits encBits)) encBits := by fun_prop
    have htail1 := ComputableInPolyTime.bitsTail.comp hstate
    have htail2 := ComputableInPolyTime.bitsTail.comp htail1
    have hhead1 := (ComputableInPolyTime.headD (encA := encBool) true).comp hstate
    have hhead2 := (ComputableInPolyTime.headD (encA := encBool) true).comp htail1
    have hforward : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => (p.1, p.2.1.tail.tail, p.2.2))
        (encPair encUnary (encPair encBits encBits))
        (encPair encUnary (encPair encBits encBits)) :=
      (ComputableInPolyTime.fst _ _).prod (htail2.prod (by fun_prop))
    apply IsPPTOn.cond (by polytime)
    · apply IsPPTOn.cond (by polytime)
      · exact (ComputableInPolyTime.const false).isPPTOn
      · exact hzero.guess.preprocess hforward
    · apply IsPPTOn.cond (by polytime)
      · exact hlinkTrue.guess.preprocess hforward
      · exact hlinkFalse.guess.preprocess hforward

end Cslib.Crypto.Homomorphic.Leveled
