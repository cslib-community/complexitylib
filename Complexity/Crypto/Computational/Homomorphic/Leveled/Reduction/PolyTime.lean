/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Leveled.Reduction
public import Complexity.Crypto.Computational.Homomorphic.KeyChain.Hybrid.PolyTime
import Complexity.Computability.Probabilistic.Repeat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Tactic.PPT

/-!
# Native runtime of the leveled security reductions

The public-artifact test charges both adaptive adversary stages and the complete tagged
challenge. The zero-link adversary charges the generated key list, all zero-link encryptions,
public serialization and the adversary's saved state.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.isPPTOn_publicKeyGame`: native public-artifact postprocessing.
* `Cslib.Crypto.Homomorphic.Leveled.isPPT_zeroLinkAdversary`: native base-game admissibility.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
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
  have hchoose := hadversary.choose
  have hguess := hadversary.guess
  have hpublic := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.snd encUnary encPublicKey).encoded
  unfold publicKeyGame
  dsimp only [encPublicKey] at hpublic ⊢
  ppt

/-- The all-zero simulation is strict PPT with the parameter, complete input public key and
saved state charged. The supported-width hypothesis is needed only for the semantic proof. -/
theorem isPPT_zeroLinkAdversary
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    {depth : ℕ → ℕ} (hdepth : ComputableTidilyInPolyTime depth encUnary encUnary) :
    (zeroLinkAdversary E depth adversary).IsPPT := by
  have hchoose := hadversary.choose
  have hguess := hadversary.guess
  constructor
  · change IsPPTOn (encPair encUnary encBits) (encPair (encPair encBool encBool) encBits)
      (fun p => (zeroLinkAdversary E depth adversary).choose p.1 p.2)
    dsimp only [zeroLinkAdversary]
    have hrest := (hkeyGen.preprocess
      (ComputableInPolyTime.fst encUnary encBits)).replicate
        (hdepth.comp (ComputableTidilyInPolyTime.fst encUnary encBits))
    apply hrest.bind_with
    have hlinks : IsPPTOn
        (encPair (encPair encUnary encBits) (encList (encPair encBits encBits)))
        (encList (encList encBits))
        (fun p => E.encryptZeroKeyLinks p.1.1 ((p.1.2, (p.2.headD ([], [])).2) :: p.2)) := by
      apply Scheme.isPPTOn_encryptZeroKeyLinks hencrypt <;> fun_prop
    apply hlinks.bind_with
    have hpublic : ComputableTidilyInPolyTime
        (fun p : ((ℕ × List Bool) × List (List Bool × List Bool)) ×
          List (List (List Bool)) => (p.1.1.2 :: p.1.2.map Prod.fst, p.2))
        (encPair (encPair (encPair encUnary encBits) (encList (encPair encBits encBits)))
          (encList (encList encBits))) encPublicKey := by
      unfold encPublicKey
      fun_prop
    exact hchoose.preprocess (by fun_prop) hpublic.encoded
  · change IsPPTOn (encPair encUnary (encPair encBits encBits)) encBool
      (fun p => adversary.guess p.1 p.2.1 (false :: p.2.2))
    ppt

end Cslib.Crypto.Homomorphic.Leveled
