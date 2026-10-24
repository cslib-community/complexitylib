/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.FixedKey.Reduction
public import Complexity.Crypto.Computational.Homomorphic.FixedKey.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Probabilistic.PPT.Composition

/-!
# Security from a single self-encrypted key

The circular premise concerns the actual joint public artifact: one public key and the complete
vector encrypting its own secret bits. Native public-artifact postprocessing lets an adversary
choose its messages after seeing that artifact and retain its full saved state.

The proof replaces self-encryptions by zero encryptions in each challenge world, and reduces
the middle comparison to ordinary base IND-CPA. The zero-world simulator obtains the fixed
supported secret length from an independent key sample. No efficient width function,
correctness or bootstrappability premise is needed for this security transfer.

## Main results

* `Cslib.Crypto.Homomorphic.FixedKey.negligible_publicKeyGame`: replacing the self-encrypted
  public vector by zero encryptions changes either adaptive challenge world negligibly.
* `Cslib.Crypto.Homomorphic.FixedKey.indCPA_scheme`: the actual fixed-key scheme preserves
  IND-CPA under the explicit additional one-key circular premise.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*][Gentry2009], Section 2.
* [D. Boneh, S. Halevi, M. Hamburg, R. Ostrovsky,
  *Circular-Secure Encryption from Decision Diffie-Hellman*][BonehHaleviHamburgOstrovsky2008],
  Section 2.1.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.FixedKey

open Probability Turing.MultiTapeTM

/-- The actual public marginal is the serialized self-encryption experiment. -/
theorem eval_keyGen_public (E : Scheme) (n : ℕ) :
    (ProbComp.eval (keyGen E n)).map Prod.fst =
      (ProbComp.eval (Encryption.circularPublicKey E.keyGen E.encrypt true n)).map
        encPublicKey := by
  simp [keyGen, Encryption.circularPublicKey, Scheme.encryptBits, ProbComp.eval_bind,
    PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- The actual scheme challenge is the real public artifact followed by adaptive message
selection. The private secret component is never passed to the adversary. -/
theorem eval_game_keyGen (E : Scheme) (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.game (keyGen E) (encrypt E) adversary bit n) =
      ProbComp.eval (Encryption.circularPublicKey E.keyGen E.encrypt true n >>=
        publicKeyGame E adversary bit n) := by
  simp only [Encryption.game, keyGen, encrypt, publicKeyGame, Encryption.circularPublicKey,
    Scheme.encryptBits, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.bind_bind, PMF.pure_bind, publicKeyDecoder_decode_enc]

/-- The circular premise applies to the exact serialized public artifact of the construction. -/
theorem publicKey_indistinguishable_zero {E : Scheme}
    (hcircular : Encryption.CircularSecure E.keyGen E.encrypt) :
    ComputationallyIndistinguishable
      (fun n => (ProbComp.eval (keyGen E n)).map Prod.fst)
      (fun n => (ProbComp.eval (Encryption.circularPublicKey E.keyGen E.encrypt false n)).map
        encPublicKey) := by
  simpa only [eval_keyGen_public, Encryption.CircularSecure] using hcircular

/-- The circular premise protects either adaptive chosen-message experiment. Honest
encryption and both adversary stages are certified on their complete inputs. -/
theorem negligible_publicKeyGame {E : Scheme}
    (hcircular : Encryption.CircularSecure E.keyGen E.encrypt)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => E.encrypt p.1 p.2.1 p.2.2))
    {adversary : Encryption.Adversary} (hadversary : adversary.IsPPT) (bit : Bool) :
    Negligible (fun n => Game.advantage
      (ProbComp.eval (Encryption.circularPublicKey E.keyGen E.encrypt true n >>=
        publicKeyGame E adversary bit n))
      (ProbComp.eval (Encryption.circularPublicKey E.keyGen E.encrypt false n >>=
        publicKeyGame E adversary bit n))) := by
  have hgame := isPPTOn_publicKeyGame hencrypt hadversary bit
  have htest : IsPPT encBool (fun n word =>
      publicKeyGame E adversary bit n (publicKeyDecoder.decode word)) :=
    hgame.preprocess (ComputableInPolyTime.of_tidy
      ((ComputableTidilyInPolyTime.fst encUnary encBits).prod
      (publicKeyDecoder.computableTidilyInPolyTime.comp
        (ComputableTidilyInPolyTime.snd encUnary encBits))))
  have h := hcircular _ htest
  simpa only [distinguishingGame, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def,
    publicKeyDecoder.decode_enc, ProbComp.eval_bind] using h

/-- Self-encrypted evaluation keys preserve adaptive IND-CPA under ordinary base IND-CPA and
the separate joint circular premise. Fixed supported secret length is semantic; the reduction
learns it from an independent key sample and needs no computable width function. -/
theorem indCPA_keyGen {E : Scheme}
    (hsecure : Encryption.INDCPA E.keyGen E.encrypt)
    (hcircular : Encryption.CircularSecure E.keyGen E.encrypt)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => E.encrypt p.1 p.2.1 p.2.2))
    {width : ℕ → ℕ}
    (hwidth : ∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support → keys.2.length = width n) :
    Encryption.INDCPA (keyGen E) (encrypt E) := by
  let zero (bit : Bool) (adversary : Encryption.Adversary) (n : ℕ) : Game :=
    ProbComp.eval (do
      let artifact ← Encryption.circularPublicKey E.keyGen E.encrypt false n
      publicKeyGame E adversary bit n artifact)
  have hhop (bit : Bool) : Game.Indistinguishable
      (fun adversary n => ProbComp.eval
        (Encryption.game (keyGen E) (encrypt E) adversary bit n))
      (zero bit) Encryption.Adversary.IsPPT := by
    intro adversary hadversary
    simpa only [eval_game_keyGen] using
      negligible_publicKeyGame hcircular hencrypt hadversary bit
  have hzero : Game.Indistinguishable (zero false) (zero true) Encryption.Adversary.IsPPT := by
    intro adversary hadversary
    have heq (bit : Bool) (n : ℕ) :=
      eval_zeroAdversary E adversary bit n (width n) (hwidth n)
    simpa only [heq] using hsecure (zeroAdversary E adversary)
      (isPPT_zeroAdversary hencrypt hadversary hkeyGen)
  exact (hhop false).trans (hzero.trans (hhop true).symm)

/-- The actual all-circuit fixed-key scheme is conditionally IND-CPA secure. The decryption
family identifies the construction but contributes no security assumption. -/
theorem indCPA_scheme {E : Scheme} {secretWidth ciphertextWidth : ℕ → ℕ}
    (D : DecryptionCircuits E secretWidth ciphertextWidth)
    (hsecure : Encryption.INDCPA E.keyGen E.encrypt)
    (hcircular : Encryption.CircularSecure E.keyGen E.encrypt)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => E.encrypt p.1 p.2.1 p.2.2))
    {width : ℕ → ℕ}
    (hwidth : ∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support → keys.2.length = width n) :
    Encryption.INDCPA (scheme D).keyGen (scheme D).encrypt :=
  indCPA_keyGen hsecure hcircular hkeyGen hencrypt hwidth

end Cslib.Crypto.Homomorphic.FixedKey
