/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.KeyChain.Security
public import Complexity.Crypto.Computational.Homomorphic.Leveled.Reduction.Game
public import Complexity.Crypto.Computational.Homomorphic.Leveled.Reduction.PolyTime
public import Complexity.Crypto.Computational.Basic

/-!
# IND-CPA security of the acyclic leveled construction

Every native two-stage adversary against the actual serialized leveled scheme has negligible
advantage, assuming base IND-CPA security, native base key generation and encryption, fixed
supported secret length, and an efficient unary depth budget. The public key includes the
complete encrypted-key chain, and message selection occurs after the adversary sees it.

Two public-artifact hybrids replace secret encryptions by zero encryptions in the two challenge
worlds. A concrete base adversary simulates the intervening zero-link experiment. This proves
qualitative single-challenge security with explicit uniform reductions; it does not assert
Gentry's exact concrete-security loss. Correctness, evaluation efficiency, compactness, a concrete
base cryptosystem and fixed-key unbounded-depth bootstrapping are separate results or obligations.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.publicKey_indistinguishable_zero`: the serialized public
  artifact is indistinguishable from its zero-link hybrid.
* `Cslib.Crypto.Homomorphic.Leveled.indCPA_keyGen`: security of the actual key generation and
  tagged encryption algorithms.
* `Cslib.Crypto.Homomorphic.Leveled.indCPA_scheme`: security of the actual depth-budgeted scheme.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2, Theorem 4][Gentry2009]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Section 11.2][BonehShoup2023]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Probability Turing.MultiTapeTM

variable {E : Scheme}
  (hsecure : Encryption.INDCPA E.keyGen E.encrypt)
  (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
  (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => E.encrypt p.1 p.2.1 p.2.2))
  {width budget : ℕ → ℕ}
  (hwidth : ∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support → keys.2.length = width n)
  (hbudget : ComputableInPolyTime budget encUnary encUnary)

include hsecure hkeyGen hencrypt hwidth hbudget

/-- The actual serialized public key is computationally indistinguishable from the same
independent public keys with equal-length zero plaintexts in every encrypted link. -/
theorem publicKey_indistinguishable_zero :
    ComputationallyIndistinguishable
      (fun n => (ProbComp.eval (keyGen E n (budget n))).map Prod.fst)
      (fun n => (ProbComp.eval (E.publicKeyChainHybrid n (2 * budget n) 0)).map encPublicKey) := by
  intro adversary hadversary
  have hpublic := (ComputableTidilyInPolyTime.snd encUnary encPublicKey).encoded
  have htest : IsPPTOn (encPair encUnary encPublicKey) encBool
      (fun p => adversary p.1 (encPublicKey p.2)) :=
    hadversary.preprocess (by fun_prop) hpublic
  have hdepth : ComputableTidilyInPolyTime (fun n => 2 * budget n) encUnary encUnary := by
    have hbudget := hbudget.tidy
    fun_prop
  have h := Scheme.negligible_publicKeyChainHybrid hsecure hkeyGen hencrypt hwidth (.of_tidy hdepth)
    (test := fun n artifact => adversary n (encPublicKey artifact)) htest
  simpa only [eval_keyGen_public, distinguishingGame, PMF.monad_bind_eq_bind, PMF.bind_map,
    Function.comp_def,
    ProbComp.eval_bind] using h

/-- The actual serialized acyclic public key and fresh tagged encryption preserve IND-CPA.
Both adversary stages are uniform strict PPT, with arbitrary polynomial saved state. -/
theorem indCPA_keyGen :
    Encryption.INDCPA (fun n => keyGen E n (budget n)) (encrypt E) := by
  let depth := fun n => 2 * budget n
  have hdepth : ComputableTidilyInPolyTime depth encUnary encUnary := by
    dsimp only [depth]
    have hbudget := hbudget.tidy
    fun_prop
  let zero (bit : Bool) (adversary : Encryption.Adversary) (n : ℕ) : Game :=
    ProbComp.eval (do
      let artifact ← E.publicKeyChainHybrid n (depth n) 0
      publicKeyGame E adversary bit n artifact)
  have hhop (bit : Bool) : Game.Indistinguishable
      (fun adversary n => ProbComp.eval
        (Encryption.game (fun n => keyGen E n (budget n)) (encrypt E) adversary bit n))
      (zero bit) Encryption.Adversary.IsPPT := by
    intro adversary hadversary
    simpa only [eval_game_keyGen] using
      Scheme.negligible_publicKeyChainHybrid hsecure hkeyGen hencrypt hwidth (.of_tidy hdepth)
        (isPPTOn_publicKeyGame hencrypt hadversary bit)
  have hzero : Game.Indistinguishable (zero false) (zero true) Encryption.Adversary.IsPPT := by
    intro adversary hadversary
    have heq (bit : Bool) (n : ℕ) :=
      eval_zeroLinkAdversary E depth adversary bit n (width n) (hwidth n)
    simpa only [heq] using hsecure (zeroLinkAdversary E depth adversary)
      (isPPT_zeroLinkAdversary hencrypt hadversary hkeyGen (.of_tidy hdepth))
  exact (hhop false).trans (hzero.trans (hhop true).symm)

/-- The actual depth-budgeted scheme is IND-CPA secure. The decryption circuit family identifies
the scheme but supplies no security premise; only base security and the stated native hypotheses
are used. -/
theorem indCPA_scheme {secretWidth ciphertextWidth : ℕ → ℕ}
    (D : DecryptionCircuits E secretWidth ciphertextWidth) :
    Encryption.INDCPA (scheme D budget).keyGen (scheme D budget).encrypt :=
  indCPA_keyGen hsecure hkeyGen hencrypt hwidth hbudget

end Cslib.Crypto.Homomorphic.Leveled
