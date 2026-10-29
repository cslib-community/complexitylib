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
worlds, and `zeroLinkAdversary` simulates the intervening zero-link experiment. The unified
two-stage reduction `leveledAdversary` combines all three hops into a single base IND-CPA
adversary with concrete loss `4 * dyadicSize (2 * budget n) * dyadicSize (capacity n) ≤
16 * (2 * budget n + 1) * (capacity n + 1)`, matching Gentry's Theorem 4 ([Gentry2009], Section 2,
p. 171) up to a constant factor from power-of-two coin sampling and NAND-compiled depth `2 * d`,
with asymptotic `IsPPT` rather than a multiplicative runtime bound relative to the adversary.
Correctness, evaluation efficiency, compactness, a concrete base cryptosystem and fixed-key
unbounded-depth bootstrapping are separate results or obligations.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.advantage_scheme_eq_leveledAdversary`: exact concrete-security
  identity for `scheme D budget` via `leveledAdversary`.
* `Cslib.Crypto.Homomorphic.Leveled.advantage_scheme_le_mul_leveledAdversary`: concrete polynomial
  loss bound `16 * (2 * budget n + 1) * (capacity n + 1)` for `scheme D budget`.
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
open scoped NNReal

/-- Exact chosen-message advantage of the depth-budgeted scheme `scheme D budget` in terms of
the unified two-stage base reduction `leveledAdversary` ([Gentry2009], Section 2, Theorem 4,
p. 171, up to a constant factor in the loss;
the running-time clause is not formalized). -/
theorem advantage_scheme_eq_leveledAdversary {E : Scheme}
    {secretWidth ciphertextWidth : ℕ → ℕ}
    (D : DecryptionCircuits E secretWidth ciphertextWidth)
    (budget capacity : ℕ → ℕ) (adversary : Encryption.Adversary) (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    Game.advantage
      (ProbComp.eval (Encryption.game (scheme D budget).keyGen (scheme D budget).encrypt
        adversary false n))
      (ProbComp.eval (Encryption.game (scheme D budget).keyGen (scheme D budget).encrypt
        adversary true n)) =
    4 * (dyadicSize (2 * budget n) : ℝ≥0) * dyadicSize (capacity n) *
      Game.advantage
        (ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (leveledAdversary E (fun n => 2 * budget n) capacity adversary) false n))
        (ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (leveledAdversary E (fun n => 2 * budget n) capacity adversary) true n)) :=
  advantage_game_eq_leveledAdversary E budget capacity adversary n width hwidth hcapacity

/-- Polynomial concrete-security bound for the depth-budgeted scheme `scheme D budget` with
explicit factor `16 * (2 * budget n + 1) * (capacity n + 1)` ([Gentry2009], Section 2,
Theorem 4, p. 171, up to a constant factor in the loss;
the running-time clause is not formalized). -/
theorem advantage_scheme_le_mul_leveledAdversary {E : Scheme}
    {secretWidth ciphertextWidth : ℕ → ℕ}
    (D : DecryptionCircuits E secretWidth ciphertextWidth)
    (budget capacity : ℕ → ℕ) (adversary : Encryption.Adversary) (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    Game.advantage
      (ProbComp.eval (Encryption.game (scheme D budget).keyGen (scheme D budget).encrypt
        adversary false n))
      (ProbComp.eval (Encryption.game (scheme D budget).keyGen (scheme D budget).encrypt
        adversary true n)) ≤
    16 * (2 * budget n + 1 : ℝ≥0) * (capacity n + 1) *
      Game.advantage
        (ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (leveledAdversary E (fun n => 2 * budget n) capacity adversary) false n))
        (ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (leveledAdversary E (fun n => 2 * budget n) capacity adversary) true n)) :=
  advantage_game_le_mul_leveledAdversary E budget capacity adversary n width hwidth hcapacity

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
  have hpublic := (ComputableInPolyTime.snd encUnary encPublicKey).of_enc_eq fun _ => rfl
  have htest : IsPPTOn (encPair encUnary encPublicKey) encBool
      (fun p => adversary p.1 (encPublicKey p.2)) :=
    hadversary.on.preprocess ((ComputableInPolyTime.fst encUnary encPublicKey).prod hpublic)
  have hdepth : ComputableInPolyTime (fun n => 2 * budget n) encUnary encUnary := by
    fun_prop
  have h := Scheme.negligible_publicKeyChainHybrid hsecure hkeyGen hencrypt hwidth hdepth
    (test := fun n artifact => adversary n (encPublicKey artifact)) htest
  simpa only [eval_keyGen_public, distinguishingGame, PMF.monad_bind_eq_bind, PMF.bind_map,
    Function.comp_def,
    ProbComp.eval_bind] using h

/-- The actual serialized acyclic public key and fresh tagged encryption preserve IND-CPA.
Both adversary stages are uniform strict PPT, with arbitrary polynomial saved state. -/
theorem indCPA_keyGen :
    Encryption.INDCPA (fun n => keyGen E n (budget n)) (encrypt E) := by
  let depth := fun n => 2 * budget n
  have hdepth : ComputableInPolyTime depth encUnary encUnary := by
    dsimp only [depth]
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
      Scheme.negligible_publicKeyChainHybrid hsecure hkeyGen hencrypt hwidth hdepth
        (isPPTOn_publicKeyGame hencrypt hadversary bit)
  have hzero : Game.Indistinguishable (zero false) (zero true) Encryption.Adversary.IsPPT := by
    intro adversary hadversary
    have heq (bit : Bool) (n : ℕ) :=
      eval_zeroLinkAdversary E depth adversary bit n (width n) (hwidth n)
    simpa only [heq] using hsecure (zeroLinkAdversary E depth adversary)
      (isPPT_zeroLinkAdversary hencrypt hadversary hkeyGen hdepth)
  exact (hhop false).trans (hzero.trans (hhop true).symm)

/-- The actual depth-budgeted scheme is IND-CPA secure. The decryption circuit family identifies
the scheme but supplies no security premise; only base security and the stated native hypotheses
are used. -/
theorem indCPA_scheme {secretWidth ciphertextWidth : ℕ → ℕ}
    (D : DecryptionCircuits E secretWidth ciphertextWidth) :
    Encryption.INDCPA (scheme D budget).keyGen (scheme D budget).encrypt :=
  indCPA_keyGen hsecure hkeyGen hencrypt hwidth hbudget

end Cslib.Crypto.Homomorphic.Leveled
