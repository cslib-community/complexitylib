/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.CoinTape.Realization
public import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.ExactSecurity
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Tactic.PPT

/-!
# Polynomial overhead realizations for the leveled reduction

The leveled reduction of `CslibFrontier.Crypto.Computational.Homomorphic.Leveled.ExactSecurity`
runs four native components: base key generation, base encryption, and the two stages of the
attacked adversary. This module fixes one polynomial envelope per component, evaluated at the
largest encoded input that the reduction passes to it, and realizes each component on a coin
tape of that size ([Gentry2009], Section 2, Theorem 4, p. 171, without the theorem's
running-time clause).

## Main definitions

* `Cslib.Crypto.Homomorphic.Leveled.OverheadBudget`: the four envelopes and the derived key,
  encryption, public-key, message-selection and guessing budgets.
* `Cslib.Crypto.Homomorphic.Leveled.OverheadRealization`: `CoinTapeRealization`s of the four
  components on their bounded inputs at those budgets.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.exists_overheadRealization`: one budget serves every chain
  depth and secret capacity.
* `Cslib.Crypto.Homomorphic.Leveled.OverheadBudget.polynomiallyBounded_leveledChooseCoinBudget`,
  `Cslib.Crypto.Homomorphic.Leveled.OverheadBudget.polynomiallyBounded_leveledGuessCoinBudget`:
  the coin counts of `leveledAdversary` at these budgets are polynomially bounded.
* `Cslib.Crypto.Homomorphic.Leveled.OverheadRealization.length_keys_le`,
  `Cslib.Crypto.Homomorphic.Leveled.OverheadRealization.length_encPublicKey_le`,
  `Cslib.Crypto.Homomorphic.Leveled.OverheadRealization.length_state_le`: supported keys,
  public artifacts and saved states fit the budgets.

There is no replay law for `leveledAdversary` itself and no running-time comparison with the
attacked adversary.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2, Theorem 4][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

open ProbComp Probability Turing.MultiTapeTM

/-- Polynomial envelopes for the four native components of a leveled reduction. Each envelope
`c * (m + 1) ^ d` is evaluated at the largest encoded input that the reduction passes to that
component: base key generation at `1ⁿ`, base encryption at a bounded base public key,
`adversary.choose` at a bounded serialized leveled public key, and `adversary.guess` at a bounded
saved state with a tagged base ciphertext. -/
structure OverheadBudget where
  /-- Factor of the base key-generation envelope. -/
  keyFactor : ℕ
  /-- Degree of the base key-generation envelope. -/
  keyDegree : ℕ
  /-- Factor of the base encryption envelope. -/
  encFactor : ℕ
  /-- Degree of the base encryption envelope. -/
  encDegree : ℕ
  /-- Factor of the message-selection envelope. -/
  chooseFactor : ℕ
  /-- Degree of the message-selection envelope. -/
  chooseDegree : ℕ
  /-- Factor of the guessing envelope. -/
  guessFactor : ℕ
  /-- Degree of the guessing envelope. -/
  guessDegree : ℕ

namespace OverheadBudget

variable (B : OverheadBudget) (depth capacity : ℕ → ℕ)

/-- Coins for, and length of every supported key pair from, base key generation. -/
def keyCoins (n : ℕ) : ℕ := B.keyFactor * (n + 1) ^ B.keyDegree

/-- Coins for, and length of every supported ciphertext from, base encryption under a public key
of length at most `B.keyCoins n`. -/
def encCoins (n : ℕ) : ℕ := B.encFactor * (2 * n + 2 * B.keyCoins n + 5) ^ B.encDegree

/-- Bound on every serialized leveled public key of chain depth `depth n`. -/
def publicKeyLength (n : ℕ) : ℕ :=
  publicKeyLengthBound (depth n) (capacity n) (B.keyCoins n) (B.encCoins n)

/-- Coins for, and saved-state length of, `adversary.choose` on a leveled public key of length at
most `B.publicKeyLength depth capacity n`. -/
def chooseCoins (n : ℕ) : ℕ :=
  B.chooseFactor * (2 * n + B.publicKeyLength depth capacity n + 2) ^ B.chooseDegree

/-- Coins for `adversary.guess` on a saved state of length at most
`B.chooseCoins depth capacity n` and a tagged ciphertext of length at most `B.encCoins n + 1`. -/
def guessCoins (n : ℕ) : ℕ :=
  B.guessFactor *
    (2 * n + 2 * B.chooseCoins depth capacity n + B.encCoins n + 4) ^ B.guessDegree

theorem computableInPolyTime_keyCoins : ComputableInPolyTime B.keyCoins encUnary encUnary := by
  unfold keyCoins
  fun_prop

theorem computableInPolyTime_encCoins : ComputableInPolyTime B.encCoins encUnary encUnary := by
  unfold encCoins keyCoins
  fun_prop

variable {depth capacity}

theorem computableInPolyTime_chooseCoins (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary) :
    ComputableInPolyTime (B.chooseCoins depth capacity) encUnary encUnary := by
  unfold chooseCoins publicKeyLength publicKeyLengthBound encCoins keyCoins
  fun_prop

theorem computableInPolyTime_guessCoins (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary) :
    ComputableInPolyTime (B.guessCoins depth capacity) encUnary encUnary := by
  unfold guessCoins chooseCoins publicKeyLength publicKeyLengthBound encCoins keyCoins
  fun_prop

/-- The message-selection coin count of `leveledAdversary` at these envelopes is polynomially
bounded. -/
theorem polynomiallyBounded_leveledChooseCoinBudget
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary) :
    PolynomiallyBounded (fun n => leveledChooseCoinBudget (depth n) (capacity n)
      (B.keyCoins n) (B.encCoins n) (B.chooseCoins depth capacity n)) :=
  Leveled.polynomiallyBounded_leveledChooseCoinBudget hdepth.polynomiallyBounded
    hcapacity.polynomiallyBounded B.computableInPolyTime_keyCoins.polynomiallyBounded
    B.computableInPolyTime_encCoins.polynomiallyBounded
    (B.computableInPolyTime_chooseCoins hdepth hcapacity).polynomiallyBounded

/-- The guessing coin count of `leveledAdversary` at these envelopes is polynomially bounded. -/
theorem polynomiallyBounded_leveledGuessCoinBudget
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary) :
    PolynomiallyBounded (fun n => leveledGuessCoinBudget (depth n) (capacity n)
      (B.encCoins n) (B.chooseCoins depth capacity n) (B.guessCoins depth capacity n)) :=
  Leveled.polynomiallyBounded_leveledGuessCoinBudget hdepth.polynomiallyBounded
    hcapacity.polynomiallyBounded B.computableInPolyTime_encCoins.polynomiallyBounded
    (B.computableInPolyTime_chooseCoins hdepth hcapacity).polynomiallyBounded
    (B.computableInPolyTime_guessCoins hdepth hcapacity).polynomiallyBounded

end OverheadBudget

/-- Native coin-tape realizations of the four components of a leveled reduction at the
envelopes `B`, for chain depth `depth` and secret capacity `capacity`. Base key generation is
realized everywhere; base encryption on public keys of length at most `B.keyCoins n`;
`adversary.choose` on leveled public keys of length at most `B.publicKeyLength depth capacity n`;
and `adversary.guess` on saved states of length at most `B.chooseCoins depth capacity n` with
ciphertexts of length at most `B.encCoins n + 1`. -/
structure OverheadRealization (E : Scheme) (adversary : Encryption.Adversary)
    (depth capacity : ℕ → ℕ) (B : OverheadBudget) where
  /-- Base key generation from `B.keyCoins n` coins. -/
  keyGen : CoinTapeRealization encUnary (encPair encBits encBits) E.keyGen Set.univ B.keyCoins
  /-- Base encryption from `B.encCoins n` coins under bounded public keys. -/
  encrypt : CoinTapeRealization (encKeyedInput encBool) encBits
    (fun (n, pk, bit) => E.encrypt n pk bit)
    {(n, pk, _) : ℕ × List Bool × Bool | pk.length ≤ B.keyCoins n}
    (fun (n, _, _) => B.encCoins n)
  /-- Message selection from `B.chooseCoins depth capacity n` coins on bounded public keys. -/
  choose : CoinTapeRealization (encPair encUnary encBits)
    (Encryption.encChoiceOut encBool) (fun (n, pk) => adversary.choose n pk)
    {(n, pk) : ℕ × List Bool | pk.length ≤ B.publicKeyLength depth capacity n}
    (fun (n, _) => B.chooseCoins depth capacity n)
  /-- Guessing from `B.guessCoins depth capacity n` coins on bounded states and ciphertexts. -/
  guess : CoinTapeRealization Encryption.encGuessInput encBool
    (fun (n, state, ct) => adversary.guess n state ct)
    {(n, state, ct) : ℕ × List Bool × List Bool |
      state.length ≤ B.chooseCoins depth capacity n ∧ ct.length ≤ B.encCoins n + 1}
    (fun (n, _, _) => B.guessCoins depth capacity n)

/-- Polynomial component envelopes and native coin-tape realizations for the leveled reduction
motivated by [Gentry2009], Section 2, Theorem 4, p. 171. One choice of envelopes serves every
chain depth and secret capacity. Strict PPT of `leveledAdversary` and `modLeveledAdversary` is
`isPPT_leveledAdversary` and `isPPT_modLeveledAdversary_two_mul`; the coin counts of
`leveledAdversary` at these envelopes are polynomially bounded
(`OverheadBudget.polynomiallyBounded_leveledChooseCoinBudget`,
`OverheadBudget.polynomiallyBounded_leveledGuessCoinBudget`). None of these results asserts the
source's multiplicative runtime comparison. -/
theorem exists_overheadRealization {E : Scheme}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBool) encBits (fun (n, pk, bit) => E.encrypt n pk bit))
    {adversary : Encryption.Adversary} (hadversary : adversary.IsPPT) :
    ∃ B : OverheadBudget, ∀ depth capacity : ℕ → ℕ,
      Nonempty (OverheadRealization E adversary depth capacity B) := by
  obtain ⟨c_kg, d_kg, hkg⟩ := hkeyGen.exists_coinTapeRealization
  obtain ⟨c_enc, d_enc, henc⟩ := hencrypt.exists_coinTapeRealization
  obtain ⟨c_ch, d_ch, hch⟩ := hadversary.choose.on.exists_coinTapeRealization
  obtain ⟨c_gu, d_gu, hgu⟩ := hadversary.guess.exists_coinTapeRealization
  let B : OverheadBudget := ⟨c_kg, d_kg, c_enc, d_enc, c_ch, d_ch, c_gu, d_gu⟩
  refine ⟨B, fun depth capacity => ?_⟩
  obtain ⟨keyGen⟩ := hkg Set.univ B.keyCoins fun n _ => by
    simp [B, OverheadBudget.keyCoins, encUnary_apply]
  obtain ⟨encrypt⟩ := henc {(n, pk, _) : ℕ × List Bool × Bool | pk.length ≤ B.keyCoins n}
    (fun (n, _, _) => B.encCoins n)
    (by
      rintro ⟨n, pk, bit⟩ hpk
      change pk.length ≤ B.keyCoins n at hpk
      have hin : (encPair encUnary (encPair encBits encBool) (n, pk, bit)).length + 1 ≤
          2 * n + 2 * B.keyCoins n + 5 := by
        simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
          encBool_apply, List.length_singleton]
        omega
      exact Nat.mul_le_mul_left c_enc (Nat.pow_le_pow_left hin d_enc))
  obtain ⟨choose⟩ := hch
    {(n, pk) : ℕ × List Bool | pk.length ≤ B.publicKeyLength depth capacity n}
    (fun (n, _) => B.chooseCoins depth capacity n)
    (by
      rintro ⟨n, pk⟩ hpk
      change pk.length ≤ B.publicKeyLength depth capacity n at hpk
      have hin : (encPair encUnary encBits (n, pk)).length + 1 ≤
          2 * n + B.publicKeyLength depth capacity n + 2 := by
        simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
        omega
      exact Nat.mul_le_mul_left c_ch (Nat.pow_le_pow_left hin d_ch))
  obtain ⟨guess⟩ := hgu
    {(n, state, ct) : ℕ × List Bool × List Bool |
      state.length ≤ B.chooseCoins depth capacity n ∧ ct.length ≤ B.encCoins n + 1}
    (fun (n, _, _) => B.guessCoins depth capacity n)
    (by
      rintro ⟨n, state, ct⟩ ⟨hstate, hct⟩
      have hin : (encPair encUnary (encPair encBits encBits) (n, state, ct)).length + 1 ≤
          2 * n + 2 * B.chooseCoins depth capacity n + B.encCoins n + 4 := by
        simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
        omega
      exact Nat.mul_le_mul_left c_gu (Nat.pow_le_pow_left hin d_gu))
  exact ⟨⟨keyGen, encrypt, choose, guess⟩⟩

namespace OverheadRealization

variable {E : Scheme} {adversary : Encryption.Adversary} {depth capacity : ℕ → ℕ}
  {B : OverheadBudget} (R : OverheadRealization E adversary depth capacity B)
include R

/-- Supported base keys have public keys within the key-generation envelope and, under the
secret-capacity hypothesis, secrets within `capacity n`. -/
theorem length_keys_le
    (hsecret : ∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support →
      keys.2.length ≤ capacity n)
    (n : ℕ) : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support,
      keys.1.length ≤ B.keyCoins n ∧ keys.2.length ≤ capacity n := by
  intro keys hkeys
  have hlen := R.keyGen.length_le n trivial keys hkeys
  simp only [length_encPair, encBits_apply] at hlen
  exact ⟨by omega, hsecret n keys hkeys⟩

/-- Every supported leveled public artifact of chain depth `depth n` fits
`B.publicKeyLength depth capacity n`. -/
theorem length_encPublicKey_le
    (hsecret : ∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support →
      keys.2.length ≤ capacity n)
    {n cut : ℕ} {artifact : List (List Bool) × List (List (List Bool))}
    (hartifact : artifact ∈ (ProbComp.eval (E.publicKeyChainHybrid n (depth n) cut)).support) :
    (encPublicKey artifact).length ≤ B.publicKeyLength depth capacity n :=
  length_encPublicKey_support_publicKeyChainHybrid_le n (depth n) cut (capacity n)
    (B.keyCoins n) (B.encCoins n) (R.length_keys_le hsecret n)
    (fun keys hkeys bit ct hct =>
      R.encrypt.length_le (n, keys.1, bit) (R.length_keys_le hsecret n keys hkeys).1 ct hct)
    hartifact

/-- Every supported choice on a bounded public key saves a state within the message-selection
envelope. -/
theorem length_state_le {n : ℕ} {pk : List Bool}
    (hpk : pk.length ≤ B.publicKeyLength depth capacity n)
    {choice : (Bool × Bool) × List Bool}
    (hchoice : choice ∈ (ProbComp.eval (adversary.choose n pk)).support) :
    choice.2.length ≤ B.chooseCoins depth capacity n := by
  have hlen := R.choose.length_le (n, pk) hpk choice hchoice
  simp only [length_encPair, encBool_apply, List.length_singleton, encBits_apply] at hlen
  change _ ≤ B.chooseCoins depth capacity n at hlen
  omega

end OverheadRealization

end Cslib.Crypto.Homomorphic.Leveled
