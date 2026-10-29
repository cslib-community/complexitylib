/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Leveled.Reduction
public import Complexity.Crypto.Computational.Homomorphic.KeyChain.Reduction.Game
import Complexity.Probability.PMF.Bind

/-!
# Exact chosen-message games of leveled encryption

The actual serialized scheme experiment is the real public-chain hybrid followed by adaptive
message selection. At the zero-link endpoint, one base IND-CPA challenge simulates the entire
experiment, including the adversary's retained state and the fresh-ciphertext tag.

Combining the two encrypted-link hybrid reductions (`E.linkAdversary` for the `false` and
message-swapped `true` challenge worlds) with the dyadically weighted `zeroLinkAdversary` yields
`leveledAdversary`, whose base IND-CPA game achieves the exact concrete-security loss
`4 * dyadicSize (2 * budget n) * dyadicSize (capacity n)`, bounded between
`4 * (2 * budget n + 1) * (capacity n + 1)` and `16 * (2 * budget n + 1) * (capacity n + 1)` and
therefore matching Gentry's Theorem 4 loss `ℓ(d + 1)` up to a constant factor ([Gentry2009],
Section 2, Theorem 4, p. 171; the constant arises from the `2 * budget n` encrypted links, dyadic
power-of-two index rounding, and the four-way branch selector with one inactive branch).

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.eval_keyGen_public`: the exact serialized public marginal.
* `Cslib.Crypto.Homomorphic.Leveled.eval_game_keyGen`: the actual scheme game is the real-chain
  public-artifact experiment.
* `Cslib.Crypto.Homomorphic.Leveled.eval_zeroLinkAdversary`: an exact simulation of the zero-chain
  chosen-message experiment, including depth zero.
* `Cslib.Crypto.Homomorphic.Leveled.eval_leveledAdversary`: exact distributional decomposition of
  the unified base reduction `leveledAdversary`.
* `Cslib.Crypto.Homomorphic.Leveled.gap_leveledAdversary`: signed telescoping identity relating the
  leveled scheme's chosen-message gap to `leveledAdversary`.
* `Cslib.Crypto.Homomorphic.Leveled.advantage_game_eq_leveledAdversary`: exact unsigned advantage
  identity with factor `4 * dyadicSize (2 * budget n) * dyadicSize (capacity n)`.
* `Cslib.Crypto.Homomorphic.Leveled.advantage_game_le_mul_leveledAdversary`: concrete polynomial
  loss bound `16 * (2 * budget n + 1) * (capacity n + 1)` (Gentry's Theorem 4 up to a constant
  factor).

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2, Theorem 4][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

open ProbComp Probability
open scoped NNReal

/-- The actual key generator's public marginal is the serialized real-chain hybrid. -/
theorem eval_keyGen_public (E : Scheme) (n budget : ℕ) :
    (ProbComp.eval (keyGen E n budget)).map Prod.fst =
      (ProbComp.eval (E.publicKeyChainHybrid n (2 * budget) (2 * budget))).map encPublicKey := by
  rw [E.eval_publicKeyChainHybrid_depth]
  simp only [keyGen, keyPair, ProbComp.eval_map, PMF.map_comp, Function.comp_def]

/-- The public artifact and tagged challenge in the actual scheme game agree with the real
chain experiment; intermediate and endpoint secrets remain hidden. -/
theorem eval_game_keyGen (E : Scheme) (budget : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.game (fun n => keyGen E n (budget n)) (encrypt E)
      adversary bit n) =
      ProbComp.eval (E.publicKeyChainHybrid n (2 * budget n) (2 * budget n) >>=
        publicKeyGame E adversary bit n) := by
  rw [ProbComp.eval_bind, E.eval_publicKeyChainHybrid_depth]
  simp only [Encryption.game, Encryption.gameOn, ↓reduceIte, keyGen, keyPair, encrypt,
    publicKeyGame, ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map, Function.comp_def,
    publicKeyDecoder_decode_enc]

/-- The zero-link base adversary simulates the entire adaptive chosen-message experiment.
When the chain is nonempty, a generated secret supplies the unknown first secret's length;
when it is empty, no secret length is used. -/
theorem eval_zeroLinkAdversary (E : Scheme) (depth : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width) :
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (zeroLinkAdversary E depth adversary) bit n) =
      ProbComp.eval (E.publicKeyChainHybrid n (depth n) 0 >>=
        publicKeyGame E adversary bit n) := by
  simp only [Encryption.game, Encryption.gameOn, ↓reduceIte,
    zeroLinkAdversary, Scheme.publicKeyChainHybrid_zero,
    Scheme.generateKeys, OracleComp.replicate_succ, publicKeyGame,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.bind_bind, PMF.bind_map, PMF.pure_bind, Function.comp_def,
    List.map_cons, List.getD_cons_zero]
  apply Probability.PMF.bind_congr_on_support
  intro first hfirst
  apply Probability.PMF.bind_congr_on_support
  intro rest hrest
  have hlinks : E.encryptZeroKeyLinks n ((first.1, (rest.headD ([], [])).2) :: rest) =
      E.encryptZeroKeyLinks n (first :: rest) := by
    cases rest with
    | nil => rfl
    | cons second tail =>
      have hsecond : second ∈ (ProbComp.eval (E.keyGen n)).support :=
        ((ProbComp.mem_support_replicate_iff (depth n) (E.keyGen n) (second :: tail)).mp
          hrest).2 second (by simp)
      exact E.encryptZeroKeyLinks_cons_congr n (first.1, second.2) first (second :: tail)
        ((hwidth second hsecond).trans (hwidth first hfirst).symm)
  rw [hlinks]

private theorem eval_tagLeveledChoice_false_false (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (do
      let keys ← E.keyGen n
      let choice ← tagLeveledChoice false false <$>
        (E.linkAdversary depth capacity (publicKeyGame E adversary false)).choose n keys.1
      let ciphertext ← E.encrypt n keys.1 (if bit then choice.1.2 else choice.1.1)
      (leveledAdversary E depth capacity adversary).guess n choice.2 ciphertext) =
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (E.linkAdversary depth capacity (publicKeyGame E adversary false)) bit n) := by
  simp [Encryption.game, Encryption.gameOn, leveledAdversary, tagLeveledChoice,
    ProbComp.eval_bind, Function.comp_def]

private theorem eval_tagLeveledChoice_false_true (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (do
      let keys ← E.keyGen n
      let choice ← (tagLeveledChoice false true ∘ swapLeveledChoice) <$>
        (E.linkAdversary depth capacity (publicKeyGame E adversary true)).choose n keys.1
      let ciphertext ← E.encrypt n keys.1 (if bit then choice.1.2 else choice.1.1)
      (leveledAdversary E depth capacity adversary).guess n choice.2 ciphertext) =
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (E.linkAdversary depth capacity (publicKeyGame E adversary true)) (!bit) n) := by
  cases bit <;> simp [Encryption.game, Encryption.gameOn, leveledAdversary, tagLeveledChoice,
    swapLeveledChoice, ProbComp.eval_bind, Function.comp_def]

private theorem eval_tagLeveledChoice_true_false (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (do
      let keys ← E.keyGen n
      let choice ← tagLeveledChoice true false <$>
        (zeroLinkAdversary E depth adversary).choose n keys.1
      let ciphertext ← E.encrypt n keys.1 (if bit then choice.1.2 else choice.1.1)
      (leveledAdversary E depth capacity adversary).guess n choice.2 ciphertext) =
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (zeroLinkAdversary E depth adversary) bit n) := by
  simp [Encryption.game, Encryption.gameOn, leveledAdversary, tagLeveledChoice,
    ProbComp.eval_bind, Function.comp_def]

private theorem eval_rejectLeveledChoice (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (do
      let keys ← E.keyGen n
      let ciphertext ← E.encrypt n keys.1
        (if bit then rejectLeveledChoice.1.2 else rejectLeveledChoice.1.1)
      (leveledAdversary E depth capacity adversary).guess n rejectLeveledChoice.2 ciphertext) =
    PMF.pure false := by
  simp only [leveledAdversary, rejectLeveledChoice, List.headD_cons, List.tail_cons, ↓reduceIte,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_const]

private theorem leveledAdversary_choose (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (n : ℕ) (challengePk : List Bool) :
    (leveledAdversary E depth capacity adversary).choose n challengePk = (do
      let first ← ProbComp.uniform Bool
      let second ← ProbComp.uniform Bool
      if first then
        if second then
          pure rejectLeveledChoice
        else
          let keepLink ← sampleDyadicCoin (depth n) 1
          let keepBit ← sampleDyadicCoin (capacity n) 1
          if keepLink then
            if keepBit then
              tagLeveledChoice true false <$>
                (zeroLinkAdversary E depth adversary).choose n challengePk
            else
              pure rejectLeveledChoice
          else
            pure rejectLeveledChoice
      else
        if second then
          (tagLeveledChoice false true ∘ swapLeveledChoice) <$>
            (E.linkAdversary depth capacity (publicKeyGame E adversary true)).choose n challengePk
        else
          tagLeveledChoice false false <$>
            (E.linkAdversary depth capacity (publicKeyGame E adversary false)).choose n
              challengePk) := rfl

/-- The unified base reduction's encryption game is the fair four-branch average over the
`false`-world `linkAdversary`, the message-swapped `true`-world `linkAdversary`, the dyadically
weighted `zeroLinkAdversary`, and an inactive rejecting branch. -/
theorem eval_leveledAdversary (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (leveledAdversary E depth capacity adversary) bit n) =
    (PMF.uniformOfFintype Bool).bind fun first =>
      (PMF.uniformOfFintype Bool).bind fun second =>
        if first then
          if second then
            PMF.pure false
          else
            (ProbComp.eval (sampleDyadicCoin (depth n) 1)).bind fun keepLink =>
              if keepLink then
                (ProbComp.eval (sampleDyadicCoin (capacity n) 1)).bind fun keepBit =>
                  if keepBit then
                    ProbComp.eval (Encryption.game E.keyGen E.encrypt
                      (zeroLinkAdversary E depth adversary) bit n)
                  else
                    PMF.pure false
              else
                PMF.pure false
        else
          if second then
            ProbComp.eval (Encryption.game E.keyGen E.encrypt
              (E.linkAdversary depth capacity (publicKeyGame E adversary true)) (!bit) n)
          else
            ProbComp.eval (Encryption.game E.keyGen E.encrypt
              (E.linkAdversary depth capacity (publicKeyGame E adversary false)) bit n) := by
  dsimp only [Encryption.game, Encryption.gameOn]
  simp only [leveledAdversary_choose, bind_assoc, ProbComp.eval_bind, ProbComp.eval_uniform]
  rw [PMF.bind_comm]
  congr 1
  funext first
  rw [PMF.bind_comm]
  congr 1
  funext second
  cases first <;> cases second
  · simp only [Bool.false_eq_true, ↓reduceIte]
    simpa only [Encryption.game, Encryption.gameOn, ↓reduceIte, ProbComp.eval_bind] using
      eval_tagLeveledChoice_false_false E depth capacity adversary bit n
  · simp only [Bool.false_eq_true, ↓reduceIte]
    simpa only [Encryption.game, Encryption.gameOn, ↓reduceIte, ProbComp.eval_bind] using
      eval_tagLeveledChoice_false_true E depth capacity adversary bit n
  · simp only [Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind, PMF.bind_bind]
    rw [PMF.bind_comm]
    congr 1
    funext keepLink
    cases keepLink
    · simp only [Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind]
      rw [← PMF.bind_const (ProbComp.eval (sampleDyadicCoin (capacity n) 1)) (PMF.pure false)]
      rw [PMF.bind_comm]
      congr 1
      funext _
      simpa only [ProbComp.eval_bind] using
        eval_rejectLeveledChoice E depth capacity adversary bit n
    · simp only [↓reduceIte]
      rw [PMF.bind_comm]
      congr 1
      funext keepBit
      cases keepBit
      · simp only [Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind]
        simpa only [ProbComp.eval_bind] using
          eval_rejectLeveledChoice E depth capacity adversary bit n
      · simp only [↓reduceIte]
        simpa only [Encryption.game, Encryption.gameOn, ↓reduceIte, ProbComp.eval_bind] using
          eval_tagLeveledChoice_true_false E depth capacity adversary bit n
  · simp only [↓reduceIte, ProbComp.eval_pure, PMF.pure_bind]
    simpa only [ProbComp.eval_bind] using
      eval_rejectLeveledChoice E depth capacity adversary bit n

private theorem succProbability_uniform_bool (f : Bool → Game) :
    (Game.succProbability ((PMF.uniformOfFintype Bool).bind f) : ℝ) =
      ((Game.succProbability (f false) : ℝ) + Game.succProbability (f true)) / 2 := by
  rw [Game.succProbability_uniform]
  simp [add_comm]

private theorem succProbability_sampleDyadicCoin_one (bound : ℕ) (game : Game) :
    (dyadicSize bound : ℝ) *
      Game.succProbability ((ProbComp.eval (sampleDyadicCoin bound 1)).bind fun keep =>
        if keep then game else PMF.pure false) =
    Game.succProbability game := by
  have hpos : (dyadicSize bound : ℝ) ≠ 0 := by exact_mod_cast (dyadicSize_pos bound).ne'
  have hmin : min (dyadicSize bound) 1 = 1 :=
    Nat.min_eq_right ((by decide : 1 ≤ 2).trans (two_le_dyadicSize bound))
  rw [Game.coe_succProbability, Probability.PMF.bind_apply_toReal, Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true, PMF.pure_apply, Bool.true_eq_false,
    ENNReal.toReal_zero, mul_zero, add_zero, ProbComp.eval_sampleDyadicCoin_true_toReal,
    hmin, Nat.cast_one, Game.coe_succProbability, one_div]
  rw [← mul_assoc, mul_inv_cancel₀ hpos, one_mul]

/-- The exact scaled acceptance probability of `leveledAdversary` equals the sum of the two
dyadic-grid-scaled `linkAdversary` acceptance probabilities and the `zeroLinkAdversary`
acceptance probability. -/
theorem succProbability_leveledAdversary (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    4 * (dyadicSize (depth n) : ℝ) * dyadicSize (capacity n) *
      Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (leveledAdversary E depth capacity adversary) bit n)) =
    (dyadicSize (depth n) : ℝ) * dyadicSize (capacity n) *
      Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (E.linkAdversary depth capacity (publicKeyGame E adversary false)) bit n)) +
    (dyadicSize (depth n) : ℝ) * dyadicSize (capacity n) *
      Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (E.linkAdversary depth capacity (publicKeyGame E adversary true)) (!bit) n)) +
    Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (zeroLinkAdversary E depth adversary) bit n)) := by
  rw [eval_leveledAdversary, succProbability_uniform_bool, succProbability_uniform_bool,
    succProbability_uniform_bool]
  simp only [Bool.false_eq_true, ↓reduceIte, Game.succProbability, PMF.pure_apply,
    Bool.true_eq_false, ENNReal.toNNReal_zero, NNReal.coe_zero, add_zero]
  have hlink := succProbability_sampleDyadicCoin_one (depth n)
    ((ProbComp.eval (sampleDyadicCoin (capacity n) 1)).bind fun keepBit =>
      if keepBit then
        ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (zeroLinkAdversary E depth adversary) bit n)
      else PMF.pure false)
  have hbit := succProbability_sampleDyadicCoin_one (capacity n)
    (ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (zeroLinkAdversary E depth adversary) bit n))
  have hprod : (dyadicSize (depth n) : ℝ) * dyadicSize (capacity n) *
      Game.succProbability ((ProbComp.eval (sampleDyadicCoin (depth n) 1)).bind fun keepLink =>
        if keepLink then
          (ProbComp.eval (sampleDyadicCoin (capacity n) 1)).bind fun keepBit =>
            if keepBit then
              ProbComp.eval (Encryption.game E.keyGen E.encrypt
                (zeroLinkAdversary E depth adversary) bit n)
            else PMF.pure false
        else PMF.pure false) =
      Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (zeroLinkAdversary E depth adversary) bit n)) := by
    linear_combination (dyadicSize (capacity n) : ℝ) * hlink + hbit
  simp only [Game.succProbability] at hprod
  linarith

/-- The signed chosen-message gap of the actual serialized leveled scheme equals the exact
dyadic loss `4 * dyadicSize (2 * budget n) * dyadicSize (capacity n)` times the signed gap of
`leveledAdversary` against the base encryption scheme ([Gentry2009], Section 2, Theorem 4,
p. 171, up to a constant factor in the loss;
the running-time clause is not formalized). -/
theorem gap_leveledAdversary (E : Scheme) (budget capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    (Game.succProbability (ProbComp.eval
      (Encryption.game (fun n => keyGen E n (budget n)) (encrypt E) adversary false n)) : ℝ) -
      Game.succProbability (ProbComp.eval
        (Encryption.game (fun n => keyGen E n (budget n)) (encrypt E) adversary true n)) =
    4 * (dyadicSize (2 * budget n) : ℝ) * dyadicSize (capacity n) *
      (Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (leveledAdversary E (fun n => 2 * budget n) capacity adversary) false n)) -
        Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (leveledAdversary E (fun n => 2 * budget n) capacity adversary) true n))) := by
  rw [eval_game_keyGen E budget adversary false n, eval_game_keyGen E budget adversary true n]
  have hlinkFalse := E.publicKeyChainHybrid_gap_linkAdversary (fun n => 2 * budget n) capacity
    (publicKeyGame E adversary false) n width hwidth hcapacity
  have hlinkTrue := E.publicKeyChainHybrid_gap_linkAdversary (fun n => 2 * budget n) capacity
    (publicKeyGame E adversary true) n width hwidth hcapacity
  have hzeroFalse := eval_zeroLinkAdversary E (fun n => 2 * budget n) adversary false n width hwidth
  have hzeroTrue := eval_zeroLinkAdversary E (fun n => 2 * budget n) adversary true n width hwidth
  have hlevFalse := succProbability_leveledAdversary E (fun n => 2 * budget n) capacity
    adversary false n
  have hlevTrue := succProbability_leveledAdversary E (fun n => 2 * budget n) capacity
    adversary true n
  simp only [Bool.not_false, Bool.not_true, hzeroFalse, hzeroTrue] at hlevFalse hlevTrue
  linarith

/-- Exact unsigned concrete-security identity for the actual serialized leveled scheme:
its chosen-message advantage equals `4 * dyadicSize (2 * budget n) * dyadicSize (capacity n)`
times the base chosen-message advantage of `leveledAdversary` ([Gentry2009], Section 2,
Theorem 4, p. 171, up to a constant factor in the loss;
the running-time clause is not formalized). -/
theorem advantage_game_eq_leveledAdversary (E : Scheme) (budget capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    Game.advantage
      (ProbComp.eval (Encryption.game (fun n => keyGen E n (budget n)) (encrypt E)
        adversary false n))
      (ProbComp.eval (Encryption.game (fun n => keyGen E n (budget n)) (encrypt E)
        adversary true n)) =
    4 * (dyadicSize (2 * budget n) : ℝ≥0) * dyadicSize (capacity n) *
      Game.advantage
        (ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (leveledAdversary E (fun n => 2 * budget n) capacity adversary) false n))
        (ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (leveledAdversary E (fun n => 2 * budget n) capacity adversary) true n)) := by
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_ofNat,
    NNReal.coe_natCast, NNReal.coe_natCast, Game.coe_advantage, Game.coe_advantage,
    gap_leveledAdversary E budget capacity adversary n width hwidth hcapacity,
    abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4),
    Nat.abs_cast, Nat.abs_cast]

/-- Polynomial concrete-security bound for the actual serialized leveled scheme in terms of
the chain length `2 * budget n` and secret-width bound `capacity n`: rounding both dyadic
ranges via `dyadicSize_le` bounds the single-adversary reduction loss by
`16 * (2 * budget n + 1) * (capacity n + 1)` ([Gentry2009], Section 2, Theorem 4, p. 171, up to
a constant factor in the loss; the running-time clause is not formalized). -/
theorem advantage_game_le_mul_leveledAdversary (E : Scheme) (budget capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    Game.advantage
      (ProbComp.eval (Encryption.game (fun n => keyGen E n (budget n)) (encrypt E)
        adversary false n))
      (ProbComp.eval (Encryption.game (fun n => keyGen E n (budget n)) (encrypt E)
        adversary true n)) ≤
    16 * (2 * budget n + 1 : ℝ≥0) * (capacity n + 1) *
      Game.advantage
        (ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (leveledAdversary E (fun n => 2 * budget n) capacity adversary) false n))
        (ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (leveledAdversary E (fun n => 2 * budget n) capacity adversary) true n)) := by
  rw [advantage_game_eq_leveledAdversary E budget capacity adversary n width hwidth hcapacity]
  have hdepth : (dyadicSize (2 * budget n) : ℝ≥0) ≤ 2 * (2 * budget n + 1) := by
    exact_mod_cast dyadicSize_le (2 * budget n)
  have hcap : (dyadicSize (capacity n) : ℝ≥0) ≤ 2 * (capacity n + 1) := by
    exact_mod_cast dyadicSize_le (capacity n)
  calc
    4 * (dyadicSize (2 * budget n) : ℝ≥0) * dyadicSize (capacity n) *
        Game.advantage
          (ProbComp.eval (Encryption.game E.keyGen E.encrypt
            (leveledAdversary E (fun n => 2 * budget n) capacity adversary) false n))
          (ProbComp.eval (Encryption.game E.keyGen E.encrypt
            (leveledAdversary E (fun n => 2 * budget n) capacity adversary) true n))
      ≤ 4 * (2 * (2 * budget n + 1 : ℝ≥0)) * (2 * (capacity n + 1)) *
        Game.advantage
          (ProbComp.eval (Encryption.game E.keyGen E.encrypt
            (leveledAdversary E (fun n => 2 * budget n) capacity adversary) false n))
          (ProbComp.eval (Encryption.game E.keyGen E.encrypt
            (leveledAdversary E (fun n => 2 * budget n) capacity adversary) true n)) := by
        gcongr
    _ = 16 * (2 * budget n + 1 : ℝ≥0) * (capacity n + 1) *
        Game.advantage
          (ProbComp.eval (Encryption.game E.keyGen E.encrypt
            (leveledAdversary E (fun n => 2 * budget n) capacity adversary) false n))
          (ProbComp.eval (Encryption.game E.keyGen E.encrypt
            (leveledAdversary E (fun n => 2 * budget n) capacity adversary) true n)) := by
        ring

end Cslib.Crypto.Homomorphic.Leveled
