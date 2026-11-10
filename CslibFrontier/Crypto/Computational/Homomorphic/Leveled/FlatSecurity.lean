/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.ExactSecurity
public import CslibFrontier.Languages.Probabilistic.BoundedUniform
import CslibFrontier.Probability.PMF.Option.Bind
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PPT
import CslibFrontier.Computability.Probabilistic.BoundedUniform
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# A flattened finite-attempt leveled reduction

The selector samples the two link segments and the single zero-link step in one interval of
size `2 * depth * capacity + 1`. Finite-attempt exhaustion retains the rejecting tag. The
successful indices have equal unconditional mass; the signed hybrid telescope therefore
survives without an additive sampling error.

This is an original refinement of the existing reduction, not a formalization of the literal
loss or relative runtime in [Gentry2009, Section 2, Theorem 4]. The source's decryption-input
width and depth conventions remain separate from this library's secret capacity and chain depth.

## Main definitions

* `flatLeveledChoice`: dispatch to the original tagged choice callbacks.
* `flatLeveledAdversary`: bounded sampling of the actual elementary hybrid steps.

## Main results

* `isPPT_flatLeveledAdversary`: native strict PPT, including every attempted selector draw.
* `gap_flatLeveledAdversary`, `advantage_flatLeveledAdversary`: exact signed and unsigned
  security identities, retaining finite-attempt failure.
* `advantage_scheme_le_flatLeveledAdversary`: concrete loss at most
  `8/7 * (2 * depth * capacity + 1)`.
* `flatLeveled_loss_lt`: strict improvement over the old ideal loss when `depth * capacity ≥ 2`
  and at least three attempts are made.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Probability ProbComp Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- Dispatch one flattened index to the original tagged choice callbacks. Only interval indices
are sampled by `flatLeveledAdversary`; later indices use the zero-link branch. -/
def flatLeveledChoice (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (n : ℕ) (pk : List Bool) (index : ℕ) :
    ProbComp ((Bool × Bool) × List Bool) :=
  if index < depth n * capacity n then
    tagLeveledChoice false false <$>
      E.chooseLinkAt n (depth n - index / capacity n - 1) (index / capacity n)
        (index % capacity n) pk
  else if index < 2 * (depth n * capacity n) then
    (tagLeveledChoice false true ∘ swapLeveledChoice) <$>
      E.chooseLinkAt n (depth n - (index - depth n * capacity n) / capacity n - 1)
        ((index - depth n * capacity n) / capacity n)
        ((index - depth n * capacity n) % capacity n) pk
  else
    tagLeveledChoice true false <$> (zeroLinkAdversary E depth adversary).choose n pk

/-- One finite-attempt interval selects the two link segments and the zero-link step. Exhaustion
rejects in both challenge worlds. Even at zero depth or capacity the singleton interval is
sampled: a successful draw executes the original zero-link branch, while exhaustion rejects. -/
noncomputable def flatLeveledAdversary (E : Scheme) (attempts depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) : Encryption.Adversary where
  choose n pk := do
    let index ← sampleUniformInterval (2 * (depth n * capacity n) + 1) (attempts n)
    if index.isSome then flatLeveledChoice E depth capacity adversary n pk (index.getD 0)
    else pure rejectLeveledChoice
  guess := (leveledAdversary E depth capacity adversary).guess

/-- Uniform strict PPT for the changed selector and original callbacks. Unary attempts, depth
and capacity are charged inputs; the conclusion does not assert a relative runtime bound. -/
theorem isPPT_flatLeveledAdversary {E : Scheme}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun (n, pk, bit) => E.encrypt n pk bit))
    {adversary : Encryption.Adversary} (hadversary : adversary.IsPPT)
    {attempts depth capacity : ℕ → ℕ}
    (hattempts : ComputableInPolyTime attempts encUnary encUnary)
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary) :
    (flatLeveledAdversary E attempts depth capacity adversary).IsPPT := by
  have htag := computableInPolyTime_tagLeveledChoice
  have hswap := computableInPolyTime_swapLeveledChoice
  have hzero := isPPT_zeroLinkAdversary hencrypt hadversary hkeyGen hdepth
  have hlev := isPPT_leveledAdversary hencrypt hadversary hkeyGen hdepth hcapacity
  constructor
  · change IsPPTOn (encPair encUnary encBits) (encPair (encPair encBool encBool) encBits) _
    dsimp only [flatLeveledAdversary]
    apply (isPPTOn_sampleUniformInterval (by fun_prop)
      (hattempts.comp (by fun_prop))).bind_with
    apply IsPPTOn.ite (by fun_prop)
    · dsimp only [flatLeveledChoice]
      apply IsPPTOn.ite (by polytime)
      · apply IsPPTOn.map _ (htag false false)
        apply Scheme.isPPTOn_chooseLinkAt hkeyGen <;> fun_prop
      · apply IsPPTOn.ite (by polytime)
        · apply IsPPTOn.map _ ((htag false true).comp hswap)
          apply Scheme.isPPTOn_chooseLinkAt hkeyGen <;> fun_prop
        · exact (hzero.choose.on.preprocess (by fun_prop)).map (htag true false)
    · exact (ComputableInPolyTime.const rejectLeveledChoice).isPPTOn
  · exact hlev.guess

private noncomputable def flatGame (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n index : ℕ) : Game :=
  ProbComp.eval (do
    let keys ← E.keyGen n
    let choice ← flatLeveledChoice E depth capacity adversary n keys.1 index
    let ciphertext ← E.encrypt n keys.1 (if bit then choice.1.2 else choice.1.1)
    (leveledAdversary E depth capacity adversary).guess n choice.2 ciphertext)

private theorem flatGame_left (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n index : ℕ)
    (hindex : index < depth n * capacity n) :
    flatGame E depth capacity adversary bit n index =
      ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (E.linkAdversaryAt (fun _ => depth n - index / capacity n - 1)
          (fun _ => index / capacity n) (fun _ => index % capacity n)
          (publicKeyGame E adversary false)) bit n) := by
  simp [flatGame, flatLeveledChoice, hindex, Encryption.game, Encryption.gameOn,
    leveledAdversary, Scheme.linkAdversaryAt, Scheme.linkAdversary,
    tagLeveledChoice, ProbComp.eval_bind, Function.comp_def]

private theorem flatGame_right (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n index : ℕ)
    (hindex : index < depth n * capacity n) :
    flatGame E depth capacity adversary bit n (depth n * capacity n + index) =
      ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (E.linkAdversaryAt (fun _ => depth n - index / capacity n - 1)
          (fun _ => index / capacity n) (fun _ => index % capacity n)
          (publicKeyGame E adversary true)) (!bit) n) := by
  have hfirst : ¬depth n * capacity n + index < depth n * capacity n := by omega
  have hsecond : depth n * capacity n + index < 2 * (depth n * capacity n) := by omega
  cases bit <;> simp [flatGame, flatLeveledChoice, hfirst, hsecond, Encryption.game,
    Encryption.gameOn, leveledAdversary, Scheme.linkAdversaryAt, Scheme.linkAdversary,
    tagLeveledChoice, swapLeveledChoice, ProbComp.eval_bind, Function.comp_def]

private theorem flatGame_last (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    flatGame E depth capacity adversary bit n (2 * (depth n * capacity n)) =
      ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (zeroLinkAdversary E depth adversary) bit n) := by
  have hfirst : ¬2 * (depth n * capacity n) < depth n * capacity n := by omega
  simp [flatGame, flatLeveledChoice, hfirst, Encryption.game, Encryption.gameOn,
    leveledAdversary, tagLeveledChoice, ProbComp.eval_bind, Function.comp_def]

private theorem sum_link_games (E : Scheme) (depth capacity : ℕ → ℕ)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool)
    (bit : Bool) (n : ℕ) :
    (∑ index : Fin (depth n * capacity n),
      (Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (E.linkAdversaryAt (fun _ => depth n - index.val / capacity n - 1)
          (fun _ => index.val / capacity n) (fun _ => index.val % capacity n) test) bit n)) : ℝ)) =
    (depth n : ℝ) * capacity n * Game.succProbability (ProbComp.eval
      (Encryption.game E.keyGen E.encrypt (E.exactLinkAdversary depth capacity test) bit n)) := by
  by_cases hpos : 0 < depth n ∧ 0 < capacity n
  · obtain ⟨hdepth, hcapacity⟩ := hpos
    have hpos : 0 < depth n ∧ 0 < capacity n := ⟨hdepth, hcapacity⟩
    have : NeZero (depth n) := ⟨hdepth.ne'⟩
    have : NeZero (capacity n) := ⟨hcapacity.ne'⟩
    have hlaw : ProbComp.eval
        (Encryption.game E.keyGen E.encrypt (E.exactLinkAdversary depth capacity test) bit n) =
        (PMF.uniformOfFintype (Fin (depth n))).bind fun i =>
          (PMF.uniformOfFintype (Fin (capacity n))).bind fun j =>
            ProbComp.eval (Encryption.game E.keyGen E.encrypt
              (E.linkAdversaryAt (fun _ => depth n - i.val - 1) (fun _ => i.val)
                (fun _ => j.val) test) bit n) := by
      dsimp only [Encryption.game, Encryption.gameOn, Scheme.exactLinkAdversary]
      simp only [dite_eq_left_of_eq_true (eq_true hpos), bind_assoc, ProbComp.eval_bind,
        ProbComp.eval_uniform]
      pmf_swap
      rfl
    rw [hlaw, Game.succProbability_uniform]
    simp_rw [Game.succProbability_uniform]
    simp only [NNReal.coe_div, NNReal.coe_sum, Fintype.card_fin, NNReal.coe_natCast]
    rw [← (finProdFinEquiv (m := depth n) (n := capacity n)).sum_comp]
    simp only [Fintype.sum_prod_type]
    have hval (p : Fin (depth n) × Fin (capacity n)) :
        (finProdFinEquiv p).val = p.2.val + capacity n * p.1.val := rfl
    simp_rw [hval]
    have hdiv (i : Fin (depth n)) (j : Fin (capacity n)) :
        (j.val + capacity n * i.val) / capacity n = i.val := by
      rw [Nat.add_mul_div_left _ _ hcapacity, Nat.div_eq_of_lt j.isLt, zero_add]
    simp_rw [hdiv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Fin.isLt _)]
    rw [← Finset.sum_div]
    have hD : (depth n : ℝ) ≠ 0 := by exact_mod_cast hdepth.ne'
    have hC : (capacity n : ℝ) ≠ 0 := by exact_mod_cast hcapacity.ne'
    field_simp [hD, hC]
  · have hz : depth n = 0 ∨ capacity n = 0 := by omega
    rcases hz with hz | hz <;> simp [hz]

private theorem sum_flatGame (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    (∑ index : Fin (2 * (depth n * capacity n) + 1),
      (Game.succProbability (flatGame E depth capacity adversary bit n index.val) : ℝ)) =
    (depth n : ℝ) * capacity n * Game.succProbability (ProbComp.eval
      (Encryption.game E.keyGen E.encrypt
        (E.exactLinkAdversary depth capacity (publicKeyGame E adversary false)) bit n)) +
    (depth n : ℝ) * capacity n * Game.succProbability (ProbComp.eval
      (Encryption.game E.keyGen E.encrypt
        (E.exactLinkAdversary depth capacity (publicKeyGame E adversary true)) (!bit) n)) +
    Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (zeroLinkAdversary E depth adversary) bit n)) := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [flatGame_last, two_mul, Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  simp_rw [flatGame_left E depth capacity adversary bit n _ (Fin.isLt _),
    flatGame_right E depth capacity adversary bit n _ (Fin.isLt _)]
  rw [sum_link_games E depth capacity _ bit n,
    sum_link_games E depth capacity _ (!bit) n]

private theorem eval_flatLeveledAdversary (E : Scheme) (attempts depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (flatLeveledAdversary E attempts depth capacity adversary) bit n) =
      (ProbComp.eval (sampleUniformInterval (2 * (depth n * capacity n) + 1)
        (attempts n))).bind fun index =>
        if index.isSome then flatGame E depth capacity adversary bit n (index.getD 0)
        else PMF.pure false := by
  dsimp only [Encryption.game, Encryption.gameOn, flatLeveledAdversary]
  simp only [bind_assoc, ProbComp.eval_bind]
  pmf_swap with index
  cases index with
  | none =>
    simp [leveledAdversary, rejectLeveledChoice, ProbComp.eval_bind]
  | some index =>
    simp only [Option.isSome_some, ↓reduceIte, Option.getD_some, flatGame, ProbComp.eval_bind]

private theorem succProbability_flatLeveledAdversary_sum (E : Scheme)
    (attempts depth capacity : ℕ → ℕ) (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (flatLeveledAdversary E attempts depth capacity adversary) bit n)) =
    intervalSuccess (2 * (depth n * capacity n) + 1) (attempts n) /
      (2 * (depth n * capacity n) + 1 : ℕ) *
        ∑ index : Fin (2 * (depth n * capacity n) + 1),
          Game.succProbability (flatGame E depth capacity adversary bit n index.val) := by
  let N := 2 * (depth n * capacity n) + 1
  have : NeZero N := ⟨by dsimp [N]; omega⟩
  have h := Probability.PMF.bind_option_apply_of_some
    (ProbComp.eval (sampleUniformInterval N (attempts n)))
    ((PMF.uniformOfFintype (Fin N)).map Fin.val) (intervalSuccess N (attempts n))
    (fun value => eval_sampleUniformInterval_some_eq N (attempts n) value)
    (fun index => if index.isSome then flatGame E depth capacity adversary bit n (index.getD 0)
      else PMF.pure false) true
  apply NNReal.eq
  rw [eval_flatLeveledAdversary]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
  rw [h]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    show (PMF.pure false) true = 0 by simp, mul_zero, zero_add, PMF.bind_map,
    Function.comp_def,
    Option.isSome_some, Option.getD_some, ENNReal.toReal_mul, ENNReal.coe_toReal]
  change (intervalSuccess N (attempts n) : ℝ) *
    Game.succProbability ((PMF.uniformOfFintype (Fin N)).bind
      (fun index => flatGame E depth capacity adversary bit n index.val)) = _
  rw [Game.succProbability_uniform]
  simp only [NNReal.coe_div, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_natCast,
    Fintype.card_fin, N]
  ring

/-- Acceptance probability of the actual flattened game, retaining the finite-attempt success
mass and the two signed-telescope segments. No positive depth or capacity premise is needed. -/
theorem succProbability_flatLeveledAdversary (E : Scheme)
    (attempts depth capacity : ℕ → ℕ) (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    (Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (flatLeveledAdversary E attempts depth capacity adversary) bit n)) : ℝ) =
    (intervalSuccess (2 * (depth n * capacity n) + 1) (attempts n) : ℝ) /
      (2 * (depth n * capacity n) + 1 : ℕ) *
        ((depth n : ℝ) * capacity n * Game.succProbability (ProbComp.eval
          (Encryption.game E.keyGen E.encrypt
            (E.exactLinkAdversary depth capacity (publicKeyGame E adversary false)) bit n)) +
        (depth n : ℝ) * capacity n * Game.succProbability (ProbComp.eval
          (Encryption.game E.keyGen E.encrypt
            (E.exactLinkAdversary depth capacity (publicKeyGame E adversary true)) (!bit) n)) +
        Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (zeroLinkAdversary E depth adversary) bit n))) := by
  rw [succProbability_flatLeveledAdversary_sum]
  simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_sum]
  rw [sum_flatGame]

/-- The complete signed chosen-message gap is scaled by the unconditional successful-index
mass. This holds also at zero attempts, depth or capacity; no failure event is conditioned away.
Supported secrets must have the stated fixed width, bounded by capacity. -/
theorem gap_flatLeveledAdversary (E : Scheme) (attempts budget capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    (Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (flatLeveledAdversary E attempts (fun n => 2 * budget n) capacity adversary) false n)) : ℝ) -
      Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (flatLeveledAdversary E attempts (fun n => 2 * budget n) capacity adversary) true n)) =
    (intervalSuccess (2 * (2 * budget n * capacity n) + 1) (attempts n) : ℝ) /
      (2 * (2 * budget n * capacity n) + 1 : ℕ) *
        ((Game.succProbability (ProbComp.eval
          (Encryption.game (fun n => keyGen E n (budget n)) (encrypt E) adversary false n)) : ℝ) -
        Game.succProbability (ProbComp.eval
          (Encryption.game (fun n => keyGen E n (budget n)) (encrypt E) adversary true n))) := by
  rw [succProbability_flatLeveledAdversary, succProbability_flatLeveledAdversary,
    eval_game_keyGen E budget adversary false n, eval_game_keyGen E budget adversary true n]
  have hlinkFalse := E.publicKeyChainHybrid_gap_exactLinkAdversary (fun n => 2 * budget n) capacity
    (publicKeyGame E adversary false) n width hwidth hcapacity
  have hlinkTrue := E.publicKeyChainHybrid_gap_exactLinkAdversary (fun n => 2 * budget n) capacity
    (publicKeyGame E adversary true) n width hwidth hcapacity
  have hzeroFalse := eval_zeroLinkAdversary E (fun n => 2 * budget n) adversary false n width hwidth
  have hzeroTrue := eval_zeroLinkAdversary E (fun n => 2 * budget n) adversary true n width hwidth
  simp only [Bool.not_false, Bool.not_true, hzeroFalse, hzeroTrue, Nat.cast_mul,
    Nat.cast_ofNat] at *
  linear_combination
    ((intervalSuccess (2 * (2 * budget n * capacity n) + 1) (attempts n) : ℝ) /
      (2 * (2 * budget n * capacity n) + 1 : ℕ)) * (hlinkTrue - hlinkFalse)

/-- Exact unconditional advantage of the flattened reduction. The success coefficient retains
all finite-attempt failures, including the zero-attempt case. -/
theorem advantage_flatLeveledAdversary {E : Scheme}
    {secretWidth ciphertextWidth : ℕ → ℕ}
    (D : DecryptionCircuits E secretWidth ciphertextWidth)
    (attempts budget capacity : ℕ → ℕ) (adversary : Encryption.Adversary) (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    Encryption.advantage (Encryption.game E.keyGen E.encrypt
      (flatLeveledAdversary E attempts (fun n => 2 * budget n) capacity adversary)) n =
    intervalSuccess (2 * (2 * budget n * capacity n) + 1) (attempts n) /
      (2 * (2 * budget n * capacity n) + 1 : ℕ) *
      Encryption.advantage (Encryption.game (scheme D budget).keyGen (scheme D budget).encrypt
        adversary) n := by
  dsimp only [scheme]
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, Game.coe_advantage,
    Game.coe_advantage, gap_flatLeveledAdversary E attempts budget capacity adversary n width
      hwidth hcapacity, abs_mul, abs_of_nonneg (by positivity)]

private theorem flat_success_lower (depth capacity attempts : ℕ) (hattempts : 3 ≤ attempts) :
    (7 / 8 : ℝ≥0) ≤ intervalSuccess (2 * (depth * capacity) + 1) attempts := by
  have hp := intervalFailure_le_half (show 0 < 2 * (depth * capacity) + 1 by omega)
  have hpow : intervalFailure (2 * (depth * capacity) + 1) ^ attempts ≤ (1 / 8 : ℝ≥0) := by
    calc
      _ ≤ (1 / 2 : ℝ≥0) ^ attempts := by gcongr
      _ ≤ (1 / 2 : ℝ≥0) ^ 3 := pow_le_pow_right_of_le_one' (by norm_num) hattempts
      _ = 1 / 8 := by norm_num
  have hle : intervalFailure (2 * (depth * capacity) + 1) ^ attempts ≤ 1 :=
    hpow.trans (by exact_mod_cast (show (1 / 8 : ℝ) ≤ 1 by norm_num))
  have hreal : (intervalFailure (2 * (depth * capacity) + 1) : ℝ) ^ attempts ≤ 1 / 8 :=
    by exact_mod_cast hpow
  apply NNReal.coe_le_coe.mp
  simp only [intervalSuccess, NNReal.coe_sub hle, NNReal.coe_one, NNReal.coe_pow,
    NNReal.coe_div, NNReal.coe_ofNat]
  linarith

/-- The exact loss of the finite-attempt selector is at most `8/7` times the number of actual
hybrid steps once at least three attempts are made. -/
theorem flatLeveled_loss_le (depth capacity attempts : ℕ) (hattempts : 3 ≤ attempts) :
    (2 * (depth * capacity) + 1 : ℕ) /
      intervalSuccess (2 * (depth * capacity) + 1) attempts ≤
        (8 / 7 : ℝ≥0) * (2 * (depth * capacity) + 1 : ℕ) := by
  have hs := flat_success_lower depth capacity attempts hattempts
  have hpos : 0 < intervalSuccess (2 * (depth * capacity) + 1) attempts :=
    lt_of_lt_of_le (by norm_num) hs
  rw [div_le_iff₀ hpos]
  have hs' : (7 / 8 : ℝ) ≤ intervalSuccess (2 * (depth * capacity) + 1) attempts :=
    by exact_mod_cast hs
  apply NNReal.coe_le_coe.mp
  push_cast
  have hm := mul_le_mul_of_nonneg_right hs'
    (show (0 : ℝ) ≤ (2 * (depth * capacity) + 1 : ℕ) by positivity)
  push_cast at hm
  nlinarith

/-- For at least two link-bit positions, the finite-attempt flattened loss is strictly less
than the old ideal three-way selector's `3 * depth * capacity` loss. -/
theorem flatLeveled_loss_lt (depth capacity attempts : ℕ)
    (hpositions : 2 ≤ depth * capacity) (hattempts : 3 ≤ attempts) :
    (2 * (depth * capacity) + 1 : ℕ) /
      intervalSuccess (2 * (depth * capacity) + 1) attempts <
        (3 : ℝ≥0) * depth * capacity := by
  apply (flatLeveled_loss_le depth capacity attempts hattempts).trans_lt
  apply NNReal.coe_lt_coe.mp
  have hp : (2 : ℝ) ≤ (depth : ℝ) * capacity := by exact_mod_cast hpositions
  push_cast
  nlinarith

/-- A concrete bound for the actual strict-PPT flattened reduction, with no additive selector
error. Native strict PPT is supplied separately by `isPPT_flatLeveledAdversary`. -/
theorem advantage_scheme_le_flatLeveledAdversary {E : Scheme}
    {secretWidth ciphertextWidth : ℕ → ℕ}
    (D : DecryptionCircuits E secretWidth ciphertextWidth)
    (attempts budget capacity : ℕ → ℕ) (adversary : Encryption.Adversary) (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) (hattempts : 3 ≤ attempts n) :
    Encryption.advantage (Encryption.game (scheme D budget).keyGen (scheme D budget).encrypt
      adversary) n ≤
    (8 / 7 : ℝ≥0) * (2 * (2 * budget n * capacity n) + 1 : ℕ) *
      Encryption.advantage (Encryption.game E.keyGen E.encrypt
        (flatLeveledAdversary E attempts (fun n => 2 * budget n) capacity adversary)) n := by
  have hs := flat_success_lower (2 * budget n) (capacity n) (attempts n) hattempts
  rw [advantage_flatLeveledAdversary D attempts budget capacity adversary n width
    hwidth hcapacity]
  have hc : (8 / 7 : ℝ≥0) * (2 * (2 * budget n * capacity n) + 1 : ℕ) *
      (intervalSuccess (2 * (2 * budget n * capacity n) + 1) (attempts n) /
        (2 * (2 * budget n * capacity n) + 1 : ℕ)) ≥ 1 := by
    have hs' : (7 / 8 : ℝ) ≤ intervalSuccess (2 * (2 * budget n * capacity n) + 1)
        (attempts n) := by exact_mod_cast hs
    apply NNReal.coe_le_coe.mp
    push_cast
    field_simp
    nlinarith
  simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right hc
    (show 0 ≤ Encryption.advantage (Encryption.game (scheme D budget).keyGen
      (scheme D budget).encrypt adversary) n from zero_le)

end Cslib.Crypto.Homomorphic.Leveled
