/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.Security
public import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.Size
public import CslibFrontier.Crypto.Game.Statistical
import CslibFrontier.Crypto.Computational.Homomorphic.KeyChain.Size
import CslibFrontier.Computability.Probabilistic.CoinTape.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT

/-!
# Exact hybrid loss for Gentry Theorem 4, modular index sampling, and overhead bounds

`CslibFrontier.Crypto.Computational.Homomorphic.Leveled.Security` proves IND-CPA security of the
depth-budgeted leveled scheme `scheme D budget` via `leveledAdversary`, which samples link and
secret-bit coordinates from power-of-two ranges `dyadicSize (2 * budget n)` and
`dyadicSize (capacity n)` and therefore incurs a constant-factor dyadic rounding loss
`4 * dyadicSize (2 * budget n) * dyadicSize (capacity n)`, which is at most
`16 * (2 * budget n + 1) * (capacity n + 1)`.

This module formalizes the two remaining quantitative refinements noted in Issue #1104 (Item 3)
for [Gentry2009, Section 2, Theorem 4, p. 171], up to a constant factor in the loss and without
the theorem's running-time clause:

1. **Exact `(2 * budget n) * (capacity n)` hybrid loss and `sampleModNat` bridge**:
   * `Scheme.exactKeyChainHybridGame` and `Scheme.exactLinkAdversary` sample the reverse link index
     uniformly from `Fin (depth n)` and the secret-bit index uniformly from `Fin (capacity n)` when
     both bounds are positive, achieving the exact key-chain advantage identity with loss
     `(depth n : ℝ≥0) * capacity n` (`Scheme.publicKeyChainHybrid_advantage_exactLinkAdversary`)
     and no `dyadicSize` factor.
   * `Leveled.exactLeveledAdversary` combines the two key-chain hybrid hops and the zero-link hop
     using a uniform `Fin 3` hop selector and uniform `Fin (2 * budget n) × Fin (capacity n)`
     coordinates, achieving the exact concrete-security identity with loss
     `3 * (2 * budget n : ℝ≥0) * capacity n` (`Leveled.advantage_scheme_eq_exactLeveledAdversary`),
     together with the unattenuated three-hop decomposition bound
     `Leveled.advantage_scheme_le_exactLinkAdversary_add_zeroLinkAdversary`.
   * `Scheme.modLinkAdversary` and `Leveled.modLeveledAdversary` replace exact finite-range index
     sampling by strict-PPT modular sampling via `ProbComp.sampleModNat`, certified uniform strict
     PPT (`Scheme.isPPT_modLinkAdversary`, `Leveled.isPPT_modLeveledAdversary`); no such
     certificate is proved for the two exact adversaries. The resulting bound multiplies the exact
     loss factor by the sum of the base advantage and a statistical tail
     (`Leveled.advantage_scheme_le_modLeveledAdversary`). With `2 * n` coins per sample that tail
     is at most `2 / 2 ^ n` when `3 + 2 * budget n + capacity n ≤ 2 ^ n`
     (`Leveled.advantage_scheme_le_modLeveledAdversary_two_mul`).

2. **Explicit polynomial artifact-length, saved-state, and coin-budget overhead bounds**:
   * `Leveled.publicKeyLengthBound` and
     `Leveled.length_encPublicKey_support_publicKeyChainHybrid_le` bound the bit length of every
     serialized public key passed to `adversary.choose` in terms of the chain depth `2 * budget n`,
     secret width `width`, and base key/ciphertext lengths.
   * `Scheme.linkStateLengthBound` and `Scheme.length_activeLinkState_le` bound the bit length of
     every active reduction state saved by `Scheme.chooseLinkAt`.
   * `Leveled.exists_leveledAdversary_overhead` packages polynomial length bounds and seeded
     replay laws for the base scheme's `keyGen`/`encrypt` and for `adversary`'s two stages at the
     leveled public-key and ciphertext sizes, polynomial boundedness of the coin-count formulas
     `Leveled.leveledChooseCoinBudget` and `Leveled.leveledGuessCoinBudget`, and strict-PPT
     certificates for `leveledAdversary` and `modLeveledAdversary`. It contains no replay law for
     `leveledAdversary` itself and no running-time comparison with `adversary`.

## Main definitions

* `Cslib.Crypto.Homomorphic.Scheme.exactKeyChainHybridGame`: exact uniform
  `Fin depth × Fin capacity` key-chain hybrid game.
* `Cslib.Crypto.Homomorphic.Scheme.exactLinkAdversary`: uniform-index two-stage key-chain reduction.
* `Cslib.Crypto.Homomorphic.Scheme.sampleModIndex`: modular residue sampler capped for unary
  output.
* `Cslib.Crypto.Homomorphic.Scheme.modLinkAdversary`: strict-PPT `sampleModNat` key-chain reduction.
* `Cslib.Crypto.Homomorphic.Scheme.linkStateLengthBound`: explicit upper bound on active link-state
  length.
* `Cslib.Crypto.Homomorphic.Leveled.exactLeveledAdversary`: uniform-index unified leveled reduction.
* `Cslib.Crypto.Homomorphic.Leveled.modLeveledAdversary`: strict-PPT `sampleModNat` unified leveled
  reduction.
* `Cslib.Crypto.Homomorphic.Leveled.publicKeyLengthBound`: explicit upper bound on serialized
  leveled public-key length.
* `Cslib.Crypto.Homomorphic.Leveled.leveledChooseCoinBudget`,
  `Cslib.Crypto.Homomorphic.Leveled.leveledGuessCoinBudget`: coin-count formulas for the two
  stages of `leveledAdversary`, proved polynomially bounded here.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.publicKeyChainHybrid_advantage_exactLinkAdversary`: exact
  key-chain reduction loss `(depth n : ℝ≥0) * capacity n`.
* `Cslib.Crypto.Homomorphic.Scheme.isPPT_modLinkAdversary`,
  `Cslib.Crypto.Homomorphic.Scheme.publicKeyChainHybrid_advantage_le_modLinkAdversary`: strict-PPT
  modular key-chain reduction and concrete advantage bound.
* `Cslib.Crypto.Homomorphic.Leveled.advantage_scheme_eq_exactLeveledAdversary`: exact
  concrete-security identity with loss `3 * (2 * budget n : ℝ≥0) * capacity n` and no dyadic
  rounding (Gentry's Theorem 4 up to a constant factor).
* `Cslib.Crypto.Homomorphic.Leveled.isPPT_modLeveledAdversary`,
  `Cslib.Crypto.Homomorphic.Leveled.advantage_scheme_le_modLeveledAdversary`,
  `Cslib.Crypto.Homomorphic.Leveled.advantage_scheme_le_modLeveledAdversary_two_mul`: strict-PPT
  modular leveled reduction, whose bound multiplies the loss factor by the sum of the base
  advantage and a statistical tail (`2 / 2 ^ n` in the `2 * n`-coin specialization).
* `Cslib.Crypto.Homomorphic.Leveled.length_encPublicKey_support_publicKeyChainHybrid_le`,
  `Cslib.Crypto.Homomorphic.Leveled.exists_leveledAdversary_overhead`: explicit polynomial
  artifact-length bounds, component replay laws, polynomially bounded coin-count formulas and
  strict-PPT certificates for `leveledAdversary` and `modLeveledAdversary`.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2, Theorem 4][Gentry2009]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Section 11.2][BonehShoup2023]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

open ProbComp Probability Turing.MultiTapeTM
open scoped NNReal Cslib.Probability.PMF

variable (E : Scheme)

/-! ### Exact uniform-index key-chain hybrids and reduction -/

/-- Telescope the bit hybrids of one link over `Fin capacity` without dyadic rounding. -/
theorem publicKeyLinkHybrid_exact_gap (n beforeCount afterCount width capacity : ℕ)
    [NeZero capacity]
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity)
    (test : (List (List Bool) × List (List (List Bool))) → ProbComp Bool) :
    (Game.succProbability (ProbComp.eval
      (E.publicKeyChainHybrid n (beforeCount + afterCount + 1) (beforeCount + 1) >>= test)) : ℝ) -
      Game.succProbability (ProbComp.eval
        (E.publicKeyChainHybrid n (beforeCount + afterCount + 1) beforeCount >>= test)) =
      (capacity : ℝ) *
        (Game.succProbability ((PMF.uniformOfFintype (Fin capacity)).bind
          (fun j => if j.val < width then ProbComp.eval
            (E.publicKeyLinkHybrid n beforeCount afterCount j.val >>= test) else PMF.pure false)) -
        Game.succProbability ((PMF.uniformOfFintype (Fin capacity)).bind
          (fun j => if j.val < width then ProbComp.eval
            (E.publicKeyLinkHybrid n beforeCount afterCount (j.val + 1) >>= test)
            else PMF.pure false))) := by
  have h := Game.succProbability_hybrid_average
    (fun j => ProbComp.eval (E.publicKeyLinkHybrid n beforeCount afterCount j >>= test))
    width capacity hcapacity
  simpa only [ProbComp.eval_bind, E.eval_publicKeyLinkHybrid_zero,
    E.eval_publicKeyLinkHybrid_length n beforeCount afterCount width hwidth] using h

/-- Average reverse link indices in `Fin depth` and forward bit indices in `Fin capacity` when
both ranges are positive; otherwise reject in both worlds. -/
noncomputable def exactKeyChainHybridGame (n depth width capacity : ℕ)
    (test : (List (List Bool) × List (List (List Bool))) → ProbComp Bool) (bit : Bool) : Game :=
  if h : 0 < depth ∧ 0 < capacity then
    have : NeZero depth := ⟨h.1.ne'⟩
    have : NeZero capacity := ⟨h.2.ne'⟩
    do
      let i ← PMF.uniformOfFintype (Fin depth)
      let j ← PMF.uniformOfFintype (Fin capacity)
      if j.val < width then
        ProbComp.eval (E.publicKeyLinkHybrid n (depth - i.val - 1) i.val
          (j.val + if bit then 1 else 0) >>= test)
      else pure false
  else pure false

/-- When all supported secrets have length zero, the real-link and zero-link hybrids coincide. -/
private theorem eval_publicKeyChainHybrid_of_width_zero (n depth : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = 0)
    (test : (List (List Bool) × List (List (List Bool))) → ProbComp Bool) :
    ProbComp.eval (E.publicKeyChainHybrid n depth depth >>= test) =
      ProbComp.eval (E.publicKeyChainHybrid n depth 0 >>= test) := by
  have hstep : ∀ k ≤ depth,
      ProbComp.eval (E.publicKeyChainHybrid n depth k >>= test) =
        ProbComp.eval (E.publicKeyChainHybrid n depth 0 >>= test) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk_lt : k < depth := Nat.lt_of_succ_le hk
      have hdepth_eq : k + (depth - k - 1) + 1 = depth := by omega
      have h0 := E.eval_publicKeyLinkHybrid_zero n k (depth - k - 1)
      have hlen := E.eval_publicKeyLinkHybrid_length n k (depth - k - 1) 0 hwidth
      rw [hdepth_eq] at h0 hlen
      have hlink : ProbComp.eval (E.publicKeyChainHybrid n depth (k + 1) >>= test) =
          ProbComp.eval (E.publicKeyChainHybrid n depth k >>= test) := by
        rw [ProbComp.eval_bind, ProbComp.eval_bind, ← h0, hlen]
      exact hlink.trans (ih hk_lt.le)
  exact hstep depth le_rfl

/-- The real-to-zero public-key gap equals `(depth : ℝ) * capacity` times the signed gap of
`exactKeyChainHybridGame`, with no dyadic rounding factor. -/
theorem publicKeyChainHybrid_exact_gap (n depth width capacity : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity)
    (test : (List (List Bool) × List (List (List Bool))) → ProbComp Bool) :
    (Game.succProbability (ProbComp.eval (E.publicKeyChainHybrid n depth depth >>= test)) : ℝ) -
      Game.succProbability (ProbComp.eval (E.publicKeyChainHybrid n depth 0 >>= test)) =
      (depth : ℝ) * capacity *
        (Game.succProbability (E.exactKeyChainHybridGame n depth width capacity test false) -
          Game.succProbability (E.exactKeyChainHybridGame n depth width capacity test true)) := by
  by_cases hpos : 0 < depth ∧ 0 < capacity
  · have : NeZero depth := ⟨hpos.1.ne'⟩
    have : NeZero capacity := ⟨hpos.2.ne'⟩
    let games := fun i => ProbComp.eval (E.publicKeyChainHybrid n depth (depth - i) >>= test)
    let original := fun i => (PMF.uniformOfFintype (Fin capacity)).bind
      (fun j => if j.val < width then ProbComp.eval
        (E.publicKeyLinkHybrid n (depth - i - 1) i j.val >>= test) else PMF.pure false)
    let replacement := fun i => (PMF.uniformOfFintype (Fin capacity)).bind
      (fun j => if j.val < width then ProbComp.eval
        (E.publicKeyLinkHybrid n (depth - i - 1) i (j.val + 1) >>= test) else PMF.pure false)
    have hstep (i : ℕ) (hi : i < depth) :
        (Game.succProbability (games i) : ℝ) - Game.succProbability (games (i + 1)) =
          (capacity : ℝ) *
            (Game.succProbability (original i) - Game.succProbability (replacement i)) := by
      have hdepth : depth - i - 1 + i + 1 = depth := by omega
      have hbefore : depth - i - 1 + 1 = depth - i := by omega
      have h := E.publicKeyLinkHybrid_exact_gap n (depth - i - 1) i width capacity
        hwidth hcapacity test
      rw [hdepth, hbefore] at h
      simpa only [games, original, replacement, Nat.sub_sub] using h
    have h := Game.succProbability_hybrid_reduction games original replacement
      depth depth le_rfl capacity hstep
    have hfin (g : ℕ → Game) :
        ((PMF.uniformOfFintype (Fin depth)).bind
          fun i : Fin depth => if i.val < depth then g i.val else PMF.pure false) =
        ((PMF.uniformOfFintype (Fin depth)).bind fun i : Fin depth => g i.val) := by
      congr 1; funext i
      simp only [i.isLt, ↓reduceIte]
    rw [hfin original, hfin replacement] at h
    have hfalse :
        E.exactKeyChainHybridGame n depth width capacity test false =
          (PMF.uniformOfFintype (Fin depth)).bind fun i : Fin depth => original i.val := by
      unfold exactKeyChainHybridGame
      rw [dite_eq_left_of_eq_true (eq_true hpos)]
      simp only [original, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    have htrue :
        E.exactKeyChainHybridGame n depth width capacity test true =
          (PMF.uniformOfFintype (Fin depth)).bind fun i : Fin depth => replacement i.val := by
      unfold exactKeyChainHybridGame
      rw [dite_eq_left_of_eq_true (eq_true hpos)]
      simp only [replacement, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ↓reduceIte]
    rw [hfalse, htrue]
    simpa only [games, Nat.sub_zero, Nat.sub_self] using h
  · have hfalse : E.exactKeyChainHybridGame n depth width capacity test false = pure false := by
      unfold exactKeyChainHybridGame
      exact dite_eq_right_of_eq_false (eq_false hpos)
    have htrue : E.exactKeyChainHybridGame n depth width capacity test true = pure false := by
      unfold exactKeyChainHybridGame
      exact dite_eq_right_of_eq_false (eq_false hpos)
    rw [hfalse, htrue, sub_self, mul_zero]
    rcases Nat.eq_zero_or_pos depth with rfl | hdepth
    · simp
    · have hcap0 : capacity = 0 := by omega
      have hwidth0 : width = 0 := by omega
      subst hwidth0
      rw [E.eval_publicKeyChainHybrid_of_width_zero n depth hwidth test, sub_self]

/-- Two-stage base IND-CPA reduction that samples the reverse link coordinate uniformly from
`Fin (depth n)` and the bit coordinate uniformly from `Fin (capacity n)` when both bounds are
positive, avoiding the factor-of-four dyadic rounding loss of `Scheme.linkAdversary`. No
strict-PPT certificate is proved for it; `modLinkAdversary` is the certified counterpart, and
`advantage_exactLinkAdversary_modLinkAdversary_le` compares the two. -/
noncomputable def exactLinkAdversary (depth capacity : ℕ → ℕ)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool) :
    Encryption.Adversary where
  choose n pk :=
    if h : 0 < depth n ∧ 0 < capacity n then
      have : NeZero (depth n) := ⟨h.1.ne'⟩
      have : NeZero (capacity n) := ⟨h.2.ne'⟩
      do
        let reverseIndex ← ProbComp.uniform (Fin (depth n))
        let bitIndex ← ProbComp.uniform (Fin (capacity n))
        E.chooseLinkAt n (depth n - reverseIndex.val - 1) reverseIndex.val bitIndex.val pk
    else pure rejectLinkChoice
  guess := E.guessLink test

/-- `exactLinkAdversary` realizes `exactKeyChainHybridGame` at each challenge bit. -/
theorem eval_exactLinkAdversary (depth capacity : ℕ → ℕ)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool)
    (n width : ℕ) (bit : Bool)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width) :
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (E.exactLinkAdversary depth capacity test) bit n) =
        E.exactKeyChainHybridGame n (depth n) width (capacity n) (test n) bit := by
  by_cases hpos : 0 < depth n ∧ 0 < capacity n
  · have : NeZero (depth n) := ⟨hpos.1.ne'⟩
    have : NeZero (capacity n) := ⟨hpos.2.ne'⟩
    dsimp only [Encryption.game, Encryption.gameOn, exactLinkAdversary, exactKeyChainHybridGame]
    simp only [dite_eq_left_of_eq_true (eq_true hpos), ↓reduceIte, bind_assoc, ProbComp.eval_bind,
      ProbComp.eval_uniform, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    rw [PMF.bind_comm]
    congr 1 with i : 1
    rw [PMF.bind_comm]
    congr 1 with j : 1
    simpa only [Encryption.game, Encryption.gameOn, ↓reduceIte,
      linkAdversaryAt, ProbComp.eval_bind, PMF.monad_pure_eq_pure] using
      E.eval_linkAdversaryAt (fun _ => depth n - i.val - 1) (fun _ => i.val)
        (fun _ => j.val) test n width bit hwidth
  · dsimp only [Encryption.game, Encryption.gameOn, exactLinkAdversary, exactKeyChainHybridGame]
    simp only [dite_eq_right_of_eq_false (eq_false hpos), ↓reduceIte, rejectLinkChoice,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, guessLink_reject, PMF.bind_const,
      PMF.monad_pure_eq_pure]

/-- Signed key-chain hybrid gap in terms of `exactLinkAdversary`, with exact factor
`(depth n : ℝ) * capacity n`. -/
theorem publicKeyChainHybrid_gap_exactLinkAdversary (depth capacity : ℕ → ℕ)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool)
    (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    (Game.succProbability (ProbComp.eval
      (E.publicKeyChainHybrid n (depth n) (depth n) >>= test n)) : ℝ) -
      Game.succProbability (ProbComp.eval
        (E.publicKeyChainHybrid n (depth n) 0 >>= test n)) =
      (depth n : ℝ) * capacity n *
        (Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (E.exactLinkAdversary depth capacity test) false n)) -
          Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
            (E.exactLinkAdversary depth capacity test) true n))) := by
  rw [E.eval_exactLinkAdversary depth capacity test n width false hwidth,
    E.eval_exactLinkAdversary depth capacity test n width true hwidth]
  exact E.publicKeyChainHybrid_exact_gap n (depth n) width (capacity n) hwidth hcapacity (test n)

/-- Unsigned key-chain hybrid advantage in terms of `exactLinkAdversary`, with exact factor
`(depth n : ℝ≥0) * capacity n` and no `dyadicSize` rounding. -/
theorem publicKeyChainHybrid_advantage_exactLinkAdversary (depth capacity : ℕ → ℕ)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool)
    (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    Game.advantage
      (ProbComp.eval (E.publicKeyChainHybrid n (depth n) (depth n) >>= test n))
      (ProbComp.eval (E.publicKeyChainHybrid n (depth n) 0 >>= test n)) =
      (depth n : ℝ≥0) * capacity n *
        Encryption.advantage (Encryption.game E.keyGen E.encrypt
          (E.exactLinkAdversary depth capacity test)) n := by
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_natCast,
    Game.coe_advantage, Game.coe_advantage,
    E.publicKeyChainHybrid_gap_exactLinkAdversary depth capacity test n width hwidth hcapacity,
    abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]

/-! ### Strict-PPT `sampleModNat` key-chain reduction and statistical-tail bound -/

/-- Replacing an exact uniform draw on `Fin M` by `ProbComp.sampleModNat width M` changes
`Game.advantage` of any Boolean continuation by at most `(M : ℝ≥0) / 2 ^ width`. -/
theorem advantage_bind_sampleModNat_fin_le (width M : ℕ) [NeZero M] (k : ℕ → Game) :
    Game.advantage
      ((ProbComp.eval (sampleModNat width M)).bind k)
      ((PMF.uniformOfFintype (Fin M)).bind fun i => k i.val) ≤
      (M : ℝ≥0) / 2 ^ width := by
  have hmod :
      (ProbComp.eval (sampleModNat width M)).bind k =
        ((ProbComp.eval (sampleModNat width M)).map (Nat.cast : ℕ → ZMod M)).bind
          (fun r : ZMod M => k r.val) := by
    rw [PMF.bind_map, eval_sampleModNat, PMF.bind_map, PMF.bind_map]
    congr 1 with x : 1
    simp only [Function.comp_def, ZMod.val_natCast,
      Nat.mod_eq_of_lt (Nat.mod_lt x.val (NeZero.pos M))]
  have hunif :
      ((PMF.uniformOfFintype (Fin M)).bind fun i => k i.val) =
        (PMF.uniformOfFintype (ZMod M)).bind (fun r : ZMod M => k r.val) := by
    rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne M) with ⟨m, rfl⟩
    rfl
  rw [← NNReal.coe_le_coe, hmod, hunif, Game.advantage_eq_nndist, coe_nndist]
  exact (PMF.dist_bind_le
    ((ProbComp.eval (sampleModNat width M)).map (Nat.cast : ℕ → ZMod M))
    (PMF.uniformOfFintype (ZMod M)) (fun r : ZMod M => k r.val)).trans
    (by simpa only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat] using
      ProbComp.dist_map_natCast_eval_sampleModNat_le width M)

/-- Replacing exact uniform draws on `Fin M` and then `Fin N` by two `sampleModNat width` draws
changes `Game.advantage` of any Boolean continuation by at most `(M + N) / 2 ^ width`. -/
private theorem advantage_bind_sampleModNat_fin_fin_le (width M N : ℕ) [NeZero M] [NeZero N]
    (k : ℕ → ℕ → Game) :
    Game.advantage
      ((ProbComp.eval (sampleModNat width M)).bind fun i =>
        (ProbComp.eval (sampleModNat width N)).bind fun j => k i j)
      ((PMF.uniformOfFintype (Fin M)).bind fun i =>
        (PMF.uniformOfFintype (Fin N)).bind fun j => k i.val j.val) ≤
      ((M + N : ℕ) : ℝ≥0) / 2 ^ width := by
  have hstep1 :
      Game.advantage
        ((ProbComp.eval (sampleModNat width M)).bind fun i =>
          (ProbComp.eval (sampleModNat width N)).bind fun j => k i j)
        ((PMF.uniformOfFintype (Fin M)).bind fun i =>
          (ProbComp.eval (sampleModNat width N)).bind fun j => k i.val j) ≤
        (M : ℝ≥0) / 2 ^ width :=
    advantage_bind_sampleModNat_fin_le width M _
  have hstep2 :
      Game.advantage
        ((PMF.uniformOfFintype (Fin M)).bind fun i =>
          (ProbComp.eval (sampleModNat width N)).bind fun j => k i.val j)
        ((PMF.uniformOfFintype (Fin M)).bind fun i =>
          (PMF.uniformOfFintype (Fin N)).bind fun j => k i.val j.val) ≤
        (N : ℝ≥0) / 2 ^ width :=
    Game.advantage_bind_le_nnreal _ _ _ fun i =>
      advantage_bind_sampleModNat_fin_le width N fun j => k i.val j
  refine (Game.advantage_triangle _ _ _).trans ((add_le_add hstep1 hstep2).trans_eq ?_)
  push_cast
  ring

/-- Sample a modular residue via `ProbComp.sampleModNat width bound`, capped at `bound` so its
unary encoding is polynomially bounded even when `bound = 0`. When `0 < bound`, every residue modulo
`bound` is strictly below `bound`, so `sampleModIndex width bound = sampleModNat width bound`. -/
noncomputable def sampleModIndex (width bound : ℕ) : ProbComp ℕ :=
  min bound <$> sampleModNat width bound

/-- When `0 < bound`, `sampleModIndex width bound` equals `sampleModNat width bound`. -/
@[simp] theorem sampleModIndex_eq_sampleModNat (width : ℕ) {bound : ℕ} (hbound : 0 < bound) :
    sampleModIndex width bound = sampleModNat width bound := by
  simp only [sampleModIndex, sampleModNat, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  congr 1; funext x
  rw [Nat.min_eq_right (Nat.mod_lt x hbound).le]

/-- Sampling a modular index with unary bit width and unary modulus is uniformly strict PPT with
unary output. -/
@[program_certificate]
theorem isPPTOn_sampleModIndex {α : Type} {input : α ↪ List Bool}
    {width bound : α → ℕ}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hbound : ComputableInPolyTime bound input encUnary) :
    IsPPTOn input encUnary (fun a => sampleModIndex (width a) (bound a)) := by
  have hmod := isPPTOn_sampleModNat hwidth (ComputableInPolyTime.unary_to_binary.comp hbound)
  have hmin : ComputableInPolyTime (fun p : α × ℕ => min (bound p.1) p.2)
      (encPair input encNat) encUnary :=
    ComputableInPolyTime.binary_min_unary'
      (hbound.comp (ComputableInPolyTime.fst input encNat))
      (ComputableInPolyTime.snd input encNat)
  exact hmod.map_with hmin

/-- Strict-PPT two-stage key-chain reduction that samples the reverse link index via
`sampleModIndex (coins n) (depth n)` and the bit index via
`sampleModIndex (coins n) (capacity n)` (which equal `ProbComp.sampleModNat` whenever
`0 < depth n` and `0 < capacity n`). -/
noncomputable def modLinkAdversary (coins depth capacity : ℕ → ℕ)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool) :
    Encryption.Adversary where
  choose n pk := do
    let reverseIndex ← sampleModIndex (coins n) (depth n)
    let bitIndex ← sampleModIndex (coins n) (capacity n)
    if reverseIndex < depth n then
      if bitIndex < capacity n then
        E.chooseLinkAt n (depth n - reverseIndex - 1) reverseIndex bitIndex pk
      else pure rejectLinkChoice
    else pure rejectLinkChoice
  guess := E.guessLink test

/-- `modLinkAdversary` is uniform strict PPT whenever the coin count, depth, and capacity are
computable in polynomial time in unary. -/
theorem isPPT_modLinkAdversary {E : Scheme}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun (n, pk, bit) => E.encrypt n pk bit))
    {test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool}
    (htest : IsPPTOn
      (encPair encUnary (encPair (encList encBits) (encList (encList encBits)))) encBool
      (fun (n, artifact) => test n artifact))
    {coins depth capacity : ℕ → ℕ}
    (hcoins : ComputableInPolyTime coins encUnary encUnary)
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary) :
    (E.modLinkAdversary coins depth capacity test).IsPPT := by
  constructor
  · change IsPPTOn (encPair encUnary encBits) (encPair (encPair encBool encBool) encBits)
      (fun p => (E.modLinkAdversary coins depth capacity test).choose p.1 p.2)
    have hchoose : IsPPTOn
        (encPair (encPair (encPair encUnary encBits) encUnary) encUnary)
        (encPair (encPair encBool encBool) encBits)
        (fun p : ((ℕ × List Bool) × ℕ) × ℕ => E.chooseLinkAt p.1.1.1
          (depth p.1.1.1 - p.1.2 - 1) p.1.2 p.2 p.1.1.2) := by
      apply isPPTOn_chooseLinkAt hkeyGen <;> fun_prop
    dsimp only [modLinkAdversary]
    ppt
  · exact isPPTOn_guessLink hencrypt htest (by fun_prop) (by fun_prop) (by fun_prop)

private noncomputable def linkRunAt
    (depth capacity : ℕ → ℕ)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool)
    (bit : Bool) (n i j : ℕ) : Game :=
  if i < depth n then
    if j < capacity n then
      ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (E.linkAdversaryAt (fun _ => depth n - i - 1) (fun _ => i) (fun _ => j) test) bit n)
    else PMF.pure false
  else PMF.pure false

/-- In each challenge world `bit`, the encryption game of `modLinkAdversary` is within
`((depth n + capacity n : ℕ) : ℝ≥0) / 2 ^ (coins n)` of `exactLinkAdversary`. -/
theorem advantage_exactLinkAdversary_modLinkAdversary_le
    (coins depth capacity : ℕ → ℕ)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool)
    (bit : Bool) (n : ℕ) :
    Game.advantage
      (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (E.exactLinkAdversary depth capacity test) bit n))
      (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (E.modLinkAdversary coins depth capacity test) bit n)) ≤
      ((depth n + capacity n : ℕ) : ℝ≥0) / 2 ^ (coins n) := by
  have hmod :
      ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (E.modLinkAdversary coins depth capacity test) bit n) =
      (ProbComp.eval (sampleModIndex (coins n) (depth n))).bind fun i =>
        (ProbComp.eval (sampleModIndex (coins n) (capacity n))).bind fun j =>
          E.linkRunAt depth capacity test bit n i j := by
    dsimp only [Encryption.game, Encryption.gameOn, modLinkAdversary, linkRunAt, linkAdversaryAt]
    simp only [↓reduceIte, bind_assoc, ProbComp.eval_bind]
    rw [PMF.bind_comm]
    congr 1; funext i
    rw [PMF.bind_comm]
    congr 1; funext j
    by_cases hi : i < depth n
    · by_cases hj : j < capacity n
      · simp only [hi, hj, ↓reduceIte]
      · simp only [hi, hj, ↓reduceIte, rejectLinkChoice, ProbComp.eval_pure,
          PMF.pure_bind, guessLink_reject, PMF.bind_const]
    · simp only [hi, ↓reduceIte, rejectLinkChoice, ProbComp.eval_pure,
        PMF.pure_bind, guessLink_reject, PMF.bind_const]
  by_cases hpos : 0 < depth n ∧ 0 < capacity n
  · have : NeZero (depth n) := ⟨hpos.1.ne'⟩
    have : NeZero (capacity n) := ⟨hpos.2.ne'⟩
    rw [sampleModIndex_eq_sampleModNat (coins n) hpos.1,
      sampleModIndex_eq_sampleModNat (coins n) hpos.2] at hmod
    have hexact :
        ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (E.exactLinkAdversary depth capacity test) bit n) =
        (PMF.uniformOfFintype (Fin (depth n))).bind fun i =>
          (PMF.uniformOfFintype (Fin (capacity n))).bind fun j =>
            E.linkRunAt depth capacity test bit n i.val j.val := by
      dsimp only [Encryption.game, Encryption.gameOn, exactLinkAdversary, linkRunAt,
        linkAdversaryAt]
      simp only [dite_eq_left_of_eq_true (eq_true hpos), ↓reduceIte, bind_assoc,
        ProbComp.eval_bind, ProbComp.eval_uniform]
      rw [PMF.bind_comm]
      congr 1; funext i
      rw [PMF.bind_comm]
      congr 1; funext j
      simp only [i.isLt, j.isLt, ↓reduceIte]
    rw [hexact, hmod, Game.advantage_comm]
    exact advantage_bind_sampleModNat_fin_fin_le (coins n) (depth n) (capacity n)
      (E.linkRunAt depth capacity test bit n)
  · have hrun_reject (i : ℕ) (hi : i ≤ depth n) (j : ℕ) (hj : j ≤ capacity n) :
        E.linkRunAt depth capacity test bit n i j = PMF.pure false := by
      dsimp only [linkRunAt]
      by_cases hi_lt : i < depth n
      · have hj_not : ¬ j < capacity n := by omega
        simp only [hi_lt, hj_not, ↓reduceIte]
      · simp only [hi_lt, ↓reduceIte]
    have hmod_false :
        ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (E.modLinkAdversary coins depth capacity test) bit n) = PMF.pure false := by
      rw [hmod]
      have hinner (i : ℕ) (hi : i ≤ depth n) :
          ((ProbComp.eval (sampleModIndex (coins n) (capacity n))).bind fun j =>
            E.linkRunAt depth capacity test bit n i j) = PMF.pure false := by
        rw [← PMF.bind_const (ProbComp.eval (sampleModIndex (coins n) (capacity n)))
          (PMF.pure false)]
        apply Probability.PMF.bind_congr_on_support
        intro j hj
        simp only [sampleModIndex, ProbComp.eval_map, PMF.mem_support_map_iff] at hj
        rcases hj with ⟨x, _, rfl⟩
        exact hrun_reject i hi (min (capacity n) x) (Nat.min_le_left _ _)
      rw [← PMF.bind_const (ProbComp.eval (sampleModIndex (coins n) (depth n))) (PMF.pure false)]
      apply Probability.PMF.bind_congr_on_support
      intro i hi
      simp only [sampleModIndex, ProbComp.eval_map, PMF.mem_support_map_iff] at hi
      rcases hi with ⟨x, _, rfl⟩
      exact hinner (min (depth n) x) (Nat.min_le_left _ _)
    have hexact_false :
        ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (E.exactLinkAdversary depth capacity test) bit n) = PMF.pure false := by
      dsimp only [Encryption.game, Encryption.gameOn, exactLinkAdversary]
      simp only [dite_eq_right_of_eq_false (eq_false hpos), ↓reduceIte, rejectLinkChoice,
        ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, guessLink_reject, PMF.bind_const]
    rw [hexact_false, hmod_false, Game.advantage_self]
    exact zero_le

theorem advantage_le_of_triangle_both_div {g₀ g₁ m₀ m₁ : Game} {a b : ℝ≥0}
    (h₀ : Game.advantage g₀ m₀ ≤ a / b) (h₁ : Game.advantage g₁ m₁ ≤ a / b) :
    Game.advantage g₀ g₁ ≤ Game.advantage m₀ m₁ + 2 * a / b := by
  have htri1 := Game.advantage_triangle g₀ m₀ g₁
  have htri2 := Game.advantage_triangle m₀ m₁ g₁
  rw [Game.advantage_comm m₁ g₁] at htri2
  have hstep : Game.advantage m₀ g₁ ≤ Game.advantage m₀ m₁ + a / b :=
    htri2.trans (add_le_add_right h₁ _)
  have hstep2 : Game.advantage g₀ g₁ ≤ a / b + (Game.advantage m₀ m₁ + a / b) :=
    htri1.trans (add_le_add h₀ hstep)
  exact hstep2.trans_eq (by ring)

/-- Concrete key-chain hybrid advantage bound via the strict-PPT `modLinkAdversary` reduction:
the key-chain advantage is at most `(depth n : ℝ≥0) * capacity n` times the sum of
`modLinkAdversary`'s base advantage and the modular-sampling statistical tail
`2 * (depth n + capacity n) / 2 ^ (coins n)`. -/
theorem publicKeyChainHybrid_advantage_le_modLinkAdversary
    (coins depth capacity : ℕ → ℕ)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool)
    (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    Game.advantage
      (ProbComp.eval (E.publicKeyChainHybrid n (depth n) (depth n) >>= test n))
      (ProbComp.eval (E.publicKeyChainHybrid n (depth n) 0 >>= test n)) ≤
    (depth n : ℝ≥0) * capacity n *
      (Encryption.advantage (Encryption.game E.keyGen E.encrypt
        (E.modLinkAdversary coins depth capacity test)) n +
        2 * ((depth n + capacity n : ℕ) : ℝ≥0) / 2 ^ (coins n)) := by
  rw [E.publicKeyChainHybrid_advantage_exactLinkAdversary depth capacity test n width
    hwidth hcapacity]
  exact mul_le_mul_of_nonneg_left
    (advantage_le_of_triangle_both_div
      (E.advantage_exactLinkAdversary_modLinkAdversary_le coins depth capacity test false n)
      (E.advantage_exactLinkAdversary_modLinkAdversary_le coins depth capacity test true n))
    zero_le

/-! ### Explicit bit-length bound for active saved link states -/

/-- Upper bound on the bit length of `activeLinkState before predecessor challengePk after bitIndex`
when `before.length + after.length + 1 = depth`, every key pair `(pk, sk)` has
`pk.length ≤ pkBound` and `sk.length ≤ width`, `challengePk.length ≤ pkBound`, and
`bitIndex ≤ width`. -/
def linkStateLengthBound (depth width pkBound : ℕ) : ℕ :=
  let keyPairLen := 2 * pkBound + 1 + width
  3 + 4 * ((depth - 1) * (2 * keyPairLen + 1) + 1) + 4 * keyPairLen + 2 * pkBound + width

/-- Every active reduction state `activeLinkState before predecessor challengePk after bitIndex`
with `before.length + after.length + 1 ≤ depth`, base keys bounded by `(pkBound, width)`, and
`bitIndex ≤ width` has encoded bit length at most `linkStateLengthBound depth width pkBound`. -/
theorem length_activeLinkState_le (depth width pkBound : ℕ)
    (before : List (List Bool × List Bool)) (predecessor : List Bool × List Bool)
    (challengePk : List Bool) (after : List (List Bool × List Bool)) (bitIndex : ℕ)
    (hcount : before.length + after.length + 1 ≤ depth)
    (hbefore : ∀ k ∈ before, k.1.length ≤ pkBound ∧ k.2.length ≤ width)
    (hpred : predecessor.1.length ≤ pkBound ∧ predecessor.2.length ≤ width)
    (hpk : challengePk.length ≤ pkBound)
    (hafter : ∀ k ∈ after, k.1.length ≤ pkBound ∧ k.2.length ≤ width)
    (hbit : bitIndex ≤ width) :
    (activeLinkState before predecessor challengePk after bitIndex).length ≤
      linkStateLengthBound depth width pkBound := by
  let keyPairLen := 2 * pkBound + 1 + width
  have hpair (k : List Bool × List Bool) (hk : k.1.length ≤ pkBound ∧ k.2.length ≤ width) :
      (encPair encBits encBits k).length ≤ keyPairLen := by
    simp only [length_encPair, encBits_apply, keyPairLen]
    omega
  have hbefore_len :
      (encList (encPair encBits encBits) before).length ≤
        before.length * (2 * keyPairLen + 1) :=
    Turing.MultiTapeTM.length_encList_le _ before fun k hk => hpair k (hbefore k hk)
  have hafter_len :
      (encList (encPair encBits encBits) after).length ≤
        after.length * (2 * keyPairLen + 1) :=
    Turing.MultiTapeTM.length_encList_le _ after fun k hk => hpair k (hafter k hk)
  have hsum_lists :
      before.length * (2 * keyPairLen + 1) + after.length * (2 * keyPairLen + 1) ≤
        (depth - 1) * (2 * keyPairLen + 1) := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  dsimp only [keyPairLen] at hbefore_len hafter_len hsum_lists
  obtain ⟨hpred1, hpred2⟩ := hpred
  simp only [activeLinkState, encLinkState, length_encPair, encBool_apply, List.length_singleton,
    encBits_apply, encUnary_apply, List.length_replicate, linkStateLengthBound]
  linarith

end Cslib.Crypto.Homomorphic.Scheme

namespace Cslib.Crypto.Homomorphic.Leveled

open ProbComp Probability Turing.MultiTapeTM
open scoped NNReal Cslib.Probability.PMF

/-! ### Exact uniform-index leveled reduction and three-hop decomposition -/

/-- Unattenuated three-hop concrete-security bound for the leveled scheme `scheme D budget`:
its IND-CPA advantage is bounded by the sum of the two `exactLinkAdversary` advantages (each
scaled by the exact hybrid count `(2 * budget n) * capacity n`) and the `zeroLinkAdversary`
advantage, with no dyadic rounding factor. -/
theorem advantage_scheme_le_exactLinkAdversary_add_zeroLinkAdversary {E : Scheme}
    {secretWidth ciphertextWidth : ℕ → ℕ}
    (D : DecryptionCircuits E secretWidth ciphertextWidth)
    (budget capacity : ℕ → ℕ) (adversary : Encryption.Adversary) (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    Encryption.advantage (Encryption.game (scheme D budget).keyGen (scheme D budget).encrypt
      adversary) n ≤
    (2 * budget n : ℝ≥0) * capacity n *
      Encryption.advantage (Encryption.game E.keyGen E.encrypt
        (E.exactLinkAdversary (fun n => 2 * budget n) capacity
          (publicKeyGame E adversary false))) n +
    Encryption.advantage (Encryption.game E.keyGen E.encrypt
      (zeroLinkAdversary E (fun n => 2 * budget n) adversary)) n +
    (2 * budget n : ℝ≥0) * capacity n *
      Encryption.advantage (Encryption.game E.keyGen E.encrypt
        (E.exactLinkAdversary (fun n => 2 * budget n) capacity
          (publicKeyGame E adversary true))) n := by
  dsimp only [scheme]
  rw [Encryption.advantage, eval_game_keyGen E budget adversary false n,
    eval_game_keyGen E budget adversary true n]
  have h1 := E.publicKeyChainHybrid_advantage_exactLinkAdversary (fun n => 2 * budget n) capacity
    (publicKeyGame E adversary false) n width hwidth hcapacity
  have h2 := E.publicKeyChainHybrid_advantage_exactLinkAdversary (fun n => 2 * budget n) capacity
    (publicKeyGame E adversary true) n width hwidth hcapacity
  have hzFalse := eval_zeroLinkAdversary E (fun n => 2 * budget n) adversary false n width hwidth
  have hzTrue := eval_zeroLinkAdversary E (fun n => 2 * budget n) adversary true n width hwidth
  have htri1 := Game.advantage_triangle
    (ProbComp.eval (E.publicKeyChainHybrid n (2 * budget n) (2 * budget n) >>=
      publicKeyGame E adversary false n))
    (ProbComp.eval (E.publicKeyChainHybrid n (2 * budget n) 0 >>=
      publicKeyGame E adversary false n))
    (ProbComp.eval (E.publicKeyChainHybrid n (2 * budget n) (2 * budget n) >>=
      publicKeyGame E adversary true n))
  have htri2 := Game.advantage_triangle
    (ProbComp.eval (E.publicKeyChainHybrid n (2 * budget n) 0 >>=
      publicKeyGame E adversary false n))
    (ProbComp.eval (E.publicKeyChainHybrid n (2 * budget n) 0 >>=
      publicKeyGame E adversary true n))
    (ProbComp.eval (E.publicKeyChainHybrid n (2 * budget n) (2 * budget n) >>=
      publicKeyGame E adversary true n))
  rw [Game.advantage_comm
    (ProbComp.eval (E.publicKeyChainHybrid n (2 * budget n) 0 >>=
      publicKeyGame E adversary true n))] at htri2
  have hcast : ((2 * budget n : ℕ) : ℝ≥0) = 2 * budget n := by push_cast; rfl
  rw [hcast] at h1 h2
  rw [h1, ← hzFalse] at htri1
  rw [h2, ← hzFalse, ← hzTrue] at htri2
  exact (htri1.trans (add_le_add_right htri2 _)).trans_eq (add_assoc _ _ _).symm

/-- Unified two-stage base IND-CPA reduction for the leveled construction that samples the hop
selector uniformly from `Fin 3`, the reverse link coordinate uniformly from `Fin (depth n)`, and
the secret-bit coordinate uniformly from `Fin (capacity n)` when `0 < depth n ∧ 0 < capacity n`,
eliminating the `dyadicSize` rounding factor of `leveledAdversary`. No strict-PPT certificate is
proved for it; `modLeveledAdversary` is the certified counterpart, and
`advantage_exactLeveledAdversary_modLeveledAdversary_le` compares the two. -/
noncomputable def exactLeveledAdversary (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) : Encryption.Adversary where
  choose n challengePk :=
    if h : 0 < depth n ∧ 0 < capacity n then
      have : NeZero (depth n) := ⟨h.1.ne'⟩
      have : NeZero (capacity n) := ⟨h.2.ne'⟩
      do
        let hop ← ProbComp.uniform (Fin 3)
        if hop.val = 0 then
          tagLeveledChoice false false <$>
            (E.exactLinkAdversary depth capacity (publicKeyGame E adversary false)).choose n
              challengePk
        else if hop.val = 1 then
          (tagLeveledChoice false true ∘ swapLeveledChoice) <$>
            (E.exactLinkAdversary depth capacity (publicKeyGame E adversary true)).choose n
              challengePk
        else
          let reverseIndex ← ProbComp.uniform (Fin (depth n))
          let bitIndex ← ProbComp.uniform (Fin (capacity n))
          if reverseIndex.val = 0 then
            if bitIndex.val = 0 then
              tagLeveledChoice true false <$>
                (zeroLinkAdversary E depth adversary).choose n challengePk
            else pure rejectLeveledChoice
          else pure rejectLeveledChoice
    else
      tagLeveledChoice true false <$>
        (zeroLinkAdversary E depth adversary).choose n challengePk
  guess := (leveledAdversary E depth capacity adversary).guess

private theorem eval_exactLeveled_hop_zero (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (do
      let keys ← E.keyGen n
      let choice ← tagLeveledChoice false false <$>
        (E.exactLinkAdversary depth capacity (publicKeyGame E adversary false)).choose n keys.1
      let ciphertext ← E.encrypt n keys.1 (if bit then choice.1.2 else choice.1.1)
      (leveledAdversary E depth capacity adversary).guess n choice.2 ciphertext) =
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (E.exactLinkAdversary depth capacity (publicKeyGame E adversary false)) bit n) := by
  simp [Encryption.game, Encryption.gameOn, leveledAdversary, Scheme.exactLinkAdversary,
    Scheme.linkAdversary, tagLeveledChoice, ProbComp.eval_bind, Function.comp_def]

private theorem eval_exactLeveled_hop_one (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (do
      let keys ← E.keyGen n
      let choice ← (tagLeveledChoice false true ∘ swapLeveledChoice) <$>
        (E.exactLinkAdversary depth capacity (publicKeyGame E adversary true)).choose n keys.1
      let ciphertext ← E.encrypt n keys.1 (if bit then choice.1.2 else choice.1.1)
      (leveledAdversary E depth capacity adversary).guess n choice.2 ciphertext) =
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (E.exactLinkAdversary depth capacity (publicKeyGame E adversary true)) (!bit) n) := by
  cases bit <;> simp [Encryption.game, Encryption.gameOn, leveledAdversary,
    Scheme.exactLinkAdversary, Scheme.linkAdversary, tagLeveledChoice, swapLeveledChoice,
    ProbComp.eval_bind, Function.comp_def]

private theorem eval_modLeveled_hop_zero (E : Scheme) (coins depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (do
      let keys ← E.keyGen n
      let choice ← tagLeveledChoice false false <$>
        (E.modLinkAdversary coins depth capacity (publicKeyGame E adversary false)).choose n keys.1
      let ciphertext ← E.encrypt n keys.1 (if bit then choice.1.2 else choice.1.1)
      (leveledAdversary E depth capacity adversary).guess n choice.2 ciphertext) =
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (E.modLinkAdversary coins depth capacity (publicKeyGame E adversary false)) bit n) := by
  simp [Encryption.game, Encryption.gameOn, leveledAdversary, Scheme.modLinkAdversary,
    Scheme.linkAdversary, tagLeveledChoice, ProbComp.eval_bind, Function.comp_def]

private theorem eval_modLeveled_hop_one (E : Scheme) (coins depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (do
      let keys ← E.keyGen n
      let choice ← (tagLeveledChoice false true ∘ swapLeveledChoice) <$>
        (E.modLinkAdversary coins depth capacity (publicKeyGame E adversary true)).choose n keys.1
      let ciphertext ← E.encrypt n keys.1 (if bit then choice.1.2 else choice.1.1)
      (leveledAdversary E depth capacity adversary).guess n choice.2 ciphertext) =
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (E.modLinkAdversary coins depth capacity (publicKeyGame E adversary true)) (!bit) n) := by
  cases bit <;> simp [Encryption.game, Encryption.gameOn, leveledAdversary,
    Scheme.modLinkAdversary, Scheme.linkAdversary, tagLeveledChoice, swapLeveledChoice,
    ProbComp.eval_bind, Function.comp_def]

private theorem eval_leveled_hop_two (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n i j : ℕ) :
    ProbComp.eval (do
      let keys ← E.keyGen n
      let choice ←
        (if i = 0 then
          if j = 0 then
            tagLeveledChoice true false <$>
              (zeroLinkAdversary E depth adversary).choose n keys.1
          else pure rejectLeveledChoice
        else pure rejectLeveledChoice : ProbComp ((Bool × Bool) × List Bool))
      let ciphertext ← E.encrypt n keys.1 (if bit then choice.1.2 else choice.1.1)
      (leveledAdversary E depth capacity adversary).guess n choice.2 ciphertext) =
    if i = 0 then
      if j = 0 then
        ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (zeroLinkAdversary E depth adversary) bit n)
      else PMF.pure false
    else PMF.pure false := by
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · simp [Encryption.game, Encryption.gameOn, hi, hj, leveledAdversary, tagLeveledChoice,
        ProbComp.eval_bind, Function.comp_def]
    · simp only [hi, hj, ↓reduceIte, leveledAdversary, rejectLeveledChoice, List.headD_cons,
        List.tail_cons, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, PMF.bind_const]
  · simp only [hi, ↓reduceIte, leveledAdversary, rejectLeveledChoice, List.headD_cons,
      List.tail_cons, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, PMF.bind_const]

/-- Exact distributional decomposition of `exactLeveledAdversary` when `0 < depth n` and
`0 < capacity n`. -/
theorem eval_exactLeveledAdversary (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ)
    [NeZero (depth n)] [NeZero (capacity n)] :
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (exactLeveledAdversary E depth capacity adversary) bit n) =
    (PMF.uniformOfFintype (Fin 3)).bind fun hop =>
      if hop.val = 0 then
        ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (E.exactLinkAdversary depth capacity (publicKeyGame E adversary false)) bit n)
      else if hop.val = 1 then
        ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (E.exactLinkAdversary depth capacity (publicKeyGame E adversary true)) (!bit) n)
      else
        (PMF.uniformOfFintype (Fin (depth n))).bind fun i =>
          (PMF.uniformOfFintype (Fin (capacity n))).bind fun j =>
            if i.val = 0 then
              if j.val = 0 then
                ProbComp.eval (Encryption.game E.keyGen E.encrypt
                  (zeroLinkAdversary E depth adversary) bit n)
              else PMF.pure false
            else PMF.pure false := by
  have hpos : 0 < depth n ∧ 0 < capacity n := ⟨NeZero.pos (depth n), NeZero.pos (capacity n)⟩
  dsimp only [Encryption.game, Encryption.gameOn, exactLeveledAdversary]
  simp only [dite_eq_left_of_eq_true (eq_true hpos), ↓reduceIte, bind_assoc, ProbComp.eval_bind,
    ProbComp.eval_uniform]
  rw [PMF.bind_comm]
  congr 1 with hop : 1
  by_cases h0 : hop.val = 0
  · simp only [h0, ↓reduceIte]
    simpa only [Encryption.game, Encryption.gameOn, ↓reduceIte, ProbComp.eval_bind] using
      eval_exactLeveled_hop_zero E depth capacity adversary bit n
  · by_cases h1 : hop.val = 1
    · simp only [h1, one_ne_zero, ↓reduceIte]
      simpa only [Encryption.game, Encryption.gameOn, ↓reduceIte, ProbComp.eval_bind] using
        eval_exactLeveled_hop_one E depth capacity adversary bit n
    · simp only [h0, h1, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_uniform, PMF.bind_bind]
      rw [PMF.bind_comm]
      congr 1; funext i
      rw [PMF.bind_comm]
      congr 1; funext j
      simpa only [Encryption.game, Encryption.gameOn, ↓reduceIte, ProbComp.eval_bind] using
        eval_leveled_hop_two E depth capacity adversary bit n i.val j.val

private theorem succProbability_uniform_fin_zero (M : ℕ) [NeZero M] (game : Game) :
    (M : ℝ) *
      Game.succProbability ((PMF.uniformOfFintype (Fin M)).bind fun i : Fin M =>
        if i.val = 0 then game else PMF.pure false) =
      Game.succProbability game := by
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have h0 : 0 < M := NeZero.pos M
  let z : Fin M := ⟨0, h0⟩
  have hiff (i : Fin M) : i.val = 0 ↔ i = z := by
    constructor
    · intro hi; ext; exact hi
    · intro hi; subst hi; rfl
  rw [Game.succProbability_uniform]
  simp only [NNReal.coe_div, NNReal.coe_sum, NNReal.coe_natCast, Fintype.card_fin, hiff]
  have hsum :
      (∑ a : Fin M, (Game.succProbability (if a = z then game else PMF.pure false) : ℝ)) =
        Game.succProbability game := by
    rw [Finset.sum_eq_single z]
    · simp
    · intro b _ hb
      simp [hb, Game.succProbability]
    · intro hz
      exact False.elim (hz (Finset.mem_univ z))
  rw [hsum, mul_div_cancel₀ _ hM]

/-- Scaled acceptance probability of `exactLeveledAdversary` when `0 < depth n` and
`0 < capacity n`. -/
theorem succProbability_exactLeveledAdversary (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ)
    (hdepth : 0 < depth n) (hcapacity_pos : 0 < capacity n) :
    3 * (depth n : ℝ) * capacity n *
      Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (exactLeveledAdversary E depth capacity adversary) bit n)) =
    (depth n : ℝ) * capacity n *
      Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (E.exactLinkAdversary depth capacity (publicKeyGame E adversary false)) bit n)) +
    (depth n : ℝ) * capacity n *
      Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (E.exactLinkAdversary depth capacity (publicKeyGame E adversary true)) (!bit) n)) +
    Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (zeroLinkAdversary E depth adversary) bit n)) := by
  have : NeZero (depth n) := ⟨hdepth.ne'⟩
  have : NeZero (capacity n) := ⟨hcapacity_pos.ne'⟩
  rw [eval_exactLeveledAdversary E depth capacity adversary bit n,
    Game.succProbability_uniform]
  simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_ofNat,
    Fintype.card_fin, Nat.cast_ofNat, Fin.sum_univ_three, Fin.isValue, Fin.val_zero, ↓reduceIte,
    Fin.val_one, one_ne_zero, Fin.val_two, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
  have hite (i : Fin (depth n)) :
      ((PMF.uniformOfFintype (Fin (capacity n))).bind fun j : Fin (capacity n) =>
        if i.val = 0 then
          if j.val = 0 then
            ProbComp.eval (Encryption.game E.keyGen E.encrypt
              (zeroLinkAdversary E depth adversary) bit n)
          else PMF.pure false
        else PMF.pure false) =
      if i.val = 0 then
        (PMF.uniformOfFintype (Fin (capacity n))).bind fun j : Fin (capacity n) =>
          if j.val = 0 then
            ProbComp.eval (Encryption.game E.keyGen E.encrypt
              (zeroLinkAdversary E depth adversary) bit n)
          else PMF.pure false
      else PMF.pure false := by
    by_cases hi : i.val = 0 <;> simp [hi, PMF.bind_const]
  simp_rw [hite]
  have hlink := succProbability_uniform_fin_zero (depth n)
    ((PMF.uniformOfFintype (Fin (capacity n))).bind fun j : Fin (capacity n) =>
      if j.val = 0 then
        ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (zeroLinkAdversary E depth adversary) bit n)
      else PMF.pure false)
  have hbit := succProbability_uniform_fin_zero (capacity n)
    (ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (zeroLinkAdversary E depth adversary) bit n))
  have hprod :
      (depth n : ℝ) * capacity n *
        Game.succProbability ((PMF.uniformOfFintype (Fin (depth n))).bind fun i : Fin (depth n) =>
          if i.val = 0 then
            (PMF.uniformOfFintype (Fin (capacity n))).bind fun j : Fin (capacity n) =>
              if j.val = 0 then
                ProbComp.eval (Encryption.game E.keyGen E.encrypt
                  (zeroLinkAdversary E depth adversary) bit n)
              else PMF.pure false
          else PMF.pure false) =
      Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (zeroLinkAdversary E depth adversary) bit n)) := by
    linear_combination (capacity n : ℝ) * hlink + hbit
  linarith

/-- Signed chosen-message gap of the leveled scheme in terms of `exactLeveledAdversary` when
`0 < budget n` and `0 < capacity n`, with exact factor `3 * (2 * budget n : ℝ) * capacity n`
([Gentry2009], Section 2, Theorem 4, p. 171, up to a constant factor in the loss;
the running-time clause is not formalized). -/
theorem gap_exactLeveledAdversary (E : Scheme) (budget capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (n width : ℕ)
    (hbudget_pos : 0 < budget n) (hcapacity_pos : 0 < capacity n)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    (Game.succProbability (ProbComp.eval
      (Encryption.game (fun n => keyGen E n (budget n)) (encrypt E) adversary false n)) : ℝ) -
      Game.succProbability (ProbComp.eval
        (Encryption.game (fun n => keyGen E n (budget n)) (encrypt E) adversary true n)) =
    3 * (2 * budget n : ℝ) * capacity n *
      (Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (exactLeveledAdversary E (fun n => 2 * budget n) capacity adversary) false n)) -
        Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (exactLeveledAdversary E (fun n => 2 * budget n) capacity adversary) true n))) := by
  have hdepth_pos : 0 < 2 * budget n := by omega
  rw [eval_game_keyGen E budget adversary false n, eval_game_keyGen E budget adversary true n]
  have hlinkFalse := E.publicKeyChainHybrid_gap_exactLinkAdversary (fun n => 2 * budget n) capacity
    (publicKeyGame E adversary false) n width hwidth hcapacity
  have hlinkTrue := E.publicKeyChainHybrid_gap_exactLinkAdversary (fun n => 2 * budget n) capacity
    (publicKeyGame E adversary true) n width hwidth hcapacity
  have hzeroFalse := eval_zeroLinkAdversary E (fun n => 2 * budget n) adversary false n width hwidth
  have hzeroTrue := eval_zeroLinkAdversary E (fun n => 2 * budget n) adversary true n width hwidth
  have hlevFalse := succProbability_exactLeveledAdversary E (fun n => 2 * budget n) capacity
    adversary false n hdepth_pos hcapacity_pos
  have hlevTrue := succProbability_exactLeveledAdversary E (fun n => 2 * budget n) capacity
    adversary true n hdepth_pos hcapacity_pos
  simp only [Bool.not_false, Bool.not_true, hzeroFalse, hzeroTrue, Nat.cast_mul,
    Nat.cast_ofNat] at hlevFalse hlevTrue hlinkFalse hlinkTrue
  linarith

/-- Exact unsigned concrete-security identity for the depth-budgeted scheme `scheme D budget` via
`exactLeveledAdversary` ([Gentry2009], Section 2, Theorem 4, p. 171, up to a constant factor in
the loss; the running-time clause is not formalized): when `0 < budget n` and `0 < capacity n`,
the advantage equals `3 * (2 * budget n : ℝ≥0) * capacity n` times the base advantage of
`exactLeveledAdversary`, eliminating the `dyadicSize` rounding factor of
`advantage_scheme_eq_leveledAdversary`. -/
theorem advantage_scheme_eq_exactLeveledAdversary {E : Scheme}
    {secretWidth ciphertextWidth : ℕ → ℕ}
    (D : DecryptionCircuits E secretWidth ciphertextWidth)
    (budget capacity : ℕ → ℕ) (adversary : Encryption.Adversary) (n width : ℕ)
    (hbudget_pos : 0 < budget n) (hcapacity_pos : 0 < capacity n)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    Encryption.advantage (Encryption.game (scheme D budget).keyGen (scheme D budget).encrypt
      adversary) n =
    3 * (2 * budget n : ℝ≥0) * capacity n *
      Encryption.advantage (Encryption.game E.keyGen E.encrypt
        (exactLeveledAdversary E (fun n => 2 * budget n) capacity adversary)) n := by
  dsimp only [scheme]
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_mul,
    NNReal.coe_ofNat, NNReal.coe_ofNat, NNReal.coe_natCast, NNReal.coe_natCast,
    Game.coe_advantage, Game.coe_advantage,
    gap_exactLeveledAdversary E budget capacity adversary n width hbudget_pos hcapacity_pos
      hwidth hcapacity,
    abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3),
    abs_of_pos (by positivity : (0 : ℝ) < 2), Nat.abs_cast, Nat.abs_cast]

/-! ### Strict-PPT `sampleModNat` leveled reduction and statistical-tail bound -/

/-- Strict-PPT unified two-stage base IND-CPA reduction for the leveled construction that samples
the three-way hop selector via `Scheme.sampleModIndex (coins n) 3`, delegating hops `0` and `1` to
`E.modLinkAdversary` and hop `2` to `zeroLinkAdversary` weighted by
`Scheme.sampleModIndex (coins n) (depth n)` and `Scheme.sampleModIndex (coins n) (capacity n)` when
`0 < depth n ∧ 0 < capacity n` (falling back to `zeroLinkAdversary` when `depth n = 0` or
`capacity n = 0`). -/
noncomputable def modLeveledAdversary (E : Scheme) (coins depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) : Encryption.Adversary where
  choose n challengePk :=
    if 0 < depth n ∧ 0 < capacity n then
      do
        let hop ← Scheme.sampleModIndex (coins n) 3
        if hop = 0 then
          tagLeveledChoice false false <$>
            (E.modLinkAdversary coins depth capacity (publicKeyGame E adversary false)).choose n
              challengePk
        else if hop = 1 then
          (tagLeveledChoice false true ∘ swapLeveledChoice) <$>
            (E.modLinkAdversary coins depth capacity (publicKeyGame E adversary true)).choose n
              challengePk
        else
          let reverseIndex ← Scheme.sampleModIndex (coins n) (depth n)
          let bitIndex ← Scheme.sampleModIndex (coins n) (capacity n)
          if reverseIndex = 0 then
            if bitIndex = 0 then
              tagLeveledChoice true false <$>
                (zeroLinkAdversary E depth adversary).choose n challengePk
            else pure rejectLeveledChoice
          else pure rejectLeveledChoice
    else
      tagLeveledChoice true false <$>
        (zeroLinkAdversary E depth adversary).choose n challengePk
  guess := (leveledAdversary E depth capacity adversary).guess

/-- `modLeveledAdversary` is uniform strict PPT whenever the base scheme, adversary, coin count,
depth, and capacity are. -/
theorem isPPT_modLeveledAdversary {E : Scheme}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun (n, pk, bit) => E.encrypt n pk bit))
    {adversary : Encryption.Adversary} (hadversary : adversary.IsPPT)
    {coins depth capacity : ℕ → ℕ}
    (hcoins : ComputableInPolyTime coins encUnary encUnary)
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary) :
    (modLeveledAdversary E coins depth capacity adversary).IsPPT := by
  have htag := computableInPolyTime_tagLeveledChoice
  have hswap := computableInPolyTime_swapLeveledChoice
  have hzero := isPPT_zeroLinkAdversary hencrypt hadversary hkeyGen hdepth
  have hlinkFalse := Scheme.isPPT_modLinkAdversary hkeyGen hencrypt
    (isPPTOn_publicKeyGame hencrypt hadversary false) hcoins hdepth hcapacity
  have hlinkTrue := Scheme.isPPT_modLinkAdversary hkeyGen hencrypt
    (isPPTOn_publicKeyGame hencrypt hadversary true) hcoins hdepth hcapacity
  have hlev := isPPT_leveledAdversary hencrypt hadversary hkeyGen hdepth hcapacity
  constructor
  · change IsPPTOn (encPair encUnary encBits) (encPair (encPair encBool encBool) encBits)
      (fun p => (modLeveledAdversary E coins depth capacity adversary).choose p.1 p.2)
    dsimp only [modLeveledAdversary]
    apply IsPPTOn.ite (by polytime)
    · apply (Scheme.isPPTOn_sampleModIndex
        (hcoins.comp (by fun_prop)) (ComputableInPolyTime.const 3)).bind_with
      apply IsPPTOn.ite (by polytime)
      · exact (hlinkFalse.choose.on.preprocess (by fun_prop)).map (htag false false)
      · apply IsPPTOn.ite (by polytime)
        · exact (hlinkTrue.choose.on.preprocess (by fun_prop)).map ((htag false true).comp hswap)
        · apply (Scheme.isPPTOn_sampleModIndex
            (hcoins.comp (by fun_prop)) (hdepth.comp (by fun_prop))).bind_with
          apply (Scheme.isPPTOn_sampleModIndex
            (hcoins.comp (by fun_prop)) (hcapacity.comp (by fun_prop))).bind_with
          apply IsPPTOn.ite (by polytime)
          · apply IsPPTOn.ite (by polytime)
            · exact (hzero.choose.on.preprocess (by fun_prop)).map (htag true false)
            · exact (ComputableInPolyTime.const rejectLeveledChoice).isPPTOn
          · exact (ComputableInPolyTime.const rejectLeveledChoice).isPPTOn
    · exact hzero.choose.on.map (htag true false)
  · exact hlev.guess

/-- Specialization of `isPPT_modLeveledAdversary` to `2 * n` coins per modular index sample. -/
theorem isPPT_modLeveledAdversary_two_mul {E : Scheme}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun (n, pk, bit) => E.encrypt n pk bit))
    {adversary : Encryption.Adversary} (hadversary : adversary.IsPPT)
    {depth capacity : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary) :
    (modLeveledAdversary E (fun n => 2 * n) depth capacity adversary).IsPPT :=
  isPPT_modLeveledAdversary hkeyGen hencrypt hadversary (by fun_prop) hdepth hcapacity

private noncomputable def leveledZeroAt (E : Scheme) (depth : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n i j : ℕ) : Game :=
  if i = 0 then
    if j = 0 then
      ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (zeroLinkAdversary E depth adversary) bit n)
    else PMF.pure false
  else PMF.pure false

private noncomputable def exactLeveledBranch (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ)
    [NeZero (depth n)] [NeZero (capacity n)] (hop : ℕ) : Game :=
  if hop = 0 then
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (E.exactLinkAdversary depth capacity (publicKeyGame E adversary false)) bit n)
  else if hop = 1 then
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (E.exactLinkAdversary depth capacity (publicKeyGame E adversary true)) (!bit) n)
  else
    (PMF.uniformOfFintype (Fin (depth n))).bind fun i =>
      (PMF.uniformOfFintype (Fin (capacity n))).bind fun j =>
        leveledZeroAt E depth adversary bit n i.val j.val

private noncomputable def modLeveledBranch (E : Scheme) (coins depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n hop : ℕ) : Game :=
  if hop = 0 then
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (E.modLinkAdversary coins depth capacity (publicKeyGame E adversary false)) bit n)
  else if hop = 1 then
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (E.modLinkAdversary coins depth capacity (publicKeyGame E adversary true)) (!bit) n)
  else
    (ProbComp.eval (sampleModNat (coins n) (depth n))).bind fun i =>
      (ProbComp.eval (sampleModNat (coins n) (capacity n))).bind fun j =>
        leveledZeroAt E depth adversary bit n i j

/-- In each challenge world `bit`, the base IND-CPA game of `modLeveledAdversary` is within
`((3 + depth n + capacity n : ℕ) : ℝ≥0) / 2 ^ (coins n)` of `exactLeveledAdversary`. -/
theorem advantage_exactLeveledAdversary_modLeveledAdversary_le (E : Scheme)
    (coins depth capacity : ℕ → ℕ) (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    Game.advantage
      (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (exactLeveledAdversary E depth capacity adversary) bit n))
      (ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (modLeveledAdversary E coins depth capacity adversary) bit n)) ≤
      ((3 + depth n + capacity n : ℕ) : ℝ≥0) / 2 ^ (coins n) := by
  by_cases hpos : 0 < depth n ∧ 0 < capacity n
  · have : NeZero (depth n) := ⟨hpos.1.ne'⟩
    have : NeZero (capacity n) := ⟨hpos.2.ne'⟩
    have hexact :
        ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (exactLeveledAdversary E depth capacity adversary) bit n) =
        (PMF.uniformOfFintype (Fin 3)).bind fun hop =>
          exactLeveledBranch E depth capacity adversary bit n hop.val :=
      eval_exactLeveledAdversary E depth capacity adversary bit n
    have hmod :
        ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (modLeveledAdversary E coins depth capacity adversary) bit n) =
        (ProbComp.eval (sampleModNat (coins n) 3)).bind
          (modLeveledBranch E coins depth capacity adversary bit n) := by
      dsimp only [Encryption.game, Encryption.gameOn, modLeveledAdversary]
      simp only [hpos, and_self, ↓reduceIte, Scheme.sampleModIndex_eq_sampleModNat (coins n)
        (by decide : 0 < 3), Scheme.sampleModIndex_eq_sampleModNat (coins n) hpos.1,
        Scheme.sampleModIndex_eq_sampleModNat (coins n) hpos.2, bind_assoc, ProbComp.eval_bind]
      rw [PMF.bind_comm]
      congr 1; funext hop
      dsimp only [modLeveledBranch, leveledZeroAt]
      by_cases h0 : hop = 0
      · simp only [h0, ↓reduceIte]
        simpa only [Encryption.game, Encryption.gameOn, ↓reduceIte, ProbComp.eval_bind] using
          eval_modLeveled_hop_zero E coins depth capacity adversary bit n
      · by_cases h1 : hop = 1
        · simp only [h1, one_ne_zero, ↓reduceIte]
          simpa only [Encryption.game, Encryption.gameOn, ↓reduceIte, ProbComp.eval_bind] using
            eval_modLeveled_hop_one E coins depth capacity adversary bit n
        · simp only [h0, h1, ↓reduceIte, ProbComp.eval_bind, PMF.bind_bind]
          rw [PMF.bind_comm]
          congr 1; funext i
          rw [PMF.bind_comm]
          congr 1; funext j
          simpa only [Encryption.game, Encryption.gameOn, ↓reduceIte, ProbComp.eval_bind] using
            eval_leveled_hop_two E depth capacity adversary bit n i j
    rw [hexact, hmod, Game.advantage_comm]
    have hstep1 :
        Game.advantage
          ((ProbComp.eval (sampleModNat (coins n) 3)).bind
            (modLeveledBranch E coins depth capacity adversary bit n))
          ((PMF.uniformOfFintype (Fin 3)).bind fun hop =>
            modLeveledBranch E coins depth capacity adversary bit n hop.val) ≤
          (3 : ℝ≥0) / 2 ^ (coins n) := by
      simpa using Scheme.advantage_bind_sampleModNat_fin_le (coins n) 3
        (modLeveledBranch E coins depth capacity adversary bit n)
    have hbranch (hop : Fin 3) :
        Game.advantage
          (modLeveledBranch E coins depth capacity adversary bit n hop.val)
          (exactLeveledBranch E depth capacity adversary bit n hop.val) ≤
          ((depth n + capacity n : ℕ) : ℝ≥0) / 2 ^ (coins n) := by
      dsimp only [modLeveledBranch, exactLeveledBranch]
      by_cases h0 : hop.val = 0
      · simp only [h0, ↓reduceIte]
        rw [Game.advantage_comm]
        exact E.advantage_exactLinkAdversary_modLinkAdversary_le coins depth capacity
          (publicKeyGame E adversary false) bit n
      · by_cases h1 : hop.val = 1
        · simp only [h1, one_ne_zero, ↓reduceIte]
          rw [Game.advantage_comm]
          exact E.advantage_exactLinkAdversary_modLinkAdversary_le coins depth capacity
            (publicKeyGame E adversary true) (!bit) n
        · simp only [h0, h1, ↓reduceIte]
          exact Scheme.advantage_bind_sampleModNat_fin_fin_le (coins n) (depth n) (capacity n)
            (leveledZeroAt E depth adversary bit n)
    have hstep2 :
        Game.advantage
          ((PMF.uniformOfFintype (Fin 3)).bind fun hop =>
            modLeveledBranch E coins depth capacity adversary bit n hop.val)
          ((PMF.uniformOfFintype (Fin 3)).bind fun hop =>
            exactLeveledBranch E depth capacity adversary bit n hop.val) ≤
          ((depth n + capacity n : ℕ) : ℝ≥0) / 2 ^ (coins n) :=
      Game.advantage_bind_le_nnreal _ _ _ hbranch
    have htri := Game.advantage_triangle
      ((ProbComp.eval (sampleModNat (coins n) 3)).bind
        (modLeveledBranch E coins depth capacity adversary bit n))
      ((PMF.uniformOfFintype (Fin 3)).bind fun hop =>
        modLeveledBranch E coins depth capacity adversary bit n hop.val)
      ((PMF.uniformOfFintype (Fin 3)).bind fun hop =>
        exactLeveledBranch E depth capacity adversary bit n hop.val)
    have hsum :
        (3 : ℝ≥0) / 2 ^ (coins n) + ((depth n + capacity n : ℕ) : ℝ≥0) / 2 ^ (coins n) =
          ((3 + depth n + capacity n : ℕ) : ℝ≥0) / 2 ^ (coins n) := by
      push_cast; ring
    exact htri.trans ((add_le_add hstep1 hstep2).trans_eq hsum)
  · have heq :
        ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (exactLeveledAdversary E depth capacity adversary) bit n) =
        ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (modLeveledAdversary E coins depth capacity adversary) bit n) := by
      dsimp only [Encryption.game, Encryption.gameOn, exactLeveledAdversary, modLeveledAdversary]
      simp only [hpos, ↓reduceDIte, ↓reduceIte]
    rw [heq, Game.advantage_self]
    exact zero_le

/-- Concrete Gentry Theorem 4 advantage bound for `scheme D budget` via the strict-PPT modular
reduction `modLeveledAdversary`: when `0 < budget n` and `0 < capacity n`, the scheme advantage is
bounded by the exact factor `3 * (2 * budget n : ℝ≥0) * capacity n` times the sum of
`modLeveledAdversary`'s base advantage and the `sampleModNat` statistical tail
`2 * (3 + 2 * budget n + capacity n) / 2 ^ (coins n)`. -/
theorem advantage_scheme_le_modLeveledAdversary {E : Scheme}
    {secretWidth ciphertextWidth : ℕ → ℕ}
    (D : DecryptionCircuits E secretWidth ciphertextWidth)
    (coins budget capacity : ℕ → ℕ) (adversary : Encryption.Adversary) (n width : ℕ)
    (hbudget_pos : 0 < budget n) (hcapacity_pos : 0 < capacity n)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    Encryption.advantage (Encryption.game (scheme D budget).keyGen (scheme D budget).encrypt
      adversary) n ≤
    3 * (2 * budget n : ℝ≥0) * capacity n *
      (Encryption.advantage (Encryption.game E.keyGen E.encrypt
        (modLeveledAdversary E coins (fun n => 2 * budget n) capacity adversary)) n +
        2 * ((3 + 2 * budget n + capacity n : ℕ) : ℝ≥0) / 2 ^ (coins n)) := by
  rw [advantage_scheme_eq_exactLeveledAdversary D budget capacity adversary n width
    hbudget_pos hcapacity_pos hwidth hcapacity]
  exact mul_le_mul_of_nonneg_left
    (Scheme.advantage_le_of_triangle_both_div
      (advantage_exactLeveledAdversary_modLeveledAdversary_le E coins
        (fun n => 2 * budget n) capacity adversary false n)
      (advantage_exactLeveledAdversary_modLeveledAdversary_le E coins
        (fun n => 2 * budget n) capacity adversary true n))
    zero_le

/-- `2 * n`-coin specialization of `advantage_scheme_le_modLeveledAdversary`: when
`3 + 2 * budget n + capacity n ≤ 2 ^ n`, sampling each coordinate with `2 * n` coins via
`sampleModNat` bounds the statistical tail by `2 / 2 ^ n`, so the scheme advantage is at most
`3 * (2 * budget n : ℝ≥0) * capacity n` times the sum of the base advantage and `2 / 2 ^ n`. -/
theorem advantage_scheme_le_modLeveledAdversary_two_mul {E : Scheme}
    {secretWidth ciphertextWidth : ℕ → ℕ}
    (D : DecryptionCircuits E secretWidth ciphertextWidth)
    (budget capacity : ℕ → ℕ) (adversary : Encryption.Adversary) (n width : ℕ)
    (hbudget_pos : 0 < budget n) (hcapacity_pos : 0 < capacity n)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n)
    (htail : 3 + 2 * budget n + capacity n ≤ 2 ^ n) :
    Encryption.advantage (Encryption.game (scheme D budget).keyGen (scheme D budget).encrypt
      adversary) n ≤
    3 * (2 * budget n : ℝ≥0) * capacity n *
      (Encryption.advantage (Encryption.game E.keyGen E.encrypt
        (modLeveledAdversary E (fun n => 2 * n) (fun n => 2 * budget n) capacity adversary)) n +
        2 / 2 ^ n) := by
  refine (advantage_scheme_le_modLeveledAdversary D (fun n => 2 * n) budget capacity adversary
    n width hbudget_pos hcapacity_pos hwidth hcapacity).trans ?_
  have hpow : (2 : ℝ≥0) ^ (2 * n) = (2 : ℝ≥0) ^ n * (2 : ℝ≥0) ^ n := by
    rw [Nat.two_mul, pow_add]
  have hle : ((3 + 2 * budget n + capacity n : ℕ) : ℝ≥0) ≤ (2 : ℝ≥0) ^ n := by
    exact_mod_cast htail
  have hpos : (0 : ℝ≥0) < (2 : ℝ≥0) ^ n := by positivity
  have htail_div :
      2 * ((3 + 2 * budget n + capacity n : ℕ) : ℝ≥0) / 2 ^ (2 * n) ≤ 2 / 2 ^ n := by
    rw [hpow]
    calc
      2 * ((3 + 2 * budget n + capacity n : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ n * (2 : ℝ≥0) ^ n)
        ≤ 2 * (2 : ℝ≥0) ^ n / ((2 : ℝ≥0) ^ n * (2 : ℝ≥0) ^ n) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle zero_le_two) (by positivity)
      _ = 2 / 2 ^ n := by
          rw [mul_div_mul_right _ _ hpos.ne']
  gcongr

/-! ### Explicit polynomial artifact-length bounds, coin-count formulas, and efficiency witnesses -/

/-- Every public artifact in the support of `E.publicKeyChainHybrid n depth cut` has serialized
bit length at most `publicKeyLengthBound depth width pkBound ctBound` whenever supported base keys
and ciphertexts obey `(pkBound, width, ctBound)`. -/
theorem length_encPublicKey_support_publicKeyChainHybrid_le {E : Scheme}
    (n depth cut width pkBound ctBound : ℕ)
    (hkey : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support,
      keys.1.length ≤ pkBound ∧ keys.2.length ≤ width)
    (henc : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, ∀ b ct,
      ct ∈ (ProbComp.eval (E.encrypt n keys.1 b)).support → ct.length ≤ ctBound)
    {artifact : List (List Bool) × List (List (List Bool))}
    (hart : artifact ∈ (ProbComp.eval (E.publicKeyChainHybrid n depth cut)).support) :
    (encPublicKey artifact).length ≤ publicKeyLengthBound depth width pkBound ctBound := by
  simp only [Scheme.publicKeyChainHybrid, Scheme.encryptKeyLinksHybrid, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hart
  rcases hart with ⟨keys, hkeys, _, ⟨front, hfront, back, hback, rfl⟩, rfl⟩
  obtain ⟨hkeys_len, hkeys_mem⟩ := (E.mem_support_generateKeys_iff n depth keys).mp hkeys
  have hkeys_bound (k : List Bool × List Bool) (hk : k ∈ keys) :
      k.2.length ≤ width ∧
        ∀ b ct, ct ∈ (ProbComp.eval (E.encrypt n k.1 b)).support → ct.length ≤ ctBound :=
    ⟨(hkey k (hkeys_mem k hk)).2, henc k (hkeys_mem k hk)⟩
  have hfront_info := Scheme.length_and_mem_of_mem_support_encryptKeyLinks
    (fun k hk => hkeys_bound k (List.mem_of_mem_take hk)) hfront
  have hback_info := Scheme.length_and_mem_of_mem_support_encryptZeroKeyLinks
    (fun k hk => hkeys_bound k (List.mem_of_mem_drop hk)) hback
  apply length_encPublicKey_le depth width pkBound ctBound
  · simp [hkeys_len]
  · intro pk hpk
    rcases List.mem_map.mp hpk with ⟨k, hk, rfl⟩
    exact (hkey k (hkeys_mem k hk)).1
  · rw [List.length_append, hfront_info.1, hback_info.1, List.length_take, List.length_drop,
      hkeys_len]
    omega
  · intro link hlink
    rcases List.mem_append.mp hlink with h | h
    · exact hfront_info.2 link h
    · exact hback_info.2 link h

/-- Every public key generated by `keyGen E n budget` (or `(scheme D budget).keyGen n`) has bit
length at most `publicKeyLengthBound (2 * budget) width pkBound ctBound`. -/
theorem length_publicKey_support_keyGen_le {E : Scheme}
    (n budget width pkBound ctBound : ℕ)
    (hkey : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support,
      keys.1.length ≤ pkBound ∧ keys.2.length ≤ width)
    (henc : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, ∀ b ct,
      ct ∈ (ProbComp.eval (E.encrypt n keys.1 b)).support → ct.length ≤ ctBound)
    {kp : List Bool × List Bool}
    (hkp : kp ∈ (ProbComp.eval (keyGen E n budget)).support) :
    kp.1.length ≤ publicKeyLengthBound (2 * budget) width pkBound ctBound := by
  have hmap : kp.1 ∈ ((ProbComp.eval (keyGen E n budget)).map Prod.fst).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨kp, hkp, rfl⟩
  rw [eval_keyGen_public] at hmap
  rcases (PMF.mem_support_map_iff _ _ _).mp hmap with ⟨artifact, hart, hfst⟩
  rw [← hfst]
  exact length_encPublicKey_support_publicKeyChainHybrid_le n (2 * budget) (2 * budget)
    width pkBound ctBound hkey henc hart

/-- Coin-count formula for the message-selection stage of `leveledAdversary` in terms of
`depth`, `capacity`, and the per-call coin budgets of `E.keyGen`, `E.encrypt`, and
`adversary.choose`. It is proved polynomially bounded
(`polynomiallyBounded_leveledChooseCoinBudget`); no replay law for that stage on this many coins
is proved. It counts:
* `2` selector bits plus `(Nat.log 2 depth + 1) + (Nat.log 2 capacity + 1)` dyadic index/coin bits,
* `depth` calls to `E.keyGen`,
* at most `depth * capacity` calls to `E.encrypt` (in the `zeroLinkAdversary` branch), and
* at most `1` call to `adversary.choose`. -/
def leveledChooseCoinBudget
    (depth capacity keyGenCoins encCoins advChooseCoins : ℕ) : ℕ :=
  2 + (Nat.log 2 depth + 1) + (Nat.log 2 capacity + 1) +
    depth * keyGenCoins + depth * capacity * encCoins + advChooseCoins

/-- Explicit coin-tape budget for the guessing stage of `leveledAdversary` in terms of
`depth`, `capacity`, and the per-call coin budgets of `E.encrypt`, `adversary.choose`, and
`adversary.guess`:
* at most `depth * capacity` calls to `E.encrypt` (splicing the `depth - 1` surrounding links,
  the `width - 1` non-challenge bits of the active link, and the `1` tagged challenge ciphertext
  in `publicKeyGame`),
* at most `1` call to `adversary.choose` (inside `publicKeyGame`), and
* at most `1` call to `adversary.guess`. -/
def leveledGuessCoinBudget
    (depth capacity encCoins advChooseCoins advGuessCoins : ℕ) : ℕ :=
  depth * capacity * encCoins + advChooseCoins + advGuessCoins

/-- When `depth` and `capacity` are polynomially bounded and the component coin budgets are
polynomially bounded, `leveledChooseCoinBudget` and `leveledGuessCoinBudget` are polynomially
bounded. -/
theorem polynomiallyBounded_leveledChooseCoinBudget
    {depth capacity keyGenCoins encCoins advChooseCoins : ℕ → ℕ}
    (hdepth : PolynomiallyBounded depth) (hcap : PolynomiallyBounded capacity)
    (hkg : PolynomiallyBounded keyGenCoins) (henc : PolynomiallyBounded encCoins)
    (hch : PolynomiallyBounded advChooseCoins) :
    PolynomiallyBounded (fun n =>
      leveledChooseCoinBudget (depth n) (capacity n) (keyGenCoins n) (encCoins n)
        (advChooseCoins n)) := by
  have hlog_d : PolynomiallyBounded (fun n => Nat.log 2 (depth n)) :=
    hdepth.mono (Filter.Eventually.of_forall fun n => Nat.log_le_self 2 (depth n))
  have hlog_c : PolynomiallyBounded (fun n => Nat.log 2 (capacity n)) :=
    hcap.mono (Filter.Eventually.of_forall fun n => Nat.log_le_self 2 (capacity n))
  unfold leveledChooseCoinBudget
  fun_prop

/-- Polynomial boundedness of `leveledGuessCoinBudget`. -/
theorem polynomiallyBounded_leveledGuessCoinBudget
    {depth capacity encCoins advChooseCoins advGuessCoins : ℕ → ℕ}
    (hdepth : PolynomiallyBounded depth) (hcap : PolynomiallyBounded capacity)
    (henc : PolynomiallyBounded encCoins) (hch : PolynomiallyBounded advChooseCoins)
    (hgu : PolynomiallyBounded advGuessCoins) :
    PolynomiallyBounded (fun n =>
      leveledGuessCoinBudget (depth n) (capacity n) (encCoins n) (advChooseCoins n)
        (advGuessCoins n)) := by
  unfold leveledGuessCoinBudget
  fun_prop

/-- Polynomial artifact-length, component replay and native-efficiency witnesses for the
leveled reduction motivated by [Gentry2009], Section 2, Theorem 4, p. 171. These witnesses do not
assert the source's multiplicative runtime comparison.
Given uniform strict-PPT certificates for `E.keyGen`, `E.encrypt`, and `adversary`, and
polynomial-time unary certificates for `budget` and `capacity`, there exist explicit polynomial
bounds:
* `pkBound n = c_kg * (n + 1) ^ d_kg` on base key lengths and key-generation coin count,
* `ctBound n = c_enc * (2 * n + 2 * pkBound n + 5) ^ d_enc` on base ciphertext lengths and coin
  count,
* `pubLen n = publicKeyLengthBound (2 * budget n) (capacity n) (pkBound n) (ctBound n)` on every
  serialized leveled public key passed to `adversary.choose n`,
* `advChooseBudget n = c_ch * (2 * n + pubLen n + 2) ^ d_ch` and
  `advGuessBudget n = c_gu * (2 * n + 2 * advChooseBudget n + ctBound n + 4) ^ d_gu` on
  `adversary`'s own coin and output-state lengths at the leveled public-key and ciphertext sizes,
such that:
1. Key generation has native replay using `pkBound n` coins, and supported base keys obey the
   stated public-key and secret-capacity bounds. Every bounded base public key has native
   encryption replay using `ctBound n` coins, and every supported ciphertext fits that bound.
2. Every supported public artifact
   `artifact ∈ (ProbComp.eval (E.publicKeyChainHybrid n (2 * budget n) cut)).support`
   has `(encPublicKey artifact).length ≤ pubLen n`.
3. On every public key `pk'` of length at most `pubLen n`, `adversary.choose n pk'` is realized by a
   total polynomial-time seeded evaluator using `advChooseBudget n` fair coins and produces saved
   states of length at most `advChooseBudget n`.
4. On every saved state of length at most `advChooseBudget n` and tagged ciphertext of length at
   most `ctBound n + 1`, `adversary.guess n state ct'` is realized by a total polynomial-time seeded
   evaluator using `advGuessBudget n` fair coins.
5. Both `leveledAdversary` and `modLeveledAdversary` are uniform strict PPT, and the composite
   coin-tape budgets `leveledChooseCoinBudget` and `leveledGuessCoinBudget` are polynomially
   bounded in `n`. -/
theorem exists_leveledAdversary_overhead {E : Scheme}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun (n, pk, bit) => E.encrypt n pk bit))
    {adversary : Encryption.Adversary} (hadversary : adversary.IsPPT)
    {width budget capacity : ℕ → ℕ}
    (hwidth : ∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support → keys.2.length = width n)
    (hcapacity_le : ∀ n, width n ≤ capacity n)
    (hbudget : ComputableInPolyTime budget encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary) :
    ∃ (c_kg d_kg c_enc d_enc c_ch d_ch c_gu d_gu : ℕ)
      (evalKey : ℕ → List Bool → List Bool × List Bool)
      (evalEncrypt : ℕ × List Bool × Bool → List Bool → List Bool)
      (evalChoose : ℕ × List Bool → List Bool → (Bool × Bool) × List Bool)
      (evalGuess : ℕ × List Bool × List Bool → List Bool → Bool),
      let pkBound (n : ℕ) := c_kg * (n + 1) ^ d_kg
      let ctBound (n : ℕ) := c_enc * (2 * n + 2 * pkBound n + 5) ^ d_enc
      let pubLen (n : ℕ) :=
        publicKeyLengthBound (2 * budget n) (capacity n) (pkBound n) (ctBound n)
      let advChooseBudget (n : ℕ) := c_ch * (2 * n + pubLen n + 2) ^ d_ch
      let advGuessBudget (n : ℕ) :=
        c_gu * (2 * n + 2 * advChooseBudget n + ctBound n + 4) ^ d_gu
      ComputableInPolyTime (fun (n, coins) => evalKey n coins)
        (encPair encUnary encBits) (encPair encBits encBits) ∧
      ComputableInPolyTime (fun (x, coins) => evalEncrypt x coins)
        (encPair (encPair encUnary (encPair encBits encBool)) encBits) encBits ∧
      ComputableInPolyTime (fun (x, coins) => evalChoose x coins)
        (encPair (encPair encUnary encBits) encBits)
        (encPair (encPair encBool encBool) encBits) ∧
      ComputableInPolyTime (fun (x, coins) => evalGuess x coins)
        (encPair (encPair encUnary (encPair encBits encBits)) encBits) encBool ∧
      (∀ n, ProbComp.eval (E.keyGen n) =
        (BitString.uniformList (pkBound n)).map (evalKey n)) ∧
      (∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support →
        keys.1.length ≤ pkBound n ∧ keys.2.length ≤ capacity n) ∧
      (∀ n pk bit, pk.length ≤ pkBound n →
        ProbComp.eval (E.encrypt n pk bit) =
          (BitString.uniformList (ctBound n)).map (evalEncrypt (n, pk, bit)) ∧
        ∀ ct ∈ (ProbComp.eval (E.encrypt n pk bit)).support, ct.length ≤ ctBound n) ∧
      (∀ n cut artifact,
        artifact ∈ (ProbComp.eval (E.publicKeyChainHybrid n (2 * budget n) cut)).support →
          (encPublicKey artifact).length ≤ pubLen n) ∧
      (∀ n pk', pk'.length ≤ pubLen n →
        ProbComp.eval (adversary.choose n pk') =
          (BitString.uniformList (advChooseBudget n)).map (evalChoose (n, pk')) ∧
        ∀ choice ∈ (ProbComp.eval (adversary.choose n pk')).support,
          choice.2.length ≤ advChooseBudget n) ∧
      (∀ n state ct', state.length ≤ advChooseBudget n → ct'.length ≤ ctBound n + 1 →
        ProbComp.eval (adversary.guess n state ct') =
          (BitString.uniformList (advGuessBudget n)).map (evalGuess (n, state, ct'))) ∧
      PolynomiallyBounded (fun n =>
        leveledChooseCoinBudget (2 * budget n) (capacity n) (pkBound n) (ctBound n)
          (advChooseBudget n)) ∧
      PolynomiallyBounded (fun n =>
        leveledGuessCoinBudget (2 * budget n) (capacity n) (ctBound n)
          (advChooseBudget n) (advGuessBudget n)) ∧
      (leveledAdversary E (fun n => 2 * budget n) capacity adversary).IsPPT ∧
      (modLeveledAdversary E (fun n => 2 * n) (fun n => 2 * budget n) capacity
        adversary).IsPPT := by
  obtain ⟨c_kg, d_kg, evalKey, hevalKey, _, hkey_law, hkey_len⟩ :=
    hkeyGen.exists_total_seeded_evaluator_with_length
  have hkg_len (n keys) (hkeys : keys ∈ (ProbComp.eval (E.keyGen n)).support) :
      keys.1.length + keys.2.length ≤ c_kg * (n + 1) ^ d_kg := by
    have hlen := hkey_len n keys hkeys
    simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate] at hlen
    omega
  obtain ⟨c_enc, d_enc, evalEncrypt, hevalEncrypt, _, henc_law, henc_len⟩ :=
    hencrypt.exists_total_seeded_evaluator_with_length
  obtain ⟨c_ch, d_ch, evalChoose, hevalChoose, _, hchoose_law, hchoose_len⟩ :=
    hadversary.choose.on.exists_total_seeded_evaluator_with_length
  obtain ⟨c_gu, d_gu, evalGuess, hevalGuess, _, hguess_law⟩ :=
    hadversary.guess.exists_total_seeded_evaluator
  let pkBound (n : ℕ) := c_kg * (n + 1) ^ d_kg
  let ctBound (n : ℕ) := c_enc * (2 * n + 2 * pkBound n + 5) ^ d_enc
  let pubLen (n : ℕ) :=
    publicKeyLengthBound (2 * budget n) (capacity n) (pkBound n) (ctBound n)
  let advChooseBudget (n : ℕ) := c_ch * (2 * n + pubLen n + 2) ^ d_ch
  let advGuessBudget (n : ℕ) :=
    c_gu * (2 * n + 2 * advChooseBudget n + ctBound n + 4) ^ d_gu
  have hdepth : ComputableInPolyTime (fun n => 2 * budget n) encUnary encUnary := by fun_prop
  have hd : PolynomiallyBounded (fun n => 2 * budget n) := hdepth.polynomiallyBounded
  have hc : PolynomiallyBounded capacity := hcapacity.polynomiallyBounded
  have hpk : PolynomiallyBounded pkBound := by dsimp only [pkBound]; fun_prop
  have hct : PolynomiallyBounded ctBound := by dsimp only [ctBound]; fun_prop
  have hpub : PolynomiallyBounded pubLen := by
    dsimp only [pubLen, publicKeyLengthBound]
    fun_prop
  have hch : PolynomiallyBounded advChooseBudget := by
    dsimp only [advChooseBudget]
    fun_prop
  refine ⟨c_kg, d_kg, c_enc, d_enc, c_ch, d_ch, c_gu, d_gu, evalKey, evalEncrypt, evalChoose,
    evalGuess, hevalKey, hevalEncrypt, hevalChoose, hevalGuess, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    isPPT_leveledAdversary hencrypt hadversary hkeyGen hdepth hcapacity,
    isPPT_modLeveledAdversary_two_mul hkeyGen hencrypt hadversary hdepth hcapacity⟩
  · intro n
    exact hkey_law n (pkBound n) (by simp [pkBound, encUnary_apply])
  · intro n keys hkeys
    have hlen := hkg_len n keys hkeys
    have hw := hwidth n keys hkeys
    have hc := hcapacity_le n
    exact ⟨by dsimp only [pkBound]; omega, by omega⟩
  · intro n pk bit hpk
    change pk.length ≤ pkBound n at hpk
    have hin : (encPair encUnary (encPair encBits encBool) (n, pk, bit)).length + 1 ≤
        2 * n + 2 * pkBound n + 5 := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
        encBool_apply, List.length_singleton]
      omega
    have hbound : c_enc *
        ((encPair encUnary (encPair encBits encBool) (n, pk, bit)).length + 1) ^ d_enc ≤
        ctBound n := Nat.mul_le_mul_left c_enc (Nat.pow_le_pow_left hin d_enc)
    exact ⟨henc_law (n, pk, bit) (ctBound n) hbound,
      fun ct hct => (henc_len (n, pk, bit) ct hct).trans hbound⟩
  · intro n cut artifact hart
    apply length_encPublicKey_support_publicKeyChainHybrid_le n (2 * budget n) cut (capacity n)
      (pkBound n) (ctBound n)
    · intro keys hkeys
      have hlen := hkg_len n keys hkeys
      have hw := hwidth n keys hkeys
      have hcap := hcapacity_le n
      dsimp only [pkBound]
      exact ⟨by omega, by omega⟩
    · intro keys hkeys b ct hct
      have hpk : keys.1.length ≤ pkBound n := by
        have hlen := hkg_len n keys hkeys
        dsimp only [pkBound]
        omega
      have hlen := henc_len (n, keys.1, b) ct hct
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
        encBool_apply, List.length_singleton] at hlen
      have hin : (2 * n + 1 + (2 * keys.1.length + 1 + 1)) + 1 ≤
          2 * n + 2 * pkBound n + 5 := by omega
      exact hlen.trans (Nat.mul_le_mul_left c_enc (Nat.pow_le_pow_left hin d_enc))
    · exact hart
  · intro n pk' hpk'
    change pk'.length ≤ pubLen n at hpk'
    have hin : (encPair encUnary encBits (n, pk')).length + 1 ≤ 2 * n + pubLen n + 2 := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
      omega
    have hch_le :
        c_ch * ((encPair encUnary encBits (n, pk')).length + 1) ^ d_ch ≤ advChooseBudget n :=
      Nat.mul_le_mul_left c_ch (Nat.pow_le_pow_left hin d_ch)
    refine ⟨hchoose_law (n, pk') (advChooseBudget n) hch_le, fun choice hchoice => ?_⟩
    have hchoice2 : choice.2.length ≤
        (encPair (encPair encBool encBool) encBits choice).length := by
      simp only [length_encPair, encBool_apply, List.length_singleton, encBits_apply]
      omega
    exact (hchoice2.trans (hchoose_len (n, pk') choice hchoice)).trans hch_le
  · intro n state ct' hstate hct'
    change state.length ≤ advChooseBudget n at hstate
    change ct'.length ≤ ctBound n + 1 at hct'
    apply hguess_law (n, state, ct') (advGuessBudget n)
    have hin : (encPair encUnary (encPair encBits encBits) (n, state, ct')).length + 1 ≤
        2 * n + 2 * advChooseBudget n + ctBound n + 4 := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
      omega
    exact Nat.mul_le_mul_left c_gu (Nat.pow_le_pow_left hin d_gu)
  · exact polynomiallyBounded_leveledChooseCoinBudget hd hc hpk hct hch
  · have hgu : PolynomiallyBounded advGuessBudget := by
      dsimp only [advGuessBudget]
      fun_prop
    exact polynomiallyBounded_leveledGuessCoinBudget hd hc hct hch hgu

end Cslib.Crypto.Homomorphic.Leveled
