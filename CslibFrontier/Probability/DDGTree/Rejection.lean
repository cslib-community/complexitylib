/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Init
public import CslibFrontier.Probability.DDGTree
public import CslibFrontier.Probability.UniformNat
import CslibFrontier.Probability.Option
import CslibFrontier.Probability.PMF.Filter
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.StatisticalDistance
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Exact fair-bit block-rejection sampling and capped trials

A block-rejection sampler (`Cslib.Probability.BlockRejectionSpec`) reads fair bits in independent
blocks of length `width` and applies a single-block decoder `attempt : List Bool → Option α`. On
`some a` the sampler accepts and halts with `a`; on `none` it rejects the block and repeats on the
remaining bits.

Running at most `trials` blocks gives the capped law `BlockRejectionSpec.runTrials` (realized by
`decodeTrials` on `trials * width` fair bits), whose failure probability is `rejectProb ^ trials`
and whose fallback completion `runCapped` lies within statistical distance
`(rejectProb ^ trials).toReal` of the target distribution. Reading arbitrarily many blocks defines a
computable discrete distribution generating tree `BlockRejectionSpec.toDDGTree` satisfying
`toDDGTree.run n = runTrials (n / width)` for every bit budget `n`, generating the target law
whenever `0 < width` and `acceptProb ≠ 0`, and reading `width / acceptProb` fair bits in
expectation (`expectedFlips_toDDGTree`).

Instantiating `BlockRejectionSpec` with binary decoding yields:
* `uniformFinRejectionSpec` and `uniformFinTree` for `Fin n` (`[NeZero n]`), generating
  `PMF.uniformOfFintype (Fin n)` with expected flips at most `2 * Nat.clog 2 n` (attaining `k` at
  powers of two `2 ^ k`) and `t`-trial failure probability at most `(1 / 2) ^ t`;
* `dyadicFinRejectionSpec` using `UniformNat.dyadicSize n` (`Nat.log 2 n + 1` bits per trial),
  giving `t`-trial failure probability at most `(1 / 2) ^ t` for all `n ≥ 1`;
* `subsetDyadicSpec` for exact uniform sampling on a nonempty subset `S : Finset α` inside an
  indexed range `Fin m → α`.

## Main definitions

* `Cslib.Probability.BlockRejectionSpec`: block width and single-block acceptance decoder.
* `Cslib.Probability.BlockRejectionSpec.decodeTrials`, `runTrials`, `runCapped`: capped `t`-trial
  decoder, optional law, and fallback completion.
* `Cslib.Probability.BlockRejectionSpec.toDDGTree`: exact unbounded `DDGTree` of a block sampler.
* `Cslib.Probability.finCutoffSpec`, `uniformFinRejectionSpec`, `uniformFinTree`,
  `dyadicFinRejectionSpec`, `subsetDyadicSpec`: exact bounded-integer and subset fair-bit rejection
  samplers.

## Main results

* `Cslib.Probability.BlockRejectionSpec.runTrials_none`,
  `Cslib.Probability.BlockRejectionSpec.runTrials_some_of_singleLaw`: exact `t`-trial laws.
* `Cslib.Probability.BlockRejectionSpec.dist_runCapped_le`: statistical distance of the capped
  fallback sampler from the target law.
* `Cslib.Probability.BlockRejectionSpec.run_toDDGTree`,
  `Cslib.Probability.BlockRejectionSpec.toDDGTree_generates`,
  `Cslib.Probability.BlockRejectionSpec.expectedFlips_toDDGTree`: exact `DDGTree` generation and
  closed-form expected fair-bit cost `width / acceptProb`.
* `Cslib.Probability.uniformFinTree_generates`,
  `Cslib.Probability.expectedFlips_uniformFinTree_two_pow`,
  `Cslib.Probability.expectedFlips_uniformFinTree_le`,
  `Cslib.Probability.runTrials_dyadicFinRejectionSpec_none_le`: bounded-integer exactness, expected
  flip bounds, and exponential trial-failure decay.
* `Cslib.Probability.subsetDyadicSpec_generates`,
  `Cslib.Probability.expectedFlips_subsetDyadicSpec`: exact subset generation and expected flips.

## References

* [D. E. Knuth, A. C. Yao, *The complexity of nonuniform random number generation*][KnuthYao1976].
-/

public section

open scoped ENNReal Cslib.Probability.PMF
open Filter Topology

namespace Cslib.Probability

/-- Specification of a block-rejection fair-bit sampler: each trial reads `width` independent fair
bits and applies `attempt`; `some a` accepts `a`, and `none` rejects the block. -/
structure BlockRejectionSpec (α : Type*) where
  /-- Number of fair bits read per rejection trial. -/
  width : ℕ
  /-- Single-block decoder returning `some a` on acceptance and `none` on rejection. -/
  attempt : List Bool → Option α

namespace BlockRejectionSpec

variable {α : Type*}

/-- Law of a single `width`-bit rejection trial. -/
@[expose] noncomputable def singleLaw (spec : BlockRejectionSpec α) : PMF (Option α) :=
  (BitString.uniformList spec.width).map spec.attempt

/-- Rejection probability of a single `width`-bit trial. -/
@[expose] noncomputable def rejectProb (spec : BlockRejectionSpec α) : ℝ≥0∞ :=
  spec.singleLaw none

/-- Acceptance probability `1 - rejectProb` of a single `width`-bit trial. -/
@[expose] noncomputable def acceptProb (spec : BlockRejectionSpec α) : ℝ≥0∞ :=
  1 - spec.rejectProb

theorem rejectProb_le_one (spec : BlockRejectionSpec α) : spec.rejectProb ≤ 1 :=
  PMF.coe_le_one _ _

theorem acceptProb_add_rejectProb (spec : BlockRejectionSpec α) :
    spec.acceptProb + spec.rejectProb = 1 :=
  tsub_add_cancel_of_le spec.rejectProb_le_one

theorem one_sub_rejectProb (spec : BlockRejectionSpec α) :
    1 - spec.rejectProb = spec.acceptProb :=
  rfl

theorem rejectProb_lt_one_iff (spec : BlockRejectionSpec α) :
    spec.rejectProb < 1 ↔ spec.acceptProb ≠ 0 := by
  rw [acceptProb, ne_eq, tsub_eq_zero_iff_le, not_le]

/-- Decode at most `trials` consecutive `width`-bit blocks from `bits`, returning the first
accepted value or `none`. -/
@[expose] def decodeTrials (spec : BlockRejectionSpec α) : ℕ → List Bool → Option α
  | 0, _ => none
  | t + 1, bits =>
    match spec.attempt (bits.take spec.width) with
    | some a => some a
    | none => spec.decodeTrials t (bits.drop spec.width)

@[simp]
theorem decodeTrials_zero (spec : BlockRejectionSpec α) (bits : List Bool) :
    spec.decodeTrials 0 bits = none :=
  rfl

theorem decodeTrials_succ (spec : BlockRejectionSpec α) (t : ℕ) (bits : List Bool) :
    spec.decodeTrials (t + 1) bits =
      match spec.attempt (bits.take spec.width) with
      | some a => some a
      | none => spec.decodeTrials t (bits.drop spec.width) :=
  rfl

theorem decodeTrials_append_of_some {spec : BlockRejectionSpec α} {t : ℕ} {w : List Bool} {a : α}
    (hw : t * spec.width ≤ w.length) (h : spec.decodeTrials t w = some a) (v : List Bool) :
    spec.decodeTrials t (w ++ v) = some a := by
  induction t generalizing w with
  | zero => simp at h
  | succ t ih =>
    have hw1 : spec.width ≤ w.length := by
      have : 1 * spec.width ≤ (t + 1) * spec.width := Nat.mul_le_mul_right _ (by omega)
      omega
    have htake : (w ++ v).take spec.width = w.take spec.width :=
      List.take_append_of_le_length hw1
    have hdrop : (w ++ v).drop spec.width = w.drop spec.width ++ v :=
      List.drop_append_of_le_length hw1
    rw [decodeTrials_succ, htake, hdrop]
    rw [decodeTrials_succ] at h
    cases hatt : spec.attempt (w.take spec.width) with
    | some b =>
      rw [hatt] at h
      exact h
    | none =>
      rw [hatt] at h
      refine ih ?_ h
      rw [List.length_drop]
      rw [Nat.succ_mul] at hw
      omega

theorem decodeTrials_mono_of_some {spec : BlockRejectionSpec α} {t t' : ℕ} {w : List Bool} {a : α}
    (htt : t ≤ t') (h : spec.decodeTrials t w = some a) :
    spec.decodeTrials t' w = some a := by
  induction t generalizing t' w with
  | zero => simp at h
  | succ t ih =>
    obtain ⟨k, rfl⟩ : ∃ k, t' = k + 1 := ⟨t' - 1, by omega⟩
    rw [decodeTrials_succ] at h ⊢
    cases hatt : spec.attempt (w.take spec.width) with
    | some b =>
      rw [hatt] at h
      exact h
    | none =>
      rw [hatt] at h
      exact ih (by omega) h

theorem decodeTrials_take (spec : BlockRejectionSpec α) (t : ℕ) (w : List Bool) :
    spec.decodeTrials t (w.take (t * spec.width)) = spec.decodeTrials t w := by
  induction t generalizing w with
  | zero => rfl
  | succ t ih =>
    have hle : spec.width ≤ (t + 1) * spec.width := by
      rw [Nat.succ_mul]
      omega
    have htake : (w.take ((t + 1) * spec.width)).take spec.width = w.take spec.width := by
      rw [List.take_take, Nat.min_eq_left hle]
    have hdrop : (w.take ((t + 1) * spec.width)).drop spec.width =
        (w.drop spec.width).take (t * spec.width) := by
      rw [List.drop_take, show (t + 1) * spec.width - spec.width = t * spec.width by
        rw [Nat.succ_mul]; omega]
    rw [decodeTrials_succ, decodeTrials_succ, htake, hdrop]
    cases spec.attempt (w.take spec.width) with
    | some a => rfl
    | none => exact ih (w.drop spec.width)

/-- Distribution of running at most `trials` independent `width`-bit blocks. -/
@[expose] noncomputable def runTrials (spec : BlockRejectionSpec α) (trials : ℕ) :
    PMF (Option α) :=
  (BitString.uniformList (trials * spec.width)).map (spec.decodeTrials trials)

@[simp]
theorem runTrials_zero (spec : BlockRejectionSpec α) :
    spec.runTrials 0 = PMF.pure none := by
  simp [runTrials, decodeTrials]

theorem runTrials_succ (spec : BlockRejectionSpec α) (t : ℕ) :
    spec.runTrials (t + 1) =
      spec.singleLaw.bind fun o =>
        match o with
        | some a => PMF.pure (some a)
        | none => spec.runTrials t := by
  have hmul : (t + 1) * spec.width = spec.width + t * spec.width := by
    rw [Nat.succ_mul, Nat.add_comm]
  unfold runTrials singleLaw
  rw [hmul]
  have hsplit := BitString.uniformList_bind_split spec.width (t * spec.width)
    (fun front rest => PMF.pure (match spec.attempt front with
      | some a => some a
      | none => spec.decodeTrials t rest))
  calc
    (BitString.uniformList (spec.width + t * spec.width)).map (spec.decodeTrials (t + 1)) =
        (BitString.uniformList (spec.width + t * spec.width)).bind
          (fun tape => PMF.pure (match spec.attempt (tape.take spec.width) with
            | some a => some a
            | none => spec.decodeTrials t (tape.drop spec.width))) := rfl
    _ = (BitString.uniformList spec.width).bind (fun front =>
          (BitString.uniformList (t * spec.width)).bind (fun rest =>
            PMF.pure (match spec.attempt front with
              | some a => some a
              | none => spec.decodeTrials t rest))) := hsplit
    _ = ((BitString.uniformList spec.width).map spec.attempt).bind (fun o =>
          match o with
          | some a => PMF.pure (some a)
          | none => (BitString.uniformList (t * spec.width)).map (spec.decodeTrials t)) := by
      rw [PMF.bind_map]
      congr 1
      funext front
      simp only [Function.comp_apply]
      cases spec.attempt front with
      | some a => simp [PMF.bind_const]
      | none => rfl

/-- Failure probability after `t` trials is `rejectProb ^ t`. -/
theorem runTrials_none (spec : BlockRejectionSpec α) (t : ℕ) :
    spec.runTrials t none = spec.rejectProb ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [runTrials_succ, PMF.bind_apply, tsum_option_eq]
    have hsome : ∑' a : α, spec.singleLaw (some a) *
        (PMF.pure (some a) : PMF (Option α)) none = 0 := by
      simp
    rw [hsome, add_zero, ih, pow_succ']
    rfl

/-- Accepted outcome mass after `t` trials. -/
theorem runTrials_some (spec : BlockRejectionSpec α) (t : ℕ) (a : α) :
    spec.runTrials t (some a) =
      spec.singleLaw (some a) * ∑ j ∈ Finset.range t, spec.rejectProb ^ j := by
  induction t with
  | zero => simp
  | succ t ih =>
    classical
    rw [runTrials_succ, PMF.bind_apply, tsum_option_eq, ih, Finset.sum_range_succ]
    have hsome : ∑' b : α, spec.singleLaw (some b) *
        (PMF.pure (some b) : PMF (Option α)) (some a) = spec.singleLaw (some a) := by
      rw [tsum_eq_single a]
      · simp
      · intro b hb
        simp [hb.symm]
    rw [hsome]
    change spec.rejectProb * (spec.singleLaw (some a) * ∑ j ∈ Finset.range t, spec.rejectProb ^ j) +
      spec.singleLaw (some a) = _
    have hgeom : ∀ m : ℕ, (∑ j ∈ Finset.range m, spec.rejectProb ^ j) * spec.rejectProb + 1 =
        (∑ j ∈ Finset.range m, spec.rejectProb ^ j) + spec.rejectProb ^ m := fun m => by
      induction m with
      | zero => simp
      | succ k ihk =>
        rw [Finset.sum_range_succ, add_mul, add_right_comm _ _ 1, ihk, ← pow_succ, add_assoc]
    calc
      spec.rejectProb * (spec.singleLaw (some a) * ∑ j ∈ Finset.range t, spec.rejectProb ^ j) +
          spec.singleLaw (some a) =
          spec.singleLaw (some a) *
            ((∑ j ∈ Finset.range t, spec.rejectProb ^ j) * spec.rejectProb + 1) := by ring
      _ = spec.singleLaw (some a) *
            ((∑ j ∈ Finset.range t, spec.rejectProb ^ j) + spec.rejectProb ^ t) := by rw [hgeom t]

private theorem mul_geom_sum_eq_one_sub_pow {r : ℝ≥0∞} (hr : r ≤ 1) (t : ℕ) :
    (1 - r) * ∑ j ∈ Finset.range t, r ^ j = 1 - r ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hpow : r ^ t ≤ 1 := pow_le_one₀ zero_le hr
    have hpow_succ : r ^ (t + 1) ≤ r ^ t := by
      rw [pow_succ]
      exact mul_le_of_le_one_right' hr
    rw [Finset.sum_range_succ, mul_add, ih]
    have hterm : (1 - r) * r ^ t = r ^ t - r ^ (t + 1) := by
      rw [ENNReal.sub_mul (fun _ _ => ne_top_of_le_ne_top ENNReal.one_ne_top hpow), one_mul,
        pow_succ']
    rw [hterm]
    exact tsub_add_tsub_cancel hpow hpow_succ

/-- When a single trial outputs `some a` with probability `acceptProb * target a`, `t` trials
output `some a` with probability `(1 - rejectProb ^ t) * target a`. -/
theorem runTrials_some_of_singleLaw {spec : BlockRejectionSpec α} {target : PMF α}
    (h : ∀ a, spec.singleLaw (some a) = spec.acceptProb * target a) (t : ℕ) (a : α) :
    spec.runTrials t (some a) = (1 - spec.rejectProb ^ t) * target a := by
  rw [runTrials_some, h a, mul_right_comm, acceptProb,
    mul_geom_sum_eq_one_sub_pow spec.rejectProb_le_one t]

/-- Capped `t`-trial sampler substituting `fallback` if all `t` blocks reject. -/
@[expose] noncomputable def runCapped (spec : BlockRejectionSpec α) (fallback : α) (t : ℕ) :
    PMF α :=
  (spec.runTrials t).map fun o => o.getD fallback

theorem runCapped_apply [DecidableEq α] {spec : BlockRejectionSpec α} {target : PMF α}
    (h : ∀ a, spec.singleLaw (some a) = spec.acceptProb * target a)
    (fallback : α) (t : ℕ) (a : α) :
    spec.runCapped fallback t a =
      (1 - spec.rejectProb ^ t) * target a +
        if a = fallback then spec.rejectProb ^ t else 0 := by
  classical
  rw [runCapped, PMF.map_apply, tsum_option_eq]
  simp only [Option.getD_none, Option.getD_some, runTrials_none]
  rw [tsum_eq_single a]
  · simp only [↓reduceIte, runTrials_some_of_singleLaw h t a, add_comm]
  · intro b hb
    simp [hb.symm]

/-- Statistical distance between the capped fallback sampler and the target distribution is
`(rejectProb ^ t).toReal * (1 - (target fallback).toReal)`, hence at most
`(rejectProb ^ t).toReal`. -/
theorem dist_runCapped_eq [Fintype α] {spec : BlockRejectionSpec α} {target : PMF α}
    (h : ∀ a, spec.singleLaw (some a) = spec.acceptProb * target a)
    (fallback : α) (t : ℕ) :
    dist (spec.runCapped fallback t) target =
      (spec.rejectProb ^ t).toReal * (1 - (target fallback).toReal) := by
  classical
  set r := spec.rejectProb ^ t
  have hr1 : r ≤ 1 := pow_le_one₀ zero_le spec.rejectProb_le_one
  have hr_top : r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hr1
  have h1r_top : 1 - r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have h1r_toReal : (1 - r).toReal = 1 - r.toReal := by
    rw [ENNReal.toReal_sub_of_le hr1 ENNReal.one_ne_top, ENNReal.toReal_one]
  have hval (a : α) : (spec.runCapped fallback t a).toReal =
      (1 - r.toReal) * (target a).toReal + if a = fallback then r.toReal else 0 := by
    rw [runCapped_apply h fallback t a]
    by_cases haf : a = fallback
    · subst haf
      simp only [↓reduceIte]
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top h1r_top (PMF.apply_ne_top _ _)) hr_top,
        ENNReal.toReal_mul, h1r_toReal]
    · simp only [haf, ↓reduceIte, add_zero]
      rw [ENNReal.toReal_mul, h1r_toReal]
  rw [PMF.dist_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ fallback)]
  have hrest : ∑ b ∈ Finset.univ.erase fallback,
      |(spec.runCapped fallback t b).toReal - (target b).toReal| =
      r.toReal * ∑ b ∈ Finset.univ.erase fallback, (target b).toReal := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hne : b ≠ fallback := Finset.ne_of_mem_erase hb
    rw [hval b, ite_eq_right hne, add_zero,
      show (1 - r.toReal) * (target b).toReal - (target b).toReal =
        -(r.toReal * (target b).toReal) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
  have hsum :
      (target fallback).toReal + ∑ b ∈ Finset.univ.erase fallback, (target b).toReal = 1 := by
    rw [Finset.add_sum_erase _ (fun b => (target b).toReal) (Finset.mem_univ fallback)]
    exact PMF.sum_toReal target
  have hfb_le : (target fallback).toReal ≤ 1 := PMF.toReal_apply_le_one target fallback
  have hfb : |(spec.runCapped fallback t fallback).toReal - (target fallback).toReal| =
      r.toReal * (1 - (target fallback).toReal) := by
    rw [hval fallback, ite_eq_left rfl,
      show (1 - r.toReal) * (target fallback).toReal + r.toReal - (target fallback).toReal =
        r.toReal * (1 - (target fallback).toReal) by ring,
      abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (by linarith))]
  have herase : ∑ b ∈ Finset.univ.erase fallback, (target b).toReal =
      1 - (target fallback).toReal := by linarith
  rw [hfb, hrest, herase]
  ring

theorem dist_runCapped_le [Fintype α] {spec : BlockRejectionSpec α} {target : PMF α}
    (h : ∀ a, spec.singleLaw (some a) = spec.acceptProb * target a)
    (fallback : α) (t : ℕ) :
    dist (spec.runCapped fallback t) target ≤ (spec.rejectProb ^ t).toReal := by
  rw [dist_runCapped_eq h fallback t]
  have h0 : 0 ≤ (target fallback).toReal := ENNReal.toReal_nonneg
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg (by linarith)

/-! ### Unbounded `DDGTree` realization -/

/-- Exact discrete distribution generating tree executing `spec` on consecutive `width`-bit
blocks. -/
@[expose] def toDDGTree (spec : BlockRejectionSpec α) : DDGTree α where
  output w := spec.decodeTrials (w.length / spec.width) w
  output_append_singleton w a b h := by
    have hw : (w.length / spec.width) * spec.width ≤ w.length :=
      Nat.div_mul_le_self w.length spec.width
    have happ := decodeTrials_append_of_some hw h [b]
    have hle : w.length / spec.width ≤ (w ++ [b]).length / spec.width :=
      Nat.div_le_div_right (by simp)
    exact decodeTrials_mono_of_some hle happ

/-- Running `toDDGTree` on `n` fair bits has the exact law of `n / width` rejection trials. -/
theorem run_toDDGTree (spec : BlockRejectionSpec α) (n : ℕ) :
    spec.toDDGTree.run n = spec.runTrials (n / spec.width) := by
  set t := n / spec.width
  have ht : t * spec.width ≤ n := Nat.div_mul_le_self n spec.width
  unfold DDGTree.run runTrials
  rw [← BitString.uniformList_take ht, PMF.map_comp]
  apply PMF.map_congr_on_support
  intro w hw
  have hlen : w.length = n := BitString.length_of_mem_support_uniformList hw
  change spec.decodeTrials (w.length / spec.width) w =
    spec.decodeTrials t (w.take (t * spec.width))
  rw [hlen, decodeTrials_take]

/-- If `0 < width`, `acceptProb ≠ 0`, and accepted trials follow `target`, `toDDGTree` generates
`target` exactly. -/
theorem toDDGTree_generates {spec : BlockRejectionSpec α} {target : PMF α}
    (hw : 0 < spec.width) (hacc : spec.acceptProb ≠ 0)
    (h : ∀ a, spec.singleLaw (some a) = spec.acceptProb * target a) :
    spec.toDDGTree.Generates target := by
  intro a
  apply le_antisymm
  · refine iSup_le fun n => ?_
    rw [run_toDDGTree, runTrials_some_of_singleLaw h]
    exact mul_le_of_le_one_left' tsub_le_self
  · have hr_lt : spec.rejectProb < 1 := spec.rejectProb_lt_one_iff.mpr hacc
    have hpow : Tendsto (fun t : ℕ => spec.rejectProb ^ t) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr_lt
    have hsub : Tendsto (fun t : ℕ => (1 - spec.rejectProb ^ t) * target a) atTop
        (𝓝 ((1 - 0) * target a)) := by
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr (PMF.apply_ne_top target a))
      exact ENNReal.Tendsto.sub tendsto_const_nhds hpow (Or.inr ENNReal.zero_ne_top)
    rw [tsub_zero, one_mul] at hsub
    have hle : ∀ t : ℕ, (1 - spec.rejectProb ^ t) * target a ≤ spec.toDDGTree.outputProb a := by
      intro t
      have hdiv : (t * spec.width) / spec.width = t := Nat.mul_div_cancel t hw
      calc
        (1 - spec.rejectProb ^ t) * target a =
            spec.toDDGTree.run (t * spec.width) (some a) := by
          rw [run_toDDGTree, hdiv, runTrials_some_of_singleLaw h]
        _ ≤ spec.toDDGTree.outputProb a := spec.toDDGTree.run_le_outputProb _ a
    exact le_of_tendsto' hsub hle

/-- Closed-form expected fair-bit cost of `toDDGTree`: `(width : ℝ≥0∞) / acceptProb` whenever
`0 < width` (including `⊤` when `acceptProb = 0`). -/
theorem expectedFlips_toDDGTree (spec : BlockRejectionSpec α) (hw : 0 < spec.width) :
    spec.toDDGTree.expectedFlips = (spec.width : ℝ≥0∞) / spec.acceptProb := by
  unfold DDGTree.expectedFlips
  simp_rw [run_toDDGTree, runTrials_none]
  let e : ℕ × Fin spec.width ≃ ℕ :=
    { toFun := fun p => p.1 * spec.width + p.2.val
      invFun := fun n => (n / spec.width, ⟨n % spec.width, Nat.mod_lt n hw⟩)
      left_inv := fun ⟨q, r⟩ => by
        ext
        · dsimp only
          rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt r.isLt, Nat.add_zero]
        · dsimp only
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt r.isLt]
      right_inv := fun n => by
        dsimp only
        rw [Nat.mul_comm, Nat.div_add_mod] }
  rw [← e.tsum_eq]
  have hdiv : ∀ p : ℕ × Fin spec.width,
      (e p) / spec.width = p.1 := fun ⟨q, r⟩ => by
    change (q * spec.width + r.val) / spec.width = q
    rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt r.isLt, Nat.add_zero]
  simp_rw [hdiv]
  rw [tsum_prod']
  simp_rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ← one_sub_rejectProb, div_eq_mul_inv]

/-- When `0 < width` and `1 / 2 ≤ acceptProb`, `toDDGTree` reads at most `2 * width` fair bits in
expectation. -/
theorem expectedFlips_toDDGTree_le_two_mul {spec : BlockRejectionSpec α}
    (hw : 0 < spec.width) (hacc : (1 / 2 : ℝ≥0∞) ≤ spec.acceptProb) :
    spec.toDDGTree.expectedFlips ≤ 2 * (spec.width : ℝ≥0∞) := by
  rw [expectedFlips_toDDGTree spec hw, div_eq_mul_inv]
  have hinv : spec.acceptProb⁻¹ ≤ (1 / 2 : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.mpr hacc
  have htwo : (1 / 2 : ℝ≥0∞)⁻¹ = 2 := by
    rw [one_div, inv_inv]
  rw [htwo] at hinv
  calc
    (spec.width : ℝ≥0∞) * spec.acceptProb⁻¹ ≤ (spec.width : ℝ≥0∞) * 2 :=
      mul_le_mul_right hinv _
    _ = 2 * (spec.width : ℝ≥0∞) := mul_comm _ _

end BlockRejectionSpec

/-! ### Bounded integers (`Fin n`) -/

/-- Block-rejection specification for `Fin n` reading `k` bits per trial and keeping binary values
strictly below `n`. -/
@[expose] def finCutoffSpec (n k : ℕ) : BlockRejectionSpec (Fin n) where
  width := k
  attempt w :=
    if h : BitString.binaryValue w < n then some ⟨BitString.binaryValue w, h⟩ else none

/-- Exact block-rejection specification for `Fin n` reading `Nat.clog 2 n` bits per trial. -/
@[expose] def uniformFinRejectionSpec (n : ℕ) : BlockRejectionSpec (Fin n) :=
  finCutoffSpec n (Nat.clog 2 n)

/-- Dyadic bounded-integer rejection specification reading `Nat.log 2 n + 1` bits per trial
(`2 ^ width = dyadicSize n`), matching `UniformNat.dyadicSize`. -/
@[expose] def dyadicFinRejectionSpec (n : ℕ) : BlockRejectionSpec (Fin n) :=
  finCutoffSpec n (Nat.log 2 n + 1)

private theorem singleLaw_finCutoffSpec_some {n k : ℕ} (hnk : n ≤ 2 ^ k) (i : Fin n) :
    (finCutoffSpec n k).singleLaw (some i) = ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ := by
  let f : ℕ → Option (Fin n) := fun v => if h : v < n then some ⟨v, h⟩ else none
  have hmap : (finCutoffSpec n k).singleLaw =
      ((PMF.uniformOfFintype (Fin (2 ^ k))).map Fin.val).map f := by
    calc
      (finCutoffSpec n k).singleLaw =
          (BitString.uniformList k).map (f ∘ BitString.binaryValue) := rfl
      _ = ((BitString.uniformList k).map BitString.binaryValue).map f :=
        (PMF.map_comp _ _ _).symm
      _ = ((PMF.uniformOfFintype (Fin (2 ^ k))).map Fin.val).map f := by
        rw [BitString.uniformList_binaryValue]
  rw [hmap, PMF.map_comp, PMF.map_apply, tsum_fintype]
  have hi : i.val < 2 ^ k := lt_of_lt_of_le i.isLt hnk
  rw [Finset.sum_eq_single ⟨i.val, hi⟩]
  · simp [f, i.isLt, PMF.uniformOfFintype_apply]
  · intro j _ hj
    simp only [Function.comp_apply, f]
    by_cases hlt : j.val < n
    · simp only [hlt, ↓reduceDIte]
      split_ifs with heq
      · exfalso
        apply hj
        ext
        exact (congrArg Fin.val (Option.some.inj heq)).symm
      · rfl
    · simp [hlt]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

private theorem acceptProb_finCutoffSpec {n k : ℕ} (hnk : n ≤ 2 ^ k) :
    (finCutoffSpec n k).acceptProb = (n : ℝ≥0∞) / ((2 ^ k : ℕ) : ℝ≥0∞) := by
  have htotal := (finCutoffSpec n k).singleLaw.tsum_coe
  rw [tsum_option_eq, tsum_fintype] at htotal
  have hsum : ∑ i : Fin n, (finCutoffSpec n k).singleLaw (some i) =
      (n : ℝ≥0∞) / ((2 ^ k : ℕ) : ℝ≥0∞) := by
    simp_rw [singleLaw_finCutoffSpec_some hnk]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]
  rw [hsum] at htotal
  have hnone : (finCutoffSpec n k).rejectProb =
      1 - (n : ℝ≥0∞) / ((2 ^ k : ℕ) : ℝ≥0∞) :=
    ENNReal.eq_sub_of_add_eq
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top n) (by positivity)) htotal
  have hle : (n : ℝ≥0∞) / ((2 ^ k : ℕ) : ℝ≥0∞) ≤ 1 := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _)),
      one_mul]
    exact_mod_cast hnk
  rw [BlockRejectionSpec.acceptProb, hnone]
  exact ENNReal.sub_sub_cancel ENNReal.one_ne_top hle

private theorem singleLaw_finCutoffSpec_eq_mul {n k : ℕ} [NeZero n] (hnk : n ≤ 2 ^ k) (i : Fin n) :
    (finCutoffSpec n k).singleLaw (some i) =
      (finCutoffSpec n k).acceptProb * PMF.uniformOfFintype (Fin n) i := by
  rw [acceptProb_finCutoffSpec hnk, PMF.uniformOfFintype_apply, Fintype.card_fin,
    div_eq_mul_inv, mul_right_comm,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (NeZero.ne n)) (ENNReal.natCast_ne_top n),
    one_mul]
  exact singleLaw_finCutoffSpec_some hnk i

theorem acceptProb_uniformFinRejectionSpec (n : ℕ) :
    (uniformFinRejectionSpec n).acceptProb = (n : ℝ≥0∞) / ((2 ^ Nat.clog 2 n : ℕ) : ℝ≥0∞) :=
  acceptProb_finCutoffSpec (Nat.le_pow_clog Nat.one_lt_two n)

theorem singleLaw_uniformFinRejectionSpec_some (n : ℕ) [NeZero n] (i : Fin n) :
    (uniformFinRejectionSpec n).singleLaw (some i) =
      (uniformFinRejectionSpec n).acceptProb * PMF.uniformOfFintype (Fin n) i :=
  singleLaw_finCutoffSpec_eq_mul (Nat.le_pow_clog Nat.one_lt_two n) i

theorem one_half_le_acceptProb_uniformFinRejectionSpec (n : ℕ) [NeZero n] :
    (1 / 2 : ℝ≥0∞) ≤ (uniformFinRejectionSpec n).acceptProb := by
  rw [acceptProb_uniformFinRejectionSpec]
  have hpow : 2 ^ Nat.clog 2 n ≤ 2 * n := by
    by_cases hn1 : n ≤ 1
    · have : n = 1 := by have := NeZero.pos n; omega
      subst this
      simp
    · have hne : n - 1 ≠ 0 := by omega
      have hclog : Nat.clog 2 n ≤ Nat.log 2 (n - 1) + 1 := by
        rw [Nat.clog_le_iff_le_pow Nat.one_lt_two]
        have := Nat.lt_pow_succ_log_self Nat.one_lt_two (n - 1)
        omega
      have hle1 : 2 ^ Nat.clog 2 n ≤ 2 ^ (Nat.log 2 (n - 1) + 1) :=
        Nat.pow_le_pow_right (by decide) hclog
      have hle2 : 2 ^ Nat.log 2 (n - 1) ≤ n - 1 := Nat.pow_log_le_self 2 hne
      rw [pow_succ] at hle1
      omega
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _))]
  calc
    (1 / 2 : ℝ≥0∞) * ((2 ^ Nat.clog 2 n : ℕ) : ℝ≥0∞) ≤
        (1 / 2 : ℝ≥0∞) * ((2 * n : ℕ) : ℝ≥0∞) := by
      gcongr
    _ = (n : ℝ≥0∞) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, ← mul_assoc, one_div,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- After `t` trials of `uniformFinRejectionSpec n` (`n ≥ 1`), rejection probability is at most
`(1 / 2) ^ t`. -/
theorem runTrials_uniformFinRejectionSpec_none_le (n : ℕ) [NeZero n] (t : ℕ) :
    (uniformFinRejectionSpec n).runTrials t none ≤ (1 / 2 : ℝ≥0∞) ^ t := by
  rw [BlockRejectionSpec.runTrials_none]
  refine pow_le_pow_left' ?_ t
  have h1 := (uniformFinRejectionSpec n).acceptProb_add_rejectProb
  have h2 := one_half_le_acceptProb_uniformFinRejectionSpec n
  have hhalf : (1 : ℝ≥0∞) - 1 / 2 = 1 / 2 := by
    apply ENNReal.sub_eq_of_eq_add (by norm_num)
    rw [one_div, ENNReal.inv_two_add_inv_two]
  calc
    (uniformFinRejectionSpec n).rejectProb =
        1 - (uniformFinRejectionSpec n).acceptProb :=
      ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (by
        rw [← h1]; exact le_self_add)) ((add_comm _ _).trans h1)
    _ ≤ 1 - 1 / 2 := tsub_le_tsub_left h2 1
    _ = 1 / 2 := hhalf

/-- Root-leaf `DDGTree` outputting `0 : Fin n` without flipping any fair bits. -/
@[expose] def constZeroFinTree (n : ℕ) [NeZero n] : DDGTree (Fin n) where
  output _ := some ⟨0, NeZero.pos n⟩
  output_append_singleton _ _ _ h := h

/-- Exact `DDGTree` generating the uniform distribution on `Fin n`: `0` flips at `n = 1` and
`Nat.clog 2 n`-bit block rejection for `n ≥ 2`. -/
@[expose] def uniformFinTree (n : ℕ) [NeZero n] : DDGTree (Fin n) :=
  if n = 1 then constZeroFinTree n else (uniformFinRejectionSpec n).toDDGTree

theorem uniformFinTree_generates (n : ℕ) [NeZero n] :
    (uniformFinTree n).Generates (PMF.uniformOfFintype (Fin n)) := by
  unfold uniformFinTree
  split_ifs with hn1
  · subst hn1
    intro i
    have hi : i = ⟨0, NeZero.pos 1⟩ := Subsingleton.elim _ _
    subst hi
    have hrun : ∀ m, (constZeroFinTree 1).run m (some ⟨0, NeZero.pos 1⟩) = 1 := fun m => by
      rw [DDGTree.run_eq_pure_of_output_nil (T := constZeroFinTree 1) rfl m]
      simp
    rw [DDGTree.outputProb]
    simp_rw [hrun]
    simp [PMF.uniformOfFintype_apply]
  · have hn_gt : 1 < n := by have := NeZero.pos n; omega
    have hw : 0 < (uniformFinRejectionSpec n).width :=
      Nat.clog_pos Nat.one_lt_two hn_gt
    have hacc : (uniformFinRejectionSpec n).acceptProb ≠ 0 := by
      have hle := one_half_le_acceptProb_uniformFinRejectionSpec n
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hle)
    exact BlockRejectionSpec.toDDGTree_generates hw hacc
      (singleLaw_uniformFinRejectionSpec_some n)

theorem expectedFlips_uniformFinTree_of_two_le {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    (uniformFinTree n).expectedFlips =
      (Nat.clog 2 n : ℝ≥0∞) * ((2 ^ Nat.clog 2 n : ℕ) : ℝ≥0∞) / n := by
  have hn1 : n ≠ 1 := by omega
  unfold uniformFinTree
  rw [ite_eq_right hn1]
  have hw : 0 < (uniformFinRejectionSpec n).width :=
    Nat.clog_pos Nat.one_lt_two (by omega : 1 < n)
  rw [BlockRejectionSpec.expectedFlips_toDDGTree _ hw, acceptProb_uniformFinRejectionSpec]
  have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  change (Nat.clog 2 n : ℝ≥0∞) / ((n : ℝ≥0∞) / ((2 ^ Nat.clog 2 n : ℕ) : ℝ≥0∞)) = _
  rw [div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top _)), inv_inv,
    mul_comm (n : ℝ≥0∞)⁻¹, ← mul_assoc, ← div_eq_mul_inv]

/-- At any power of two `2 ^ k`, `uniformFinTree (2 ^ k)` reads `k` fair bits in expectation,
attaining the Knuth–Yao entropy lower bound. -/
theorem expectedFlips_uniformFinTree_two_pow (k : ℕ) :
    (uniformFinTree (2 ^ k)).expectedFlips = k := by
  cases k with
  | zero =>
    unfold uniformFinTree
    rw [ite_eq_left (by simp : 2 ^ 0 = 1), Nat.cast_zero, DDGTree.expectedFlips]
    have hrun : ∀ m, (constZeroFinTree (2 ^ 0)).run m none = 0 := fun m => by
      rw [DDGTree.run_eq_pure_of_output_nil (T := constZeroFinTree (2 ^ 0)) rfl m]
      simp
    simp_rw [hrun]
    exact tsum_zero
  | succ k =>
    have h2 : 2 ≤ 2 ^ (k + 1) := by
      rw [pow_succ]
      have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
      omega
    rw [expectedFlips_uniformFinTree_of_two_le h2, Nat.clog_pow _ _ Nat.one_lt_two,
      ENNReal.mul_div_cancel_right (by positivity) (ENNReal.natCast_ne_top _)]

/-- For every `n ≥ 1`, `uniformFinTree n` reads at most `2 * Nat.clog 2 n` fair bits in
expectation. -/
theorem expectedFlips_uniformFinTree_le (n : ℕ) [NeZero n] :
    (uniformFinTree n).expectedFlips ≤ 2 * (Nat.clog 2 n : ℝ≥0∞) := by
  unfold uniformFinTree
  split_ifs with hn1
  · subst hn1
    have hrun : ∀ m, (constZeroFinTree 1).run m none = 0 := fun m => by
      rw [DDGTree.run_eq_pure_of_output_nil (T := constZeroFinTree 1) rfl m]
      simp
    rw [DDGTree.expectedFlips]
    simp_rw [hrun]
    rw [tsum_zero]
    exact zero_le
  · have hn_gt : 1 < n := by have := NeZero.pos n; omega
    have hw : 0 < (uniformFinRejectionSpec n).width := Nat.clog_pos Nat.one_lt_two hn_gt
    exact BlockRejectionSpec.expectedFlips_toDDGTree_le_two_mul hw
      (one_half_le_acceptProb_uniformFinRejectionSpec n)

theorem singleLaw_dyadicFinRejectionSpec_some (n : ℕ) [NeZero n] (i : Fin n) :
    (dyadicFinRejectionSpec n).singleLaw (some i) =
      (dyadicFinRejectionSpec n).acceptProb * PMF.uniformOfFintype (Fin n) i :=
  singleLaw_finCutoffSpec_eq_mul (lt_dyadicSize n).le i

theorem dyadicFinRejectionSpec_generates (n : ℕ) [NeZero n] :
    (dyadicFinRejectionSpec n).toDDGTree.Generates (PMF.uniformOfFintype (Fin n)) := by
  have hacc_eq : (dyadicFinRejectionSpec n).acceptProb =
      (n : ℝ≥0∞) / ((2 ^ (Nat.log 2 n + 1) : ℕ) : ℝ≥0∞) :=
    acceptProb_finCutoffSpec (lt_dyadicSize n).le
  have hacc : (dyadicFinRejectionSpec n).acceptProb ≠ 0 := by
    rw [hacc_eq]
    exact ENNReal.div_ne_zero.mpr ⟨Nat.cast_ne_zero.mpr (NeZero.ne n), ENNReal.natCast_ne_top _⟩
  have hw : 0 < (dyadicFinRejectionSpec n).width := Nat.succ_pos (Nat.log 2 n)
  exact BlockRejectionSpec.toDDGTree_generates hw hacc
    (singleLaw_dyadicFinRejectionSpec_some n)

theorem runTrials_dyadicFinRejectionSpec_none_le (n : ℕ) [NeZero n] (t : ℕ) :
    (dyadicFinRejectionSpec n).runTrials t none ≤ (1 / 2 : ℝ≥0∞) ^ t := by
  have hacc_eq : (dyadicFinRejectionSpec n).acceptProb =
      (n : ℝ≥0∞) / ((2 ^ (Nat.log 2 n + 1) : ℕ) : ℝ≥0∞) :=
    acceptProb_finCutoffSpec (lt_dyadicSize n).le
  have hpow : 2 ^ (Nat.log 2 n + 1) ≤ 2 * n := by
    have h1 := Nat.pow_log_le_self 2 (NeZero.ne n)
    rw [pow_succ]
    omega
  rw [BlockRejectionSpec.runTrials_none]
  refine pow_le_pow_left' ?_ t
  have h1 := (dyadicFinRejectionSpec n).acceptProb_add_rejectProb
  have h2 : (1 / 2 : ℝ≥0∞) ≤ (dyadicFinRejectionSpec n).acceptProb := by
    rw [hacc_eq, ENNReal.le_div_iff_mul_le (Or.inl (by positivity))
      (Or.inl (ENNReal.natCast_ne_top _))]
    calc
      (1 / 2 : ℝ≥0∞) * ((2 ^ (Nat.log 2 n + 1) : ℕ) : ℝ≥0∞) ≤
          (1 / 2 : ℝ≥0∞) * ((2 * n : ℕ) : ℝ≥0∞) := by
        gcongr
      _ = (n : ℝ≥0∞) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, ← mul_assoc, one_div,
          ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  have hhalf : (1 : ℝ≥0∞) - 1 / 2 = 1 / 2 := by
    apply ENNReal.sub_eq_of_eq_add (by norm_num)
    rw [one_div, ENNReal.inv_two_add_inv_two]
  calc
    (dyadicFinRejectionSpec n).rejectProb =
        1 - (dyadicFinRejectionSpec n).acceptProb :=
      ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (by
        rw [← h1]; exact le_self_add)) ((add_comm _ _).trans h1)
    _ ≤ 1 - 1 / 2 := tsub_le_tsub_left h2 1
    _ = 1 / 2 := hhalf

/-! ### Subset rejection sampling -/

/-- Exact dyadic block-rejection sampler for a subset `S : Finset α` inside an indexed range
`enum : Fin m → α`. -/
@[expose] def subsetDyadicSpec {α : Type*} [DecidableEq α] (m : ℕ) (enum : Fin m → α)
    (S : Finset α) : BlockRejectionSpec α where
  width := Nat.log 2 m + 1
  attempt w :=
    if h : BitString.binaryValue w < m then
      let a := enum ⟨BitString.binaryValue w, h⟩
      if a ∈ S then some a else none
    else none

private theorem singleLaw_subsetDyadicSpec_some {α : Type*} [DecidableEq α] {m : ℕ}
    {enum : Fin m → α} (hinj : Function.Injective enum) {S : Finset α}
    (hcov : ∀ a ∈ S, ∃ i : Fin m, enum i = a) (a : α) :
    (subsetDyadicSpec m enum S).singleLaw (some a) =
      if a ∈ S then ((dyadicSize m : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  have hmk : m ≤ 2 ^ (Nat.log 2 m + 1) := (lt_dyadicSize m).le
  set K := 2 ^ (Nat.log 2 m + 1)
  let g : ℕ → Option α := fun v =>
    if h : v < m then (if enum ⟨v, h⟩ ∈ S then some (enum ⟨v, h⟩) else none) else none
  have hmap : (subsetDyadicSpec m enum S).singleLaw =
      ((PMF.uniformOfFintype (Fin K)).map Fin.val).map g := by
    calc
      (subsetDyadicSpec m enum S).singleLaw =
          (BitString.uniformList (Nat.log 2 m + 1)).map (g ∘ BitString.binaryValue) := rfl
      _ = ((BitString.uniformList (Nat.log 2 m + 1)).map BitString.binaryValue).map g :=
        (PMF.map_comp _ _ _).symm
      _ = ((PMF.uniformOfFintype (Fin K)).map Fin.val).map g := by
        rw [BitString.uniformList_binaryValue]
  rw [hmap, PMF.map_comp, PMF.map_apply, tsum_fintype]
  split_ifs with haS
  · obtain ⟨i, rfl⟩ := hcov a haS
    have hiK : i.val < K := lt_of_lt_of_le i.isLt hmk
    rw [Finset.sum_eq_single ⟨i.val, hiK⟩]
    · simp [g, i.isLt, haS, PMF.uniformOfFintype_apply, dyadicSize, K]
    · intro j _ hj
      simp only [Function.comp_apply, g]
      by_cases hlt : j.val < m
      · simp only [hlt, ↓reduceDIte]
        by_cases hmS : enum ⟨j.val, hlt⟩ ∈ S
        · simp only [hmS, ↓reduceIte]
          split_ifs with heq
          · exfalso
            apply hj
            ext
            exact (congrArg Fin.val (hinj (Option.some.inj heq))).symm
          · rfl
        · simp [hmS]
      · simp [hlt]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  · refine Finset.sum_eq_zero fun j _ => ?_
    simp only [Function.comp_apply, g]
    by_cases hlt : j.val < m
    · simp only [hlt, ↓reduceDIte]
      by_cases hmS : enum ⟨j.val, hlt⟩ ∈ S
      · simp only [hmS, ↓reduceIte]
        split_ifs with heq
        · exfalso
          exact haS (Option.some.inj heq ▸ hmS)
        · rfl
      · simp [hmS]
    · simp [hlt]

theorem acceptProb_subsetDyadicSpec {α : Type*} [DecidableEq α] {m : ℕ} {enum : Fin m → α}
    (hinj : Function.Injective enum) {S : Finset α}
    (hcov : ∀ a ∈ S, ∃ i : Fin m, enum i = a) :
    (subsetDyadicSpec m enum S).acceptProb =
      (S.card : ℝ≥0∞) / ((dyadicSize m : ℕ) : ℝ≥0∞) := by
  have hmk : m ≤ dyadicSize m := (lt_dyadicSize m).le
  have htotal := (subsetDyadicSpec m enum S).singleLaw.tsum_coe
  rw [tsum_option_eq] at htotal
  have hsum_some : ∑' a : α, (subsetDyadicSpec m enum S).singleLaw (some a) =
      (S.card : ℝ≥0∞) / ((dyadicSize m : ℕ) : ℝ≥0∞) := by
    simp_rw [singleLaw_subsetDyadicSpec_some hinj hcov]
    rw [tsum_eq_sum (s := S) fun a ha => by simp [ha], Finset.sum_ite_mem, Finset.inter_self,
      Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  rw [hsum_some] at htotal
  have hS_le_m : S.card ≤ m := by
    classical
    have hsub : S ⊆ Finset.univ.image enum := fun a ha => by
      obtain ⟨i, rfl⟩ := hcov a ha
      exact Finset.mem_image_of_mem enum (Finset.mem_univ i)
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  have hKpos : 0 < dyadicSize m := dyadicSize_pos m
  have hle1 : (S.card : ℝ≥0∞) / ((dyadicSize m : ℕ) : ℝ≥0∞) ≤ 1 := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl (Nat.cast_ne_zero.mpr hKpos.ne'))
      (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
    exact_mod_cast hS_le_m.trans hmk
  have hnone : (subsetDyadicSpec m enum S).rejectProb =
      1 - (S.card : ℝ≥0∞) / ((dyadicSize m : ℕ) : ℝ≥0∞) :=
    ENNReal.eq_sub_of_add_eq
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (Nat.cast_ne_zero.mpr hKpos.ne')) htotal
  rw [BlockRejectionSpec.acceptProb, hnone]
  exact ENNReal.sub_sub_cancel ENNReal.one_ne_top hle1

theorem subsetDyadicSpec_generates {α : Type*} [DecidableEq α] {m : ℕ} {enum : Fin m → α}
    (hinj : Function.Injective enum) {S : Finset α} (hS : S.Nonempty)
    (hcov : ∀ a ∈ S, ∃ i : Fin m, enum i = a) :
    (subsetDyadicSpec m enum S).toDDGTree.Generates (PMF.uniformOfFinset S hS) := by
  have hacc_eq := acceptProb_subsetDyadicSpec hinj hcov
  have hacc : (subsetDyadicSpec m enum S).acceptProb ≠ 0 := by
    rw [hacc_eq]
    exact ENNReal.div_ne_zero.mpr
      ⟨Nat.cast_ne_zero.mpr hS.card_ne_zero, ENNReal.natCast_ne_top _⟩
  have hw : 0 < (subsetDyadicSpec m enum S).width := Nat.succ_pos (Nat.log 2 m)
  refine BlockRejectionSpec.toDDGTree_generates hw hacc fun a => ?_
  rw [singleLaw_subsetDyadicSpec_some hinj hcov a, hacc_eq, PMF.uniformOfFinset_apply]
  split_ifs with haS
  · rw [div_eq_mul_inv, mul_right_comm,
      ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr hS.card_ne_zero) (ENNReal.natCast_ne_top _),
      one_mul]
  · rw [mul_zero]

theorem expectedFlips_subsetDyadicSpec {α : Type*} [DecidableEq α] {m : ℕ} {enum : Fin m → α}
    (hinj : Function.Injective enum) {S : Finset α} (hS : S.Nonempty)
    (hcov : ∀ a ∈ S, ∃ i : Fin m, enum i = a) :
    (subsetDyadicSpec m enum S).toDDGTree.expectedFlips =
      ((Nat.log 2 m + 1 : ℕ) : ℝ≥0∞) * ((dyadicSize m : ℕ) : ℝ≥0∞) / S.card := by
  have hw : 0 < (subsetDyadicSpec m enum S).width := Nat.succ_pos (Nat.log 2 m)
  rw [BlockRejectionSpec.expectedFlips_toDDGTree _ hw,
    acceptProb_subsetDyadicSpec hinj hcov]
  have hS0 : (S.card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hS.card_ne_zero
  change ((Nat.log 2 m + 1 : ℕ) : ℝ≥0∞) /
    ((S.card : ℝ≥0∞) / ((dyadicSize m : ℕ) : ℝ≥0∞)) = _
  rw [div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl hS0) (Or.inl (ENNReal.natCast_ne_top _)), inv_inv,
    mul_comm (S.card : ℝ≥0∞)⁻¹, ← mul_assoc, ← div_eq_mul_inv]

end Cslib.Probability
