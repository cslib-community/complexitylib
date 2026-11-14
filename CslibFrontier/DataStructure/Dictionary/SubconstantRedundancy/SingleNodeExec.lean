/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.RehashBounds
public import CslibFrontier.Languages.Probabilistic.Retry
import CslibFrontier.Foundations.Data.Finset.Density
import CslibFrontier.Probability.PMF.Uniform

/-!
# Good-Seed Oracle Interface and Single-Node `OracleComp` Reset Process

This file defines the good-seed resampling oracle (`GoodSeedQuery`, `goodSeedSpec`, `goodSeedLaw`),
proves the bounded rejection-sampling cost bridge (`expectedCost_retry_goodNodeSeed_le`), provides
general two-stage and coordinatewise `OracleComp.expectedCost` factorization helpers, and bounds the
single-node online seed-resampling process with forced ancestor resets (`singleNodeFresh`,
`expectedCost_singleNodeFresh_le`) for the multi-level dictionary tree of Tianxiao Li, Jingxun
Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary with Subconstant Wasted Bits per Key*
([LiLiangYuZhou2024, Section 5.5, Algorithm 4 and Lemma 5.3];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 34–35 / printed pp. 33–34).

## Main definitions

* `TreeSchedule.GoodSeedQuery`, `TreeSchedule.goodSeedSpec`, `TreeSchedule.goodSeedLaw`,
  `TreeSchedule.rehashWorkCost`, `TreeSchedule.levelRehashCost`: good-seed resampling oracle,
  uniform good-seed law, and work/count query costs.
* `TreeSchedule.queryGoodOrArb`, `TreeSchedule.singleNodeStep`, `TreeSchedule.singleNodeFresh`:
  single-node online `OracleComp` resampling process with forced reset flags.

## Main results

* `TreeSchedule.expectedCost_retry_goodNodeSeed_le`: bounded rejection sampling `OracleComp.retry`
  costs at most `2 * expectedCost trial` for every `fuel`.
* `TreeSchedule.expectedCost_singleNodeFresh_le`: single-node expected rehashes across arbitrary
  reset flags are bounded by `(1 + countResets evs) + 20 * unresetChanges s₀ evs / (nFloor L) ^ 2`.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

open scoped ENNReal

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Cslib.Probability
open Finset

namespace TreeSchedule

/-! ## Section 1: Good-Seed Oracle Interface and Rejection-Sampling Cost Bridge -/

/-- Oracle query requesting a good node seed at level `lvl ≤ P.depth` for an active primitive-ID
set `primSet` satisfying `P.nLow lvl ≤ #primSet ≤ P.nHigh lvl`. -/
structure GoodSeedQuery (P : TreeSchedule) where
  /-- Tree level `0 ≤ lvl ≤ P.depth` of the node being rehashed. -/
  lvl : ℕ
  /-- Level bound `lvl ≤ P.depth`. -/
  lvl_le : lvl ≤ P.depth
  /-- Active primitive-ID set routed to the node. -/
  primSet : Finset (P.PrimId lvl)
  /-- Occupancy window invariant `P.nLow lvl ≤ #primSet ≤ P.nHigh lvl`. -/
  card_bounds : P.nLow lvl ≤ #primSet ∧ #primSet ≤ P.nHigh lvl

/-- Good-seed oracle specification answering `q : P.GoodSeedQuery` with a seed satisfying
`P.IsGoodNodeSeed q.lvl g q.primSet`. -/
abbrev goodSeedSpec (P : TreeSchedule) : OracleSpec P.GoodSeedQuery :=
  fun q => { g : P.NodeSeed q.lvl // P.IsGoodNodeSeed q.lvl g q.primSet }

open Classical in
noncomputable instance instFintypeGoodSeedSpec (P : TreeSchedule) (q : P.GoodSeedQuery) :
    Fintype (P.goodSeedSpec q) :=
  Subtype.fintype _

/-- Uniform distribution over good node seeds answering `q : P.GoodSeedQuery` under
`P.ConcentrationReady` (`Algorithm 4`, lines 2–5). Note that `goodSeedLaw` models the post-condition
of successful rejection sampling (sampling directly from good seeds) without executing rejection
trials within `execHistory`. -/
noncomputable def goodSeedLaw (P : TreeSchedule) (hcr : P.ConcentrationReady)
    (q : P.GoodSeedQuery) : PMF (P.goodSeedSpec q) :=
  have : Nonempty (P.goodSeedSpec q) :=
    let ⟨g, hg⟩ := P.exists_isGoodNodeSeed hcr q.lvl_le q.primSet q.card_bounds.1 q.card_bounds.2
    ⟨⟨g, hg⟩⟩
  PMF.uniformOfFintype (P.goodSeedSpec q)

/-- Per-call rehashing work `2 * P.nFloor q.lvl` charged to a good-seed oracle call at level
`q.lvl`. This weight accounts for at most `2` expected rejection-sampling trials of cost
`nFloor q.lvl` (motivated by `expectedCost_retry_goodNodeSeed_le`), allowing `execHistory` to
charge the work of rejection sampling while querying the idealized `goodSeedLaw` oracle once. -/
noncomputable def rehashWorkCost (P : TreeSchedule) (q : P.GoodSeedQuery) : ℝ≥0∞ :=
  2 * (P.nFloor q.lvl : ℝ≥0∞)

/-- Indicator cost counting oracle calls specifically at level `ℓ`. -/
@[expose]
def levelRehashCost {P : TreeSchedule} (ℓ : ℕ) (q : P.GoodSeedQuery) : ℝ≥0∞ :=
  if q.lvl = ℓ then 1 else 0

theorem rehashWorkCost_eq_sum (P : TreeSchedule) :
    P.rehashWorkCost =
      ∑ ℓ ∈ Finset.range (P.depth + 1),
        fun q : P.GoodSeedQuery => 2 * (P.nFloor ℓ : ℝ≥0∞) * levelRehashCost ℓ q := by
  ext q
  rw [Finset.sum_apply, Finset.sum_eq_single q.lvl]
  · simp [rehashWorkCost, levelRehashCost]
  · intro b _ hb
    simp [levelRehashCost, hb.symm]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le q.lvl_le)))

open Classical in
/-- **Bounded rejection-sampling cost bridge (`Algorithm 4` Lines 2–5)**: for any `q :
P.GoodSeedQuery` under `P.ConcentrationReady` and any single-trial program `trial` whose output
distribution is `PMF.uniformOfFintype (P.NodeSeed q.lvl)`, `OracleComp.retry` incurs at most twice
the expected cost of one trial for every `fuel : ℕ`. -/
theorem expectedCost_retry_goodNodeSeed_le (P : TreeSchedule) (hcr : P.ConcentrationReady)
    (q : P.GoodSeedQuery) {ι : Type} {spec : OracleSpec ι}
    (h : (r : ι) → PMF (spec r)) (cost : ι → ℝ≥0∞)
    (trial : OracleComp spec (P.NodeSeed q.lvl))
    (htrial : OracleComp.evalWith h trial = PMF.uniformOfFintype (P.NodeSeed q.lvl))
    (fuel : ℕ) :
    OracleComp.expectedCost h cost
        (OracleComp.retry (fun g => P.IsGoodNodeSeed q.lvl g q.primSet) trial fuel) ≤
      2 * OracleComp.expectedCost h cost trial := by
  refine OracleComp.expectedCost_retry_le_two_mul _ _ _ _ ?_ fuel
  rw [htrial, Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype]
  have hnF6 := hcr.six_le_nFloor q.lvl q.lvl_le
  have h36 : 36 ≤ (P.nFloor q.lvl) ^ 2 := by nlinarith
  have hc_pos : 0 < Fintype.card (P.NodeSeed q.lvl) := Fintype.card_pos
  have hd := P.dens_not_isGoodNodeSeed_le hcr q.lvl_le q.primSet q.card_bounds.1 q.card_bounds.2
  rw [dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
    div_le_div_iff₀ (Nat.cast_pos.mpr hc_pos) (by positivity)] at hd
  have hd_nat : #(Finset.univ.filter fun g : P.NodeSeed q.lvl =>
      ¬ P.IsGoodNodeSeed q.lvl g q.primSet) * (P.nFloor q.lvl) ^ 2 ≤
      3 * Fintype.card (P.NodeSeed q.lvl) := by exact_mod_cast hd
  have h2bad : 2 * #(Finset.univ.filter fun g : P.NodeSeed q.lvl =>
      ¬ P.IsGoodNodeSeed q.lvl g q.primSet) ≤ Fintype.card (P.NodeSeed q.lvl) := by nlinarith
  have hfilt : (Finset.univ.filter (· ∈ {g : P.NodeSeed q.lvl |
      ¬ P.IsGoodNodeSeed q.lvl g q.primSet})) =
      Finset.univ.filter fun g => ¬ P.IsGoodNodeSeed q.lvl g q.primSet := rfl
  rw [hfilt]
  have hcard_ne : (Fintype.card (P.NodeSeed q.lvl) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr hc_pos.ne'
  have hcast : (2 : ℝ≥0∞) *
      (#(Finset.univ.filter fun g : P.NodeSeed q.lvl =>
        ¬ P.IsGoodNodeSeed q.lvl g q.primSet) : ℝ≥0∞) ≤
      (Fintype.card (P.NodeSeed q.lvl) : ℝ≥0∞) := by exact_mod_cast h2bad
  have hle_half : (#(Finset.univ.filter fun g : P.NodeSeed q.lvl =>
      ¬ P.IsGoodNodeSeed q.lvl g q.primSet) : ℝ≥0∞) ≤
      2⁻¹ * (Fintype.card (P.NodeSeed q.lvl) : ℝ≥0∞) :=
    calc (#(Finset.univ.filter fun g : P.NodeSeed q.lvl =>
          ¬ P.IsGoodNodeSeed q.lvl g q.primSet) : ℝ≥0∞)
        = 2⁻¹ * ((2 : ℝ≥0∞) * #(Finset.univ.filter fun g : P.NodeSeed q.lvl =>
            ¬ P.IsGoodNodeSeed q.lvl g q.primSet)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) ENNReal.ofNat_ne_top, one_mul]
      _ ≤ 2⁻¹ * (Fintype.card (P.NodeSeed q.lvl) : ℝ≥0∞) := by gcongr
  calc (#(Finset.univ.filter fun g : P.NodeSeed q.lvl =>
        ¬ P.IsGoodNodeSeed q.lvl g q.primSet) : ℝ≥0∞) *
        (Fintype.card (P.NodeSeed q.lvl) : ℝ≥0∞)⁻¹
      ≤ (2⁻¹ * (Fintype.card (P.NodeSeed q.lvl) : ℝ≥0∞)) *
          (Fintype.card (P.NodeSeed q.lvl) : ℝ≥0∞)⁻¹ := by gcongr
    _ = 2⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hcard_ne (ENNReal.natCast_ne_top _), mul_one]

/-! ## Section 2: General `OracleComp` Expectation Factorization Helpers -/

theorem isCostBounded_pi_unit {ι : Type} {spec : OracleSpec ι}
    {m : ℕ} {β : Fin m → Type} {programs : (i : Fin m) → OracleComp spec (β i)}
    (h1 : ∀ i, OracleComp.IsQueryBounded (programs i) 1) :
    OracleComp.IsQueryBounded (OracleComp.pi programs) m := by
  induction m with
  | zero =>
    rw [OracleComp.pi_zero]
    exact .pure _ 0
  | succ m ih =>
    rw [OracleComp.pi_succ]
    simpa only [Nat.add_comm 1 m] using
      (h1 0).bind fun _ =>
        (OracleComp.isCostBounded_map_iff _ _ m).mpr (ih fun i => h1 i.succ)

theorem tsum_evalWith_pi_coord {ι : Type} {spec : OracleSpec ι}
    (h : (q : ι) → PMF (spec q)) {m : ℕ} {β : Fin m → Type}
    (programs : (i : Fin m) → OracleComp spec (β i)) (i : Fin m) (f : β i → ℝ≥0∞) :
    (∑' r, OracleComp.evalWith h (OracleComp.pi programs) r * f (r i)) =
      ∑' a, OracleComp.evalWith h (programs i) a * f a := by
  classical
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    revert f
    refine Fin.cases ?_ (fun j => ?_) i <;> intro f
    · rw [OracleComp.pi_succ, OracleComp.evalWith_bind]
      simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right]
      rw [tsum_comm]
      have hstep0 : ∀ a0 : β 0,
          (∑' r, OracleComp.evalWith h (Fin.cons a0 <$> OracleComp.pi fun k => programs k.succ) r *
              f (r 0)) = f a0 := by
        intro a0
        have hsum :
            (∑' r, OracleComp.evalWith h
                (Fin.cons a0 <$> OracleComp.pi fun k => programs k.succ) r * f (r 0)) =
              ∑' rest : (k : Fin m) → β k.succ,
                OracleComp.evalWith h (OracleComp.pi fun k => programs k.succ) rest * f a0 := by
          simp only [OracleComp.evalWith_map, PMF.map_apply, ← ENNReal.tsum_mul_right]
          rw [tsum_comm]
          refine tsum_congr fun rest => ?_
          rw [tsum_eq_single (Fin.cons a0 rest) fun b hb => by simp [hb]]
          simp
        rw [hsum, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      refine tsum_congr fun a0 => ?_
      simp_rw [mul_assoc]
      rw [ENNReal.tsum_mul_left, hstep0 a0]
    · rw [OracleComp.pi_succ, OracleComp.evalWith_bind]
      simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right]
      rw [tsum_comm]
      have hstep : ∀ a0 : β 0,
          (∑' r, OracleComp.evalWith h (Fin.cons a0 <$> OracleComp.pi fun k => programs k.succ) r *
              f (r j.succ)) =
            ∑' rest : (k : Fin m) → β k.succ,
              OracleComp.evalWith h (OracleComp.pi fun k => programs k.succ) rest * f (rest j) := by
        intro a0
        simp only [OracleComp.evalWith_map, PMF.map_apply, ← ENNReal.tsum_mul_right]
        rw [tsum_comm]
        refine tsum_congr fun rest => ?_
        rw [tsum_eq_single (Fin.cons a0 rest) fun b hb => by simp [hb]]
        simp
      have hrew : (∑' a0, ∑' r, OracleComp.evalWith h (programs 0) a0 *
            (OracleComp.evalWith h (Fin.cons a0 <$> OracleComp.pi fun k => programs k.succ) r *
              f (r j.succ))) =
          ∑' a0, OracleComp.evalWith h (programs 0) a0 *
            (∑' a, OracleComp.evalWith h (programs j.succ) a * f a) := by
        refine tsum_congr fun a0 => ?_
        rw [ENNReal.tsum_mul_left, hstep a0, ih (fun k => programs k.succ) j]
      simp_rw [mul_assoc]
      rw [hrew, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Coordinatewise `OracleComp.pi` fold across a list of steps. -/
@[expose]
def runPiChain {ι Step : Type} {spec : OracleSpec ι} {m : ℕ} {β : Fin m → Type}
    (stepC : Step → (i : Fin m) → β i → OracleComp spec (β i)) :
    List Step → ((i : Fin m) → β i) → OracleComp spec ((i : Fin m) → β i)
  | [], b => pure b
  | s :: ss, b => OracleComp.pi (fun i => stepC s i (b i)) >>= runPiChain stepC ss

/-- Single-coordinate sequential fold across a list of steps. -/
@[expose]
def runCoordChain {ι Step : Type} {spec : OracleSpec ι} {γ : Type}
    (stepOne : Step → γ → OracleComp spec γ) : List Step → γ → OracleComp spec γ
  | [], c => pure c
  | s :: ss, c => stepOne s c >>= runCoordChain stepOne ss

theorem expectedCost_runPiChain {ι Step : Type} {spec : OracleSpec ι}
    (h : (q : ι) → PMF (spec q)) (cost : ι → ℝ≥0∞) {m : ℕ} {β : Fin m → Type}
    (stepC : Step → (i : Fin m) → β i → OracleComp spec (β i)) :
    ∀ (tr : List Step) (b : (i : Fin m) → β i),
      OracleComp.expectedCost h cost (runPiChain stepC tr b) =
        ∑ i : Fin m, OracleComp.expectedCost h cost (runCoordChain (fun s => stepC s i) tr (b i))
  | [], b => by simp [runPiChain, runCoordChain]
  | s :: ss, b => by
    dsimp only [runPiChain, runCoordChain]
    rw [OracleComp.expectedCost_bind, OracleComp.expectedCost_pi]
    simp_rw [expectedCost_runPiChain h cost stepC ss, Finset.mul_sum]
    rw [Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [OracleComp.expectedCost_bind]
    congr 1
    exact tsum_evalWith_pi_coord h (fun j => stepC s j (b j)) i
      fun c => OracleComp.expectedCost h cost (runCoordChain (fun s' => stepC s' i) ss c)

theorem expectedCost_pi_bind_runPiChain {ι Step : Type} {spec : OracleSpec ι}
    (h : (q : ι) → PMF (spec q)) (cost : ι → ℝ≥0∞) {m : ℕ} {β : Fin m → Type}
    (initC : (i : Fin m) → OracleComp spec (β i))
    (stepC : Step → (i : Fin m) → β i → OracleComp spec (β i)) (tr : List Step) :
    OracleComp.expectedCost h cost (OracleComp.pi initC >>= runPiChain stepC tr) =
      ∑ i : Fin m,
        OracleComp.expectedCost h cost (initC i >>= runCoordChain (fun s => stepC s i) tr) := by
  rw [OracleComp.expectedCost_bind, OracleComp.expectedCost_pi]
  simp_rw [expectedCost_runPiChain h cost stepC tr, Finset.mul_sum]
  rw [Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [OracleComp.expectedCost_bind]
  congr 1
  exact tsum_evalWith_pi_coord h initC i
    fun c => OracleComp.expectedCost h cost (runCoordChain (fun s' => stepC s' i) tr c)

/-- Recorded upstream step entry `(step, state, mask)` in a two-stage trace factorization. -/
structure TraceItem (Step α μ : Type) where
  /-- Input step value. -/
  step : Step
  /-- Post-step upstream state. -/
  state : α
  /-- Auxiliary mask emitted by the upstream step. -/
  mask : μ

/-- Interleaved execution of upstream `stepA` and downstream `stepB` over `List Step`. -/
@[expose]
def runInterleaved {ι Step α μ β : Type} {spec : OracleSpec ι}
    (stepA : Step → α → OracleComp spec (α × μ))
    (stepB : Step → α → μ → β → OracleComp spec β) :
    List Step → α → β → OracleComp spec (α × β)
  | [], a, b => pure (a, b)
  | st :: sts, a, b =>
    stepA st a >>= fun am =>
      stepB st am.1 am.2 b >>= fun b' =>
        runInterleaved stepA stepB sts am.1 b'

/-- Standalone upstream trace execution recording `TraceItem`s across `List Step`. -/
@[expose]
def runTraceA {ι Step α μ : Type} {spec : OracleSpec ι}
    (stepA : Step → α → OracleComp spec (α × μ)) :
    List Step → α → OracleComp spec (List (TraceItem Step α μ))
  | [], _ => pure []
  | st :: sts, a =>
    stepA st a >>= fun am =>
      runTraceA stepA sts am.1 >>= fun tr => pure (⟨st, am.1, am.2⟩ :: tr)

/-- Downstream execution conditioned on a fixed upstream trace `List (TraceItem Step α μ)`. -/
@[expose]
def runGivenTraceB {ι Step α μ β : Type} {spec : OracleSpec ι}
    (stepB : Step → α → μ → β → OracleComp spec β) :
    List (TraceItem Step α μ) → β → OracleComp spec β
  | [], b => pure b
  | item :: tr, b =>
    stepB item.step item.state item.mask b >>= runGivenTraceB stepB tr

theorem expectedCost_runInterleaved_eq {ι Step α μ β : Type} {spec : OracleSpec ι}
    (h : (q : ι) → PMF (spec q)) (cost : ι → ℝ≥0∞)
    (stepA : Step → α → OracleComp spec (α × μ))
    (stepB : Step → α → μ → β → OracleComp spec β) :
    ∀ (sts : List Step) (a : α) (b : β),
      OracleComp.expectedCost h cost (runInterleaved stepA stepB sts a b) =
        OracleComp.expectedCost h cost (runTraceA stepA sts a >>= fun tr =>
          runGivenTraceB stepB tr b)
  | [], a, b => by simp [runInterleaved, runTraceA, runGivenTraceB]
  | st :: sts, a, b => by
    dsimp only [runInterleaved, runTraceA]
    rw [OracleComp.expectedCost_bind, bind_assoc, OracleComp.expectedCost_bind]
    congr 1
    refine tsum_congr fun am => ?_
    congr 1
    rw [OracleComp.expectedCost_bind, bind_assoc, OracleComp.expectedCost_bind]
    simp_rw [pure_bind, expectedCost_runInterleaved_eq h cost stepA stepB sts am.1,
      OracleComp.expectedCost_bind]
    simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    rw [show OracleComp.expectedCost h cost (stepB st am.1 am.2 b) +
          (OracleComp.expectedCost h cost (runTraceA stepA sts am.1) +
            ∑' b', OracleComp.evalWith h (stepB st am.1 am.2 b) b' *
              ∑' tr, OracleComp.evalWith h (runTraceA stepA sts am.1) tr *
                OracleComp.expectedCost h cost (runGivenTraceB stepB tr b')) =
        OracleComp.expectedCost h cost (runTraceA stepA sts am.1) +
          (OracleComp.expectedCost h cost (stepB st am.1 am.2 b) +
            ∑' b', OracleComp.evalWith h (stepB st am.1 am.2 b) b' *
              ∑' tr, OracleComp.evalWith h (runTraceA stepA sts am.1) tr *
                OracleComp.expectedCost h cost (runGivenTraceB stepB tr b')) by ac_rfl]
    congr 1
    have hc1 : OracleComp.expectedCost h cost (stepB st am.1 am.2 b) =
        ∑' tr, OracleComp.evalWith h (runTraceA stepA sts am.1) tr *
          OracleComp.expectedCost h cost (stepB st am.1 am.2 b) := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    have hsw : (∑' b', OracleComp.evalWith h (stepB st am.1 am.2 b) b' *
          ∑' tr, OracleComp.evalWith h (runTraceA stepA sts am.1) tr *
            OracleComp.expectedCost h cost (runGivenTraceB stepB tr b')) =
        ∑' tr, OracleComp.evalWith h (runTraceA stepA sts am.1) tr *
          ∑' b', OracleComp.evalWith h (stepB st am.1 am.2 b) b' *
            OracleComp.expectedCost h cost (runGivenTraceB stepB tr b') := by
      simp only [← ENNReal.tsum_mul_left]
      rw [tsum_comm]
      exact tsum_congr fun tr => tsum_congr fun b' => by ac_rfl
    rw [hc1, hsw, ← tsum_add]
    refine tsum_congr fun tr => ?_
    rw [← mul_add]
    dsimp only [runGivenTraceB]
    rw [OracleComp.expectedCost_bind]

theorem expectedCost_init_runInterleaved_eq {ι Step α μ β : Type} {spec : OracleSpec ι}
    (h : (q : ι) → PMF (spec q)) (cost : ι → ℝ≥0∞)
    (p₀ : OracleComp spec α) (q₀ : α → OracleComp spec β)
    (stepA : Step → α → OracleComp spec (α × μ))
    (stepB : Step → α → μ → β → OracleComp spec β) (sts : List Step) :
    OracleComp.expectedCost h cost
        (p₀ >>= fun a₀ => q₀ a₀ >>= fun b₀ => runInterleaved stepA stepB sts a₀ b₀) =
      OracleComp.expectedCost h cost
        (p₀ >>= fun a₀ => runTraceA stepA sts a₀ >>= fun tr =>
          q₀ a₀ >>= runGivenTraceB stepB tr) := by
  rw [OracleComp.expectedCost_bind, OracleComp.expectedCost_bind]
  congr 1
  refine tsum_congr fun a₀ => ?_
  congr 1
  rw [OracleComp.expectedCost_bind, OracleComp.expectedCost_bind]
  simp_rw [expectedCost_runInterleaved_eq h cost stepA stepB sts a₀, OracleComp.expectedCost_bind]
  simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [show OracleComp.expectedCost h cost (q₀ a₀) +
        (OracleComp.expectedCost h cost (runTraceA stepA sts a₀) +
          ∑' b₀, OracleComp.evalWith h (q₀ a₀) b₀ *
            ∑' tr, OracleComp.evalWith h (runTraceA stepA sts a₀) tr *
              OracleComp.expectedCost h cost (runGivenTraceB stepB tr b₀)) =
      OracleComp.expectedCost h cost (runTraceA stepA sts a₀) +
        (OracleComp.expectedCost h cost (q₀ a₀) +
          ∑' b₀, OracleComp.evalWith h (q₀ a₀) b₀ *
            ∑' tr, OracleComp.evalWith h (runTraceA stepA sts a₀) tr *
              OracleComp.expectedCost h cost (runGivenTraceB stepB tr b₀)) by ac_rfl]
  congr 1
  have hc1 : OracleComp.expectedCost h cost (q₀ a₀) =
      ∑' tr, OracleComp.evalWith h (runTraceA stepA sts a₀) tr *
        OracleComp.expectedCost h cost (q₀ a₀) := by
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hsw : (∑' b₀, OracleComp.evalWith h (q₀ a₀) b₀ *
        ∑' tr, OracleComp.evalWith h (runTraceA stepA sts a₀) tr *
          OracleComp.expectedCost h cost (runGivenTraceB stepB tr b₀)) =
      ∑' tr, OracleComp.evalWith h (runTraceA stepA sts a₀) tr *
        ∑' b₀, OracleComp.evalWith h (q₀ a₀) b₀ *
          OracleComp.expectedCost h cost (runGivenTraceB stepB tr b₀) := by
    simp only [← ENNReal.tsum_mul_left]
    rw [tsum_comm]
    exact tsum_congr fun tr => tsum_congr fun b₀ => by ac_rfl
  rw [hc1, hsw]

/-! ## Section 3: Single-Node Online Process with Forced Resets -/

private theorem expectedRemRehashes_nonneg (P : TreeSchedule) (ℓ : ℕ) :
    ∀ (T : ℕ) (seq : Fin (T + 1) → Finset (P.PrimId ℓ)) (g : P.NodeSeed ℓ),
      0 ≤ P.expectedRemRehashes ℓ T seq g ∧ 0 ≤ P.expectedSubseqSuccesses ℓ T seq
  | 0, seq, _ => by
    classical
    refine ⟨le_refl 0, ?_⟩
    rw [P.expectedSubseqSuccesses_eq_one_add_avg_rem]
    simp [expectedRemRehashes]
  | m + 1, seq, g => by
    classical
    have ih := fun g' => expectedRemRehashes_nonneg P ℓ m (fun i => seq i.succ) g'
    have hrem_nn : ∀ g', 0 ≤ P.expectedRemRehashes ℓ (m + 1) seq g' := fun g' => by
      dsimp only [expectedRemRehashes]
      split_ifs
      · exact (ih g').1
      · exact (ih g').2
    refine ⟨hrem_nn g, ?_⟩
    rw [P.expectedSubseqSuccesses_eq_one_add_avg_rem]
    dsimp only
    have hsum_nn : (0 : ℝ) ≤ ∑ g' ∈ Finset.univ.filter
        (fun x : P.NodeSeed ℓ => P.IsGoodNodeSeed ℓ x (seq 0)),
        P.expectedRemRehashes ℓ (m + 1) seq g' :=
      Finset.sum_nonneg fun g' _ => hrem_nn g'
    have hdiv_nn : 0 ≤ (∑ g' ∈ Finset.univ.filter
        (fun x : P.NodeSeed ℓ => P.IsGoodNodeSeed ℓ x (seq 0)),
        P.expectedRemRehashes ℓ (m + 1) seq g') /
        (#(Finset.univ.filter fun x : P.NodeSeed ℓ => P.IsGoodNodeSeed ℓ x (seq 0)) : ℝ) :=
      div_nonneg hsum_nn (Nat.cast_nonneg _)
    linarith

/-- Node occupancy bounds `P.nLow L ≤ #s ≤ P.nHigh L` on `s : Finset (P.PrimId L)`. -/
abbrev validPrimBounds (P : TreeSchedule) (L : ℕ) (s : Finset (P.PrimId L)) : Prop :=
  P.nLow L ≤ #s ∧ #s ≤ P.nHigh L

/-- Query `goodSeedSpec` when `s` satisfies `validPrimBounds`, or return a fixed fallback seed. -/
@[expose]
noncomputable def queryGoodOrArb (P : TreeSchedule) (L : ℕ) (hL : L ≤ P.depth)
    (s : Finset (P.PrimId L)) : OracleComp P.goodSeedSpec (P.NodeSeed L) :=
  if hb : P.validPrimBounds L s then
    OracleComp.query (spec := P.goodSeedSpec) ⟨L, hL, s, hb⟩ >>= fun r => pure r.1
  else
    pure (Classical.choice (Fintype.card_pos_iff.mp Fintype.card_pos))

theorem isQueryBounded_queryGoodOrArb (P : TreeSchedule) (L : ℕ) (hL : L ≤ P.depth)
    (s : Finset (P.PrimId L)) :
    OracleComp.IsQueryBounded (P.queryGoodOrArb L hL s) 1 := by
  dsimp only [queryGoodOrArb]
  split_ifs with hb
  · have hq := OracleComp.IsCostBounded.query (spec := P.goodSeedSpec)
      (cost := fun _ => 1) (⟨L, hL, s, hb⟩ : P.GoodSeedQuery)
    simpa using hq.bind fun r =>
      OracleComp.IsCostBounded.pure (spec := P.goodSeedSpec) (cost := fun _ => 1) r.1 0
  · exact OracleComp.IsCostBounded.pure (spec := P.goodSeedSpec) (cost := fun _ => 1)
      (Classical.choice (Fintype.card_pos_iff.mp Fintype.card_pos)) 1

open Classical in
/-- Single-step node update: resamples when `ev.2 = true` (parent reset) or `g` fails on `ev.1`. -/
@[expose]
noncomputable def singleNodeStep (P : TreeSchedule) (L : ℕ) (hL : L ≤ P.depth)
    (ev : Finset (P.PrimId L) × Bool) (g : P.NodeSeed L) :
    OracleComp P.goodSeedSpec (P.NodeSeed L) :=
  if ev.2 || !decide (P.IsGoodNodeSeed L g ev.1) then
    P.queryGoodOrArb L hL ev.1
  else
    pure g

theorem isQueryBounded_singleNodeStep (P : TreeSchedule) (L : ℕ) (hL : L ≤ P.depth)
    (ev : Finset (P.PrimId L) × Bool) (g : P.NodeSeed L) :
    OracleComp.IsQueryBounded (P.singleNodeStep L hL ev g) 1 := by
  classical
  dsimp only [singleNodeStep]
  split_ifs
  · exact P.isQueryBounded_queryGoodOrArb L hL ev.1
  · exact OracleComp.IsCostBounded.pure _ 1

/-- Remaining single-node execution starting from seed `g` across `evs`. -/
@[expose]
noncomputable def singleNodeRem (P : TreeSchedule) (L : ℕ) (hL : L ≤ P.depth)
    (evs : List (Finset (P.PrimId L) × Bool)) (g : P.NodeSeed L) :
    OracleComp P.goodSeedSpec (P.NodeSeed L) :=
  runCoordChain (P.singleNodeStep L hL) evs g

/-- Freshly initialized single-node execution on `(s₀, evs)`. -/
@[expose]
noncomputable def singleNodeFresh (P : TreeSchedule) (L : ℕ) (hL : L ≤ P.depth)
    (s₀ : Finset (P.PrimId L)) (evs : List (Finset (P.PrimId L) × Bool)) :
    OracleComp P.goodSeedSpec (P.NodeSeed L) :=
  P.queryGoodOrArb L hL s₀ >>= P.singleNodeRem L hL evs

/-- Number of forced reset events (`p.2 = true`) in `evs`. -/
@[expose]
def countResets {α : Type*} (evs : List (α × Bool)) : ℕ :=
  (evs.filter fun p => p.2).length

/-- Number of active set changes on unreset (`p.2 = false`) steps of `(s₀, evs)`. -/
@[expose]
def unresetChanges {α : Type*} [DecidableEq α] : α → List (α × Bool) → ℕ
  | _, [] => 0
  | _, (s₁, true) :: rest => unresetChanges s₁ rest
  | s₀, (s₁, false) :: rest => (if s₁ = s₀ then 0 else 1) + unresetChanges s₁ rest

private theorem unresetChanges_of_all_false {α : Type*} [DecidableEq α] :
    ∀ (evs : List (α × Bool)) (s₀ : α), (∀ p ∈ evs, p.2 = false) →
      unresetChanges s₀ evs = listChanges s₀ (evs.map Prod.fst)
  | [], _, _ => rfl
  | (s₁, b) :: rest, s₀, hall => by
    obtain rfl : b = false := hall (s₁, b) List.mem_cons_self
    simp only [unresetChanges, List.map_cons, listChanges]
    rw [unresetChanges_of_all_false rest s₁ fun p hp => hall p (List.mem_cons_of_mem _ hp)]

private theorem unresetChanges_append_true {α : Type*} [DecidableEq α]
    (s_r : α) (sfx : List (α × Bool)) :
    ∀ (pfx : List (α × Bool)) (s₀ : α), (∀ p ∈ pfx, p.2 = false) →
      unresetChanges s₀ (pfx ++ (s_r, true) :: sfx) =
        unresetChanges s₀ pfx + unresetChanges s_r sfx
  | [], _, _ => by simp [unresetChanges]
  | (s₁, b) :: pfx, s₀, hall => by
    obtain rfl : b = false := hall (s₁, b) List.mem_cons_self
    dsimp only [List.cons_append, unresetChanges]
    rw [unresetChanges_append_true s_r sfx pfx s₁ fun p hp =>
      hall p (List.mem_cons_of_mem _ hp), Nat.add_assoc]

private theorem expectedCost_singleNode_noResets {P : TreeSchedule} (hcr : P.ConcentrationReady)
    {L : ℕ} (hL : L ≤ P.depth) :
    ∀ (evs : List (Finset (P.PrimId L) × Bool)) (s₀ : Finset (P.PrimId L)),
      P.validPrimBounds L s₀ →
      (∀ p ∈ evs, P.validPrimBounds L p.1 ∧ p.2 = false) →
      (∀ g : P.NodeSeed L,
        OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost L)
            (P.singleNodeRem L hL evs g) =
          ENNReal.ofReal
            (P.expectedRemRehashes L (evs.map Prod.fst).length
              (seqOfHeadList s₀ (evs.map Prod.fst)) g)) ∧
      OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost L)
          (P.singleNodeFresh L hL s₀ evs) =
        ENNReal.ofReal
          (P.expectedSubseqSuccesses L (evs.map Prod.fst).length
            (seqOfHeadList s₀ (evs.map Prod.fst)))
  | [], s₀, hs₀, _ => by
    classical
    have hrem : ∀ g, OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost L)
        (P.singleNodeRem L hL [] g) = 0 := fun g => by simp [singleNodeRem, runCoordChain]
    refine ⟨fun g => ?_, ?_⟩
    · change _ = ENNReal.ofReal (P.expectedRemRehashes L 0 (seqOfHeadList s₀ []) g)
      rw [hrem g]
      dsimp only [expectedRemRehashes]
      simp
    · dsimp only [singleNodeFresh, queryGoodOrArb]
      rw [dite_eq_left hs₀, bind_assoc, OracleComp.expectedCost_query_bind]
      simp only [pure_bind, levelRehashCost, ↓reduceIte, hrem, mul_zero, tsum_zero, add_zero]
      change 1 = ENNReal.ofReal (P.expectedSubseqSuccesses L 0 (seqOfHeadList s₀ []))
      rw [P.expectedSubseqSuccesses_eq_one_add_avg_rem]
      dsimp only [expectedRemRehashes]
      simp
  | (s₁, b) :: rest, s₀, hs₀, hall => by
    classical
    obtain ⟨hs₁, rfl⟩ := hall (s₁, b) List.mem_cons_self
    have hall_rest : ∀ p ∈ rest, P.validPrimBounds L p.1 ∧ p.2 = false :=
      fun p hp => hall p (List.mem_cons_of_mem _ hp)
    obtain ⟨ih_rem, ih_fresh⟩ := expectedCost_singleNode_noResets hcr hL rest s₁ hs₁ hall_rest
    have htail_seq : (fun i : Fin (rest.map Prod.fst).length.succ =>
        (seqOfHeadList s₀ (s₁ :: rest.map Prod.fst)) i.succ) =
        seqOfHeadList s₁ (rest.map Prod.fst) := by
      funext i
      cases i using Fin.cases <;> rfl
    have hrem : ∀ g : P.NodeSeed L,
        OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost L)
            (P.singleNodeRem L hL ((s₁, false) :: rest) g) =
          ENNReal.ofReal
            (P.expectedRemRehashes L (s₁ :: rest.map Prod.fst).length
              (seqOfHeadList s₀ (s₁ :: rest.map Prod.fst)) g) := by
      intro g
      dsimp only [singleNodeRem, runCoordChain, singleNodeStep, List.length_cons,
        expectedRemRehashes]
      have hc1 : seqOfHeadList s₀ (s₁ :: rest.map Prod.fst) 1 = s₁ := rfl
      rw [hc1, htail_seq]
      by_cases hg1 : P.IsGoodNodeSeed L g s₁
      · have hcond : (false || !decide (P.IsGoodNodeSeed L g s₁)) = false := by simp [hg1]
        rw [hcond]
        simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, ite_eq_left hg1]
        exact ih_rem g
      · have hcond : (false || !decide (P.IsGoodNodeSeed L g s₁)) = true := by simp [hg1]
        rw [hcond]
        simp only [↓reduceIte, ite_eq_right hg1]
        exact ih_fresh
    refine ⟨hrem, ?_⟩
    dsimp only [singleNodeFresh, queryGoodOrArb]
    rw [dite_eq_left hs₀, bind_assoc, OracleComp.expectedCost_query_bind]
    simp only [pure_bind, levelRehashCost, ↓reduceIte]
    let q₀ : P.GoodSeedQuery := ⟨L, hL, s₀, hs₀⟩
    let G₀ := Finset.univ.filter fun g : P.NodeSeed L => P.IsGoodNodeSeed L g s₀
    have hcard_q₀ : Fintype.card (P.goodSeedSpec q₀) = #G₀ := by
      simpa [G₀, q₀] using Fintype.card_subtype (fun g : P.NodeSeed L => P.IsGoodNodeSeed L g s₀)
    obtain ⟨g_wit, hg_wit⟩ := P.exists_isGoodNodeSeed hcr hL s₀ hs₀.1 hs₀.2
    have hG₀_pos : 0 < #G₀ := Finset.card_pos.mpr ⟨g_wit, mem_filter.mpr ⟨mem_univ _, hg_wit⟩⟩
    have : Nonempty (P.goodSeedSpec q₀) := ⟨⟨g_wit, hg_wit⟩⟩
    have hlaw_apply : ∀ a : P.goodSeedSpec q₀, P.goodSeedLaw hcr q₀ a = (#G₀ : ℝ≥0∞)⁻¹ := by
      intro a
      dsimp only [goodSeedLaw]
      rw [PMF.uniformOfFintype_apply, hcard_q₀]
    have hterm : ∀ a : P.goodSeedSpec q₀,
        P.goodSeedLaw hcr q₀ a *
          OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost L)
            (P.singleNodeRem L hL ((s₁, false) :: rest) a.1) =
          (#G₀ : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (P.expectedRemRehashes L (s₁ :: rest.map Prod.fst).length
              (seqOfHeadList s₀ (s₁ :: rest.map Prod.fst)) a.val) := by
      intro a
      rw [hlaw_apply a, ← hrem a.val]
    rw [tsum_fintype, Finset.sum_congr rfl fun a _ => hterm a, ← Finset.mul_sum]
    have hsum_sub : (∑ a : P.goodSeedSpec q₀,
        ENNReal.ofReal (P.expectedRemRehashes L (s₁ :: rest.map Prod.fst).length
          (seqOfHeadList s₀ (s₁ :: rest.map Prod.fst)) a.val)) =
        ∑ g ∈ G₀, ENNReal.ofReal (P.expectedRemRehashes L (s₁ :: rest.map Prod.fst).length
          (seqOfHeadList s₀ (s₁ :: rest.map Prod.fst)) g) :=
      Finset.sum_bij (fun (a : P.goodSeedSpec q₀) _ => a.val)
        (fun a _ => mem_filter.mpr ⟨mem_univ _, a.2⟩)
        (fun _ _ _ _ h => Subtype.ext h)
        (fun g hg => ⟨⟨g, (mem_filter.mp hg).2⟩, mem_univ _, rfl⟩)
        (fun _ _ => rfl)
    rw [hsum_sub, ← ENNReal.ofReal_sum_of_nonneg fun g _ =>
      (P.expectedRemRehashes_nonneg L _ _ g).1]
    rw [P.expectedSubseqSuccesses_eq_one_add_avg_rem]
    have h0_eq : seqOfHeadList s₀ (s₁ :: rest.map Prod.fst) 0 = s₀ := rfl
    change _ = ENNReal.ofReal
      (let G₀' := Finset.univ.filter fun g : P.NodeSeed L =>
        P.IsGoodNodeSeed L g (seqOfHeadList s₀ (s₁ :: rest.map Prod.fst) 0)
      1 + (∑ g ∈ G₀', P.expectedRemRehashes L (s₁ :: rest.map Prod.fst).length
        (seqOfHeadList s₀ (s₁ :: rest.map Prod.fst)) g) / (#G₀' : ℝ))
    dsimp only
    rw [h0_eq]
    have hsum_nn : 0 ≤ ∑ g ∈ G₀, P.expectedRemRehashes L (s₁ :: rest.map Prod.fst).length
        (seqOfHeadList s₀ (s₁ :: rest.map Prod.fst)) g :=
      Finset.sum_nonneg fun g _ => (P.expectedRemRehashes_nonneg L _ _ g).1
    have hG₀_real : (0 : ℝ) < #G₀ := Nat.cast_pos.mpr hG₀_pos
    rw [ENNReal.ofReal_add zero_le_one (div_nonneg hsum_nn hG₀_real.le), ENNReal.ofReal_one,
      ENNReal.ofReal_div_of_pos hG₀_real, ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul]

private theorem singleNode_split_at_true (P : TreeSchedule) (L : ℕ) (hL : L ≤ P.depth)
    (s_r : Finset (P.PrimId L)) (sfx : List (Finset (P.PrimId L) × Bool)) :
    ∀ (pfx : List (Finset (P.PrimId L) × Bool)), (∀ p ∈ pfx, p.2 = false) →
      (∀ g : P.NodeSeed L,
        P.singleNodeRem L hL (pfx ++ (s_r, true) :: sfx) g =
          (P.singleNodeRem L hL pfx g >>= fun _ => P.singleNodeFresh L hL s_r sfx)) ∧
      (∀ s₀ : Finset (P.PrimId L),
        P.singleNodeFresh L hL s₀ (pfx ++ (s_r, true) :: sfx) =
          (P.singleNodeFresh L hL s₀ pfx >>= fun _ => P.singleNodeFresh L hL s_r sfx))
  | [], _ => by
    classical
    have hrem0 : ∀ g : P.NodeSeed L,
        P.singleNodeRem L hL ([] ++ (s_r, true) :: sfx) g =
          (P.singleNodeRem L hL [] g >>= fun _ => P.singleNodeFresh L hL s_r sfx) := by
      intro g
      dsimp only [List.nil_append, singleNodeRem, runCoordChain, singleNodeStep]
      rw [Bool.true_or]
      simp only [↓reduceIte, pure_bind]
      rfl
    refine ⟨hrem0, fun s₀ => ?_⟩
    dsimp only [singleNodeFresh]
    rw [bind_assoc]
    exact congrArg _ (funext hrem0)
  | (s₁, b) :: pfx, hall => by
    classical
    obtain rfl : b = false := hall (s₁, b) List.mem_cons_self
    obtain ⟨ih_rem, ih_fresh⟩ :=
      P.singleNode_split_at_true L hL s_r sfx pfx fun p hp => hall p (List.mem_cons_of_mem _ hp)
    have hrem : ∀ g : P.NodeSeed L,
        P.singleNodeRem L hL ((s₁, false) :: pfx ++ (s_r, true) :: sfx) g =
          (P.singleNodeRem L hL ((s₁, false) :: pfx) g >>= fun _ =>
            P.singleNodeFresh L hL s_r sfx) := by
      intro g
      dsimp only [List.cons_append, singleNodeRem, runCoordChain, singleNodeStep]
      by_cases hg1 : P.IsGoodNodeSeed L g s₁
      · have hc : (false || !decide (P.IsGoodNodeSeed L g s₁)) = false := by simp [hg1]
        rw [hc]; simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]; exact ih_rem g
      · have hc : (false || !decide (P.IsGoodNodeSeed L g s₁)) = true := by simp [hg1]
        rw [hc]; simp only [↓reduceIte]
        exact ih_fresh s₁
    refine ⟨hrem, fun s₀ => ?_⟩
    dsimp only [singleNodeFresh]
    rw [bind_assoc]
    exact congrArg _ (funext hrem)

private theorem split_first_true {α : Type*} :
    ∀ (evs : List (α × Bool)),
      (∀ p ∈ evs, p.2 = false) ∨
        ∃ (pfx : List (α × Bool)) (s_r : α) (sfx : List (α × Bool)),
          evs = pfx ++ (s_r, true) :: sfx ∧ (∀ p ∈ pfx, p.2 = false)
  | [] => Or.inl fun _ h => False.elim (List.not_mem_nil h)
  | (s₁, true) :: rest =>
    Or.inr ⟨[], s₁, rest, rfl, fun _ h => False.elim (List.not_mem_nil h)⟩
  | (s₁, false) :: rest => by
    rcases split_first_true rest with hall | ⟨pfx, s_r, sfx, rfl, hpfx⟩
    · refine Or.inl fun p hp => ?_
      rcases List.mem_cons.mp hp with rfl | hm
      · rfl
      · exact hall p hm
    · refine Or.inr ⟨(s₁, false) :: pfx, s_r, sfx, rfl, fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hm
      · rfl
      · exact hpfx p hm

/-- **Single-node expected rehash bound with forced resets**: across any event sequence `evs` of
valid primitive-ID sets paired with forced parent-reset flags, `singleNodeFresh` makes at most
`(1 + countResets evs) + 20 * unresetChanges s₀ evs / (nFloor L) ^ 2` expected calls. -/
theorem expectedCost_singleNodeFresh_le {P : TreeSchedule} (hcr : P.ConcentrationReady)
    {L : ℕ} (hL : L ≤ P.depth) :
    ∀ (n : ℕ) (evs : List (Finset (P.PrimId L) × Bool)) (s₀ : Finset (P.PrimId L)),
      evs.length ≤ n →
      P.validPrimBounds L s₀ →
      (∀ p ∈ evs, P.validPrimBounds L p.1) →
      OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost L)
          (P.singleNodeFresh L hL s₀ evs) ≤
        ENNReal.ofReal
          ((1 + countResets evs : ℝ) +
            20 * (unresetChanges s₀ evs : ℝ) / (P.nFloor L : ℝ) ^ 2)
  | n, evs, s₀, hlen, hs₀, hevs => by
    rcases split_first_true evs with hall | ⟨pfx, s_r, sfx, hsplit, hpfx_false⟩
    · have hcr0 : countResets evs = 0 := by
        dsimp only [countResets]
        rw [List.filter_eq_nil_iff.mpr fun p hp => by simp [hall p hp]]; rfl
      rw [hcr0, Nat.cast_zero, add_zero, unresetChanges_of_all_false evs s₀ hall,
        (expectedCost_singleNode_noResets hcr hL evs s₀ hs₀
          (fun p hp => ⟨hevs p hp, hall p hp⟩)).2]
      exact ENNReal.ofReal_le_ofReal
        (P.expectedSubseqSuccesses_seqOfHeadList_le hcr hL s₀ (evs.map Prod.fst) hs₀ fun s hs => by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs; exact hevs p hp)
    · cases n with
      | zero =>
        have hl := hsplit ▸ hlen
        rw [List.length_append, List.length_cons] at hl
        omega
      | succ m =>
        rw [hsplit, (P.singleNode_split_at_true L hL s_r sfx pfx hpfx_false).2 s₀,
          OracleComp.expectedCost_bind]
        simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        have hpfx_all : ∀ p ∈ pfx, P.validPrimBounds L p.1 ∧ p.2 = false := fun p hp =>
          ⟨hevs p (hsplit ▸ List.mem_append_left _ hp), hpfx_false p hp⟩
        have hs_r : P.validPrimBounds L s_r :=
          hevs (s_r, true) (hsplit ▸ List.mem_append_right _ List.mem_cons_self)
        have hsfx_valid : ∀ p ∈ sfx, P.validPrimBounds L p.1 := fun p hp =>
          hevs p (hsplit ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hp))
        have hsfx_len : sfx.length ≤ m := by
          have hl := hsplit ▸ hlen
          rw [List.length_append, List.length_cons] at hl
          omega
        have hb_pfx : OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost L)
            (P.singleNodeFresh L hL s₀ pfx) ≤
            ENNReal.ofReal (1 + 20 * (unresetChanges s₀ pfx : ℝ) / (P.nFloor L : ℝ) ^ 2) := by
          rw [unresetChanges_of_all_false pfx s₀ hpfx_false,
            (expectedCost_singleNode_noResets hcr hL pfx s₀ hs₀ hpfx_all).2]
          exact ENNReal.ofReal_le_ofReal
            (P.expectedSubseqSuccesses_seqOfHeadList_le hcr hL s₀ (pfx.map Prod.fst) hs₀
              fun s hs => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs; exact (hpfx_all p hp).1)
        have hb_sfx := expectedCost_singleNodeFresh_le hcr hL m sfx s_r hsfx_len hs_r hsfx_valid
        have hres_eq : countResets (pfx ++ (s_r, true) :: sfx) = 1 + countResets sfx := by
          dsimp only [countResets]
          rw [List.filter_append, List.filter_eq_nil_iff.mpr fun p hp => by
            simp [hpfx_false p hp]]
          simp [Nat.add_comm]
        have hchg_eq := unresetChanges_append_true s_r sfx pfx s₀ hpfx_false
        have hsq_pos : (0 : ℝ) < (P.nFloor L : ℝ) ^ 2 :=
          sq_pos_of_pos (Nat.cast_pos.mpr (P.nFloor_pos L hL))
        have hnn1 : 0 ≤ 1 + 20 * (unresetChanges s₀ pfx : ℝ) / (P.nFloor L : ℝ) ^ 2 :=
          add_nonneg zero_le_one (div_nonneg (by positivity) hsq_pos.le)
        have hnn2 : 0 ≤ (1 + countResets sfx : ℝ) +
            20 * (unresetChanges s_r sfx : ℝ) / (P.nFloor L : ℝ) ^ 2 :=
          add_nonneg (by positivity) (div_nonneg (by positivity) hsq_pos.le)
        refine (add_le_add hb_pfx hb_sfx).trans ?_
        rw [← ENNReal.ofReal_add hnn1 hnn2, hres_eq, hchg_eq]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        push_cast
        ring
termination_by n => n

end TreeSchedule

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
