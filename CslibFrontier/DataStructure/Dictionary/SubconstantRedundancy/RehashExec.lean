/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.SeedTruncExec

/-!
# Unconditional `Lemma 5.3` Expected Rehashing Bound on Padded Update Histories

This file proves the truncation projection (`expectedCost_level_execTrunc_eq`), the unconditional
top-level (`hbase`) and parent-to-child (`hstep`) expected-rehash recurrences
(`expectedCost_execTruncHistory_zero_le`, `expectedCost_execTruncHistory_succ_le`), and the
unconditional `Lemma 5.3` expected rehashing work bound (`expectedCost_execSeedSteps_le`) across
arbitrary single-key sentinel-padded update chains for the subconstant-redundancy dictionary tree of
Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary with Subconstant
Wasted Bits per Key* ([LiLiangYuZhou2024, Section 5.5, Lemma 5.3];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 34–35 / printed pp. 33–34).

## Main definitions

* `TreeSchedule.traceMaskCount`: total count of node-rehash flags across a recorded upstream trace.

## Main results

* `TreeSchedule.expectedCost_level_execTrunc_eq`: level-`ℓ` expected rehash count of full-depth
  `execSeedSteps` equals that of level-`ℓ` truncated `execTruncHistory`.
* `TreeSchedule.expectedCost_execTruncHistory_zero_le`,
  `TreeSchedule.expectedCost_execTruncHistory_succ_le`: unconditional `hbase` and `hstep`
  recurrence bounds on expected rehash counts.
* `TreeSchedule.expectedCost_execSeedSteps_le`: unconditional `14 * (depth + 1) * (cap + M)`
  expected rehashing work bound across initialization and `M` single-key padded updates.

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

/-! ## Section 1: Level Projection and Trace Rehash-Count Identity -/

private theorem tsum_pmf_bind_mul {α β : Type*} (p : PMF α) (f : α → PMF β) (g : β → ℝ≥0∞) :
    (∑' b, (p.bind f) b * g b) = ∑' a, p a * ∑' b, f a b * g b := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right, mul_assoc]
  rw [tsum_comm]
  exact tsum_congr fun _ => ENNReal.tsum_mul_left

private theorem tsum_pmf_pure_mul {α : Type*} (a : α) (g : α → ℝ≥0∞) :
    (∑' x, (PMF.pure a : PMF α) x * g x) = g a := by
  classical
  rw [tsum_eq_single a fun b hb => by rw [PMF.pure_apply_of_ne _ _ hb, zero_mul],
    PMF.pure_apply_self, one_mul]

private theorem expectedCost_queryGoodOrArb_eq_zero {P : TreeSchedule}
    (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q))
    {cost : P.GoodSeedQuery → ℝ≥0∞} {L : ℕ} (hL : L ≤ P.depth)
    (hc : ∀ q : P.GoodSeedQuery, q.lvl = L → cost q = 0) (s : Finset (P.PrimId L)) :
    OracleComp.expectedCost h cost (P.queryGoodOrArb L hL s) = 0 := by
  dsimp only [queryGoodOrArb]
  split_ifs with hb
  · rw [OracleComp.expectedCost_query_bind, hc _ rfl]
    simp
  · simp

private theorem expectedCost_singleNodeStep_eq_zero {P : TreeSchedule}
    (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q))
    {cost : P.GoodSeedQuery → ℝ≥0∞} {L : ℕ} (hL : L ≤ P.depth)
    (hc : ∀ q : P.GoodSeedQuery, q.lvl = L → cost q = 0)
    (ev : Finset (P.PrimId L) × Bool) (g : P.NodeSeed L) :
    OracleComp.expectedCost h cost (P.singleNodeStep L hL ev g) = 0 := by
  classical
  dsimp only [singleNodeStep]
  split_ifs
  · exact expectedCost_queryGoodOrArb_eq_zero h hL hc ev.1
  · simp

private theorem expectedCost_runTruncSteps_succ_of_cost_zero {P : TreeSchedule}
    (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q))
    {cost : P.GoodSeedQuery → ℝ≥0∞} {m : ℕ} (hm1 : m + 1 ≤ P.depth)
    (hc : ∀ q : P.GoodSeedQuery, q.lvl = m + 1 → cost q = 0) :
    ∀ (sts : List P.PaddedStep) (ts : P.TruncSeeds (m + 1)),
      OracleComp.expectedCost h cost (P.runTruncSteps (m + 1) hm1 sts ts) =
        OracleComp.expectedCost h cost (P.runTruncSteps m (Nat.le_of_succ_le hm1) sts ts.restrict)
  | [], _ => by simp [runTruncSteps]
  | st :: sts, ts => by
    dsimp only [runTruncSteps, stepTrunc]
    rw [bind_assoc, OracleComp.expectedCost_bind, OracleComp.expectedCost_bind]
    congr 1
    refine tsum_congr fun am => ?_
    congr 1
    rw [bind_assoc, OracleComp.expectedCost_bind, OracleComp.expectedCost_pi]
    have hpi0 : (∑ v : Fin (P.numNodes (m + 1)), OracleComp.expectedCost h cost
        (P.singleNodeStep (m + 1) hm1
          (am.1.toFull.primSetAt st.postSet (m + 1) hm1 v, am.2 (P.parentNode m v))
          (ts.lastRow hm1 v))) = 0 :=
      Finset.sum_eq_zero fun v _ => expectedCost_singleNodeStep_eq_zero h hm1 hc _ _
    rw [hpi0, zero_add]
    simp_rw [pure_bind, expectedCost_runTruncSteps_succ_of_cost_zero h hm1 hc sts,
      TruncSeeds.restrict_extend, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

private theorem expectedCost_execTruncHistory_succ_of_cost_zero {P : TreeSchedule}
    (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q))
    {cost : P.GoodSeedQuery → ℝ≥0∞} {m : ℕ} (hm1 : m + 1 ≤ P.depth)
    (hc : ∀ q : P.GoodSeedQuery, q.lvl = m + 1 → cost q = 0)
    (S₀ : Finset (Fin P.paddedUniv)) (sts : List P.PaddedStep) :
    OracleComp.expectedCost h cost (P.execTruncHistory (m + 1) hm1 S₀ sts) =
      OracleComp.expectedCost h cost (P.execTruncHistory m (Nat.le_of_succ_le hm1) S₀ sts) := by
  dsimp only [execTruncHistory, initTrunc]
  rw [bind_assoc, OracleComp.expectedCost_bind, OracleComp.expectedCost_bind]
  congr 1
  refine tsum_congr fun anc => ?_
  congr 1
  rw [bind_assoc, OracleComp.expectedCost_bind, OracleComp.expectedCost_pi]
  have hpi0 : (∑ v : Fin (P.numNodes (m + 1)), OracleComp.expectedCost h cost
      (P.queryGoodOrArb (m + 1) hm1 (anc.toFull.primSetAt S₀ (m + 1) hm1 v))) = 0 :=
    Finset.sum_eq_zero fun v _ => expectedCost_queryGoodOrArb_eq_zero h hm1 hc _
  rw [hpi0, zero_add]
  simp_rw [pure_bind, expectedCost_runTruncSteps_succ_of_cost_zero h hm1 hc sts,
    TruncSeeds.restrict_extend, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **Truncation projection**: for every `ℓ ≤ P.depth`, the expected level-`ℓ` rehash count of
full-depth `execSeedSteps S₀ sts` equals that of level-`ℓ` truncated `execTruncHistory ℓ hℓ S₀ sts`.
-/
theorem expectedCost_level_execTrunc_eq {P : TreeSchedule}
    (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q))
    {ℓ : ℕ} (hℓ : ℓ ≤ P.depth) (S₀ : Finset (Fin P.paddedUniv)) (sts : List P.PaddedStep) :
    OracleComp.expectedCost h (levelRehashCost ℓ) (P.execSeedSteps S₀ sts) =
      OracleComp.expectedCost h (levelRehashCost ℓ) (P.execTruncHistory ℓ hℓ S₀ sts) := by
  have hexec : OracleComp.expectedCost h (levelRehashCost ℓ) (P.execSeedSteps S₀ sts) =
      OracleComp.expectedCost h (levelRehashCost ℓ) (P.execTruncHistory P.depth le_rfl S₀ sts) := by
    dsimp only [execSeedSteps]
    rw [OracleComp.expectedCost_bind]
    simp
  rw [hexec]
  have hdesc : ∀ (m : ℕ), ℓ ≤ m → (hm : m ≤ P.depth) →
      OracleComp.expectedCost h (levelRehashCost ℓ) (P.execTruncHistory m hm S₀ sts) =
        OracleComp.expectedCost h (levelRehashCost ℓ) (P.execTruncHistory ℓ hℓ S₀ sts) := by
    intro m
    induction m with
    | zero =>
      intro hle _
      obtain rfl := Nat.eq_zero_of_le_zero hle
      rfl
    | succ m ih =>
      intro hle hm1
      by_cases hlm : ℓ ≤ m
      · rw [expectedCost_execTruncHistory_succ_of_cost_zero h hm1
          (fun q hq => by
            dsimp only [levelRehashCost]
            rw [hq, ite_eq_right (by omega)]),
          ih hlm (Nat.le_of_succ_le hm1)]
      · have heq : ℓ = m + 1 := by omega
        subst heq
        rfl
  exact hdesc P.depth hℓ le_rfl

private theorem expectedCost_initTrunc_zero_above {P : TreeSchedule}
    (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q)) :
    ∀ {ℓ L : ℕ} (hℓ : ℓ ≤ P.depth), ℓ < L → ∀ S₀ : Finset (Fin P.paddedUniv),
      OracleComp.expectedCost h (levelRehashCost L) (P.initTrunc ℓ hℓ S₀) = 0
  | 0, L, h0, hlt, S₀ => by
    dsimp only [initTrunc]
    rw [OracleComp.expectedCost_bind, OracleComp.expectedCost_pi]
    have h0' : (∑ _ : Fin (P.numNodes 0), OracleComp.expectedCost h (levelRehashCost L)
        (P.queryGoodOrArb 0 h0 (P.primSetZero S₀))) = 0 :=
      Finset.sum_eq_zero fun _ _ => expectedCost_queryGoodOrArb_eq_zero h h0
        (fun q hq => by dsimp only [levelRehashCost]; rw [hq, ite_eq_right (by omega)]) _
    rw [h0']
    simp
  | ℓ + 1, L, hℓ1, hlt, S₀ => by
    dsimp only [initTrunc]
    rw [OracleComp.expectedCost_bind,
      expectedCost_initTrunc_zero_above h (Nat.le_of_succ_le hℓ1) (by omega), zero_add]
    have hcont : ∀ anc : P.TruncSeeds ℓ,
        OracleComp.expectedCost h (levelRehashCost L)
          (OracleComp.pi (fun v : Fin (P.numNodes (ℓ + 1)) =>
            P.queryGoodOrArb (ℓ + 1) hℓ1 (anc.toFull.primSetAt S₀ (ℓ + 1) hℓ1 v)) >>=
            fun row => pure (anc.extend row)) = 0 := fun anc => by
      rw [OracleComp.expectedCost_bind, OracleComp.expectedCost_pi]
      have h0' : (∑ v : Fin (P.numNodes (ℓ + 1)), OracleComp.expectedCost h (levelRehashCost L)
          (P.queryGoodOrArb (ℓ + 1) hℓ1 (anc.toFull.primSetAt S₀ (ℓ + 1) hℓ1 v))) = 0 :=
        Finset.sum_eq_zero fun _ _ => expectedCost_queryGoodOrArb_eq_zero h hℓ1
          (fun q hq => by dsimp only [levelRehashCost]; rw [hq, ite_eq_right (by omega)]) _
      rw [h0']
      simp
    simp_rw [hcont, mul_zero, tsum_zero]

private theorem expectedCost_stepTrunc_zero_above {P : TreeSchedule}
    (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q)) :
    ∀ {ℓ L : ℕ} (hℓ : ℓ ≤ P.depth), ℓ < L → ∀ (st : P.PaddedStep) (ts : P.TruncSeeds ℓ),
      OracleComp.expectedCost h (levelRehashCost L) (P.stepTrunc ℓ hℓ st ts) = 0
  | 0, L, h0, hlt, st, ts => by
    dsimp only [stepTrunc]
    rw [OracleComp.expectedCost_bind, OracleComp.expectedCost_pi]
    have h0' : (∑ u : Fin (P.numNodes 0), OracleComp.expectedCost h (levelRehashCost L)
        (P.singleNodeStep 0 h0 (P.primSetZero st.postSet, false)
          (ts.seed 0 le_rfl h0 u))) = 0 :=
      Finset.sum_eq_zero fun _ _ => expectedCost_singleNodeStep_eq_zero h h0
        (fun q hq => by dsimp only [levelRehashCost]; rw [hq, ite_eq_right (by omega)]) _ _
    rw [h0']
    simp
  | ℓ + 1, L, hℓ1, hlt, st, ts => by
    classical
    dsimp only [stepTrunc]
    rw [OracleComp.expectedCost_bind,
      expectedCost_stepTrunc_zero_above h (Nat.le_of_succ_le hℓ1) (by omega), zero_add]
    have hcont : ∀ am : P.TruncSeeds ℓ × (Fin (P.numNodes ℓ) → Bool),
        OracleComp.expectedCost h (levelRehashCost L)
          (OracleComp.pi (fun v : Fin (P.numNodes (ℓ + 1)) =>
            P.singleNodeStep (ℓ + 1) hℓ1
              (am.1.toFull.primSetAt st.postSet (ℓ + 1) hℓ1 v, am.2 (P.parentNode ℓ v))
              (ts.lastRow hℓ1 v)) >>=
            fun row_new =>
              pure (am.1.extend row_new, fun v =>
                am.2 (P.parentNode ℓ v) ||
                  !decide (P.IsGoodNodeSeed (ℓ + 1) (ts.lastRow hℓ1 v)
                    (am.1.toFull.primSetAt st.postSet (ℓ + 1) hℓ1 v)))) = 0 := fun am => by
      rw [OracleComp.expectedCost_bind, OracleComp.expectedCost_pi]
      have h0' : (∑ v : Fin (P.numNodes (ℓ + 1)), OracleComp.expectedCost h (levelRehashCost L)
          (P.singleNodeStep (ℓ + 1) hℓ1
            (am.1.toFull.primSetAt st.postSet (ℓ + 1) hℓ1 v, am.2 (P.parentNode ℓ v))
            (ts.lastRow hℓ1 v))) = 0 :=
        Finset.sum_eq_zero fun _ _ => expectedCost_singleNodeStep_eq_zero h hℓ1
          (fun q hq => by dsimp only [levelRehashCost]; rw [hq, ite_eq_right (by omega)]) _ _
      rw [h0']
      simp
    simp_rw [hcont, mul_zero, tsum_zero]

private theorem expectedCost_runTraceA_zero_above {P : TreeSchedule}
    (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q)) {ℓ L : ℕ} (hℓ : ℓ ≤ P.depth)
    (hlt : ℓ < L) :
    ∀ (sts : List P.PaddedStep) (a : P.TruncSeeds ℓ),
      OracleComp.expectedCost h (levelRehashCost L) (runTraceA (P.stepTrunc ℓ hℓ) sts a) = 0
  | [], _ => by simp [runTraceA]
  | st :: sts, a => by
    dsimp only [runTraceA]
    rw [OracleComp.expectedCost_bind, expectedCost_stepTrunc_zero_above h hℓ hlt]
    simp_rw [OracleComp.expectedCost_bind, expectedCost_runTraceA_zero_above h hℓ hlt sts]
    simp

private theorem mem_support_of_evalWith_ne_zero {ι : Type} {spec : OracleSpec ι} {α : Type}
    {h : (q : ι) → PMF (spec q)} {prog : OracleComp spec α} {a : α}
    (hne : OracleComp.evalWith h prog a ≠ 0) : a ∈ prog.support :=
  OracleComp.supportWith_mono (fun _ _ _ => trivial) prog
    ((OracleComp.support_evalWith h prog) ▸ (PMF.mem_support_iff _ a).mpr hne)

/-- Total number of `true` node-rehash flags across a recorded trace `tr`. -/
def traceMaskCount {Step α : Type} {N : ℕ}
    (tr : List (TraceItem Step α (Fin N → Bool))) : ℕ :=
  (tr.map fun item => ∑ p : Fin N, if item.mask p then 1 else 0).sum

private theorem expectedCost_queryGoodOrArb_self {P : TreeSchedule}
    (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q)) {L : ℕ} (hL : L ≤ P.depth)
    {s : Finset (P.PrimId L)} (hb : P.validPrimBounds L s) :
    OracleComp.expectedCost h (levelRehashCost L) (P.queryGoodOrArb L hL s) = 1 := by
  dsimp only [queryGoodOrArb]
  rw [dite_eq_left hb, OracleComp.expectedCost_query_bind]
  simp [levelRehashCost]

private theorem expectedCost_initTrunc_self {P : TreeSchedule}
    (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q)) :
    ∀ (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) {S₀ : Finset (Fin P.paddedUniv)},
      P.validRootBounds S₀ →
      OracleComp.expectedCost h (levelRehashCost ℓ) (P.initTrunc ℓ hℓ S₀) = P.numNodes ℓ
  | 0, h0, S₀, hS₀ => by
    dsimp only [initTrunc]
    rw [OracleComp.expectedCost_bind, OracleComp.expectedCost_pi]
    simp_rw [expectedCost_queryGoodOrArb_self h h0 (P.validPrimBounds_primSetZero_of_root hS₀)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    simp
  | ℓ + 1, hℓ1, S₀, hS₀ => by
    dsimp only [initTrunc]
    rw [OracleComp.expectedCost_bind,
      expectedCost_initTrunc_zero_above h (Nat.le_of_succ_le hℓ1) (Nat.lt_succ_self ℓ), zero_add]
    have hterm : ∀ anc : P.TruncSeeds ℓ,
        OracleComp.evalWith h (P.initTrunc ℓ (Nat.le_of_succ_le hℓ1) S₀) anc *
          OracleComp.expectedCost h (levelRehashCost (ℓ + 1))
            (OracleComp.pi (fun v : Fin (P.numNodes (ℓ + 1)) =>
              P.queryGoodOrArb (ℓ + 1) hℓ1 (anc.toFull.primSetAt S₀ (ℓ + 1) hℓ1 v)) >>=
              fun row => pure (anc.extend row)) =
        OracleComp.evalWith h (P.initTrunc ℓ (Nat.le_of_succ_le hℓ1) S₀) anc *
          (P.numNodes (ℓ + 1) : ℝ≥0∞) := fun anc => by
      by_cases h0 : OracleComp.evalWith h (P.initTrunc ℓ (Nat.le_of_succ_le hℓ1) S₀) anc = 0
      · rw [h0, zero_mul, zero_mul]
      · have hg_anc := mem_support_initTrunc ℓ (Nat.le_of_succ_le hℓ1) hS₀
          (mem_support_of_evalWith_ne_zero h0)
        congr 1
        rw [OracleComp.expectedCost_bind, OracleComp.expectedCost_pi]
        simp_rw [expectedCost_queryGoodOrArb_self h hℓ1 (hg_anc.validPrimBounds_succ hℓ1 _)]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        simp
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

private theorem expectedCost_stepTrunc_self {P : TreeSchedule}
    (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q)) :
    ∀ (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) (st : P.PaddedStep) (ts : P.TruncSeeds ℓ),
      OracleComp.expectedCost h (levelRehashCost ℓ) (P.stepTrunc ℓ hℓ st ts) =
        ∑' am, OracleComp.evalWith h (P.stepTrunc ℓ hℓ st ts) am *
          ((∑ p : Fin (P.numNodes ℓ), if am.2 p then 1 else 0 : ℕ) : ℝ≥0∞)
  | 0, h0, st, ts => by
    classical
    dsimp only [stepTrunc]
    rw [OracleComp.expectedCost_bind, OracleComp.expectedCost_pi, OracleComp.evalWith_bind,
      tsum_pmf_bind_mul]
    simp_rw [OracleComp.expectedCost_pure, mul_zero, tsum_zero, add_zero, OracleComp.evalWith_pure,
      tsum_pmf_pure_mul]
    let c0 : ℝ≥0∞ := ((∑ p : Fin (P.numNodes 0),
      if !decide (P.IsGoodNodeSeed 0 (ts.seed 0 le_rfl h0 p) (P.primSetZero st.postSet)) then 1
      else 0 : ℕ) : ℝ≥0∞)
    have hrhs : (∑' a, OracleComp.evalWith h
        (OracleComp.pi fun u => P.singleNodeStep 0 h0 (P.primSetZero st.postSet, false)
          (ts.seed 0 le_rfl h0 u)) a * c0) = c0 := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    change _ = ∑' a, OracleComp.evalWith h _ a * c0
    rw [hrhs]
    dsimp only [c0]
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    dsimp only [singleNodeStep]
    by_cases hcond : !decide (P.IsGoodNodeSeed 0 (ts.seed 0 le_rfl h0 u) (P.primSetZero st.postSet))
    · simp only [Bool.false_or, hcond, ↓reduceIte, Nat.cast_one]
      exact expectedCost_queryGoodOrArb_self h h0
        (P.validPrimBounds_primSetZero_of_root st.post_bounds)
    · simp [hcond]
  | ℓ + 1, hℓ1, st, ts => by
    classical
    dsimp only [stepTrunc]
    rw [OracleComp.expectedCost_bind,
      expectedCost_stepTrunc_zero_above h (Nat.le_of_succ_le hℓ1) (Nat.lt_succ_self ℓ), zero_add,
      OracleComp.evalWith_bind, tsum_pmf_bind_mul]
    refine tsum_congr fun am => ?_
    by_cases h0 :
        OracleComp.evalWith h (P.stepTrunc ℓ (Nat.le_of_succ_le hℓ1) st ts.restrict) am = 0
    · rw [h0, zero_mul, zero_mul]
    · have hg_am := (mem_support_stepTrunc ℓ (Nat.le_of_succ_le hℓ1) st ts.restrict
        (mem_support_of_evalWith_ne_zero h0)).1
      congr 1
      rw [OracleComp.expectedCost_bind, OracleComp.expectedCost_pi, OracleComp.evalWith_bind,
        tsum_pmf_bind_mul]
      simp_rw [OracleComp.expectedCost_pure, mul_zero, tsum_zero, add_zero,
        OracleComp.evalWith_pure, tsum_pmf_pure_mul]
      let c1 : ℝ≥0∞ := ((∑ p : Fin (P.numNodes (ℓ + 1)),
        if am.2 (P.parentNode ℓ p) || !decide (P.IsGoodNodeSeed (ℓ + 1) (ts.lastRow hℓ1 p)
            (am.1.toFull.primSetAt st.postSet (ℓ + 1) hℓ1 p)) then 1
        else 0 : ℕ) : ℝ≥0∞)
      have hrhs : (∑' a, OracleComp.evalWith h
          (OracleComp.pi fun v => P.singleNodeStep (ℓ + 1) hℓ1
            (am.1.toFull.primSetAt st.postSet (ℓ + 1) hℓ1 v, am.2 (P.parentNode ℓ v))
            (ts.lastRow hℓ1 v)) a * c1) = c1 := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      change _ = ∑' a, OracleComp.evalWith h _ a * c1
      rw [hrhs]
      dsimp only [c1]
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      dsimp only [singleNodeStep]
      by_cases hcond : am.2 (P.parentNode ℓ v) ||
          !decide (P.IsGoodNodeSeed (ℓ + 1) (ts.lastRow hℓ1 v)
            (am.1.toFull.primSetAt st.postSet (ℓ + 1) hℓ1 v))
      · simp only [hcond, ↓reduceIte, Nat.cast_one]
        exact expectedCost_queryGoodOrArb_self h hℓ1 (hg_am.validPrimBounds_succ hℓ1 v)
      · simp [hcond]

private theorem expectedCost_runTruncSteps_eq_trace {P : TreeSchedule}
    (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q)) (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) :
    ∀ (sts : List P.PaddedStep) (a : P.TruncSeeds ℓ),
      OracleComp.expectedCost h (levelRehashCost ℓ) (P.runTruncSteps ℓ hℓ sts a) =
        ∑' tr, OracleComp.evalWith h (runTraceA (P.stepTrunc ℓ hℓ) sts a) tr *
          (traceMaskCount tr : ℝ≥0∞)
  | [], a => by
    dsimp only [runTruncSteps, runTraceA]
    rw [OracleComp.expectedCost_pure, OracleComp.evalWith_pure, tsum_pmf_pure_mul]
    simp [traceMaskCount]
  | st :: sts, a => by
    dsimp only [runTruncSteps, runTraceA]
    rw [OracleComp.expectedCost_bind, expectedCost_stepTrunc_self h ℓ hℓ st a,
      OracleComp.evalWith_bind, tsum_pmf_bind_mul, ← tsum_add]
    refine tsum_congr fun am => ?_
    rw [← mul_add, expectedCost_runTruncSteps_eq_trace h ℓ hℓ sts am.1, OracleComp.evalWith_bind,
      tsum_pmf_bind_mul]
    simp_rw [OracleComp.evalWith_pure, tsum_pmf_pure_mul]
    congr 1
    have hc1 : ((∑ p : Fin (P.numNodes ℓ), if am.2 p then 1 else 0 : ℕ) : ℝ≥0∞) =
        ∑' tr, OracleComp.evalWith h (runTraceA (P.stepTrunc ℓ hℓ) sts am.1) tr *
          ((∑ p : Fin (P.numNodes ℓ), if am.2 p then 1 else 0 : ℕ) : ℝ≥0∞) := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    rw [hc1, ← tsum_add]
    refine tsum_congr fun tr => ?_
    rw [← mul_add]
    congr 1
    dsimp only [traceMaskCount, List.map_cons, List.sum_cons]
    exact (Nat.cast_add _ _).symm

private theorem expectedCost_execTruncHistory_eq_trace {P : TreeSchedule}
    (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q)) (ℓ : ℕ) (hℓ : ℓ ≤ P.depth)
    {S₀ : Finset (Fin P.paddedUniv)} (hS₀ : P.validRootBounds S₀) (sts : List P.PaddedStep) :
    OracleComp.expectedCost h (levelRehashCost ℓ) (P.execTruncHistory ℓ hℓ S₀ sts) =
      ∑' a₀, OracleComp.evalWith h (P.initTrunc ℓ hℓ S₀) a₀ *
        ∑' tr, OracleComp.evalWith h (runTraceA (P.stepTrunc ℓ hℓ) sts a₀) tr *
          (((P.numNodes ℓ + traceMaskCount tr : ℕ) : ℝ≥0∞)) := by
  dsimp only [execTruncHistory]
  rw [OracleComp.expectedCost_bind, expectedCost_initTrunc_self h ℓ hℓ hS₀]
  simp_rw [expectedCost_runTruncSteps_eq_trace h ℓ hℓ sts]
  have hn : (P.numNodes ℓ : ℝ≥0∞) =
      ∑' a₀, OracleComp.evalWith h (P.initTrunc ℓ hℓ S₀) a₀ *
        ∑' tr, OracleComp.evalWith h (runTraceA (P.stepTrunc ℓ hℓ) sts a₀) tr *
          (P.numNodes ℓ : ℝ≥0∞) := by
    simp_rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [hn, ← tsum_add]
  refine tsum_congr fun a₀ => ?_
  rw [← mul_add, ← tsum_add]
  congr 1
  refine tsum_congr fun tr => ?_
  rw [← mul_add, Nat.cast_add]

/-! ## Section 2: Unconditional `hbase`, `hstep`, and `Lemma 5.3` (`expectedCost_execSeedSteps_le`)
-/

private theorem unresetChanges_le_length {α : Type*} [DecidableEq α] :
    ∀ (evs : List (α × Bool)) (s₀ : α), unresetChanges s₀ evs ≤ evs.length
  | [], _ => le_rfl
  | (s₁, true) :: rest, _ => (unresetChanges_le_length rest s₁).trans (Nat.le_succ _)
  | (s₁, false) :: rest, s₀ => by
    dsimp only [unresetChanges, List.length_cons]
    have h1 : (if s₁ = s₀ then 0 else 1) ≤ 1 := by split_ifs <;> omega
    have h2 := unresetChanges_le_length rest s₁
    omega

/-- **Unconditional top-level (`ℓ = 0`) expected rehash bound (`hbase`)**. -/
theorem expectedCost_execTruncHistory_zero_le {P : TreeSchedule} (hcr : P.ConcentrationReady)
    {S₀ : Finset (Fin P.paddedUniv)} (hS₀ : P.validRootBounds S₀) (sts : List P.PaddedStep) :
    OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost 0)
        (P.execTruncHistory 0 (Nat.zero_le _) S₀ sts) ≤
      ENNReal.ofReal (1 + 20 * (sts.length : ℝ) / (P.nFloor 0 : ℝ) ^ 2) := by
  let h0 : 0 ≤ P.depth := Nat.zero_le _
  let stepC : P.PaddedStep → (u : Fin (P.numNodes 0)) → P.NodeSeed 0 →
      OracleComp P.goodSeedSpec (P.NodeSeed 0) :=
    fun st _ g => P.singleNodeStep 0 h0 (P.primSetZero st.postSet, false) g
  have hrun : ∀ (ss : List P.PaddedStep) (row : Fin (P.numNodes 0) → P.NodeSeed 0),
      OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost 0)
          (P.runTruncSteps 0 h0 ss ⟨fun j hj0 _ u => by
            obtain rfl := Nat.eq_zero_of_le_zero hj0; exact row u⟩) =
        OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost 0)
          (runPiChain stepC ss row) := by
    intro ss
    induction ss with
    | nil => intro row; simp only [runTruncSteps, runPiChain, OracleComp.expectedCost_pure]
    | cons st ss ih =>
      intro row
      dsimp only [runTruncSteps, stepTrunc, runPiChain, stepC]
      rw [bind_assoc, OracleComp.expectedCost_bind, OracleComp.expectedCost_bind]
      congr 1
      refine tsum_congr fun row_new => ?_
      rw [pure_bind, ih row_new]
  have hexec : OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost 0)
      (P.execTruncHistory 0 h0 S₀ sts) =
      OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost 0)
        (OracleComp.pi (fun _ : Fin (P.numNodes 0) => P.queryGoodOrArb 0 h0 (P.primSetZero S₀)) >>=
          runPiChain stepC sts) := by
    dsimp only [execTruncHistory, initTrunc]
    rw [bind_assoc, OracleComp.expectedCost_bind, OracleComp.expectedCost_bind]
    congr 1
    refine tsum_congr fun row₀ => ?_
    rw [pure_bind, hrun sts row₀]
  have hchain_eq : ∀ (ss : List P.PaddedStep) (g : P.NodeSeed 0),
      runCoordChain (fun st => P.singleNodeStep 0 h0 (P.primSetZero st.postSet, false)) ss g =
        P.singleNodeRem 0 h0 (ss.map fun st => (P.primSetZero st.postSet, false)) g := by
    intro ss
    induction ss with
    | nil => intro _; rfl
    | cons st ss ih =>
      intro g
      dsimp only [List.map_cons, singleNodeRem, runCoordChain]
      exact congrArg _ (funext ih)
  let evs0 := sts.map fun st => (P.primSetZero st.postSet, false)
  rw [hexec, expectedCost_pi_bind_runPiChain]
  have hu0_univ : (Finset.univ : Finset (Fin (P.numNodes 0))) = {⟨0, P.numNodes_pos 0⟩} := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim u _
  rw [hu0_univ, Finset.sum_singleton]
  have hfresh_eq : (P.queryGoodOrArb 0 h0 (P.primSetZero S₀) >>=
      runCoordChain (fun s => stepC s ⟨0, P.numNodes_pos 0⟩) sts) =
      P.singleNodeFresh 0 h0 (P.primSetZero S₀) evs0 := by
    dsimp only [singleNodeFresh, stepC]
    exact congrArg _ (funext (hchain_eq sts))
  rw [hfresh_eq]
  refine (P.expectedCost_singleNodeFresh_le hcr h0 evs0.length evs0 (P.primSetZero S₀) le_rfl
    (P.validPrimBounds_primSetZero_of_root hS₀) ?_).trans ?_
  · intro p hp
    obtain ⟨st, _, rfl⟩ := List.mem_map.mp hp
    exact P.validPrimBounds_primSetZero_of_root st.post_bounds
  · refine ENNReal.ofReal_le_ofReal ?_
    have hcr0 : countResets evs0 = 0 := by
      dsimp only [countResets, evs0]
      rw [List.filter_eq_nil_iff.mpr]; · rfl
      intro p hp; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp; simp
    have hchg : (unresetChanges (P.primSetZero S₀) evs0 : ℝ) ≤ (sts.length : ℝ) := by
      have h1 := unresetChanges_le_length evs0 (P.primSetZero S₀)
      rw [List.length_map] at h1
      exact_mod_cast h1
    rw [hcr0, Nat.cast_zero, add_zero]
    gcongr

private def ValidAncTrace {P : TreeSchedule} (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) :
    Finset (Fin P.paddedUniv) → P.TruncSeeds ℓ →
      List (TraceItem P.PaddedStep (P.TruncSeeds ℓ) (Fin (P.numNodes ℓ) → Bool)) → Prop
  | S, a, [] => GoodTrunc ℓ hℓ S a
  | S, a, item :: rest =>
    GoodTrunc ℓ hℓ S a ∧
    item.step.preSet = S ∧
    (∀ u : Fin (P.numNodes ℓ), item.mask u = false →
      ∀ (j : ℕ) (hj : j ≤ ℓ),
        item.state.seed j hj (hj.trans hℓ) (P.ancestorAt hj u) =
          a.seed j hj (hj.trans hℓ) (P.ancestorAt hj u)) ∧
    ValidAncTrace ℓ hℓ item.step.postSet item.state rest

private theorem validAncTrace_of_mem_support {P : TreeSchedule} (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) :
    ∀ {sts : List P.PaddedStep} {S : Finset (Fin P.paddedUniv)} {a : P.TruncSeeds ℓ}
      {tr : List (TraceItem P.PaddedStep (P.TruncSeeds ℓ) (Fin (P.numNodes ℓ) → Bool))},
      GoodTrunc ℓ hℓ S a → ChainSteps S sts →
      tr ∈ (runTraceA (P.stepTrunc ℓ hℓ) sts a).support →
      tr.length = sts.length ∧ ValidAncTrace ℓ hℓ S a tr
  | [], _, _, tr, hg, _, htr => by
    dsimp only [runTraceA] at htr
    obtain rfl : tr = [] := htr
    exact ⟨rfl, hg⟩
  | st :: sts, S, a, tr, hg, ⟨hpre, hchain⟩, htr => by
    dsimp only [runTraceA] at htr
    rw [OracleComp.mem_supportWith_bind_iff] at htr
    obtain ⟨am, ham, hrest⟩ := htr
    rw [OracleComp.mem_supportWith_bind_iff] at hrest
    obtain ⟨tr_tail, htail, htr_eq⟩ := hrest
    obtain rfl : tr = ⟨st, am.1, am.2⟩ :: tr_tail := htr_eq
    obtain ⟨hg_am, hfix_am⟩ := mem_support_stepTrunc ℓ hℓ st a ham
    obtain ⟨hlen, hval⟩ := validAncTrace_of_mem_support ℓ hℓ hg_am hchain htail
    exact ⟨congrArg Nat.succ hlen, hg, hpre, hfix_am, hval⟩

private theorem sum_unresetChanges_le {P : TreeSchedule} {ℓ : ℕ} (hℓ1 : ℓ + 1 ≤ P.depth) :
    ∀ (tr : List (TraceItem P.PaddedStep (P.TruncSeeds ℓ) (Fin (P.numNodes ℓ) → Bool)))
      (S : Finset (Fin P.paddedUniv)) (a : P.TruncSeeds ℓ),
      ValidAncTrace ℓ (Nat.le_of_succ_le hℓ1) S a tr →
      (∑ v : Fin (P.numNodes (ℓ + 1)),
        unresetChanges (a.toFull.primSetAt S (ℓ + 1) hℓ1 v)
          (tr.map fun item =>
            (item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v,
              item.mask (P.parentNode ℓ v)))) ≤ tr.length
  | [], _, _, _ => by simp [unresetChanges]
  | item :: rest, S, a, ⟨_, hpre, hfix, hval_rest⟩ => by
    classical
    let stepChg : Fin (P.numNodes (ℓ + 1)) → ℕ := fun v =>
      if item.mask (P.parentNode ℓ v) then 0
      else if item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v =
          a.toFull.primSetAt S (ℓ + 1) hℓ1 v then 0 else 1
    have hsplit : ∀ v : Fin (P.numNodes (ℓ + 1)),
        unresetChanges (a.toFull.primSetAt S (ℓ + 1) hℓ1 v)
            ((item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v,
              item.mask (P.parentNode ℓ v)) ::
              rest.map fun it =>
                (it.state.toFull.primSetAt it.step.postSet (ℓ + 1) hℓ1 v,
                  it.mask (P.parentNode ℓ v))) =
          stepChg v +
            unresetChanges (item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v)
              (rest.map fun it =>
                (it.state.toFull.primSetAt it.step.postSet (ℓ + 1) hℓ1 v,
                  it.mask (P.parentNode ℓ v))) := fun v => by
      dsimp only [stepChg]
      cases item.mask (P.parentNode ℓ v)
      · dsimp only [unresetChanges]; rw [ite_eq_right Bool.false_ne_true]
      · dsimp only [unresetChanges]; rw [ite_eq_left rfl, zero_add]
    simp only [List.map_cons, List.length_cons, hsplit]
    rw [Finset.sum_add_distrib]
    let v_key := item.state.toFull.nodeAt (ℓ + 1) hℓ1 item.step.key
    have hzero_off : ∀ v : Fin (P.numNodes (ℓ + 1)), v ≠ v_key → stepChg v = 0 := by
      intro v hne
      dsimp only [stepChg]
      by_cases hm : item.mask (P.parentNode ℓ v) = true
      · rw [ite_eq_left hm]
      · rw [ite_eq_right hm]
        simp only [Bool.not_eq_true] at hm
        have hpre_eq : item.state.toFull.primSetAt S (ℓ + 1) hℓ1 v =
            a.toFull.primSetAt S (ℓ + 1) hℓ1 v := by
          refine SeedAssignment.primSetAt_congr_ancestors S hℓ1 v fun j hj => ?_
          have hjℓ : j ≤ ℓ := Nat.le_of_lt_succ hj
          rw [item.state.toFull_seed hjℓ, a.toFull_seed hjℓ, P.ancestorAt_succ hjℓ v]
          exact hfix (P.parentNode ℓ v) hm j hjℓ
        have hact_eq : item.state.toFull.activeAt item.step.postSet (ℓ + 1) hℓ1 v =
            item.state.toFull.activeAt S (ℓ + 1) hℓ1 v := by
          ext y
          simp only [SeedAssignment.mem_activeAt_iff]
          rcases item.step.diff_key y with hiff | rfl
          · rw [hiff, hpre]
          · exact ⟨fun ⟨_, hn⟩ => False.elim (hne hn.symm),
              fun ⟨_, hn⟩ => False.elim (hne hn.symm)⟩
        have hpost_eq : item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v =
            item.state.toFull.primSetAt S (ℓ + 1) hℓ1 v := by
          dsimp only [SeedAssignment.primSetAt]; rw [hact_eq]
        rw [hpost_eq, hpre_eq, ite_eq_left rfl]
    have hsum_step : ∑ v : Fin (P.numNodes (ℓ + 1)), stepChg v ≤ 1 := by
      rw [Finset.sum_eq_single v_key (fun v _ hv => hzero_off v hv)
        (fun h => False.elim (h (Finset.mem_univ _)))]
      dsimp only [stepChg]; split_ifs <;> omega
    have hih := sum_unresetChanges_le hℓ1 rest item.step.postSet item.state hval_rest
    omega

private theorem sum_countResets_children_eq (P : TreeSchedule) (ℓ : ℕ)
    (hℓ1 : ℓ + 1 ≤ P.depth) :
    ∀ (tr : List (TraceItem P.PaddedStep (P.TruncSeeds ℓ) (Fin (P.numNodes ℓ) → Bool))),
      (∑ v : Fin (P.numNodes (ℓ + 1)),
        (1 + countResets
          (tr.map fun item =>
            (item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v,
              item.mask (P.parentNode ℓ v))))) =
        (P.numNodes ℓ + traceMaskCount tr) * P.branchFactor ℓ := by
  intro tr
  have hcr_eq : ∀ v : Fin (P.numNodes (ℓ + 1)),
      countResets
          (tr.map fun item =>
            (item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v,
              item.mask (P.parentNode ℓ v))) =
        (tr.map fun item => if item.mask (P.parentNode ℓ v) then 1 else 0).sum := by
    intro v
    induction tr with
    | nil => rfl
    | cons item rest ih =>
      dsimp only [countResets] at ih ⊢
      rcases hm : item.mask (P.parentNode ℓ v) with _ | _ <;>
        simp [hm, ih, Nat.add_comm]
  simp_rw [hcr_eq]
  clear hcr_eq
  rw [← Equiv.sum_comp (P.childNodeEquiv ℓ), Fintype.sum_prod_type]
  simp only [parentNode_childNodeEquiv, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  rw [← Finset.mul_sum]
  have hbf : P.branchFactor ℓ = 2 ^ P.branchBits ℓ := rfl
  rw [hbf, mul_comm (2 ^ P.branchBits ℓ)]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one]
  congr 1
  induction tr with
  | nil => simp [traceMaskCount]
  | cons item rest ih =>
    simp only [traceMaskCount, List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib]
    exact congrArg (_ + ·) ih

/-- **Unconditional parent-to-child (`ℓ → ℓ + 1`) expected rehash recurrence (`hstep`)**. -/
theorem expectedCost_execTruncHistory_succ_le {P : TreeSchedule} (hcr : P.ConcentrationReady)
    {ℓ : ℕ} (hlt : ℓ < P.depth) {S₀ : Finset (Fin P.paddedUniv)} (hS₀ : P.validRootBounds S₀)
    {sts : List P.PaddedStep} (hchain : ChainSteps S₀ sts) :
    OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost (ℓ + 1))
        (P.execTruncHistory (ℓ + 1) hlt S₀ sts) ≤
      OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost ℓ)
          (P.execTruncHistory ℓ hlt.le S₀ sts) * (P.branchFactor ℓ : ℝ≥0∞) +
        ENNReal.ofReal (20 * (sts.length : ℝ) / (P.nFloor (ℓ + 1) : ℝ) ^ 2) := by
  let hℓ : ℓ ≤ P.depth := hlt.le
  let hℓ1 : ℓ + 1 ≤ P.depth := hlt
  let p₀ := P.initTrunc ℓ hℓ S₀
  let q₀ : P.TruncSeeds ℓ →
      OracleComp P.goodSeedSpec (Fin (P.numNodes (ℓ + 1)) → P.NodeSeed (ℓ + 1)) :=
    fun anc => OracleComp.pi fun v =>
      P.queryGoodOrArb (ℓ + 1) hℓ1 (anc.toFull.primSetAt S₀ (ℓ + 1) hℓ1 v)
  let stepA := P.stepTrunc ℓ hℓ
  let stepC : TraceItem P.PaddedStep (P.TruncSeeds ℓ) (Fin (P.numNodes ℓ) → Bool) →
      (v : Fin (P.numNodes (ℓ + 1))) → P.NodeSeed (ℓ + 1) →
        OracleComp P.goodSeedSpec (P.NodeSeed (ℓ + 1)) :=
    fun item v g => P.singleNodeStep (ℓ + 1) hℓ1
      (item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v,
        item.mask (P.parentNode ℓ v)) g
  let stepB : P.PaddedStep → P.TruncSeeds ℓ → (Fin (P.numNodes ℓ) → Bool) →
      (Fin (P.numNodes (ℓ + 1)) → P.NodeSeed (ℓ + 1)) →
        OracleComp P.goodSeedSpec (Fin (P.numNodes (ℓ + 1)) → P.NodeSeed (ℓ + 1)) :=
    fun st anc reh row => OracleComp.pi fun v => stepC ⟨st, anc, reh⟩ v (row v)
  have hrun_eq : ∀ (ss : List P.PaddedStep) (anc : P.TruncSeeds ℓ)
      (row : Fin (P.numNodes (ℓ + 1)) → P.NodeSeed (ℓ + 1)),
      OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost (ℓ + 1))
          (P.runTruncSteps (ℓ + 1) hℓ1 ss (anc.extend row)) =
        OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost (ℓ + 1))
          (runInterleaved stepA stepB ss anc row) := by
    intro ss
    induction ss with
    | nil => intro anc row; simp only [runTruncSteps, runInterleaved, OracleComp.expectedCost_pure]
    | cons st ss ih =>
      intro anc row
      dsimp only [runTruncSteps, stepTrunc, runInterleaved, stepA, stepB, stepC]
      rw [anc.restrict_extend row, anc.lastRow_extend hℓ1 row, bind_assoc,
        OracleComp.expectedCost_bind, OracleComp.expectedCost_bind]
      congr 1
      refine tsum_congr fun am => ?_
      congr 1
      rw [bind_assoc, OracleComp.expectedCost_bind, OracleComp.expectedCost_bind]
      congr 1
      refine tsum_congr fun row_new => ?_
      rw [pure_bind, ih am.1 row_new]
  have hexec_eq : OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost (ℓ + 1))
      (P.execTruncHistory (ℓ + 1) hℓ1 S₀ sts) =
      OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost (ℓ + 1))
        (p₀ >>= fun a₀ => q₀ a₀ >>= fun b₀ => runInterleaved stepA stepB sts a₀ b₀) := by
    dsimp only [execTruncHistory, initTrunc, p₀, q₀]
    rw [bind_assoc, OracleComp.expectedCost_bind, OracleComp.expectedCost_bind]
    congr 1
    refine tsum_congr fun a₀ => ?_
    congr 1
    rw [bind_assoc, OracleComp.expectedCost_bind, OracleComp.expectedCost_bind]
    congr 1
    refine tsum_congr fun b₀ => ?_
    rw [pure_bind, hrun_eq sts a₀ b₀]
  have htraceB_eq : ∀ tr row, runGivenTraceB stepB tr row = runPiChain stepC tr row := by
    intro tr
    induction tr with
    | nil => intro _; rfl
    | cons item rest ih =>
      intro row
      dsimp only [runGivenTraceB, runPiChain, stepB]
      exact congrArg _ (funext ih)
  have hcoord_eq : ∀ tr v g,
      runCoordChain (fun s => stepC s v) tr g =
        P.singleNodeRem (ℓ + 1) hℓ1
          (tr.map fun item =>
            (item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v,
              item.mask (P.parentNode ℓ v))) g := by
    intro tr v
    induction tr with
    | nil => intro _; rfl
    | cons item rest ih =>
      intro g
      dsimp only [List.map_cons, singleNodeRem, runCoordChain, stepC]
      exact congrArg _ (funext ih)
  have hvalid_tr : ∀ {tr S a}, ValidAncTrace ℓ hℓ S a tr →
      ∀ v p, p ∈ (tr.map fun item =>
          (item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v,
            item.mask (P.parentNode ℓ v))) →
        P.validPrimBounds (ℓ + 1) p.1 := by
    intro tr
    induction tr with
    | nil => intro _ _ _ _ _ hp; cases hp
    | cons item rest ih =>
      intro S a ⟨_, _, _, hval_rest⟩ v p hp
      rcases List.mem_cons.mp hp with rfl | hmem
      · have hg_item : GoodTrunc ℓ hℓ item.step.postSet item.state := by
          cases rest with
          | nil => exact hval_rest
          | cons _ _ => exact hval_rest.1
        exact hg_item.validPrimBounds_succ hℓ1 v
      · exact ih hval_rest v p hmem
  rw [hexec_eq, expectedCost_init_runInterleaved_eq, OracleComp.expectedCost_bind,
    expectedCost_initTrunc_zero_above _ hℓ (Nat.lt_succ_self ℓ), zero_add]
  have htr_cost : ∀ a₀ : P.TruncSeeds ℓ,
      OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost (ℓ + 1))
        (runTraceA stepA sts a₀ >>= fun tr => q₀ a₀ >>= runGivenTraceB stepB tr) =
      ∑' tr, OracleComp.evalWith (P.goodSeedLaw hcr) (runTraceA stepA sts a₀) tr *
        OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost (ℓ + 1))
          (q₀ a₀ >>= runGivenTraceB stepB tr) := fun a₀ => by
    rw [OracleComp.expectedCost_bind,
      expectedCost_runTraceA_zero_above _ hℓ (Nat.lt_succ_self ℓ), zero_add]
  simp_rw [htr_cost]
  let remTerm := ENNReal.ofReal (20 * (sts.length : ℝ) / (P.nFloor (ℓ + 1) : ℝ) ^ 2)
  have hpointwise : ∀ a₀ : P.TruncSeeds ℓ,
      OracleComp.evalWith (P.goodSeedLaw hcr) p₀ a₀ *
        (∑' tr, OracleComp.evalWith (P.goodSeedLaw hcr) (runTraceA stepA sts a₀) tr *
          OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost (ℓ + 1))
            (q₀ a₀ >>= runGivenTraceB stepB tr)) ≤
      OracleComp.evalWith (P.goodSeedLaw hcr) p₀ a₀ *
        (∑' tr, OracleComp.evalWith (P.goodSeedLaw hcr) (runTraceA stepA sts a₀) tr *
          (((P.numNodes ℓ + traceMaskCount tr : ℕ) : ℝ≥0∞) * (P.branchFactor ℓ : ℝ≥0∞) +
            remTerm)) := by
    intro a₀
    by_cases ha0 : OracleComp.evalWith (P.goodSeedLaw hcr) p₀ a₀ = 0
    · rw [ha0, zero_mul, zero_mul]
    · have hg_a0 := mem_support_initTrunc ℓ hℓ hS₀ (mem_support_of_evalWith_ne_zero ha0)
      refine mul_le_mul_of_nonneg_left (tsum_le_tsum fun tr => ?_) zero_le
      by_cases htr0 : OracleComp.evalWith (P.goodSeedLaw hcr) (runTraceA stepA sts a₀) tr = 0
      · rw [htr0, zero_mul, zero_mul]
      · obtain ⟨hlen_tr, hval_tr⟩ :=
          validAncTrace_of_mem_support ℓ hℓ hg_a0 hchain (mem_support_of_evalWith_ne_zero htr0)
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        rw [show runGivenTraceB stepB tr = runPiChain stepC tr from funext (htraceB_eq tr),
          expectedCost_pi_bind_runPiChain]
        have hnode_le : ∀ v : Fin (P.numNodes (ℓ + 1)),
            OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost (ℓ + 1))
              (P.queryGoodOrArb (ℓ + 1) hℓ1 (a₀.toFull.primSetAt S₀ (ℓ + 1) hℓ1 v) >>=
                runCoordChain (fun s => stepC s v) tr) ≤
            ENNReal.ofReal
              ((1 + countResets
                  (tr.map fun item =>
                    (item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v,
                      item.mask (P.parentNode ℓ v))) : ℝ) +
                20 * (unresetChanges (a₀.toFull.primSetAt S₀ (ℓ + 1) hℓ1 v)
                  (tr.map fun item =>
                    (item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v,
                      item.mask (P.parentNode ℓ v))) : ℝ) /
                  (P.nFloor (ℓ + 1) : ℝ) ^ 2) := fun v => by
          have hf_eq : (P.queryGoodOrArb (ℓ + 1) hℓ1 (a₀.toFull.primSetAt S₀ (ℓ + 1) hℓ1 v) >>=
              runCoordChain (fun s => stepC s v) tr) =
              P.singleNodeFresh (ℓ + 1) hℓ1 (a₀.toFull.primSetAt S₀ (ℓ + 1) hℓ1 v)
                (tr.map fun item =>
                  (item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v,
                    item.mask (P.parentNode ℓ v))) := by
            dsimp only [singleNodeFresh]
            exact congrArg _ (funext (hcoord_eq tr v))
          rw [hf_eq]
          exact P.expectedCost_singleNodeFresh_le hcr hℓ1 tr.length _ _ (by simp)
            (hg_a0.validPrimBounds_succ hℓ1 v) (hvalid_tr hval_tr v)
        have hsq_pos : (0 : ℝ) < (P.nFloor (ℓ + 1) : ℝ) ^ 2 :=
          sq_pos_of_pos (Nat.cast_pos.mpr (P.nFloor_pos (ℓ + 1) hℓ1))
        refine (Finset.sum_le_sum fun v _ => hnode_le v).trans ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun v _ =>
          add_nonneg (by positivity) (div_nonneg (by positivity) hsq_pos.le)]
        have hsum_real :
            (∑ v : Fin (P.numNodes (ℓ + 1)),
              ((1 + countResets
                  (tr.map fun item =>
                    (item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v,
                      item.mask (P.parentNode ℓ v))) : ℝ) +
                20 * (unresetChanges (a₀.toFull.primSetAt S₀ (ℓ + 1) hℓ1 v)
                  (tr.map fun item =>
                    (item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v,
                      item.mask (P.parentNode ℓ v))) : ℝ) /
                  (P.nFloor (ℓ + 1) : ℝ) ^ 2)) ≤
            (((P.numNodes ℓ + traceMaskCount tr) * P.branchFactor ℓ : ℕ) : ℝ) +
              20 * (sts.length : ℝ) / (P.nFloor (ℓ + 1) : ℝ) ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
          have h1 : (∑ v : Fin (P.numNodes (ℓ + 1)),
              (1 + countResets
                (tr.map fun item =>
                  (item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v,
                    item.mask (P.parentNode ℓ v))) : ℝ)) =
              (((P.numNodes ℓ + traceMaskCount tr) * P.branchFactor ℓ : ℕ) : ℝ) := by
            have := P.sum_countResets_children_eq ℓ hℓ1 tr
            exact_mod_cast this
          have h2 : (∑ v : Fin (P.numNodes (ℓ + 1)),
              (unresetChanges (a₀.toFull.primSetAt S₀ (ℓ + 1) hℓ1 v)
                (tr.map fun item =>
                  (item.state.toFull.primSetAt item.step.postSet (ℓ + 1) hℓ1 v,
                    item.mask (P.parentNode ℓ v))) : ℝ)) ≤ (sts.length : ℝ) := by
            have hnat := (sum_unresetChanges_le hℓ1 tr S₀ a₀ hval_tr).trans hlen_tr.le
            exact_mod_cast hnat
          rw [h1]
          gcongr
        refine (ENNReal.ofReal_le_ofReal hsum_real).trans ?_
        rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (div_nonneg (by positivity) hsq_pos.le),
          ENNReal.ofReal_natCast, Nat.cast_mul]
  refine (tsum_le_tsum hpointwise).trans (le_of_eq ?_)
  rw [expectedCost_execTruncHistory_eq_trace (P.goodSeedLaw hcr) ℓ hℓ hS₀ sts]
  simp_rw [mul_add, tsum_add, ← mul_assoc, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  simp_rw [mul_add, tsum_add, ← mul_assoc, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rfl

private theorem expectedCost_const_mul {ι : Type} {spec : OracleSpec ι} {α : Type}
    (h : (q : ι) → PMF (spec q)) (c : ℝ≥0∞) (cost : ι → ℝ≥0∞) (prog : OracleComp spec α) :
    OracleComp.expectedCost h (fun q => c * cost q) prog =
      c * OracleComp.expectedCost h cost prog := by
  induction prog using OracleComp.induction with
  | pure _ => simp
  | query_bind q cont ih =>
    rw [OracleComp.expectedCost_query_bind, OracleComp.expectedCost_query_bind, mul_add]
    congr 1
    simp_rw [ih]
    have hcomm : ∀ a, h q a * (c * OracleComp.expectedCost h cost (cont a)) =
        c * (h q a * OracleComp.expectedCost h cost (cont a)) := fun a => by
      rw [← mul_assoc, mul_comm (h q a) c, mul_assoc]
    simp_rw [hcomm]
    exact ENNReal.tsum_mul_left

/-- **Unconditional `Lemma 5.3` over padded step histories (`[LiLiangYuZhou2024, Section 5.5]`)**:
across initialization on `S₀` (`validRootBounds S₀`) and any valid chain `sts` of `PaddedStep`s,
the total expected rehashing work of `execSeedSteps S₀ sts` under `goodSeedLaw hcr` is at most
`14 * (depth + 1) * (cap + sts.length)`. -/
theorem expectedCost_execSeedSteps_le {P : TreeSchedule} (hcr : P.ConcentrationReady)
    {S₀ : Finset (Fin P.paddedUniv)} (hS₀ : P.validRootBounds S₀)
    {sts : List P.PaddedStep} (hchain : ChainSteps S₀ sts) :
    OracleComp.expectedCost (P.goodSeedLaw hcr) P.rehashWorkCost (P.execSeedSteps S₀ sts) ≤
      ENNReal.ofReal (14 * ((P.depth + 1 : ℕ) : ℝ) * ((P.cap + sts.length : ℕ) : ℝ)) := by
  let succRehashes : ℕ → ℝ := fun ℓ =>
    if hℓ : ℓ ≤ P.depth then
      (OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost ℓ)
        (P.execTruncHistory ℓ hℓ S₀ sts)).toReal
    else 0
  have hofReal_eq : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ P.depth),
      ENNReal.ofReal (succRehashes ℓ) =
        OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost ℓ)
          (P.execTruncHistory ℓ hℓ S₀ sts) := fun ℓ hℓ => by
    dsimp only [succRehashes]
    rw [dite_eq_left hℓ]
    exact ENNReal.ofReal_toReal (expectedCost_levelRehashCost_ne_top hcr ℓ ℓ hℓ S₀ sts)
  have hnonneg : ∀ ℓ ≤ P.depth, 0 ≤ succRehashes ℓ := fun ℓ hℓ => by
    dsimp only [succRehashes]; rw [dite_eq_left hℓ]; exact ENNReal.toReal_nonneg
  have hbase : succRehashes 0 ≤ 1 + 20 * (sts.length : ℝ) / (P.nFloor 0 : ℝ) ^ 2 := by
    dsimp only [succRehashes]
    rw [dite_eq_left (Nat.zero_le _)]
    have hsq : (0 : ℝ) ≤ (P.nFloor 0 : ℝ) ^ 2 := sq_nonneg _
    exact ENNReal.toReal_le_of_le_ofReal
      (add_nonneg zero_le_one (div_nonneg (by positivity) hsq))
      (expectedCost_execTruncHistory_zero_le hcr hS₀ sts)
  have hstep : ∀ ℓ < P.depth,
      succRehashes (ℓ + 1) ≤
        succRehashes ℓ * (P.branchFactor ℓ : ℝ) +
          20 * (sts.length : ℝ) / (P.nFloor (ℓ + 1) : ℝ) ^ 2 := fun ℓ hlt => by
    have hrec := expectedCost_execTruncHistory_succ_le hcr hlt hS₀ hchain
    rw [← hofReal_eq ℓ hlt.le,
      show (P.branchFactor ℓ : ℝ≥0∞) = ENNReal.ofReal (P.branchFactor ℓ : ℝ) from
        (ENNReal.ofReal_natCast _).symm,
      ← ENNReal.ofReal_mul (hnonneg ℓ hlt.le),
      ← ENNReal.ofReal_add (mul_nonneg (hnonneg ℓ hlt.le) (Nat.cast_nonneg _))
        (div_nonneg (by positivity) (sq_nonneg _))] at hrec
    dsimp only [succRehashes]
    rw [dite_eq_left (Nat.succ_le_of_lt hlt)]
    exact ENNReal.toReal_le_of_le_ofReal
      (add_nonneg (mul_nonneg (hnonneg ℓ hlt.le) (Nat.cast_nonneg _))
        (div_nonneg (by positivity) (sq_nonneg _))) hrec
  rw [P.rehashWorkCost_eq_sum, OracleComp.expectedCost_sum]
  have hterm_eq : ∀ ℓ ∈ Finset.range (P.depth + 1),
      OracleComp.expectedCost (P.goodSeedLaw hcr)
          (fun q => 2 * (P.nFloor ℓ : ℝ≥0∞) * levelRehashCost ℓ q) (P.execSeedSteps S₀ sts) =
        ENNReal.ofReal (2 * succRehashes ℓ * (P.nFloor ℓ : ℝ)) := fun ℓ hmem => by
    have hℓ : ℓ ≤ P.depth := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem)
    rw [expectedCost_const_mul, expectedCost_level_execTrunc_eq _ hℓ, ← hofReal_eq ℓ hℓ,
      show (2 : ℝ≥0∞) * (P.nFloor ℓ : ℝ≥0∞) = ENNReal.ofReal (2 * (P.nFloor ℓ : ℝ)) by
        rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast],
      ← ENNReal.ofReal_mul (by positivity)]
    exact congrArg ENNReal.ofReal (by ring)
  rw [Finset.sum_congr rfl hterm_eq, ← ENNReal.ofReal_sum_of_nonneg fun ℓ hmem => by
    have hℓ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem)
    exact mul_nonneg (mul_nonneg zero_le_two (hnonneg ℓ hℓ)) (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (P.rehashWork_of_level_recurrence hcr hnonneg hbase hstep)

end TreeSchedule

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
