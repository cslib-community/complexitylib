/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.CellProbe.HardDist
public import CslibFrontier.DataStructure.Dictionary.CellProbe.MetaTree
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.Nat.Choose
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Single-Level Qualification, Capped Consistency, and Binomial Log Estimates

Single-level segment qualification and consistency predicates, Claim 4.1's good-segment expectation
lower bound, candidate segment simulations, global-value `HardKeyValSeed` seeds, and binomial
logarithm estimates from Sections 4–5 and 8 of Li, Liang, Yu, and Zhou ([LiLiangYuZhou2023];
locators follow `arXiv:2306.02253v3`, printed page `p` = PDF page `p + 1`).

Pinned source: [LiLiangYuZhou2023] (`arXiv:2306.02253v3`), Section 4.2, pp. 14–16 (PDF pp. 15–17);
Section 4.3, Claim 4.1, Eq. (5), Definition 4.3, p. 17 (PDF p. 18), Claim 4.2, pp. 17–18 (PDF
pp. 18–19), and Claim 4.6, Eq. (7), p. 19 (PDF p. 20); Section 5.1, Step 1, p. 22 (PDF p. 23);
Section 5.2, Eq. (11) and binomial log bounds, pp. 24–25 (PDF pp. 25–26); Section 8, p. 28 (PDF
p. 29).

Original formalization adaptation (`c = 1` deterministic probe cap): `MetaTree.IsGoodSeg`,
`IsQualified`, and `IsCappedConsistent` include `|S_A| ≤ m * t` and `|S_B| ≤ m * t` to prevent
`{W = 1}` conditional probe inflation in Eq. (11), adding at most `λ_{ℓ+1} / 16` failure mass via
Markov's inequality on `nodeProbes` so Claim 4.1 (`λ_{ℓ+1} / 4`) and Eq. (11) (`2 (β + 1) m t`)
hold.

## Main definitions

* `IsQualified`, `IsCappedConsistent`, `MetaTree.IsGoodSeg`: probe-capped qualification,
  consistency, and good child-segment predicates.
* `orderSubset`, `embSetPermEquiv`, `candidateQueryDeleteInsertOps`, `HardKeyValSeed`: candidate
  segment simulations and global-value seeds.

## Main results

* `MetaTree.isQualified_elemSlice_of_isGoodSeg`, `IsQualified.isCappedConsistent`,
  `MetaTree.quarter_fanout_le_sum_prob_isGoodSeg`: qualification, consistency, and Claim 4.1.
* `insertQueryDeleteDist_eq_bind_keyVals`, `map_ops_uniformOfFintype_hardKeyValSeed`: global-value
  reparametrization of `insertQueryDeleteDist`.
* `div_pow_le_choose`, `logb_choose_sub_logb_choose_sub_le`,
  `quarter_mul_logb_le_logb_powersetCard_sub_nbr`: binomial log estimates and Claim 4.6.

## References

* [T. Li, J. Liang, H. Yu and R. Zhou, *Tight Cell-Probe Lower Bounds for Dynamic Succinct
  Dictionaries*][LiLiangYuZhou2023], Sections 4.2, 4.3, 5.1, 5.2, and 8 (`arXiv:2306.02253v3`).
-/

public section

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.CellProbe Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.Probability
open scoped BigOperators ENNReal

/-! ### Qualification, `c = 1` capped consistency, and Claim 4.1 -/

section Qualification

variable {Op : Type*} {Result : Op → Type} {cells w : ℕ}

/-- Bob's candidate-segment qualification predicate ([LiLiangYuZhou2023], Section 4.2, pp. 15–16 /
PDF pp. 16–17, adapted with the deterministic `|S_B| ≤ m * t` probe cap). -/
@[expose] def IsQualified (D : IndexedScheme Op Result cells w) (step₀ : ℕ)
    (C_bef C_end : Mem cells w) (γ : ℝ) (m : ℕ) (t : ℝ) (ops_B : List Op) : Prop :=
  let S_B := D.probedCellsInterval step₀ C_bef ops_B
  let C_B := (D.runInterval step₀ C_bef ops_B).2
  (((S_B.filter fun j => C_B j ≠ C_end j).card : ℕ) : ℝ) ≤ γ * (m : ℝ) / 2 ∧
    ((S_B.card : ℕ) : ℝ) ≤ (m : ℝ) * t

/-- Probe-capped consistency between two candidate segment executions ([LiLiangYuZhou2023],
Section 4.3, Definition 4.3, p. 17 / PDF p. 18 and Section 5.1, Step 1, p. 22 / PDF p. 23, adapted
with `|S_A| ≤ m * t` and `|S_B| ≤ m * t`). -/
@[expose] def IsCappedConsistent (D : IndexedScheme Op Result cells w) (step₀ : ℕ)
    (C_bef : Mem cells w) (γ : ℝ) (m : ℕ) (t : ℝ) (ops_A ops_B : List Op) : Prop :=
  let S_A := D.probedCellsInterval step₀ C_bef ops_A
  let C_A := (D.runInterval step₀ C_bef ops_A).2
  let S_B := D.probedCellsInterval step₀ C_bef ops_B
  let C_B := (D.runInterval step₀ C_bef ops_B).2
  ((((S_A ∩ S_B).filter fun j => C_A j ≠ C_B j).card : ℕ) : ℝ) ≤ γ * (m : ℝ) ∧
    ((S_A.card : ℕ) : ℝ) ≤ (m : ℝ) * t ∧ ((S_B.card : ℕ) : ℝ) ≤ (m : ℝ) * t

/-- Capped consistency is symmetric in the two operation sequences `ops_A` and `ops_B`. -/
theorem IsCappedConsistent.symm {D : IndexedScheme Op Result cells w} {step₀ : ℕ}
    {C_bef : Mem cells w} {γ : ℝ} {m : ℕ} {t : ℝ} {ops_A ops_B : List Op}
    (h : IsCappedConsistent D step₀ C_bef γ m t ops_A ops_B) :
    IsCappedConsistent D step₀ C_bef γ m t ops_B ops_A := by
  obtain ⟨hdiff, hA, hB⟩ := h
  refine ⟨?_, hB, hA⟩
  convert hdiff using 3; ext j; simp [Finset.mem_inter, and_comm, ne_comm]

/-- Two segment executions qualified against the same `C_end` are capped-consistent
([LiLiangYuZhou2023], Section 4.3, proof of Claim 4.2, p. 17 / PDF p. 18). -/
theorem IsQualified.isCappedConsistent {D : IndexedScheme Op Result cells w} {step₀ : ℕ}
    {C_bef C_end : Mem cells w} {γ : ℝ} {m : ℕ} {t : ℝ} {ops_A ops_B : List Op}
    (hA : IsQualified D step₀ C_bef C_end γ m t ops_A)
    (hB : IsQualified D step₀ C_bef C_end γ m t ops_B) :
    IsCappedConsistent D step₀ C_bef γ m t ops_A ops_B := by
  set S_A := D.probedCellsInterval step₀ C_bef ops_A
  set C_A := (D.runInterval step₀ C_bef ops_A).2
  set S_B := D.probedCellsInterval step₀ C_bef ops_B
  set C_B := (D.runInterval step₀ C_bef ops_B).2
  obtain ⟨hdiffA, hcardA⟩ := hA; obtain ⟨hdiffB, hcardB⟩ := hB
  refine ⟨?_, hcardA, hcardB⟩
  have hsub : (S_A ∩ S_B).filter (fun j => C_A j ≠ C_B j) ⊆
      S_A.filter (fun j => C_A j ≠ C_end j) ∪ S_B.filter (fun j => C_B j ≠ C_end j) :=
    fun j hj => by
      rw [Finset.mem_filter, Finset.mem_inter] at hj; obtain ⟨⟨hjA, hjB⟩, hne⟩ := hj
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      exact if hAe : C_A j = C_end j then Or.inr ⟨hjB, fun hBe => hne (hAe.trans hBe.symm)⟩
        else Or.inl ⟨hjA, hAe⟩
  have hle : (((S_A ∩ S_B).filter (fun j => C_A j ≠ C_B j)).card : ℝ) ≤
      ((S_A.filter (fun j => C_A j ≠ C_end j)).card : ℝ) +
      ((S_B.filter (fun j => C_B j ≠ C_end j)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  linarith

namespace MetaTree

/-- Alice's good child-segment predicate `X_i = 1` at child `i` of internal node `(ℓ + 1, b)`
([LiLiangYuZhou2023], Section 4.2, p. 15 / PDF p. 16, adapted with `|S_A^{[i]}| ≤ m_ℓ * t`). -/
@[expose] def IsGoodSeg (T : MetaTree) (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) (γ t : ℝ) (ℓ b : ℕ)
    (i : Fin (T.fanout (ℓ + 1))) : Prop :=
  (((T.segProbedCells D initLen stride ops ℓ b i ∩
      T.badCells D initLen stride ops ℓ b).card : ℕ) : ℝ) ≤ γ * (T.blockSize ℓ : ℝ) / 2 ∧
    (((T.segProbedCells D initLen stride ops ℓ b i).card : ℕ) : ℝ) ≤ (T.blockSize ℓ : ℝ) * t

/-- When `T.IsGoodSeg` holds, the true child-segment slice `elemSlice` is qualified against `C_end`
([LiLiangYuZhou2023], Section 4.2, pp. 15–16 / PDF pp. 16–17). -/
theorem isQualified_elemSlice_of_isGoodSeg (T : MetaTree) (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) {γ t : ℝ} (ℓ b : ℕ) (i : Fin (T.fanout (ℓ + 1)))
    (hgood : T.IsGoodSeg D initLen stride ops γ t ℓ b i) :
    let segIdx := b * T.fanout (ℓ + 1) + i.val
    IsQualified D (initLen + stride * T.nodeStart ℓ segIdx)
      (memAt D ops (initLen + stride * T.nodeStart ℓ segIdx))
      (memAt D ops (initLen + stride * T.nodeStop (ℓ + 1) b))
      γ (T.blockSize ℓ) t
      (elemSlice initLen stride ops (T.nodeStart ℓ segIdx) (T.nodeStop ℓ segIdx)) := by
  dsimp only; obtain ⟨hbad, hprobe⟩ := hgood; refine ⟨?_, hprobe⟩
  set segIdx := b * T.fanout (ℓ + 1) + i.val
  have hle_seg : T.nodeStart ℓ segIdx ≤ T.nodeStop ℓ segIdx := by
    simp only [nodeStart, nodeStop]; exact Nat.mul_le_mul_right _ (Nat.le_succ _)
  have hpost := (memAt_eq_runInterval_elemSlice D initLen stride ops hle_seg).symm
  have hcard_le := T.card_filter_seg_postMem_ne_node_postMem_le D initLen stride ops ℓ b i
  change (((T.segProbedCells D initLen stride ops ℓ b i).filter _).card : ℝ) ≤ _
  rw [hpost]; exact (Nat.cast_le.mpr hcard_le).trans hbad

/-- When `T.IsGoodSeg` holds and `ops_B` is qualified against `C_end`, the true segment slice and
`ops_B` are capped-consistent ([LiLiangYuZhou2023], Section 4.3, p. 17 / PDF p. 18). -/
theorem isCappedConsistent_of_isGoodSeg (T : MetaTree) (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) {γ t : ℝ} (ℓ b : ℕ) (i : Fin (T.fanout (ℓ + 1)))
    {ops_B : List Op} (hgood : T.IsGoodSeg D initLen stride ops γ t ℓ b i)
    (hqualB : IsQualified D (initLen + stride * T.nodeStart ℓ (b * T.fanout (ℓ + 1) + i.val))
      (memAt D ops (initLen + stride * T.nodeStart ℓ (b * T.fanout (ℓ + 1) + i.val)))
      (memAt D ops (initLen + stride * T.nodeStop (ℓ + 1) b)) γ (T.blockSize ℓ) t ops_B) :
    IsCappedConsistent D (initLen + stride * T.nodeStart ℓ (b * T.fanout (ℓ + 1) + i.val))
      (memAt D ops (initLen + stride * T.nodeStart ℓ (b * T.fanout (ℓ + 1) + i.val)))
      γ (T.blockSize ℓ) t (elemSlice initLen stride ops
        (T.nodeStart ℓ (b * T.fanout (ℓ + 1) + i.val))
        (T.nodeStop ℓ (b * T.fanout (ℓ + 1) + i.val))) ops_B :=
  (T.isQualified_elemSlice_of_isGoodSeg D initLen stride ops ℓ b i hgood).isCappedConsistent hqualB

open Classical in
/-- Total bad-segment probability across all `λ_{ℓ+1}` child segments of internal node `(ℓ + 1, b)`
is at most `(41 / 400) * λ_{ℓ+1}` ([LiLiangYuZhou2023], Section 4.3, Claim 4.1 and Eq. (5), p. 17 /
PDF p. 18, extended with Markov's inequality on `nodeProbes` for the `c = 1` probe cap). -/
theorem sum_prob_not_isGoodSeg_le {Ω : Type*} [Fintype Ω]
    (T : MetaTree) (D : IndexedScheme Op Result cells w) (initLen stride : ℕ)
    (p : PMF Ω) (opsOf : Ω → List Op) {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) (ℓ b : ℕ)
    (hcost : ∑ ω, (p ω).toReal * (T.nodeCost D initLen stride (opsOf ω) ℓ b : ℝ) ≤
      (γ / 100) * (T.blockSize (ℓ + 1) : ℝ))
    (hprobe : ∑ ω, (p ω).toReal * (T.nodeProbes D initLen stride (opsOf ω) (ℓ + 1) b : ℝ) ≤
      (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * t) :
    (∑ i : Fin (T.fanout (ℓ + 1)), ∑ ω, (p ω).toReal *
        (if T.IsGoodSeg D initLen stride (opsOf ω) γ t ℓ b i then (0 : ℝ) else 1)) ≤
      (41 / 400) * (T.fanout (ℓ + 1) : ℝ) := by
  set m : ℝ := (T.blockSize ℓ : ℝ); set F : ℝ := (T.fanout (ℓ + 1) : ℝ)
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (T.blockSize_pos ℓ)
  have hblock : (T.blockSize (ℓ + 1) : ℝ) = m * F := by simp [m, F]
  let badInd (ω : Ω) (i : Fin (T.fanout (ℓ + 1))) : ℝ :=
    if (((T.segProbedCells D initLen stride (opsOf ω) ℓ b i ∩
        T.badCells D initLen stride (opsOf ω) ℓ b).card : ℕ) : ℝ) ≤ γ * m / 2 then 0 else 1
  let probeInd (ω : Ω) (i : Fin (T.fanout (ℓ + 1))) : ℝ :=
    if (((T.segProbedCells D initLen stride (opsOf ω) ℓ b i).card : ℕ) : ℝ) ≤ m * t then 0 else 1
  have hind_le (ω : Ω) (i : Fin (T.fanout (ℓ + 1))) :
      (if T.IsGoodSeg D initLen stride (opsOf ω) γ t ℓ b i then (0 : ℝ) else 1) ≤
        badInd ω i + probeInd ω i := by
    by_cases h1 : (((T.segProbedCells D initLen stride (opsOf ω) ℓ b i ∩
        T.badCells D initLen stride (opsOf ω) ℓ b).card : ℕ) : ℝ) ≤ γ * m / 2 <;>
      by_cases h2 : (((T.segProbedCells D initLen stride (opsOf ω) ℓ b i).card : ℕ) : ℝ) ≤ m * t <;>
      simp [IsGoodSeg, badInd, probeInd, m, h1, h2]
  have hpt {a c : ℝ} (hc : 0 ≤ c) : a * (if c ≤ a then (0 : ℝ) else 1) ≤ c := by
    split_ifs with h1 <;> [exact (mul_zero a).trans_le hc; (push Not at h1; linarith)]
  have hbad_sum : (∑ i, ∑ ω, (p ω).toReal * badInd ω i) ≤ (1 / 25) * F := by
    have hmul : (γ * m / 2) * (∑ i, ∑ ω, (p ω).toReal * badInd ω i) ≤ 2 * ((γ / 100) * (m * F)) :=
      calc (γ * m / 2) * (∑ i, ∑ ω, (p ω).toReal * badInd ω i)
          = ∑ ω, (p ω).toReal * (∑ i, (γ * m / 2) * badInd ω i) := by
              rw [Finset.mul_sum]; simp_rw [Finset.mul_sum, mul_left_comm (γ * m / 2)]
              exact Finset.sum_comm
        _ ≤ ∑ ω, (p ω).toReal * (2 * (T.nodeCost D initLen stride (opsOf ω) ℓ b : ℝ)) := by
              refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
              exact (Finset.sum_le_sum fun i _ => hpt (Nat.cast_nonneg _)).trans
                (by exact_mod_cast (T.sum_card_segProbedCells_inter_badCells_le_two_mul_nodeCost
                  D initLen stride (opsOf ω) ℓ b))
        _ = 2 * (∑ ω, (p ω).toReal * (T.nodeCost D initLen stride (opsOf ω) ℓ b : ℝ)) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
        _ ≤ 2 * ((γ / 100) * (m * F)) := by rw [← hblock]; linarith
    have hpos : 0 < γ * m / 2 := by positivity
    nlinarith
  have hprobe_sum : (∑ i, ∑ ω, (p ω).toReal * probeInd ω i) ≤ (1 / 16) * F := by
    have hmul : (m * t) * (∑ i, ∑ ω, (p ω).toReal * probeInd ω i) ≤ (1 / 16) * (m * F) * t :=
      calc (m * t) * (∑ i, ∑ ω, (p ω).toReal * probeInd ω i)
          = ∑ ω, (p ω).toReal * (∑ i, (m * t) * probeInd ω i) := by
              rw [Finset.mul_sum]; simp_rw [Finset.mul_sum, mul_left_comm (m * t)]
              exact Finset.sum_comm
        _ ≤ ∑ ω, (p ω).toReal * (T.nodeProbes D initLen stride (opsOf ω) (ℓ + 1) b : ℝ) := by
              refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
              exact (Finset.sum_le_sum fun i _ => hpt (Nat.cast_nonneg _)).trans
                (by exact_mod_cast (T.sum_card_segProbedCells_le_nodeProbes D initLen stride
                  (opsOf ω) ℓ b))
        _ ≤ (1 / 16) * (m * F) * t := by rw [← hblock]; exact hprobe
    have hpos : 0 < m * t := by positivity
    nlinarith
  calc (∑ i : Fin (T.fanout (ℓ + 1)), ∑ ω, (p ω).toReal *
        (if T.IsGoodSeg D initLen stride (opsOf ω) γ t ℓ b i then (0 : ℝ) else 1))
      ≤ ∑ i, ∑ ω, (p ω).toReal * (badInd ω i + probeInd ω i) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun ω _ =>
            mul_le_mul_of_nonneg_left (hind_le ω i) ENNReal.toReal_nonneg
    _ = (∑ i, ∑ ω, (p ω).toReal * badInd ω i) + (∑ i, ∑ ω, (p ω).toReal * probeInd ω i) := by
          simp_rw [mul_add, Finset.sum_add_distrib]
    _ ≤ (41 / 400) * F := by linarith

open Classical in
/-- Claim 4.1 under the `c = 1` probe cap ([LiLiangYuZhou2023], Section 4.3, Claim 4.1, p. 17 /
PDF p. 18, adapted with `|S_A^{[i]}| ≤ m_ℓ * t`): across the first `λ_{ℓ+1} / 2` child segments of
internal node `(ℓ + 1, b)`, the expected number of good segments is at least `λ_{ℓ+1} / 4`. -/
theorem quarter_fanout_le_sum_prob_isGoodSeg {Ω : Type*} [Fintype Ω]
    (T : MetaTree) (D : IndexedScheme Op Result cells w) (initLen stride : ℕ)
    (p : PMF Ω) (opsOf : Ω → List Op) {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) (ℓ b : ℕ)
    (hcost : ∑ ω, (p ω).toReal * (T.nodeCost D initLen stride (opsOf ω) ℓ b : ℝ) ≤
      (γ / 100) * (T.blockSize (ℓ + 1) : ℝ))
    (hprobe : ∑ ω, (p ω).toReal * (T.nodeProbes D initLen stride (opsOf ω) (ℓ + 1) b : ℝ) ≤
      (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * t) :
    ((T.fanout (ℓ + 1) : ℝ) / 4) ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin (T.fanout (ℓ + 1)) => i.val < T.fanout (ℓ + 1) / 2),
        ∑ ω, (p ω).toReal *
          (if T.IsGoodSeg D initLen stride (opsOf ω) γ t ℓ b i then (1 : ℝ) else 0) := by
  set halfSet := Finset.univ.filter fun i : Fin (T.fanout (ℓ + 1)) => i.val < T.fanout (ℓ + 1) / 2
  obtain ⟨q, hq⟩ := T.even_fanout (ℓ + 1) (Nat.le_add_left 1 ℓ)
  have hhalf_card : halfSet.card = T.fanout (ℓ + 1) / 2 := by
    refine (Finset.card_bij (s := halfSet) (t := Finset.range (T.fanout (ℓ + 1) / 2))
      (fun i _ => i.val) (fun _ hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2)
      (fun _ _ _ _ h => Fin.ext h) fun r hr => ?_).trans (Finset.card_range _)
    exact ⟨⟨r, by have := Finset.mem_range.mp hr; omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hr⟩, rfl⟩
  have hhalf_real : (halfSet.card : ℝ) = (T.fanout (ℓ + 1) : ℝ) / 2 := by
    rw [hhalf_card, hq, Nat.mul_div_cancel_left q (by omega)]; push_cast; ring
  have hbad_half : (∑ i ∈ halfSet, ∑ ω, (p ω).toReal *
      (if T.IsGoodSeg D initLen stride (opsOf ω) γ t ℓ b i then (0 : ℝ) else 1)) ≤
      (41 / 400) * (T.fanout (ℓ + 1) : ℝ) :=
    (Finset.sum_le_univ_sum_of_nonneg fun _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> positivity)).trans
      (T.sum_prob_not_isGoodSeg_le D initLen stride p opsOf hγ ht ℓ b hcost hprobe)
  let gprob (i : Fin (T.fanout (ℓ + 1))) (v1 v0 : ℝ) : ℝ :=
    ∑ ω, (p ω).toReal * (if T.IsGoodSeg D initLen stride (opsOf ω) γ t ℓ b i then v1 else v0)
  have hcomp (i : Fin (T.fanout (ℓ + 1))) : gprob i 1 0 + gprob i 0 1 = 1 := by
    dsimp only [gprob]; rw [← Finset.sum_add_distrib]
    refine (Finset.sum_congr rfl fun ω _ => ?_).trans (Cslib.Probability.PMF.sum_toReal p)
    split_ifs <;> ring
  have hsum_eq : (∑ i ∈ halfSet, gprob i 1 0) + (∑ i ∈ halfSet, gprob i 0 1) =
      (T.fanout (ℓ + 1) : ℝ) / 2 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hcomp, Finset.sum_const, nsmul_eq_mul, mul_one, hhalf_real]
  linarith

end MetaTree

end Qualification

/-! ### Candidate segment simulations, set-permutation equivalence, and `HardKeyValSeed` -/

/-- Order an `m`-element subset `S` of `Fin U` by permutation `π : Equiv.Perm (Fin m)`. -/
def orderSubset {U m : ℕ} (S : Finset (Fin U)) (hS : S.card = m) (π : Equiv.Perm (Fin m)) :
    Fin m ↪ Fin U :=
  π.toEmbedding.trans (S.orderEmbOfFin hS).toEmbedding

@[simp] theorem orderSubset_apply {U m : ℕ} (S : Finset (Fin U)) (hS : S.card = m)
    (π : Equiv.Perm (Fin m)) (r : Fin m) :
    orderSubset S hS π r = S.orderEmbOfFin hS (π r) := by rfl

@[simp] theorem image_orderSubset {U m : ℕ} (S : Finset (Fin U)) (hS : S.card = m)
    (π : Equiv.Perm (Fin m)) : Finset.univ.image (orderSubset S hS π) = S := by
  ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and, orderSubset_apply]
  refine ⟨fun ⟨r, hr⟩ => hr ▸ Finset.orderEmbOfFin_mem S hS (π r), fun hx => ?_⟩
  obtain ⟨j, hj⟩ := (S.orderIsoOfFin hS).surjective ⟨x, hx⟩
  exact ⟨π.symm j, by simpa using congrArg Subtype.val hj⟩

/-- Bijection decomposing `f : Fin m ↪ Fin U` into its `m`-subset and relative order `π`. -/
noncomputable def embSetPermEquiv (U m : ℕ) :
    (Fin m ↪ Fin U) ≃ { S : Finset (Fin U) // S.card = m } × Equiv.Perm (Fin m) :=
  (Equiv.ofBijective (fun sp => orderSubset sp.1.val sp.1.property sp.2) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun ⟨⟨S₁, hS₁⟩, π₁⟩ ⟨⟨S₂, hS₂⟩, π₂⟩ heq => ?_, ?_⟩
    · dsimp only at heq
      have hS_eq : S₁ = S₂ := by
        rw [← image_orderSubset S₁ hS₁ π₁, ← image_orderSubset S₂ hS₂ π₂, heq]
      subst hS_eq; refine Prod.ext rfl (Equiv.ext fun r => ?_)
      exact (S₁.orderEmbOfFin hS₁).injective (congrArg (fun g : Fin m ↪ Fin U => g r) heq)
    · rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_embedding_eq, Fintype.card_fin,
        Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
      congr 1; simp [Fintype.card_fin])).symm

@[simp] theorem embSetPermEquiv_symm_apply (U m : ℕ)
    (S : { S : Finset (Fin U) // S.card = m }) (π : Equiv.Perm (Fin m)) :
    (embSetPermEquiv U m).symm (S, π) = orderSubset S.val S.property π := by rfl

@[simp] theorem embSetPermEquiv_fst (U m : ℕ) (f : Fin m ↪ Fin U) :
    ((embSetPermEquiv U m f).1 : Finset (Fin U)) = Finset.univ.image f := by
  conv_rhs => rw [← (embSetPermEquiv U m).symm_apply_apply f]
  rw [embSetPermEquiv_symm_apply, image_orderSubset]

/-- Candidate `[query, delete, insert]` segment sequence of length `3 * m` ([LiLiangYuZhou2023],
Section 4.2, p. 15 / PDF p. 16 and Section 5, p. 21 / PDF p. 22). -/
@[expose] def candidateQueryDeleteInsertOps {U V m : ℕ}
    (d b : Fin m → Fin U) (kv : Fin U → Fin V) : List (Dynamic.Op U) :=
  (List.finRange m).flatMap fun r => [.query (d r), .delete (d r), .insert (b r) (kv (b r)).val]

/-- Candidate `[delete, insert]` update-only segment sequence of length `2 * m`
([LiLiangYuZhou2023], Section 8, p. 28 / PDF p. 29). -/
@[expose] def candidateDeleteInsertOps {U V m : ℕ}
    (d b : Fin m → Fin U) (kv : Fin U → Fin V) : List (Dynamic.Op U) :=
  (List.finRange m).flatMap fun r => [.delete (d r), .insert (b r) (kv (b r)).val]

@[simp] theorem length_candidateQueryDeleteInsertOps {U V m : ℕ}
    (d b : Fin m → Fin U) (kv : Fin U → Fin V) :
    (candidateQueryDeleteInsertOps d b kv).length = 3 * m := by
  rw [candidateQueryDeleteInsertOps,
    List.length_flatMap_of_forall_length_eq (k := 3) (fun _ _ => rfl),
    List.length_finRange, Nat.mul_comm]

@[simp] theorem length_candidateDeleteInsertOps {U V m : ℕ}
    (d b : Fin m → Fin U) (kv : Fin U → Fin V) :
    (candidateDeleteInsertOps d b kv).length = 2 * m := by
  rw [candidateDeleteInsertOps,
    List.length_flatMap_of_forall_length_eq (k := 2) (fun _ _ => rfl),
    List.length_finRange, Nat.mul_comm]

theorem candidateQueryDeleteInsertOps_congr {U V m : ℕ}
    (d : Fin m → Fin U) {B : Finset (Fin U)} (hB : B.card = m) (π : Equiv.Perm (Fin m))
    {kv₁ kv₂ : Fin U → Fin V} (hkv : ∀ x ∈ B, kv₁ x = kv₂ x) :
    candidateQueryDeleteInsertOps d (orderSubset B hB π) kv₁ =
      candidateQueryDeleteInsertOps d (orderSubset B hB π) kv₂ := by
  simp only [candidateQueryDeleteInsertOps]; refine List.flatMap_congr fun r _ => ?_
  rw [hkv _ (by rw [orderSubset_apply]; exact Finset.orderEmbOfFin_mem B hB (π r))]

/-- Injective sequence of `m` keys deleted during meta-operations `[t₀, t₀ + m)`. -/
def segDeletedKeys {U n : ℕ} (keys : Fin (2 * n) ↪ Fin U) (delPerm : Equiv.Perm (Fin n))
    (t₀ m : ℕ) (ht : t₀ + m ≤ n) : Fin m ↪ Fin U where
  toFun r := keys ⟨(delPerm ⟨t₀ + r.val, by omega⟩).val, by omega⟩
  inj' r₁ r₂ h := Fin.ext (by
    have hk := congrArg (Fin.val (n := 2 * n)) (keys.injective h)
    have hd := congrArg Fin.val (delPerm.injective (Fin.ext hk)); dsimp only at hd; omega)

@[simp] theorem segDeletedKeys_apply {U n : ℕ} (keys : Fin (2 * n) ↪ Fin U)
    (delPerm : Equiv.Perm (Fin n)) (t₀ m : ℕ) (ht : t₀ + m ≤ n) (r : Fin m) :
    segDeletedKeys keys delPerm t₀ m ht r = keys ⟨(delPerm ⟨t₀ + r.val, by omega⟩).val, by omega⟩ :=
  by rfl

/-- Injective sequence of `m` keys inserted during meta-operations `[t₀, t₀ + m)`. -/
def segInsertedKeys {U n : ℕ} (keys : Fin (2 * n) ↪ Fin U)
    (t₀ m : ℕ) (ht : t₀ + m ≤ n) : Fin m ↪ Fin U where
  toFun r := keys ⟨n + (t₀ + r.val), by omega⟩
  inj' _ _ h := Fin.ext (by have hk := congrArg Fin.val (keys.injective h); dsimp only at hk; omega)

@[simp] theorem segInsertedKeys_apply {U n : ℕ} (keys : Fin (2 * n) ↪ Fin U)
    (t₀ m : ℕ) (ht : t₀ + m ≤ n) (r : Fin m) :
    segInsertedKeys keys t₀ m ht r = keys ⟨n + (t₀ + r.val), by omega⟩ := by rfl

private theorem elemSlice_eq_flatMap_of_drop_take {Op : Type*} (initLen stride n : ℕ)
    (ops : List Op) (metaOp : Fin n → List Op)
    (hunit : ∀ j : Fin n, (ops.drop (initLen + stride * j.val)).take stride = metaOp j)
    {t₀ m : ℕ} (ht : t₀ + m ≤ n) :
    elemSlice initLen stride ops t₀ (t₀ + m) =
      (List.finRange m).flatMap (fun r => metaOp ⟨t₀ + r.val, by omega⟩) := by
  induction m with
  | zero => simp [elemSlice]
  | succ m ih =>
    have hsplit : elemSlice initLen stride ops t₀ (t₀ + (m + 1)) =
        elemSlice initLen stride ops t₀ (t₀ + m) ++
          (ops.drop (initLen + stride * (t₀ + m))).take stride := by
      simp only [elemSlice, show t₀ + (m + 1) - t₀ = m + 1 by omega,
        show t₀ + m - t₀ = m by omega, Nat.mul_add, Nat.mul_one, List.take_add, List.drop_drop,
        show initLen + stride * t₀ + stride * m = initLen + stride * (t₀ + m) by ring]
    rw [hsplit, ih (by omega), hunit ⟨t₀ + m, by omega⟩, List.finRange_succ_last,
      List.flatMap_append, List.flatMap_map]
    simp [Fin.val_castSucc, Fin.val_last]

/-- When per-step values are induced by `kv : Fin U → Fin V`, `elemSlice` on `insertQueryDeleteSeq`
over `[t₀, t₀ + m)` equals `candidateQueryDeleteInsertOps` on the true deleted and inserted keys. -/
theorem elemSlice_insertQueryDeleteSeq_eq_candidate {U V n t₀ m : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (kv : Fin U → Fin V) (delPerm : Equiv.Perm (Fin n))
    (ht : t₀ + m ≤ n) :
    elemSlice n 3 (insertQueryDeleteSeq keys (fun idx => kv (keys idx)) delPerm) t₀ (t₀ + m) =
      candidateQueryDeleteInsertOps (segDeletedKeys keys delPerm t₀ m ht)
        (segInsertedKeys keys t₀ m ht) kv := by
  rw [elemSlice_eq_flatMap_of_drop_take n 3 n _ _
    (drop_take_insertQueryDeleteSeq keys (fun idx => kv (keys idx)) delPerm) ht]; rfl

/-- Update-only counterpart of `elemSlice_insertQueryDeleteSeq_eq_candidate`. -/
theorem elemSlice_insertDeleteSeq_eq_candidate {U V n t₀ m : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (kv : Fin U → Fin V) (delPerm : Equiv.Perm (Fin n))
    (ht : t₀ + m ≤ n) :
    elemSlice n 2 (insertDeleteSeq keys (fun idx => kv (keys idx)) delPerm) t₀ (t₀ + m) =
      candidateDeleteInsertOps (segDeletedKeys keys delPerm t₀ m ht)
        (segInsertedKeys keys t₀ m ht) kv := by
  rw [elemSlice_eq_flatMap_of_drop_take n 2 n _ _
    (drop_take_insertDeleteSeq keys (fun idx => kv (keys idx)) delPerm) ht]; rfl

/-- Pulling back a uniform value table `kv : Fin U → Fin V` along any injective `keys` gives the
uniform distribution on `Fin k → Fin V`. -/
theorem map_comp_keys_uniformOfFintype {U V k : ℕ} (hV : 1 ≤ V) (keys : Fin k ↪ Fin U) :
    letI : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
    (PMF.uniformOfFintype (Fin U → Fin V)).map (fun kv i => kv (keys i)) =
      PMF.uniformOfFintype (Fin k → Fin V) := by
  let _ : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
  set I : Finset (Fin U) := Finset.univ.image keys
  let eIdx : Fin k ≃ I := Equiv.ofBijective
    (fun i => ⟨keys i, Finset.mem_image_of_mem keys (Finset.mem_univ i)⟩) (by
      rw [Fintype.bijective_iff_injective_and_card, Fintype.card_fin, Fintype.card_coe,
        Finset.card_image_of_injective _ keys.injective, Finset.card_fin]
      exact ⟨fun _ _ h => keys.injective (congrArg Subtype.val h), rfl⟩)
  let pull : (I → Fin V) ≃ (Fin k → Fin V) := Equiv.piCongrLeft' (fun _ => Fin V) eIdx.symm
  have hcomp : (fun (kv : Fin U → Fin V) i => kv (keys i)) = pull ∘ I.restrict := by
    funext kv i; change kv (keys i) = pull (I.restrict kv) i; simp [pull, Finset.restrict, eIdx]
  rw [hcomp, ← _root_.PMF.map_comp, PMF.uniformOfFintype_pi_map_restrict I,
    PMF.uniformOfFintype_map_equiv pull]

private theorem hardDist_eq_bind_keyVals {U V n : ℕ} (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (seq : (Fin (2 * n) ↪ Fin U) → (Fin (2 * n) → Fin V) →
      Equiv.Perm (Fin n) → List (Dynamic.Op U)) {dist : PMF (List (Dynamic.Op U))}
    (hdist : letI : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
      letI : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
      dist = (PMF.uniformOfFintype (((Fin (2 * n) ↪ Fin U) × (Fin (2 * n) → Fin V)) ×
        Equiv.Perm (Fin n))).map (fun ⟨⟨keys, vals⟩, delPerm⟩ => seq keys vals delPerm)) :
    letI : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
    letI : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
    dist = (PMF.uniformOfFintype (Fin (2 * n) ↪ Fin U)).bind fun keys =>
      (PMF.uniformOfFintype (Fin U → Fin V)).bind fun kv =>
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).map fun delPerm =>
          seq keys (fun idx => kv (keys idx)) delPerm := by
  let _ : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
  let _ : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
  rw [hdist, ← PMF.uniformOfFintype_prod, _root_.PMF.map_bind, ← PMF.uniformOfFintype_prod,
    _root_.PMF.bind_bind]
  congr 1 with keys; rw [← map_comp_keys_uniformOfFintype hV keys, _root_.PMF.bind_map]
  simp [_root_.PMF.map_comp, Function.comp_def]

/-- Global-value representation of `insertQueryDeleteDist` ([LiLiangYuZhou2023], Section 8, p. 28 /
PDF p. 29). -/
theorem insertQueryDeleteDist_eq_bind_keyVals {U V n : ℕ} (hU : 2 * n ≤ U) (hV : 1 ≤ V) :
    letI : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
    letI : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
    insertQueryDeleteDist U V n hU hV =
      (PMF.uniformOfFintype (Fin (2 * n) ↪ Fin U)).bind fun keys =>
        (PMF.uniformOfFintype (Fin U → Fin V)).bind fun kv =>
          (PMF.uniformOfFintype (Equiv.Perm (Fin n))).map fun delPerm =>
            insertQueryDeleteSeq keys (fun idx => kv (keys idx)) delPerm :=
  hardDist_eq_bind_keyVals hU hV _ (insertQueryDeleteDist_eq_uniformOfFintype_map hU hV)

/-- Update-only counterpart of `insertQueryDeleteDist_eq_bind_keyVals`. -/
theorem insertDeleteDist_eq_bind_keyVals {U V n : ℕ} (hU : 2 * n ≤ U) (hV : 1 ≤ V) :
    letI : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
    letI : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
    insertDeleteDist U V n hU hV =
      (PMF.uniformOfFintype (Fin (2 * n) ↪ Fin U)).bind fun keys =>
        (PMF.uniformOfFintype (Fin U → Fin V)).bind fun kv =>
          (PMF.uniformOfFintype (Equiv.Perm (Fin n))).map fun delPerm =>
            insertDeleteSeq keys (fun idx => kv (keys idx)) delPerm :=
  hardDist_eq_bind_keyVals hU hV _ (insertDeleteDist_eq_uniformOfFintype_map hU hV)

/-- Global-value seed `(keys, kv, delPerm)` underlying `insertQueryDeleteDist`. -/
@[ext] structure HardKeyValSeed (U V n : ℕ) where
  /-- Injective sequence of `2 * n` distinct keys drawn from `Fin U`. -/
  keys : Fin (2 * n) ↪ Fin U
  /-- Global value assignment mapping every universe key in `Fin U` to `Fin V`. -/
  kv : Fin U → Fin V
  /-- Permutation of `Fin n` ordering deletions among the `n` initially inserted keys. -/
  delPerm : Equiv.Perm (Fin n)
  deriving DecidableEq

/-- Deletion-ordered key embedding `(liftDelPerm s.delPerm).toEmbedding.trans s.keys`. -/
@[expose] def HardKeyValSeed.permKeyEmb {U V n : ℕ} (s : HardKeyValSeed U V n) :
    Fin (2 * n) ↪ Fin U := (liftDelPerm s.delPerm).toEmbedding.trans s.keys

/-- Reparametrized product equivalence on `HardKeyValSeed U V n` via `permKeyEmb`. -/
def hardKeyValSeedReparamEquiv (U V n : ℕ) :
    HardKeyValSeed U V n ≃ ((Fin (2 * n) ↪ Fin U) × Equiv.Perm (Fin n)) × (Fin U → Fin V) where
  toFun s := ((s.permKeyEmb, s.delPerm), s.kv)
  invFun := fun ⟨⟨pk, d⟩, kv⟩ => ⟨(liftDelPerm d.symm).toEmbedding.trans pk, kv, d⟩
  left_inv s := by ext m <;> simp [HardKeyValSeed.permKeyEmb, ← liftDelPerm_symm]
  right_inv := fun ⟨⟨_, _⟩, _⟩ => by ext m <;> simp [HardKeyValSeed.permKeyEmb, ← liftDelPerm_symm]

noncomputable instance (U V n : ℕ) : Fintype (HardKeyValSeed U V n) :=
  Fintype.ofEquiv _ (hardKeyValSeedReparamEquiv U V n).symm

/-- Full `4 * n`-operation `[query, delete, insert]` sequence generated by `s`. -/
@[expose] def HardKeyValSeed.ops {U V n : ℕ} (s : HardKeyValSeed U V n) : List (Dynamic.Op U) :=
  insertQueryDeleteSeq s.keys (fun idx => s.kv (s.keys idx)) s.delPerm

/-- Active size-`n` key set `K` before meta-operation `t₀ ≤ n`. -/
@[expose] def HardKeyValSeed.activeKeys {U V n : ℕ} (s : HardKeyValSeed U V n)
    (t₀ : ℕ) (ht : t₀ ≤ n) : Finset (Fin U) := Finset.univ.map (windowEmb s.permKeyEmb t₀ ht)

/-- Size-`r` key set inserted during meta-operations `[t₀, t₀ + r)`. -/
@[expose] def HardKeyValSeed.insertedSet {U V n : ℕ} (s : HardKeyValSeed U V n)
    (t₀ r : ℕ) (ht : t₀ + r ≤ n) : Finset (Fin U) :=
  Finset.univ.image (segInsertedKeys s.keys t₀ r ht)

/-- Candidate `[query, delete, insert]` segment sequence for candidate set `B` (`B.card = m`). -/
noncomputable def HardKeyValSeed.candidateOps {U V n : ℕ} (s : HardKeyValSeed U V n)
    (t₀ m : ℕ) (ht : t₀ + m ≤ n) (B : Finset (Fin U)) (hB : B.card = m) : List (Dynamic.Op U) :=
  candidateQueryDeleteInsertOps (segDeletedKeys s.keys s.delPerm t₀ m ht)
    (orderSubset B hB (embSetPermEquiv U m (segInsertedKeys s.keys t₀ m ht)).2) s.kv

@[simp] theorem HardKeyValSeed.candidateOps_eq {U V n : ℕ} (s : HardKeyValSeed U V n)
    (t₀ m : ℕ) (ht : t₀ + m ≤ n) (B : Finset (Fin U)) (hB : B.card = m) :
    s.candidateOps t₀ m ht B hB = candidateQueryDeleteInsertOps
      (segDeletedKeys s.keys s.delPerm t₀ m ht)
      (orderSubset B hB (embSetPermEquiv U m (segInsertedKeys s.keys t₀ m ht)).2) s.kv := by rfl

/-- Dictionary state reached after `n` initial insertions and `t ≤ n` meta-operations of `s.ops`. -/
theorem HardKeyValSeed.run_take_ops_fst {U V n t : ℕ} (s : HardKeyValSeed U V n) (ht : t ≤ n) :
    ((Dynamic.spec U V n).run (Dictionary.empty U) (s.ops.take (n + 3 * t))).1 =
      (windowDict s.permKeyEmb (fun idx => s.kv (s.permKeyEmb idx)) t ht).1 := by
  set vals := fun idx => s.kv (s.keys idx); set pvals := fun idx => s.kv (s.permKeyEmb idx)
  have hinit : ((Dynamic.spec U V n).run (Dictionary.empty U) (initInsertSeq s.keys vals)).1 =
      ((Dynamic.spec U V n).run (Dictionary.empty U) (initInsertSeq s.permKeyEmb pvals)).1 := by
    rw [run_initInsertSeq_fst, run_initInsertSeq_fst, windowDict_coe, windowDict_coe]
    have hemb (k : Fin n) : windowEmb s.permKeyEmb 0 (Nat.zero_le n) k =
        windowEmb s.keys 0 (Nat.zero_le n) (s.delPerm k) := by simp [HardKeyValSeed.permKeyEmb]
    funext u; by_cases hex : ∃ i : Fin n, windowEmb s.keys 0 (Nat.zero_le n) i = u
    · obtain ⟨i, rfl⟩ := hex
      have hk := hemb (s.delPerm.symm i); rw [Equiv.apply_symm_apply] at hk
      rw [dictOfEmb_apply_self, ← hk, dictOfEmb_apply_self]
      simp [vals, pvals, HardKeyValSeed.permKeyEmb]
    · push Not at hex
      rw [dictOfEmb_apply_eq_none _ _ hex,
        dictOfEmb_apply_eq_none _ _ fun k => by rw [hemb]; exact hex _]
  have hmeta (j : Fin n) : queryDeleteInsertMetaOp s.keys vals s.delPerm j =
      queryDeleteInsertMetaOp s.permKeyEmb pvals (Equiv.refl (Fin n)) j := by
    simp [queryDeleteInsertMetaOp, vals, pvals, HardKeyValSeed.permKeyEmb]
  have hrhs :=
    (validHistory_and_run_take_insertQueryDeleteSeq s.permKeyEmb pvals (Equiv.refl (Fin n)) ht).2
  rw [take_insertQueryDeleteSeq, StateTransitionSpec.run_append, activeWindowDict_refl] at hrhs
  rw [HardKeyValSeed.ops, take_insertQueryDeleteSeq, StateTransitionSpec.run_append]
  dsimp only at hrhs ⊢
  rw [hinit, List.flatMap_congr fun j _ => hmeta j]; exact hrhs

/-- Pushing `PMF.uniformOfFintype (HardKeyValSeed U V n)` forward by `HardKeyValSeed.ops` recovers
`insertQueryDeleteDist U V n hU hV`. -/
theorem map_ops_uniformOfFintype_hardKeyValSeed {U V n : ℕ} (hU : 2 * n ≤ U) (hV : 1 ≤ V) :
    letI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
    (PMF.uniformOfFintype (HardKeyValSeed U V n)).map HardKeyValSeed.ops =
      insertQueryDeleteDist U V n hU hV := by
  let _ : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
  let _ : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
  let e : (((Fin (2 * n) ↪ Fin U) × (Fin U → Fin V)) × Equiv.Perm (Fin n)) ≃
      HardKeyValSeed U V n :=
    ⟨fun ⟨⟨k, kv⟩, d⟩ => ⟨k, kv, d⟩, fun s => ((s.keys, s.kv), s.delPerm),
      fun ⟨⟨_, _⟩, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩
  rw [insertQueryDeleteDist_eq_bind_keyVals hU hV, ← PMF.uniformOfFintype_map_equiv e,
    _root_.PMF.map_comp, ← PMF.uniformOfFintype_prod, _root_.PMF.map_bind,
    ← PMF.uniformOfFintype_prod, _root_.PMF.bind_bind]
  congr 1 with keys; congr 1 with kv
  simp [_root_.PMF.map_comp, Function.comp_def, e, HardKeyValSeed.ops]

/-! ### Binomial logarithm estimates and candidate neighborhood counting (Sections 4.3 & 5.2) -/

/-- Real-division form of `Nat.choose_mul_pow_le` at `a = k`: `((N : ℝ) / k) ^ k ≤ N.choose k`. -/
theorem div_pow_le_choose {N k : ℕ} (hk : k ≤ N) : ((N : ℝ) / (k : ℝ)) ^ k ≤ (N.choose k : ℝ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp
  · rw [div_pow, div_le_iff₀ (pow_pos (by exact_mod_cast hpos) k)]
    exact_mod_cast (by simpa [Nat.choose_self] using Nat.choose_mul_pow_le hk k)

/-- Base-2 logarithmic form of `div_pow_le_choose` for `1 ≤ k ≤ N`. -/
theorem mul_logb_div_le_logb_choose {N k : ℕ} (hk₀ : 1 ≤ k) (hk : k ≤ N) :
    (k : ℝ) * Real.logb 2 ((N : ℝ) / (k : ℝ)) ≤ Real.logb 2 (N.choose k) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk₀
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hk_pos (by exact_mod_cast hk)
  simpa [Real.logb_pow] using Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (div_pos hN_pos hk_pos) k) (div_pow_le_choose hk)

/-- Base-2 logarithmic form of `Nat.choose_le_exp_mul_div_pow` for `k ≤ N`. -/
theorem logb_choose_le_mul_logb_exp_mul_div {N k : ℕ} (hk : k ≤ N) :
    Real.logb 2 (N.choose k) ≤ (k : ℝ) * Real.logb 2 (Real.exp 1 * (N : ℝ) / (k : ℝ)) := by
  simpa [Real.logb_pow] using Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast Nat.choose_pos hk) (Nat.choose_le_exp_mul_div_pow N k)

/-- Base-2 logarithm of `(n + m).choose m` for `1 ≤ m ≤ n` ([LiLiangYuZhou2023], Section 5.2,
p. 25 / PDF p. 26): `log₂ C(n + m, m) ≤ 3 * m + m * log₂ (n / m)`. -/
theorem logb_add_choose_le {n m : ℕ} (hm₀ : 1 ≤ m) (hmn : m ≤ n) :
    Real.logb 2 ((n + m).choose m) ≤ 3 * (m : ℝ) + (m : ℝ) * Real.logb 2 ((n : ℝ) / (m : ℝ)) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm₀
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hm_pos (by exact_mod_cast hmn)
  have h1 := logb_choose_le_mul_logb_exp_mul_div (Nat.le_add_left m n)
  have hnm : ((n + m : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    push_cast; linarith [show (m : ℝ) ≤ n by exact_mod_cast hmn]
  have h2 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
    (show Real.exp 1 * ((n + m : ℕ) : ℝ) / (m : ℝ) ≤ 8 * ((n : ℝ) / (m : ℝ)) by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right
        (by nlinarith [Real.exp_pos 1, Real.exp_one_lt_d9]) hm_pos.le)
  rw [show (8 : ℝ) * ((n : ℝ) / (m : ℝ)) = (2 : ℝ) ^ (3 : ℕ) * ((n : ℝ) / (m : ℝ)) by ring,
    Real.logb_mul (by positivity) (div_pos hn_pos hm_pos).ne', Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h2; nlinarith

/-- Shrinking `U` by `d` (`k ≤ U - d`, `2 * d + k ≤ U + 1`) multiplies `choose · k` by `≤ 2 ^ k`. -/
theorem choose_le_two_pow_mul_choose_sub {U d k : ℕ} (hk : k ≤ U - d) (h : 2 * d + k ≤ U + 1) :
    U.choose k ≤ 2 ^ k * (U - d).choose k := by
  refine Nat.le_of_mul_le_mul_left (c := (U - d + 1 - k) ^ k) ?_ (Nat.pow_pos (by omega))
  calc (U - d + 1 - k) ^ k * U.choose k
      ≤ (U - d).choose k * (U + 1 - k) ^ k :=
        Nat.pow_mul_choose_le_choose_mul_pow (d := U - d) (m := U) (s := k) (Nat.sub_le U d)
    _ ≤ (U - d).choose k * (2 * (U - d + 1 - k)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
    _ = (U - d + 1 - k) ^ k * (2 ^ k * (U - d).choose k) := by rw [Nat.mul_pow]; ring

/-- Logarithmic form of `choose_le_two_pow_mul_choose_sub` ([LiLiangYuZhou2023], Section 5.2,
pp. 24–25 / PDF pp. 25–26): `log₂ C(U, k) - log₂ C(U - d, k) ≤ k`. -/
theorem logb_choose_sub_logb_choose_sub_le {U d k : ℕ} (hk : k ≤ U - d) (h : 2 * d + k ≤ U + 1) :
    Real.logb 2 (U.choose k) - Real.logb 2 ((U - d).choose k) ≤ (k : ℝ) := by
  have hp1 : (0 : ℝ) < (U.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (hk.trans (Nat.sub_le U d))
  have hp2 : (0 : ℝ) < ((U - d).choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hp1
    (show (U.choose k : ℝ) ≤ (2 : ℝ) ^ k * ((U - d).choose k : ℝ) by
      exact_mod_cast choose_le_two_pow_mul_choose_sub hk h)
  rw [Real.logb_mul (by positivity) hp2.ne', Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog; linarith

/-- Exact cardinality of `{B ∈ R.powersetCard m | (A ∩ B).card = g}` for `A ⊆ R`, `A.card = m`. -/
theorem card_inter_filter_powersetCard {α : Type*} [DecidableEq α]
    {R A : Finset α} {m g : ℕ} (hsub : A ⊆ R) (hA : A.card = m) :
    ((R.powersetCard m).filter fun B => (A ∩ B).card = g).card =
      m.choose g * (R.card - m).choose (m - g) := by
  by_cases hg : g ≤ m
  · have hbij : ((R.powersetCard m).filter fun B => (A ∩ B).card = g).card =
        (A.powersetCard g ×ˢ (R \ A).powersetCard (m - g)).card := by
      refine Finset.card_bij (fun B _ => (A ∩ B, B \ A)) ?_ ?_ ?_
      · intro B hB; simp only [Finset.mem_filter, Finset.mem_powersetCard] at hB
        obtain ⟨⟨hBR, hBm⟩, hgB⟩ := hB
        have hdisj : Disjoint (A ∩ B) (B \ A) := Finset.disjoint_left.mpr fun _ hx₁ hx₂ =>
          (Finset.mem_sdiff.mp hx₂).2 (Finset.mem_inter.mp hx₁).1
        have hunion : (A ∩ B) ∪ (B \ A) = B := by
          ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
        have hsum := Finset.card_union_of_disjoint hdisj; rw [hunion, hBm, hgB] at hsum
        simp only [Finset.mem_product, Finset.mem_powersetCard]
        exact ⟨⟨Finset.inter_subset_left, hgB⟩,
          ⟨fun x hx => Finset.mem_sdiff.mpr ⟨hBR (Finset.mem_sdiff.mp hx).1,
            (Finset.mem_sdiff.mp hx).2⟩, by omega⟩⟩
      · intro B₁ _ B₂ _ heq; rcases Prod.mk.inj heq with ⟨hP, hQ⟩
        ext x; have h₁ : x ∈ B₁ ↔ x ∈ (A ∩ B₁) ∪ (B₁ \ A) := by
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
        have h₂ : x ∈ B₂ ↔ x ∈ (A ∩ B₂) ∪ (B₂ \ A) := by
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
        rw [h₁, h₂, hP, hQ]
      · rintro ⟨P, Q⟩ hmem; simp only [Finset.mem_product, Finset.mem_powersetCard] at hmem
        obtain ⟨⟨hPA, hPc⟩, ⟨hQR, hQc⟩⟩ := hmem
        have hdisj : Disjoint P Q :=
          Finset.disjoint_left.mpr fun _ hx₁ hx₂ => (Finset.mem_sdiff.mp (hQR hx₂)).2 (hPA hx₁)
        have hi : A ∩ (P ∪ Q) = P := by
          ext x; simp only [Finset.mem_inter, Finset.mem_union]
          exact ⟨fun ⟨hxA, hxU⟩ => hxU.elim id fun hxQ =>
            False.elim ((Finset.mem_sdiff.mp (hQR hxQ)).2 hxA), fun hxP => ⟨hPA hxP, Or.inl hxP⟩⟩
        have hs : (P ∪ Q) \ A = Q := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
          exact ⟨fun ⟨hxU, hnA⟩ => hxU.elim (fun hxP => (hnA (hPA hxP)).elim) id,
            fun hxQ => ⟨Or.inr hxQ, (Finset.mem_sdiff.mp (hQR hxQ)).2⟩⟩
        exact ⟨P ∪ Q, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
          ⟨Finset.union_subset (hPA.trans hsub) (hQR.trans Finset.sdiff_subset),
            by rw [Finset.card_union_of_disjoint hdisj, hPc, hQc]; omega⟩, by rw [hi, hPc]⟩,
          Prod.ext hi hs⟩
    rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
      Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hA]
  · rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro B _; have := Finset.card_le_card (Finset.inter_subset_left (s₁ := A) (s₂ := B)); omega

/-- Exact cardinality decomposition of `{B ∈ R.powersetCard m | k ≤ (A ∩ B).card}` for `A ⊆ R`
with `A.card = m` ([LiLiangYuZhou2023], Section 4.3, Claim 4.6, p. 19 / PDF p. 20). -/
theorem card_filter_powersetCard_inter_ge {α : Type*} [DecidableEq α]
    {R A : Finset α} {m k : ℕ} (hsub : A ⊆ R) (hA : A.card = m) :
    ((R.powersetCard m).filter fun B => k ≤ (A ∩ B).card).card =
      ∑ j ∈ Finset.Icc k m, m.choose j * (R.card - m).choose (m - j) := by
  have heq : (R.powersetCard m).filter (fun B => k ≤ (A ∩ B).card) =
      (Finset.Icc k m).biUnion fun j => (R.powersetCard m).filter fun B => (A ∩ B).card = j := by
    ext B; simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Icc]
    refine ⟨fun ⟨hB, hkB⟩ => ⟨(A ∩ B).card, ⟨hkB,
      hA ▸ Finset.card_le_card Finset.inter_subset_left⟩, hB, rfl⟩, ?_⟩
    rintro ⟨j, ⟨hkj, _⟩, hB, rfl⟩; exact ⟨hB, hkj⟩
  rw [heq, Finset.card_biUnion (fun i _ j _ hij => Finset.disjoint_filter.mpr fun _ _ hi hj =>
    hij (hi.symm.trans hj))]
  exact Finset.sum_congr rfl fun j _ => card_inter_filter_powersetCard hsub hA

/-- Upper bound on `|F_nbr|` ([LiLiangYuZhou2023], Section 4.3, Claim 4.6, p. 19 / PDF p. 20). -/
theorem card_filter_powersetCard_inter_ge_half_le {α : Type*} [DecidableEq α]
    {R A : Finset α} {m F : ℕ} (hm_even : 2 ∣ m) (hm : 2 ≤ m) (hF : 2 ≤ F)
    (hsub : A ⊆ R) (hA : A.card = m) (hR : R.card ≤ F * m) :
    ((R.powersetCard m).filter fun B => m / 2 ≤ (A ∩ B).card).card ≤
      m * m.choose (m / 2) * (F * m).choose (m / 2) := by
  rw [card_filter_powersetCard_inter_ge hsub hA]
  have h2m_le : 2 * m ≤ F * m := Nat.mul_le_mul_right m hF
  have hterm : ∀ j ∈ Finset.Icc (m / 2) m,
      m.choose j * (R.card - m).choose (m - j) ≤ m.choose (m / 2) * (F * m).choose (m / 2) := by
    intro j hj; rw [Finset.mem_Icc] at hj
    have hmj_le : m - j ≤ m / 2 := by obtain ⟨mh, rfl⟩ := hm_even; omega
    have hmono : ∀ {a b N : ℕ}, a ≤ b → b ≤ N / 2 → N.choose a ≤ N.choose b := by
      intro a b N hab hbN; induction hab with
      | refl => exact le_rfl
      | @step _ _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
    exact Nat.mul_le_mul (Nat.choose_le_middle j m)
      ((Nat.choose_le_choose (m - j) ((Nat.sub_le _ _).trans hR)).trans (hmono hmj_le (by omega)))
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, smul_eq_mul, Nat.card_Icc, mul_assoc]
  exact Nat.mul_le_mul_right _ (by omega)

/-- Section 4.3 Claim 4.6 ([LiLiangYuZhou2023], Section 4.3, Claim 4.6 and Eq. (7), p. 19 /
PDF p. 20): `log₂ |F_all| - log₂ |F_nbr| ≥ (1 / 4) * m * log₂ F`. -/
theorem quarter_mul_logb_le_logb_powersetCard_sub_nbr {α : Type*} [DecidableEq α]
    {R A : Finset α} {m F : ℕ} (hm_even : 2 ∣ m) (hm : 2 ≤ m) (hF_even : 2 ∣ F) (hF : 2 ^ 20 ≤ F)
    (hsub : A ⊆ R) (hA : A.card = m) (hR_lo : (F / 2) * m ≤ R.card) (hR_hi : R.card ≤ F * m) :
    (1 / 4 : ℝ) * (m : ℝ) * Real.logb 2 F ≤
      Real.logb 2 (R.powersetCard m).card -
        Real.logb 2 ((R.powersetCard m).filter fun B => m / 2 ≤ (A ∩ B).card).card := by
  have hm_le_Fm : m ≤ F * m := le_mul_of_one_le_left (Nat.zero_le m) (by omega)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hall_ge : (m : ℝ) * Real.logb 2 F - (m : ℝ) ≤ Real.logb 2 (R.powersetCard m).card := by
    rw [Finset.card_powersetCard]
    have h1 := mul_logb_div_le_logb_choose (by omega)
      ((Nat.le_mul_of_pos_left m (by omega : 0 < F / 2)).trans hR_lo)
    have hdiv_ge : (F : ℝ) / 2 ≤ (R.card : ℝ) / (m : ℝ) := by
      obtain ⟨q, hq⟩ := hF_even
      have hFh : ((F / 2 : ℕ) : ℝ) = (F : ℝ) / 2 := by
        rw [hq, Nat.mul_div_cancel_left q (by omega)]; push_cast; ring
      rw [← hFh, le_div_iff₀ hm_pos]; exact_mod_cast hR_lo
    have hlog_ge := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hdiv_ge
    rw [Real.logb_div (by positivity) (by norm_num),
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hlog_ge; nlinarith
  set nbr := (R.powersetCard m).filter fun B => m / 2 ≤ (A ∩ B).card
  have hnbr_pos : (0 : ℝ) < (nbr.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr
    ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, hA⟩,
      by rw [Finset.inter_self, hA]; exact Nat.div_le_self m 2⟩⟩)
  have hhalf_le_Fm : m / 2 ≤ F * m := (Nat.div_le_self m 2).trans hm_le_Fm
  have hprod_pos : (0 : ℝ) < ((F * m).choose (m / 2) : ℝ) := by
    exact_mod_cast Nat.choose_pos hhalf_le_Fm
  have hnbr_real : (nbr.card : ℝ) ≤ (2 : ℝ) ^ (2 * m) * ((F * m).choose (m / 2) : ℝ) := by
    exact_mod_cast ((card_filter_powersetCard_inter_ge_half_le hm_even hm (by omega) hsub hA
      hR_hi).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul Nat.lt_two_pow_self.le
      (Nat.choose_le_two_pow m (m / 2))))).trans_eq (by rw [← pow_add, two_mul])
  have hlog_nbr1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hnbr_pos hnbr_real
  rw [Real.logb_mul (by positivity) hprod_pos.ne', Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one, Nat.cast_mul,
    Nat.cast_ofNat] at hlog_nbr1
  obtain ⟨m_half, hm_eq⟩ := hm_even
  have hm_half_real : ((m / 2 : ℕ) : ℝ) = (m : ℝ) / 2 := by
    rw [hm_eq, Nat.mul_div_cancel_left m_half (by omega)]; push_cast; ring
  have hlog_fm := logb_choose_le_mul_logb_exp_mul_div hhalf_le_Fm
  rw [show Real.exp 1 * ((F * m : ℕ) : ℝ) / ((m / 2 : ℕ) : ℝ) = 2 * Real.exp 1 * (F : ℝ) by
    rw [hm_half_real, Nat.cast_mul]; field_simp, hm_half_real] at hlog_fm
  have hF_pos : (0 : ℝ) < (F : ℝ) := by exact_mod_cast (show 0 < F by omega)
  have hlog_2eF : Real.logb 2 (2 * Real.exp 1 * (F : ℝ)) ≤ 3 + Real.logb 2 F := by
    rw [Real.logb_mul (by positivity) hF_pos.ne']
    have h2 : Real.logb 2 (2 * Real.exp 1) ≤ 3 :=
      (Real.logb_le_iff_le_rpow (by norm_num) (by positivity)).mpr
        (by have := Real.exp_one_lt_d9; norm_num; linarith)
    linarith
  have hlogF_ge : (20 : ℝ) ≤ Real.logb 2 F := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hF_pos,
      show (2 : ℝ) ^ (20 : ℝ) = ((2 ^ 20 : ℕ) : ℝ) by norm_num]; exact_mod_cast hF
  nlinarith

end Cslib.DataStructure.Dictionary.CellProbe
