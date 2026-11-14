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
public import CslibFrontier.Foundations.Combinatorics.Hypergeometric.IntersectionTail
public import CslibFrontier.Foundations.Data.Finset.OrderEmb
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.Nat.Choose
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Uniform
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
* `candidateQueryDeleteInsertOps`, `HardKeyValSeed`: candidate segment simulations and
  global-value seeds.

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
open Finset (orderSubset orderSubset_apply image_orderSubset embSetPermEquiv
  embSetPermEquiv_symm_apply embSetPermEquiv_fst)
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

/-! ### Candidate segment simulations and `HardKeyValSeed` -/

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
  congr 1 with keys; rw [← PMF.uniformOfFintype_pi_map_comp_embedding keys, _root_.PMF.bind_map]
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

noncomputable instance (U V n : ℕ) : Fintype (HardKeyValSeed U V n) :=
  Fintype.ofEquiv
    (((Fin (2 * n) ↪ Fin U) × Equiv.Perm (Fin n)) × (Fin U → Fin V))
    (Equiv.symm (show HardKeyValSeed U V n ≃
        ((Fin (2 * n) ↪ Fin U) × Equiv.Perm (Fin n)) × (Fin U → Fin V) from
      { toFun := fun s => ((s.permKeyEmb, s.delPerm), s.kv)
        invFun := fun ⟨⟨pk, d⟩, kv⟩ => ⟨(liftDelPerm d.symm).toEmbedding.trans pk, kv, d⟩
        left_inv := fun s => by ext m <;> simp [HardKeyValSeed.permKeyEmb, ← liftDelPerm_symm]
        right_inv := fun ⟨⟨_, _⟩, _⟩ => by
          ext m <;> simp [HardKeyValSeed.permKeyEmb, ← liftDelPerm_symm] }))

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
    (orderSubset B hB (embSetPermEquiv (Fin U) m (segInsertedKeys s.keys t₀ m ht)).2) s.kv

@[simp] theorem HardKeyValSeed.candidateOps_eq {U V n : ℕ} (s : HardKeyValSeed U V n)
    (t₀ m : ℕ) (ht : t₀ + m ≤ n) (B : Finset (Fin U)) (hB : B.card = m) :
    s.candidateOps t₀ m ht B hB = candidateQueryDeleteInsertOps
      (segDeletedKeys s.keys s.delPerm t₀ m ht)
      (orderSubset B hB (embSetPermEquiv (Fin U) m
        (segInsertedKeys s.keys t₀ m ht)).2) s.kv := by rfl

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

end Cslib.DataStructure.Dictionary.CellProbe
