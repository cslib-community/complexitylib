/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.WeightedCut.Contraction
public import CslibFrontier.Probability.PMF.Event
public import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Analysis.ENNRealOneSubInvPow
import CslibFrontier.Foundations.Data.Nat.Choose
import CslibFrontier.Foundations.Data.Nat.Div

/-!
# Supervertex contractions and Karger's survival bounds

Combinatorial and probabilistic core for Karger's randomized contraction algorithm `[Karger1993]`
and the Karger–Stein recursive algorithm `[KargerStein1996]` on `n`-vertex weighted undirected
multigraphs represented as symmetric zero-diagonal adjacency matrices `W : Fin n → Fin n → ℕ`.
Multigraphs, cut weights, global minimum cuts and contractions along supervertex maps are the
general notions of `CslibFrontier.Foundations.Combinatorics.WeightedCut` (`Cslib.WeightedCut`), and
the swap-compacted contraction of one pair of supervertices (`mergePair`, `embedCompact`,
`contractMatrix`, `contractPart`) is
`CslibFrontier.Foundations.Combinatorics.WeightedCut.Contraction`;
this module adds the row-major word-RAM layout of the matrix and its edge sampling.

## Source statements and notation mapping

* **Cut-survival bounds (paraphrase):**
  - `[Karger1993]`, Section 2, Theorem 2.1 and Corollary 2.1 (paraphrase): contracting randomly
    chosen edges in an `n`-vertex multigraph down to `2` meta-vertices preserves any fixed global
    minimum cut with probability at least `C(n, 2)⁻¹ = 2 / (n * (n - 1))`, and repeating
    `O(n ^ 2 log n)` independent trials finds a minimum cut with high probability.
  - `[KargerStein1996]`, Section 2, Lemma 2.1, Theorem 2.2, and Corollary 2.3, and Section 2.1,
    Corollary 2.4 (paraphrase): a fixed cut survives contraction if and only if no contracted edge
    crosses it; at `k` active supervertices every singleton cut has weight at least `minCut W`, so
    total doubled weight `S` is at least `k * minCut W`, a single edge-weight-proportional step
    crosses a fixed minimum cut with probability at most `2 / k`, and contracting from `n` down to
    `t` supervertices preserves the cut with probability at least
    `C(t, 2) / C(n, 2) = t * (t - 1) / (n * (n - 1))`.
  - `[MitzenmacherUpfal2017]`, Section 1.5, Theorem 1.8 (paraphrase): multiplying the conditional
    single-step survival bounds `1 - 2 / i = (i - 2) / i` for `i = n, …, 3` telescopes to
    `2 / (n * (n - 1))`.
* **Notation mapping and implementation variants:**
  - `C(t, 2) / C(n, 2)` and `C(n, 2)⁻¹` ↔ `((t * (t - 1) : ℕ) : ℝ≥0∞) / (n * (n - 1))` and
    `2 / (n * (n - 1))` (`step_survival_prob_ge`, `telescope_survival_step`);
  - `[KargerStein1996]`, Section 3.1, Lemma 3.1 selects `(u, v)` with probability
    `2 * W u v / S` via two `Random-Select` draws (`u` proportional to `D(u)` then `v` proportional
    to `W(u, v)`); our `edgeOffset` / `IsSampledPair` formalizes an equivalent single-draw variant
    using one uniform draw `r ∈ Fin S` (`S = totalDoubledWeight W = ∑ u, rowDeg W u`) resolved by
    prefix sums over `rowDeg` then row weights `W u v`, achieving the same `2 * W u v / S`
    distribution;
  - `[KargerStein1996]`, Section 3.2 (Figure 5) updates the `n × n` matrix in `O(n)` time per
    contraction (hence Corollary 3.2's `O(n ^ 2)` total); our `embedCompact` / `contractMatrix`
    swap-compacts active slot `k - 1` into the removed slot `v` so each contraction on `k` active
    supervertices scans only `0..k - 1` (`O(k)` time);
  - `highProbTrials n = (n * (n - 1) / 2) * (Nat.log 2 n + 2)` and the elementary `Real.exp`-free
    Bernoulli bound `highProb_failure_le` (`≤ 1 / (2 * n)`) are our own concrete parameter choices
    instantiating the `O(n ^ 2 log n)` repeated-trial amplification of `[Karger1993]`, Section 2,
    Corollary 2.1.

## Main definitions

* `Cslib.Algorithms.WordRAM.Karger.flattenMatrix`: row-major `n ^ 2`-element flattening.
* `Cslib.Algorithms.WordRAM.Karger.edgeOffset`, `Cslib.Algorithms.WordRAM.Karger.IsSampledPair`:
  prefix-sum interval characterization of edge-weight-proportional sampling from `Fin S`.

## Main results

* `Cslib.Algorithms.WordRAM.Karger.surviving_card_eq`,
  `Cslib.Algorithms.WordRAM.Karger.step_survival_prob_ge`: a fixed minimum cut survives one
  edge-proportional contraction on `k` supervertices with probability at least `(k - 2) / k`.
* `Cslib.Algorithms.WordRAM.Karger.telescope_survival_step`: telescoping multiplication identity
  `((m - 1) / (m + 1)) * (t * (t - 1) / (m * (m - 1))) = t * (t - 1) / ((m + 1) * m)` in `ℝ≥0∞`.
* `Cslib.Algorithms.WordRAM.Karger.highProb_failure_le`: elementary Bernoulli amplification bound
  `(1 - 2 / (n * (n - 1))) ^ ((n * (n - 1) / 2) * (Nat.log 2 n + 2)) ≤ 1 / (2 * n)`.

## References

* [D. R. Karger, *Global Min-cuts in RNC, and Other Ramifications of a Simple Min-Cut
  Algorithm*][Karger1993]
* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Karger

open scoped ENNReal
open Cslib.WeightedCut

/-! ### Row-major matrix flattening -/

/-- Row-major `n * n`-element list encoding of `W : Fin n → Fin n → ℕ`. -/
def flattenMatrix {n : ℕ} (W : Fin n → Fin n → ℕ) : List ℕ :=
  List.ofFn fun idx : Fin (n * n) =>
    W ⟨idx.val / n, Nat.div_lt_of_lt_mul idx.isLt⟩
      ⟨idx.val % n, Nat.mod_lt _
        (Nat.pos_of_ne_zero fun h0 => Nat.not_lt_zero idx.val (by simpa [h0] using idx.isLt))⟩

@[simp]
theorem length_flattenMatrix {n : ℕ} (W : Fin n → Fin n → ℕ) :
    (flattenMatrix W).length = n * n := by
  simp [flattenMatrix]

theorem getElem_flattenMatrix {n : ℕ} (W : Fin n → Fin n → ℕ) (u v : Fin n) :
    (flattenMatrix W)[u.val * n + v.val]'(by
      rw [length_flattenMatrix]
      nlinarith [u.isLt, v.isLt]) = W u v := by
  simp only [flattenMatrix, List.getElem_ofFn]
  have hdiv : (u.val * n + v.val) / n = u.val := Nat.mul_add_div_of_lt _ v.isLt
  have hmod : (u.val * n + v.val) % n = v.val := Nat.mul_add_mod_of_lt v.isLt
  congr 1 <;> exact Fin.ext (by assumption)

theorem mem_flattenMatrix_le_totalDoubledWeight {n : ℕ} (W : Fin n → Fin n → ℕ)
    {x : ℕ} (hx : x ∈ flattenMatrix W) :
    x ≤ totalDoubledWeight W := by
  unfold flattenMatrix at hx
  rw [List.mem_ofFn] at hx
  rcases hx with ⟨idx, rfl⟩
  exact entry_le_totalDoubledWeight W _ _

/-! ### Prefix-sum edge-proportional sampling on `Fin S` -/

/-- Sum of `rowDeg W a` over all `a < u`. -/
def degBefore {k : ℕ} (W : Fin k → Fin k → ℕ) (u : Fin k) : ℕ :=
  ∑ a ∈ Finset.univ.filter (· < u), rowDeg W a

/-- Sum of `W u b` over all `b < v`. -/
def weightBefore {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k) : ℕ :=
  ∑ b ∈ Finset.univ.filter (· < v), W u b

/-- Flattened prefix-sum start offset of directed edge slot `(u, v)` inside `[0, S)`. -/
def edgeOffset {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k) : ℕ :=
  degBefore W u + weightBefore W u v

theorem weightBefore_add_le_rowDeg {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k) :
    weightBefore W u v + W u v ≤ rowDeg W u := by
  unfold weightBefore rowDeg
  have hmem : v ∉ Finset.univ.filter (· < v) := by simp
  calc
    (∑ b ∈ Finset.univ.filter (· < v), W u b) + W u v
      = ∑ b ∈ insert v (Finset.univ.filter (· < v)), W u b := by
        rw [Finset.sum_insert hmem, add_comm]
    _ ≤ ∑ b : Fin k, W u b :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

theorem weightBefore_le_of_lt {k : ℕ} (W : Fin k → Fin k → ℕ) (u : Fin k)
    {v₁ v₂ : Fin k} (hlt : v₁ < v₂) :
    weightBefore W u v₁ + W u v₁ ≤ weightBefore W u v₂ := by
  unfold weightBefore
  have hmem : v₁ ∉ Finset.univ.filter (· < v₁) := by simp
  have hsub : insert v₁ (Finset.univ.filter (· < v₁)) ⊆ Finset.univ.filter (· < v₂) := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rcases hb with rfl | hb
    · exact hlt
    · exact lt_trans hb hlt
  calc
    (∑ b ∈ Finset.univ.filter (· < v₁), W u b) + W u v₁
      = ∑ b ∈ insert v₁ (Finset.univ.filter (· < v₁)), W u b := by
        rw [Finset.sum_insert hmem, add_comm]
    _ ≤ ∑ b ∈ Finset.univ.filter (· < v₂), W u b :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _

theorem degBefore_add_le_totalDoubledWeight {k : ℕ} (W : Fin k → Fin k → ℕ) (u : Fin k) :
    degBefore W u + rowDeg W u ≤ totalDoubledWeight W := by
  unfold degBefore totalDoubledWeight
  have hmem : u ∉ Finset.univ.filter (· < u) := by simp
  calc
    (∑ a ∈ Finset.univ.filter (· < u), rowDeg W a) + rowDeg W u
      = ∑ a ∈ insert u (Finset.univ.filter (· < u)), rowDeg W a := by
        rw [Finset.sum_insert hmem, add_comm]
    _ ≤ ∑ a : Fin k, rowDeg W a :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

theorem degBefore_le_of_lt {k : ℕ} (W : Fin k → Fin k → ℕ) {u₁ u₂ : Fin k} (hlt : u₁ < u₂) :
    degBefore W u₁ + rowDeg W u₁ ≤ degBefore W u₂ := by
  unfold degBefore
  have hmem : u₁ ∉ Finset.univ.filter (· < u₁) := by simp
  have hsub : insert u₁ (Finset.univ.filter (· < u₁)) ⊆ Finset.univ.filter (· < u₂) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rcases ha with rfl | ha
    · exact hlt
    · exact lt_trans ha hlt
  calc
    (∑ a ∈ Finset.univ.filter (· < u₁), rowDeg W a) + rowDeg W u₁
      = ∑ a ∈ insert u₁ (Finset.univ.filter (· < u₁)), rowDeg W a := by
        rw [Finset.sum_insert hmem, add_comm]
    _ ≤ ∑ a ∈ Finset.univ.filter (· < u₂), rowDeg W a :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _

theorem edgeOffset_add_le_totalDoubledWeight {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k) :
    edgeOffset W u v + W u v ≤ totalDoubledWeight W := by
  unfold edgeOffset
  calc
    degBefore W u + weightBefore W u v + W u v
      = degBefore W u + (weightBefore W u v + W u v) := by omega
    _ ≤ degBefore W u + rowDeg W u := Nat.add_le_add_left (weightBefore_add_le_rowDeg W u v) _
    _ ≤ totalDoubledWeight W := degBefore_add_le_totalDoubledWeight W u

/-- `IsSampledPair W r u v` holds when sample `r` falls inside the half-open interval
`[edgeOffset W u v, edgeOffset W u v + W u v)`. -/
def IsSampledPair {k : ℕ} (W : Fin k → Fin k → ℕ) (r : ℕ) (u v : Fin k) : Prop :=
  edgeOffset W u v ≤ r ∧ r < edgeOffset W u v + W u v

instance {k : ℕ} (W : Fin k → Fin k → ℕ) (r : ℕ) (u v : Fin k) :
    Decidable (IsSampledPair W r u v) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem isSampledPair_ne {k : ℕ} {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    {r : ℕ} {u v : Fin k} (h : IsSampledPair W r u v) :
    u ≠ v := by
  rintro rfl
  rcases h with ⟨hle, hlt⟩
  rw [hW.2 u] at hlt
  omega

theorem isSampledPair_unique {k : ℕ} (W : Fin k → Fin k → ℕ) {r : ℕ}
    {u₁ v₁ u₂ v₂ : Fin k} (h₁ : IsSampledPair W r u₁ v₁) (h₂ : IsSampledPair W r u₂ v₂) :
    u₁ = u₂ ∧ v₁ = v₂ := by
  rcases h₁ with ⟨hle₁, hlt₁⟩
  rcases h₂ with ⟨hle₂, hlt₂⟩
  unfold edgeOffset at hle₁ hlt₁ hle₂ hlt₂
  have hu₁_upper : r < degBefore W u₁ + rowDeg W u₁ := by
    have := weightBefore_add_le_rowDeg W u₁ v₁
    omega
  have hu₂_upper : r < degBefore W u₂ + rowDeg W u₂ := by
    have := weightBefore_add_le_rowDeg W u₂ v₂
    omega
  have hu_eq : u₁ = u₂ := by
    rcases lt_trichotomy u₁ u₂ with hlt | rfl | hgt
    · have := degBefore_le_of_lt W hlt
      omega
    · rfl
    · have := degBefore_le_of_lt W hgt
      omega
  subst hu_eq
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy v₁ v₂ with hlt | rfl | hgt
  · have := weightBefore_le_of_lt W u₁ hlt
    omega
  · rfl
  · have := weightBefore_le_of_lt W u₁ hgt
    omega

theorem exists_isSampledPair {k : ℕ} (W : Fin k → Fin k → ℕ) {r : ℕ}
    (hr : r < totalDoubledWeight W) :
    ∃ u v : Fin k, IsSampledPair W r u v := by
  have hk : 0 < k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    subst hk0'
    simp [totalDoubledWeight] at hr
  have hu_ex : ∀ m ≤ k, r < (∑ a ∈ Finset.univ.filter (fun a : Fin k => a.val < m), rowDeg W a) →
      ∃ u : Fin k, u.val < m ∧ degBefore W u ≤ r ∧ r < degBefore W u + rowDeg W u := by
    intro m
    induction m with
    | zero =>
      intro _ hlt
      simp at hlt
    | succ m ih =>
      intro hm hlt
      let u_m : Fin k := ⟨m, hm⟩
      have hsplit : (Finset.univ.filter fun a : Fin k => a.val < m + 1) =
          insert u_m (Finset.univ.filter fun a : Fin k => a.val < m) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff, u_m]
        omega
      have hnotmem : u_m ∉ Finset.univ.filter fun a : Fin k => a.val < m := by simp [u_m]
      rw [hsplit, Finset.sum_insert hnotmem] at hlt
      have hdeg_eq : (∑ a ∈ Finset.univ.filter (fun a : Fin k => a.val < m), rowDeg W a) =
          degBefore W u_m := by
        unfold degBefore
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext a
        simp [Fin.lt_def, u_m]
      rw [hdeg_eq] at hlt
      by_cases hge : degBefore W u_m ≤ r
      · exact ⟨u_m, Nat.lt_succ_self m, hge, by omega⟩
      · exact (ih (by omega) (by omega)).imp fun u ⟨hu1, hu2, hu3⟩ =>
          ⟨Nat.lt_succ_of_lt hu1, hu2, hu3⟩
  have hfull_u : (Finset.univ.filter fun a : Fin k => a.val < k) = Finset.univ := by
    ext a
    simp
  rcases hu_ex k le_rfl (by simpa [hfull_u, totalDoubledWeight] using hr) with ⟨u, _, hu_le, hu_lt⟩
  let rem := r - degBefore W u
  have hrem : rem < rowDeg W u := by omega
  have hv_ex : ∀ m ≤ k, rem < (∑ b ∈ Finset.univ.filter (fun b : Fin k => b.val < m), W u b) →
      ∃ v : Fin k, v.val < m ∧ weightBefore W u v ≤ rem ∧ rem < weightBefore W u v + W u v := by
    intro m
    induction m with
    | zero =>
      intro _ hlt
      simp at hlt
    | succ m ih =>
      intro hm hlt
      let v_m : Fin k := ⟨m, hm⟩
      have hsplit : (Finset.univ.filter fun b : Fin k => b.val < m + 1) =
          insert v_m (Finset.univ.filter fun b : Fin k => b.val < m) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff, v_m]
        omega
      have hnotmem : v_m ∉ Finset.univ.filter fun b : Fin k => b.val < m := by simp [v_m]
      rw [hsplit, Finset.sum_insert hnotmem] at hlt
      have hw_eq : (∑ b ∈ Finset.univ.filter (fun b : Fin k => b.val < m), W u b) =
          weightBefore W u v_m := by
        unfold weightBefore
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext b
        simp [Fin.lt_def, v_m]
      rw [hw_eq] at hlt
      by_cases hge : weightBefore W u v_m ≤ rem
      · exact ⟨v_m, Nat.lt_succ_self m, hge, by omega⟩
      · exact (ih (by omega) (by omega)).imp fun v ⟨hv1, hv2, hv3⟩ =>
          ⟨Nat.lt_succ_of_lt hv1, hv2, hv3⟩
  rcases hv_ex k le_rfl (by simpa [hfull_u, rowDeg] using hrem) with ⟨v, _, hv_le, hv_lt⟩
  exact ⟨u, v, by unfold IsSampledPair edgeOffset; omega⟩

theorem card_sampledPair_fiber {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k) :
    (Finset.univ.filter fun r : Fin (totalDoubledWeight W) =>
      IsSampledPair W r.val u v).card = W u v := by
  have hbound := edgeOffset_add_le_totalDoubledWeight W u v
  symm
  rw [← Finset.card_fin (W u v)]
  refine Finset.card_bij (fun (i : Fin (W u v)) _ =>
    (⟨edgeOffset W u v + i.val, by have := i.isLt; omega⟩ : Fin (totalDoubledWeight W))) ?_ ?_ ?_
  · intro i _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold IsSampledPair
    simp only
    have := i.isLt
    omega
  · intro i _ j _ hij
    simp only [Fin.ext_iff] at hij
    exact Fin.ext (by omega)
  · intro r hr
    rw [Finset.mem_filter] at hr
    rcases hr.2 with ⟨hr1, hr2⟩
    refine ⟨⟨r.val - edgeOffset W u v, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp only
    omega

/-- Event on `Fin (totalDoubledWeight W)` where the edge sampled at `r` keeps both endpoints on the
same side of `B`. -/
def SampleSurvives {k : ℕ} (W : Fin k → Fin k → ℕ) (B : Finset (Fin k))
    (r : Fin (totalDoubledWeight W)) : Prop :=
  ∃ u v : Fin k, IsSampledPair W r.val u v ∧ (u ∈ B ↔ v ∈ B)

instance {k : ℕ} (W : Fin k → Fin k → ℕ) (B : Finset (Fin k))
    (r : Fin (totalDoubledWeight W)) :
    Decidable (SampleSurvives W B r) :=
  inferInstanceAs (Decidable (∃ _ _, _))

theorem not_sampleSurvives_iff_crosses {k : ℕ} (W : Fin k → Fin k → ℕ) (B : Finset (Fin k))
    (r : Fin (totalDoubledWeight W)) :
    ¬ SampleSurvives W B r ↔
      ∃ u v : Fin k, IsSampledPair W r.val u v ∧ ¬ (u ∈ B ↔ v ∈ B) := by
  rcases exists_isSampledPair W r.isLt with ⟨u₀, v₀, h₀⟩
  constructor
  · intro hns
    exact ⟨u₀, v₀, h₀, fun hiff => hns ⟨u₀, v₀, h₀, hiff⟩⟩
  · rintro ⟨u, v, huv, hnc⟩ ⟨u', v', huv', hiff⟩
    rcases isSampledPair_unique W huv huv' with ⟨rfl, rfl⟩
    exact hnc hiff

theorem crossing_card_eq {k : ℕ} {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    (B : Finset (Fin k)) :
    (Finset.univ.filter fun r : Fin (totalDoubledWeight W) => ¬ SampleSurvives W B r).card =
      2 * cutWeight W B := by
  let crossPairs : Finset (Fin k × Fin k) :=
    Finset.univ.filter fun p => ¬ (p.1 ∈ B ↔ p.2 ∈ B)
  have hbiUnion : (Finset.univ.filter fun r : Fin (totalDoubledWeight W) =>
      ¬ SampleSurvives W B r) =
        crossPairs.biUnion fun p =>
          Finset.univ.filter fun r : Fin (totalDoubledWeight W) =>
            IsSampledPair W r.val p.1 p.2 := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_sampleSurvives_iff_crosses,
      Finset.mem_biUnion, Prod.exists, crossPairs]
    exact ⟨fun ⟨u, v, huv, hnc⟩ => ⟨u, v, hnc, huv⟩,
      fun ⟨u, v, hnc, huv⟩ => ⟨u, v, huv, hnc⟩⟩
  rw [hbiUnion, Finset.card_biUnion]
  · calc
      ∑ p ∈ crossPairs,
          (Finset.univ.filter fun r : Fin (totalDoubledWeight W) =>
            IsSampledPair W r.val p.1 p.2).card
        = ∑ p ∈ crossPairs, W p.1 p.2 :=
          Finset.sum_congr rfl fun p _ => card_sampledPair_fiber W p.1 p.2
      _ = (∑ p ∈ B ×ˢ (Finset.univ \ B), W p.1 p.2) +
            ∑ p ∈ (Finset.univ \ B) ×ˢ B, W p.1 p.2 := by
          rw [← Finset.sum_union]
          · refine Finset.sum_congr ?_ fun _ _ => rfl
            ext ⟨u, v⟩
            simp only [crossPairs, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_union, Finset.mem_product, Finset.mem_sdiff]
            tauto
          · simp only [Finset.disjoint_left, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ,
              true_and]
            rintro ⟨u, v⟩ ⟨hu, _⟩ ⟨hnu, _⟩
            exact hnu hu
      _ = cutWeight W B + cutWeight W (Finset.univ \ B) := by
          have hsdiff : Finset.univ \ (Finset.univ \ B) = B := by ext x; simp
          unfold cutWeight
          rw [hsdiff, Finset.sum_product, Finset.sum_product]
      _ = 2 * cutWeight W B := by
          rw [cutWeight_compl hW B]
          ring
  · intro p₁ _ p₂ _ hpne
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    intro r h₁ h₂
    rcases isSampledPair_unique W h₁ h₂ with ⟨hu, hv⟩
    exact hpne (Prod.ext hu hv)

theorem surviving_card_eq {k : ℕ} {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    (B : Finset (Fin k)) :
    (Finset.univ.filter fun r : Fin (totalDoubledWeight W) => SampleSurvives W B r).card =
      totalDoubledWeight W - 2 * cutWeight W B := by
  let S := totalDoubledWeight W
  let posSet := Finset.univ.filter fun r : Fin S => SampleSurvives W B r
  let negSet := Finset.univ.filter fun r : Fin S => ¬ SampleSurvives W B r
  have hdisj : Disjoint posSet negSet := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and, posSet, negSet]
    exact fun _ h1 h2 => h2 h1
  have hunion : posSet ∪ negSet = Finset.univ := by
    ext r
    by_cases hr : SampleSurvives W B r <;> simp [posSet, negSet, hr]
  have hpart : posSet.card + negSet.card = S := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  have hneg : negSet.card = 2 * cutWeight W B := crossing_card_eq hW B
  have hle := two_mul_cutWeight_le_totalDoubledWeight hW B
  dsimp only [S, posSet, negSet] at hpart hneg
  omega

/-- One-step survival probability lower bound: if `k ≥ 2`, `0 < totalDoubledWeight W`, and
`k * cutWeight W B ≤ totalDoubledWeight W`, then a uniform sample `r : Fin (totalDoubledWeight W)`
satisfies `SampleSurvives W B r` with probability at least `(k - 2) / k`. -/
theorem step_survival_prob_ge {k : ℕ} (hk : 2 ≤ k) {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    {B : Finset (Fin k)} (hS : 0 < totalDoubledWeight W)
    (hdeg : k * cutWeight W B ≤ totalDoubledWeight W) :
    ((k - 2 : ℕ) : ℝ≥0∞) / k ≤
      letI : Nonempty (Fin (totalDoubledWeight W)) := ⟨⟨0, hS⟩⟩
      (Cslib.Probability.PMF.uniformOfFintype (Fin (totalDoubledWeight W))).toOuterMeasure
        {r | SampleSurvives W B r} := by
  let S := totalDoubledWeight W
  let _ : Nonempty (Fin S) := ⟨⟨0, hS⟩⟩
  rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype]
  have hcard :
      (Finset.univ.filter (· ∈ ({r : Fin S | SampleSurvives W B r} : Set (Fin S)))).card =
        S - 2 * cutWeight W B := surviving_card_eq hW B
  rw [hcard, Fintype.card_fin, ← div_eq_mul_inv]
  have hnat : (k - 2) * S ≤ k * (S - 2 * cutWeight W B) := by
    have h2 : 2 * cutWeight W B ≤ S := by
      have : 2 * cutWeight W B ≤ k * cutWeight W B := Nat.mul_le_mul_right _ hk
      omega
    zify [hk, h2]
    nlinarith
  have henn : (((k - 2 : ℕ) : ℝ≥0∞) * S) ≤
      (k : ℝ≥0∞) * ((S - 2 * cutWeight W B : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hnat
  have hk_ne_zero : (k : ℝ≥0∞) ≠ 0 := by positivity
  have hk_ne_top : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
  have hS_ne_zero : (S : ℝ≥0∞) ≠ 0 := by exact_mod_cast hS.ne'
  have hS_ne_top : (S : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top S
  rw [ENNReal.div_le_iff_le_mul (Or.inl hk_ne_zero) (Or.inl hk_ne_top)]
  rw [← ENNReal.mul_div_right_comm]
  rw [ENNReal.le_div_iff_mul_le (Or.inl hS_ne_zero) (Or.inl hS_ne_top)]
  simpa [mul_comm] using henn

/-! ### Telescoping and Bernoulli amplification -/

/-- Power of a quotient in `ℝ≥0∞`: `(a / b) ^ m = a ^ m / b ^ m`. -/
theorem ennreal_div_pow (a b : ℝ≥0∞) (m : ℕ) :
    (a / b) ^ m = a ^ m / b ^ m := by
  simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]

private theorem ennreal_div_eq_of_mul_eq {a b c d : ℝ≥0∞}
    (hb0 : b ≠ 0) (hbt : b ≠ ⊤) (hd0 : d ≠ 0) (hdt : d ≠ ⊤)
    (h : a * d = c * b) :
    a / b = c / d := by
  apply le_antisymm
  · rw [ENNReal.div_le_iff_le_mul (Or.inl hb0) (Or.inl hbt), ← ENNReal.mul_div_right_comm,
      ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdt), h]
  · rw [ENNReal.div_le_iff_le_mul (Or.inl hd0) (Or.inl hdt), ← ENNReal.mul_div_right_comm,
      ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbt), h]

private theorem two_le_mul_pred {n : ℕ} (hn : 2 ≤ n) : 2 ≤ n * (n - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
  have hsub : d + 2 - 1 = d + 1 := by omega
  rw [hsub]
  nlinarith

/-- Telescoping cancellation step for `contractDownTo` survival probability from `m + 1` down to
`t` (`2 ≤ t ≤ m`):
`((m - 1) / (m + 1)) * (t * (t - 1) / (m * (m - 1))) = t * (t - 1) / ((m + 1) * m)`. -/
theorem telescope_survival_step {t m : ℕ} (ht : 2 ≤ t) (htm : t ≤ m) :
    (((m - 1 : ℕ) : ℝ≥0∞) / (m + 1 : ℕ)) *
      (((t * (t - 1) : ℕ) : ℝ≥0∞) / ((m * (m - 1) : ℕ) : ℝ≥0∞)) =
      ((t * (t - 1) : ℕ) : ℝ≥0∞) / (((m + 1) * m : ℕ) : ℝ≥0∞) := by
  have hm1_pos : 0 < m - 1 := by omega
  have hm_pos : 0 < m := by omega
  have hm1_ne0 : ((m - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm1_pos.ne'
  have hm_ne0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm_pos.ne'
  have hmp1_ne0 : ((m + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hmp1_top : ((m + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmm1_ne0 : ((m * (m - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos hm_pos hm1_pos).ne'
  have hmm1_top : ((m * (m - 1) : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmp1m_ne0 : (((m + 1) * m : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (Nat.succ_pos m) hm_pos).ne'
  have hmp1m_top : (((m + 1) * m : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hprod : (((m - 1 : ℕ) : ℝ≥0∞) / (m + 1 : ℕ)) *
      (((t * (t - 1) : ℕ) : ℝ≥0∞) / ((m * (m - 1) : ℕ) : ℝ≥0∞)) =
      (((m - 1 : ℕ) : ℝ≥0∞) * ((t * (t - 1) : ℕ) : ℝ≥0∞)) /
        (((m + 1 : ℕ) : ℝ≥0∞) * ((m * (m - 1) : ℕ) : ℝ≥0∞)) := by
    simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hmp1_ne0) (Or.inl hmp1_top)]
    ring
  rw [hprod]
  refine ennreal_div_eq_of_mul_eq (mul_ne_zero hmp1_ne0 hmm1_ne0)
    (ENNReal.mul_ne_top hmp1_top hmm1_top) hmp1m_ne0 hmp1m_top ?_
  have hnat : ((m - 1) * (t * (t - 1))) * ((m + 1) * m) =
      (t * (t - 1)) * ((m + 1) * (m * (m - 1))) := by ring
  exact_mod_cast hnat

theorem one_sub_two_div_pairs_eq {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) =
      (((n * (n - 1) / 2 - 1 : ℕ) : ℝ≥0∞) / ((n * (n - 1) / 2 : ℕ) : ℝ≥0∞)) := by
  let m := n * (n - 1) / 2
  have heven : 2 ∣ n * (n - 1) := by
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · refine ⟨k * (2 * k - 1), ?_⟩
      have : (k + k) * (k + k - 1) = 2 * (k * (2 * k - 1)) := by
        rcases k with _ | k'
        · simp
        · have h1 : k' + 1 + (k' + 1) - 1 = 2 * k' + 1 := by omega
          have h2 : 2 * (k' + 1) - 1 = 2 * k' + 1 := by omega
          rw [h1, h2]
          ring
      exact this
    · refine ⟨(2 * k + 1) * k, ?_⟩
      have : 2 * k + 1 - 1 = 2 * k := by omega
      rw [this]
      ring
  have h2m : n * (n - 1) = 2 * m := (Nat.mul_div_cancel' heven).symm
  have hm_pos : 1 ≤ m := by
    have := two_le_mul_pred hn
    omega
  have hm_ne0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm_top : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top m
  have h2_ne0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h2n_ne0 : ((n * (n - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    have := two_le_mul_pred hn
    exact_mod_cast (by omega : n * (n - 1) ≠ 0)
  refine ENNReal.sub_eq_of_eq_add (ENNReal.div_ne_top h2_top h2n_ne0) ?_
  change (1 : ℝ≥0∞) = (((m - 1 : ℕ) : ℝ≥0∞) / (m : ℝ≥0∞)) +
    (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)
  rw [h2m, Nat.cast_mul, Nat.cast_ofNat]
  have hdiv2 : (2 : ℝ≥0∞) / ((2 : ℝ≥0∞) * (m : ℝ≥0∞)) = (1 : ℝ≥0∞) / (m : ℝ≥0∞) := by
    simpa using ENNReal.mul_div_mul_left (1 : ℝ≥0∞) (m : ℝ≥0∞) h2_ne0 h2_top
  rw [hdiv2, div_eq_mul_inv, div_eq_mul_inv, ← add_mul]
  have hsub : ((m - 1 : ℕ) : ℝ≥0∞) + 1 = (m : ℝ≥0∞) := by
    exact_mod_cast Nat.sub_add_cancel hm_pos
  rw [hsub, ← div_eq_mul_inv, ENNReal.div_self hm_ne0 hm_top]

theorem one_sub_two_div_pow_pairs_le_half {n : ℕ} (hn : 2 ≤ n) :
    ((1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ^ (n * (n - 1) / 2) ≤
      (1 : ℝ≥0∞) / 2 := by
  let m := n * (n - 1) / 2
  have hm_pos : 1 ≤ m := by
    have := two_le_mul_pred hn
    omega
  rw [one_sub_two_div_pairs_eq hn]
  change (((m - 1 : ℕ) : ℝ≥0∞) / (m : ℝ≥0∞)) ^ m ≤ (1 : ℝ≥0∞) / 2
  rw [ennreal_div_pow]
  have hm_pow_ne0 : ((m : ℝ≥0∞) ^ m) ≠ 0 := pow_ne_zero m (by exact_mod_cast (by omega : m ≠ 0))
  have hm_pow_top : ((m : ℝ≥0∞) ^ m) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top m)
  have h2_ne0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [ENNReal.div_le_iff_le_mul (Or.inl hm_pow_ne0) (Or.inl hm_pow_top)]
  rw [← ENNReal.mul_div_right_comm, one_mul]
  rw [ENNReal.le_div_iff_mul_le (Or.inl h2_ne0) (Or.inl h2_top)]
  rw [mul_comm]
  exact_mod_cast Nat.two_mul_pred_pow_le hm_pos

/-- Elementary high-probability trial count `(n * (n - 1) / 2) * (Nat.log 2 n + 2)` for Basic
Karger amplification. -/
def highProbTrials (n : ℕ) : ℕ :=
  (n * (n - 1) / 2) * (Nat.log 2 n + 2)

theorem highProbTrials_pos {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ highProbTrials n := by
  unfold highProbTrials
  have hm : 1 ≤ n * (n - 1) / 2 := by
    have := two_le_mul_pred hn
    omega
  nlinarith

/-- Elementary failure probability bound for `highProbTrials n` independent contractions:
`(1 - 2 / (n * (n - 1))) ^ ((n * (n - 1) / 2) * (Nat.log 2 n + 2)) ≤ 1 / (2 * n)`. -/
theorem highProb_failure_le {n : ℕ} (hn : 2 ≤ n) :
    ((1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ^ highProbTrials n ≤
      (1 : ℝ≥0∞) / ((2 * n : ℕ) : ℝ≥0∞) := by
  unfold highProbTrials
  rw [pow_mul]
  calc
    (((1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ^ (n * (n - 1) / 2)) ^
        (Nat.log 2 n + 2)
      ≤ ((1 : ℝ≥0∞) / 2) ^ (Nat.log 2 n + 2) :=
        pow_le_pow_left' (one_sub_two_div_pow_pairs_le_half hn) _
    _ = (1 : ℝ≥0∞) / ((2 ^ (Nat.log 2 n + 2) : ℕ) : ℝ≥0∞) := by
        rw [ennreal_div_pow, one_pow, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (1 : ℝ≥0∞) / ((2 * n : ℕ) : ℝ≥0∞) := by
        apply ENNReal.div_le_div_left
        have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by omega) n
        have hle : 2 * n ≤ 2 ^ (Nat.log 2 n + 2) := by
          rw [pow_succ']
          omega
        exact_mod_cast hle

theorem highProb_failure_le_inv_n {n : ℕ} (hn : 2 ≤ n) :
    ((1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ^ highProbTrials n ≤
      (1 : ℝ≥0∞) / (n : ℝ≥0∞) := by
  refine (highProb_failure_le hn).trans ?_
  apply ENNReal.div_le_div_left
  exact_mod_cast (by omega : n ≤ 2 * n)

end Cslib.Algorithms.WordRAM.Karger
