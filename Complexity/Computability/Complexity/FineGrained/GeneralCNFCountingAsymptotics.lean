/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.GeneralCNFBranchSchedule
public import Complexity.Computability.Complexity.FineGrained.SparseCountingScale
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingTreeBounds

/-!
# Section 6.4 Proposition 6.4 tree-wide model-count recovery and total examination bounds

This module combines the Section 6.4 disjoint sparsification leaf-to-root `ReplacementDesign`
recovery and per-leaf examination bounds
(`Complexity.Computability.Complexity.FineGrained.GeneralCNFBranchSchedule`), the branch-word
representation bridge and `2 ^ (n / B + 1)` leaf-count bounds for normalized clause sets
(`Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingTreeBounds`), and the
asymptotic `interpolationScale` tree-exponent and candidate-query overhead bounds
(`Complexity.Computability.Complexity.FineGrained.SparseCountingScale`) of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (printed pp. 38–47):

1. **Normalized Proposition 6.4 leaf decomposition (`CNF.prop64NormalizedLeaves`)**:
   Normalizing an arbitrary `k`-CNF `φ : CNF V` via `reduce (nontautological φ.toClauseSet)` before
   applying `countingLeaves` at geometric threshold schedule
   `θ j = (CNF.prop64ThresholdBase k (Fintype.card V)) ^ j` preserves `CNF.modelCountOn declared`
   (`CNF.sum_modelCountOn_prop64NormalizedLeaves`) and the exact `0`/`1` assignment partition
   (`CNF.countP_eval_toCNF_prop64NormalizedLeaves`) unconditionally (even when `φ` contains
   tautological or duplicate clauses), while ensuring every leaf `L ∈ φ.prop64NormalizedLeaves k` is
   sparse, reduced, nontautological, of clause width `≤ k`, and of clause length at most
   `CNF.prop64LeafClauseRatio k (Fintype.card V) * Fintype.card V`
   (`CNF.length_le_of_mem_prop64NormalizedLeaves`).
2. **Proposition 6.4 tree leaf-count bounds against `numGroups` and `interpolationScale`**:
   - `CNF.length_prop64NormalizedLeaves_le_two_pow`: whenever `1 ≤ numGroups (Fintype.card V)` and
     `∀ c ∈ φ, c.length ≤ k`,
     `(φ.prop64NormalizedLeaves k).length ≤ 2 ^ (Fintype.card V / numGroups (Fintype.card V) + 1)`.
   - `CNF.length_prop64NormalizedLeaves_le_interpolationScale_of_clog_ge` and
     `CNF.length_prop64NormalizedLeaves_le_interpolationScale`: whenever
     `640000 ≤ Nat.clog 2 (Fintype.card V)` (in particular for `2 ^ 640000 ≤ Fintype.card V`),
     `1 ≤ interpolationScale (Fintype.card V)` and
     `((φ.prop64NormalizedLeaves k).length : ℝ) ≤`
     `(2 : ℝ) ^ (17 * interpolationScale (Fintype.card V))`.
3. **Lemma 6.2 candidate-query indexing, overhead, and full Proposition 6.4 tree-wide
   `interpolationScale` examination bounds**:
   - `CNF.LeafCandidateQueryIndex V B ψ` and `CNF.candidateQueryRows A q`: index all parity-row
     systems evaluated during the `3 * n` greedy rounds of Lemma 6.2 (`Sum.inl (i, γ')` for
     `i : Fin (3 * Fintype.card V)` and ordered candidate list
     `γ' : Fin (BitString.greedyRowListLength B ψ.length) → Fin ψ.length × Bool`, including discarded
     candidates counted with list multiplicity, plus `Sum.inr ()` for the final query
     `A (3 * Fintype.card V)`), with exact cardinality
     `3 * Fintype.card V * (2 * ψ.length) ^ P + 1 ≤ CNF.leafCandidateQueryBound B ψ`
     (`CNF.card_leafCandidateQueryIndex_eq`, `CNF.card_leafCandidateQueryIndex_le`).
   - `CNF.candidateQueryRows_length_and_weight_le`: every candidate or final query
     `q : CNF.LeafCandidateQueryIndex V B ψ` has at most `6 * Fintype.card V` parity rows, each of
     Hamming weight at most `BitString.initialRowWeightBound B ψ.length`.
   - `CNF.greedyRowListLength_le_mul_pow_clog` and
     `CNF.exists_prop64_leafCandidateQueryBound_le_interpolationScale`: prove
     `BitString.greedyRowListLength B m ≤ 20000 * B ^ 2 * (Nat.clog 2 (2 * m + 4)) ^ 2` for all `B, m`
     and apply `SparseCountingScale.eventually_query_overhead_poly_le` to bound
     `(CNF.leafCandidateQueryBound B ψ : ℝ) ≤ (2 : ℝ) ^ interpolationScale (Fintype.card V)` for
     every Proposition 6.4 leaf formula `ψ = L.toCNF`.
   - `CNF.exists_prop64NormalizedLeaves_greedy_total_recovery_and_examBound` and
     `CNF.exists_prop64NormalizedLeaves_total_recovery_and_examBound`: for any `k ≥ 2`, there
     exists `N₃ ≥ 2 ^ 640000` such that for any finite variable type `V` with
     `N₃ ≤ Fintype.card V` and any width-`≤ k` CNF `φ : CNF V`:
     - `φ.modelCountOn Finset.univ` equals the sum of `L.toCNF.modelCountOn Finset.univ` across
       `L ∈ φ.prop64NormalizedLeaves k`,
     - `(φ.prop64NormalizedLeaves k).length ≤ 2 ^ (Fintype.card V / numGroups (Fintype.card V) + 1)`
       and `((φ.prop64NormalizedLeaves k).length : ℝ) ≤`
       `(2 : ℝ) ^ (17 * interpolationScale (Fintype.card V))`,
     - on every leaf `L ∈ φ.prop64NormalizedLeaves k` (`ψ := L.toCNF`), **every** evaluated query
       `q : CNF.LeafCandidateQueryIndex V B ψ` (including every discarded candidate
       `A i.1 ++ [testRow γ']` for `i < 3 * Fintype.card V` and `γ'` as well as the final query
       `A (3 * Fintype.card V)` at `q = Sum.inr ()`, which recovers `ψ.modelCountOn Finset.univ`)
       admits concrete per-branch `ReplacementDesign`s `D b` recovering
       `commonZeroCount univ (ψ.parityRowSystem (CNF.candidateQueryRows A q))` with branch-summed
       examination count
       `≤ (2 : ℝ) ^ ((CNF.prop64BranchExamScaleCoeff k + 32) * interpolationScale n)`,
       and summing across all `q : CNF.LeafCandidateQueryIndex V B ψ` bounds the leaf's total
       candidate-query examination count by
       `(2 : ℝ) ^ (CNF.prop64LeafQueryExamScaleCoeff k * interpolationScale n)`, and
     - summing across all leaves in `φ.prop64NormalizedLeaves k` bounds the tree-wide examination
       count by `(2 : ℝ) ^ (CNF.prop64TreeExamScaleCoeff k * interpolationScale (Fintype.card V))`
       and the total candidate-indexed examination count across the entire sparsification tree by
       `(2 : ℝ) ^ (CNF.prop64TotalExamScaleCoeff k * interpolationScale (Fintype.card V))`.

## Main definitions

* `Cslib.Logic.PL.CNF.prop64NormalizedLeaves`
* `Cslib.Logic.PL.CNF.leafCandidateQueryBound`
* `Cslib.Logic.PL.CNF.LeafCandidateQueryIndex`
* `Cslib.Logic.PL.CNF.candidateQueryRows`
* `Cslib.Logic.PL.CNF.prop64LeafQueryExamScaleCoeff`
* `Cslib.Logic.PL.CNF.prop64TreeExamScaleCoeff`
* `Cslib.Logic.PL.CNF.prop64TotalExamScaleCoeff`

## Main results

* `CNF.card_leafCandidateQueryIndex_eq`
* `CNF.card_leafCandidateQueryIndex_le`
* `CNF.sum_modelCountOn_prop64NormalizedLeaves`
* `CNF.countP_eval_toCNF_prop64NormalizedLeaves`
* `CNF.length_le_of_mem_prop64NormalizedLeaves`
* `CNF.length_prop64NormalizedLeaves_le_two_pow`
* `one_le_interpolationScale_of_clog_ge`
* `CNF.length_prop64NormalizedLeaves_le_interpolationScale_of_clog_ge`
* `CNF.length_prop64NormalizedLeaves_le_interpolationScale`
* `CNF.greedyRowListLength_le_mul_pow_clog`
* `CNF.length_candidateQueryRows_le_of_step`
* `CNF.weight_mem_candidateQueryRows_le_of_step`
* `CNF.candidateQueryRows_length_and_weight_le`
* `CNF.sum_leafCandidateQueryIndex_le`
* `CNF.exists_leafCandidateQueryBound_le_interpolationScale`
* `CNF.exists_prop64_leafCandidateQueryBound_le_interpolationScale`
* `CNF.exists_prop64NormalizedLeaves_greedy_total_recovery_and_examBound`
* `CNF.exists_prop64NormalizedLeaves_total_recovery_and_examBound`

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
  (Sections 6.1–6.4, pp. 39–44; Appendix A, pp. 44–47)
-/

public noncomputable section

namespace Cslib.Logic.PL

open Filter Finset
open Cslib.BitString
open Cslib.LinearAlgebra
open Cslib.Logic.PL.ClauseSet.Sparsification
open Cslib.Complexity.SubexponentialSAT
open Cslib.Complexity.SubexponentialSAT.ReplacementParams
open Cslib.Complexity.SubexponentialSAT.SparseCountingScale

variable {V : Type*} {n' : ℕ}

/-! ### 1. Normalized Proposition 6.4 leaf decomposition (`CNF.prop64NormalizedLeaves`) -/

/-- The normalized Proposition 6.4 disjoint counting-sparsification leaf list of `φ : CNF V`
obtained by filtering tautological clauses (`nontautological`) and reducing by subsumption
(`reduce`) before applying `countingLeaves` at geometric threshold schedule
`θ j = (CNF.prop64ThresholdBase k (Fintype.card V)) ^ j`
([OpenAI2026ETH], Lemma 6.3, Proposition 6.4, and Appendix A.1–A.3, pp. 43–47). -/
@[expose] def CNF.prop64NormalizedLeaves (k : ℕ) [Fintype V] [DecidableEq V] (φ : CNF V) :
    List (ClauseSet V) :=
  countingLeaves (fun j => (CNF.prop64ThresholdBase k (Fintype.card V)) ^ j)
    (reduce (nontautological φ.toClauseSet))

/-- The Lemma 6.2 / Section 6.3 eq. `(6.4)` candidate-query upper bound
`3 * Fintype.card V * (2 * ψ.length + 2) ^ (BitString.greedyRowListLength B ψ.length) + 1`
bounding the number of candidate parity-row systems evaluated across the `3 * n` greedy rounds on a
sparse formula `ψ : CNF V` at clause-density bound `B` ([OpenAI2026ETH], §6.3, p. 43). -/
@[expose] def CNF.leafCandidateQueryBound [Fintype V] (B : ℕ) (ψ : CNF V) : ℕ :=
  3 * Fintype.card V * (2 * ψ.length + 2) ^ (BitString.greedyRowListLength B ψ.length) + 1

/-- Index type of all parity-row systems evaluated during the Section 6.3 Lemma 6.2 greedy
procedure on a leaf formula `ψ : CNF V` at clause-density bound `B`
([OpenAI2026ETH], §6.3, eq. `(6.4)`, p. 43):
- `Sum.inl (i, γ')` indexes the candidate system `A i.1 ++ [testRow γ']` at greedy round
  `i : Fin (3 * Fintype.card V)` and ordered candidate list
  `γ' : Fin (BitString.greedyRowListLength B ψ.length) → Fin ψ.length × Bool` (including discarded
  candidates, counted with list multiplicity), and
- `Sum.inr ()` indexes the final system `A (3 * Fintype.card V)`. -/
abbrev CNF.LeafCandidateQueryIndex (V : Type*) [Fintype V] (B : ℕ) (ψ : CNF V) : Type _ :=
  (Fin (3 * Fintype.card V) ×
    (Fin (BitString.greedyRowListLength B ψ.length) → Fin ψ.length × Bool)) ⊕ Unit

/-- The parity-row list evaluated at query `q : CNF.LeafCandidateQueryIndex V B ψ` along a
trajectory `A : ℕ → List (Fin ψ.length → Bool)` ([OpenAI2026ETH], §6.3, p. 43):
- at `Sum.inl (i, γ')`, the candidate row list `A i.1 ++ [testRow γ']` at round
  `i < 3 * Fintype.card V` and ordered candidate list `γ'`, and
- at `Sum.inr ()`, the final row list `A (3 * Fintype.card V)`. -/
@[expose] def CNF.candidateQueryRows [Fintype V] {B : ℕ} {ψ : CNF V}
    (A : ℕ → List (Fin ψ.length → Bool)) :
    CNF.LeafCandidateQueryIndex V B ψ → List (Fin ψ.length → Bool)
  | Sum.inl (i, γ') => A i.1 ++ [testRow γ']
  | Sum.inr () => A (3 * Fintype.card V)

/-- Single-leaf `interpolationScale` exponent multiplier
`CNF.prop64BranchExamScaleCoeff k + 33` combining heavy-variable branching (`+ 32`) with the
Lemma 6.2 candidate-query overhead (`+ 1`) of Section 6.3 eq. `(6.4)`. -/
@[expose] def CNF.prop64LeafQueryExamScaleCoeff (k : ℕ) : ℕ :=
  CNF.prop64BranchExamScaleCoeff k + 33

/-- Tree-summed `interpolationScale` exponent multiplier
`CNF.prop64BranchExamScaleCoeff k + 49` combining per-leaf branch-summed examination (`+ 32`) with
the Proposition 6.4 sparsification tree leaf-count exponent (`+ 17`). -/
@[expose] def CNF.prop64TreeExamScaleCoeff (k : ℕ) : ℕ :=
  CNF.prop64BranchExamScaleCoeff k + 49

/-- Total Proposition 6.4 `interpolationScale` exponent multiplier
`CNF.prop64BranchExamScaleCoeff k + 50` combining per-leaf branch-summed examination (`+ 32`),
Lemma 6.2 candidate-query overhead (`+ 1`), and the Proposition 6.4 sparsification tree leaf-count
exponent (`+ 17`). -/
@[expose] def CNF.prop64TotalExamScaleCoeff (k : ℕ) : ℕ :=
  CNF.prop64BranchExamScaleCoeff k + 50

/-- `CNF.leafCandidateQueryBound B ψ` is at least `1`. -/
theorem CNF.one_le_leafCandidateQueryBound [Fintype V] (B : ℕ) (ψ : CNF V) :
    1 ≤ CNF.leafCandidateQueryBound B ψ :=
  Nat.succ_pos _

/-- The exact number of candidate and final parity-row queries indexed by
`CNF.LeafCandidateQueryIndex V B ψ` is
`3 * Fintype.card V * (2 * ψ.length) ^ (BitString.greedyRowListLength B ψ.length) + 1`. -/
theorem CNF.card_leafCandidateQueryIndex_eq [Fintype V] (B : ℕ) (ψ : CNF V) :
    Fintype.card (CNF.LeafCandidateQueryIndex V B ψ) =
      3 * Fintype.card V * (2 * ψ.length) ^ (BitString.greedyRowListLength B ψ.length) + 1 := by
  simp only [CNF.LeafCandidateQueryIndex, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_pi, Fintype.card_fin, Fintype.card_bool, Fintype.card_unit,
    Finset.prod_const, Finset.card_univ]
  ring

/-- `Fintype.card (CNF.LeafCandidateQueryIndex V B ψ)` is at most
`CNF.leafCandidateQueryBound B ψ`. -/
theorem CNF.card_leafCandidateQueryIndex_le [Fintype V] (B : ℕ) (ψ : CNF V) :
    Fintype.card (CNF.LeafCandidateQueryIndex V B ψ) ≤ CNF.leafCandidateQueryBound B ψ := by
  rw [CNF.card_leafCandidateQueryIndex_eq]
  unfold CNF.leafCandidateQueryBound
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_add_right _ 2) _)) 1

/-- **Proposition 6.4 normalized additive model-count conservation:**
Summing `L.toCNF.modelCountOn declared` across all leaves `L ∈ φ.prop64NormalizedLeaves k`
recovers `φ.modelCountOn declared` without any nontautology precondition on `φ`. -/
theorem CNF.sum_modelCountOn_prop64NormalizedLeaves [Fintype V] [DecidableEq V]
    (k : ℕ) (φ : CNF V) (declared : Finset V) :
    ((φ.prop64NormalizedLeaves k).map fun L => L.toCNF.modelCountOn declared).sum =
      φ.modelCountOn declared :=
  sum_modelCountOn_countingLeaves_nontautological
    (fun j => (CNF.prop64ThresholdBase k (Fintype.card V)) ^ j) φ declared

/-- **Proposition 6.4 normalized exact assignment partition:**
For every assignment `x : V → Bool`, the number of leaf formulas `L.toCNF`
(`L ∈ φ.prop64NormalizedLeaves k`) satisfied by `x` is `1` if `φ.eval x = true` and `0` otherwise.
-/
theorem CNF.countP_eval_toCNF_prop64NormalizedLeaves [Fintype V] [DecidableEq V]
    (k : ℕ) (φ : CNF V) (x : V → Bool) :
    ((φ.prop64NormalizedLeaves k).map ClauseSet.toCNF).countP (fun F => F.eval x) =
      if φ.eval x then 1 else 0 :=
  countP_eval_toCNF_countingLeaves_nontautological
    (fun j => (CNF.prop64ThresholdBase k (Fintype.card V)) ^ j) φ x

/-- **Proposition 6.4 normalized leaf structural and clause-density bounds:**
If `∀ c ∈ φ, c.length ≤ k`, then for every leaf `L ∈ φ.prop64NormalizedLeaves k`:
1. `L` is `Sparse` at `θ j = (CNF.prop64ThresholdBase k (Fintype.card V)) ^ j`, `Reduced`, and
   nontautological.
2. Every clause `c ∈ L.toCNF` has width `c.length ≤ k`.
3. Every variable `v : V` occurs in at most
   `2 * ∑ c ∈ range k, (CNF.prop64ThresholdBase k (Fintype.card V)) ^ c` clauses of `L.toCNF`.
4. Whenever `1 ≤ Fintype.card V`,
   `L.toCNF.length ≤ CNF.prop64LeafClauseRatio k (Fintype.card V) * Fintype.card V`. -/
theorem CNF.length_le_of_mem_prop64NormalizedLeaves [Fintype V] [DecidableEq V]
    {φ : CNF V} {k : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    {L : ClauseSet V} (hL : L ∈ φ.prop64NormalizedLeaves k) :
    Sparse (fun j => (CNF.prop64ThresholdBase k (Fintype.card V)) ^ j) L ∧
    Reduced L ∧
    (∀ C ∈ L, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C) ∧
    (∀ c ∈ L.toCNF, c.length ≤ k) ∧
    (∀ v : V, L.toCNF.occurrences v ≤
      2 * ∑ c ∈ range k, (CNF.prop64ThresholdBase k (Fintype.card V)) ^ c) ∧
    (1 ≤ Fintype.card V →
      L.toCNF.length ≤ CNF.prop64LeafClauseRatio k (Fintype.card V) * Fintype.card V) := by
  set M := CNF.prop64ThresholdBase k (Fintype.card V)
  have hM2 : 2 ≤ M := CNF.two_le_prop64ThresholdBase k (Fintype.card V)
  have hθ1 : ∀ j, 1 ≤ M ^ j := fun j => Nat.one_le_pow j M (by omega)
  have hsparse : Sparse (M ^ ·) L := sparse_of_mem_countingLeaves_pow hM2 hL
  have hred : Reduced L := reduced_of_mem_countingLeaves (reduced_reduce _) hL
  have hnt : ∀ C ∈ L, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C :=
    nontautological_of_mem_countingLeaves hθ1
      (fun _ hC => nontautological_of_mem_reduce_nontautological hC) hL
  have hroot_k : ∀ C ∈ reduce (nontautological φ.toClauseSet), C.card ≤ k := by
    intro C hC
    obtain ⟨c, hc, hcard⟩ :=
      CNF.exists_card_le_of_mem_toClauseSet (nontautological_subset _ (reduce_subset _ hC))
    exact hcard.trans (hk c hc)
  have hL_k : ∀ C ∈ L, C.card ≤ k := card_le_of_mem_countingLeaves hroot_k hL
  refine ⟨hsparse, hred, hnt, fun c hc => ClauseSet.length_le_of_mem_toCNF hL_k hc,
    fun v => ?_, fun hn1 => ?_⟩
  · rw [ClauseSet.occurrences_toCNF]
    exact occurrences_le_of_sparse hθ1 hsparse hL_k v
  · have hlen_eq : L.toCNF.length = L.card := by
      simp only [ClauseSet.toCNF, List.length_map, Finset.length_toList]
    have hcard_le : L.card ≤ 2 * (∑ c ∈ range k, M ^ c) * (univ : Finset V).card + 1 :=
      card_le_of_sparse hθ1 hsparse hL_k univ (fun _ _ _ _ => mem_univ _)
    rw [hlen_eq]
    rw [card_univ] at hcard_le
    unfold CNF.prop64LeafClauseRatio
    calc L.card
        ≤ 2 * (∑ c ∈ range k, M ^ c) * Fintype.card V + 1 := hcard_le
      _ ≤ 2 * (∑ c ∈ range k, M ^ c) * Fintype.card V + Fintype.card V :=
          Nat.add_le_add_left hn1 _
      _ = (2 * (∑ c ∈ range k, M ^ c) + 1) * Fintype.card V := by ring

/-! ### 2. Proposition 6.4 tree leaf-count bounds against `numGroups` and `interpolationScale` -/

/-- **Proposition 6.4 `2 ^ (n / numGroups n + 1)` leaf-count bound:**
Whenever `1 ≤ numGroups (Fintype.card V)` and `∀ c ∈ φ, c.length ≤ k`, the normalized
counting-sparsification leaf list `φ.prop64NormalizedLeaves k` has length at most
`2 ^ (Fintype.card V / numGroups (Fintype.card V) + 1)`. -/
theorem CNF.length_prop64NormalizedLeaves_le_two_pow [Fintype V] [DecidableEq V]
    {φ : CNF V} {k : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    (hs : 1 ≤ numGroups (Fintype.card V)) :
    (φ.prop64NormalizedLeaves k).length ≤
      2 ^ (Fintype.card V / numGroups (Fintype.card V) + 1) :=
  length_countingLeaves_nontautological_thresholdBase_le hs φ hk Finset.univ
    (fun _ _ => mem_univ _) (by rw [card_univ])

/-- When `640000 ≤ Nat.clog 2 n`, `1 ≤ interpolationScale n`. -/
theorem one_le_interpolationScale_of_clog_ge {n : ℕ} (h : 640000 ≤ Nat.clog 2 n) :
    1 ≤ interpolationScale n := by
  have hs2 : 2 ≤ numGroups n := two_le_numGroups_of_clog_ge h
  have h2pow19 : 2 ^ 19 < Nat.clog 2 n :=
    lt_of_lt_of_le (by decide : 2 ^ 19 < 640000) h
  have hnu20 : 20 ≤ Nat.clog 2 (Nat.clog 2 n) :=
    (Nat.lt_clog_iff_pow_lt one_lt_two).mpr h2pow19
  have hsq := sq_mul_pow_four_le_clog n
  have hclog_le : Nat.clog 2 n ≤ n :=
    (Nat.clog_le_iff_le_pow one_lt_two).mpr n.lt_two_pow_self.le
  have h16_mul : 16 * numGroups n ≤ n := by
    have hnu4 : 16 ≤ numGroups n * Nat.clog 2 (Nat.clog 2 n) ^ 4 := by
      have : 16 ≤ 2 * 20 ^ 4 := by decide
      exact this.trans (Nat.mul_le_mul hs2 (Nat.pow_le_pow_left hnu20 4))
    calc 16 * numGroups n
        ≤ (numGroups n * Nat.clog 2 (Nat.clog 2 n) ^ 4) * numGroups n :=
          Nat.mul_le_mul_right _ hnu4
      _ = numGroups n ^ 2 * Nat.clog 2 (Nat.clog 2 n) ^ 4 := by ring
      _ ≤ Nat.clog 2 n := hsq
      _ ≤ n := hclog_le
  have hs_pos : (0 : ℝ) < numGroups n := Nat.cast_pos.mpr (by omega)
  have h16_div : 16 ≤ (n : ℝ) / (numGroups n : ℝ) := by
    rw [le_div_iff₀ hs_pos]
    exact_mod_cast h16_mul
  have hdiv_le := div_numGroups_le_interpolationScale_of_clog_ge h
  linarith

/-- **Proposition 6.4 `(2 : ℝ) ^ (17 * interpolationScale n)` leaf-count bound under
`640000 ≤ Nat.clog 2 (Fintype.card V)`:**
For any width-`≤ k` CNF `φ : CNF V` with `640000 ≤ Nat.clog 2 (Fintype.card V)`,
`((φ.prop64NormalizedLeaves k).length : ℝ) ≤ (2 : ℝ) ^ (17 * interpolationScale (Fintype.card V))`.
-/
theorem CNF.length_prop64NormalizedLeaves_le_interpolationScale_of_clog_ge
    [Fintype V] [DecidableEq V] {φ : CNF V} {k : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    (h : 640000 ≤ Nat.clog 2 (Fintype.card V)) :
    ((φ.prop64NormalizedLeaves k).length : ℝ) ≤
      (2 : ℝ) ^ (17 * interpolationScale (Fintype.card V)) := by
  set n := Fintype.card V
  have hs2 : 2 ≤ numGroups n := two_le_numGroups_of_clog_ge h
  have hlen_nat : (φ.prop64NormalizedLeaves k).length ≤ 2 ^ (n / numGroups n + 1) :=
    CNF.length_prop64NormalizedLeaves_le_two_pow hk (le_trans one_le_two hs2)
  have hlen_r : ((φ.prop64NormalizedLeaves k).length : ℝ) ≤
      (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ ((n : ℝ) / (numGroups n : ℝ)) := by
    have hcast : ((φ.prop64NormalizedLeaves k).length : ℝ) ≤
        ((2 ^ (n / numGroups n + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hlen_nat
    refine hcast.trans ?_
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ', Real.rpow_one, ← Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le one_le_two Nat.cast_div_le) zero_le_two
  have h1_scale : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ interpolationScale n :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (one_le_interpolationScale_of_clog_ge h)
  have h16_scale :
      (2 : ℝ) ^ ((n : ℝ) / (numGroups n : ℝ)) ≤ (2 : ℝ) ^ (16 * interpolationScale n) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two
      (div_numGroups_le_interpolationScale_of_clog_ge h)
  calc ((φ.prop64NormalizedLeaves k).length : ℝ)
      ≤ (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ ((n : ℝ) / (numGroups n : ℝ)) := hlen_r
    _ ≤ (2 : ℝ) ^ interpolationScale n * (2 : ℝ) ^ (16 * interpolationScale n) :=
        mul_le_mul h1_scale h16_scale (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (17 * interpolationScale n) := by rw [← Real.rpow_add two_pos]; ring_nf

private theorem le_clog_of_two_pow_le {m n : ℕ} (hn : 2 ^ m ≤ n) : m ≤ Nat.clog 2 n :=
  (Nat.clog_pow 2 m one_lt_two).symm.le.trans (Nat.clog_mono_right 2 hn)

/-- **Proposition 6.4 `(2 : ℝ) ^ (17 * interpolationScale n)` leaf-count bound for
`2 ^ 640000 ≤ Fintype.card V`:**
For any width-`≤ k` CNF `φ : CNF V` with `2 ^ 640000 ≤ Fintype.card V`,
`((φ.prop64NormalizedLeaves k).length : ℝ) ≤ (2 : ℝ) ^ (17 * interpolationScale (Fintype.card V))`.
-/
theorem CNF.length_prop64NormalizedLeaves_le_interpolationScale
    [Fintype V] [DecidableEq V] {φ : CNF V} {k : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    (hn : 2 ^ 640000 ≤ Fintype.card V) :
    ((φ.prop64NormalizedLeaves k).length : ℝ) ≤
      (2 : ℝ) ^ (17 * interpolationScale (Fintype.card V)) :=
  CNF.length_prop64NormalizedLeaves_le_interpolationScale_of_clog_ge hk (le_clog_of_two_pow_le hn)

/-! ### 3. Lemma 6.2 candidate-query overhead and Proposition 6.4 tree-wide examination bounds -/

/-- For every `B, m : ℕ`, the Lemma 6.1–6.2 greedy candidate list length
`BitString.greedyRowListLength B m = 20000 * B ^ 2 * (Nat.log 2 m + 1) ^ 2` satisfies
`BitString.greedyRowListLength B m ≤ 20000 * B ^ 2 * (Nat.clog 2 (2 * m + 4)) ^ 2`. -/
theorem CNF.greedyRowListLength_le_mul_pow_clog (B m : ℕ) :
    BitString.greedyRowListLength B m ≤ 20000 * B ^ 2 * (Nat.clog 2 (2 * m + 4)) ^ 2 := by
  have hlog_lt : Nat.log 2 m < Nat.clog 2 (2 * m + 4) := by
    rw [Nat.lt_clog_iff_pow_lt one_lt_two]
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · decide
    · have hpow : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
      omega
  unfold BitString.greedyRowListLength
  exact Nat.mul_le_mul_left (20000 * B ^ 2) (Nat.pow_le_pow_left hlog_lt 2)

private theorem greedyRowListLength_le_initialRowWeightBound (B m : ℕ) :
    BitString.greedyRowListLength B m ≤ BitString.initialRowWeightBound B m := by
  unfold BitString.greedyRowListLength BitString.initialRowWeightBound
  exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide))
    (Nat.pow_le_pow_right (Nat.succ_pos _) (by decide))

/-- If a trajectory `A : ℕ → List (Fin ψ.length → Bool)` satisfies
`(A i).length ≤ 3 * Fintype.card V + i` for all `i ≤ 3 * Fintype.card V`, then every query
`q : CNF.LeafCandidateQueryIndex V B ψ` (including every discarded candidate
`A i.1 ++ [testRow γ']` for `i < 3 * Fintype.card V` and the final system
`A (3 * Fintype.card V)`) has at most `6 * Fintype.card V` parity rows. -/
theorem CNF.length_candidateQueryRows_le_of_step [Fintype V] {B : ℕ} {ψ : CNF V}
    {A : ℕ → List (Fin ψ.length → Bool)}
    (hlen : ∀ i ≤ 3 * Fintype.card V, (A i).length ≤ 3 * Fintype.card V + i)
    (q : CNF.LeafCandidateQueryIndex V B ψ) :
    (CNF.candidateQueryRows A q).length ≤ 6 * Fintype.card V := by
  rcases q with ⟨i, γ'⟩ | ⟨⟩
  · simp only [CNF.candidateQueryRows, List.length_append, List.length_singleton]
    have hi : (A i.1).length ≤ 3 * Fintype.card V + i.1 := hlen i.1 i.2.le
    omega
  · simp only [CNF.candidateQueryRows]
    have h3n := hlen (3 * Fintype.card V) le_rfl
    omega

/-- If every row in `A i` (`i ≤ 3 * Fintype.card V`) has Hamming weight at most
`BitString.initialRowWeightBound B ψ.length`, then every row in `CNF.candidateQueryRows A q`
(including every candidate `testRow γ'`) has Hamming weight at most
`BitString.initialRowWeightBound B ψ.length`. -/
theorem CNF.weight_mem_candidateQueryRows_le_of_step [Fintype V] {B : ℕ} {ψ : CNF V}
    {A : ℕ → List (Fin ψ.length → Bool)}
    (hw : ∀ i ≤ 3 * Fintype.card V, ∀ r ∈ A i,
      weight r ≤ BitString.initialRowWeightBound B ψ.length)
    (q : CNF.LeafCandidateQueryIndex V B ψ) :
    ∀ r ∈ CNF.candidateQueryRows A q, weight r ≤ BitString.initialRowWeightBound B ψ.length := by
  rcases q with ⟨i, γ'⟩ | ⟨⟩
  · intro r hr
    simp only [CNF.candidateQueryRows, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact hw i.1 i.2.le r hr
    · exact (weight_testRow_le γ').trans
        (greedyRowListLength_le_initialRowWeightBound B ψ.length)
  · exact hw (3 * Fintype.card V) le_rfl

/-- Along any trajectory `A` starting from `A 0 = A₀` with `A₀.length ≤ 3 * Fintype.card V`
and `∀ r ∈ A₀, weight r ≤ BitString.initialRowWeightBound B ψ.length` and appending one
`testRow (γ i)` per step, every query `q : CNF.LeafCandidateQueryIndex V B ψ` has at most
`6 * Fintype.card V` parity rows, each of Hamming weight at most
`BitString.initialRowWeightBound B ψ.length`. -/
theorem CNF.candidateQueryRows_length_and_weight_le [Fintype V] {B : ℕ} {ψ : CNF V}
    {A₀ : List (Fin ψ.length → Bool)} (hlen0 : A₀.length ≤ 3 * Fintype.card V)
    (hw0 : ∀ r ∈ A₀, weight r ≤ BitString.initialRowWeightBound B ψ.length)
    {A : ℕ → List (Fin ψ.length → Bool)}
    {γ : ℕ → Fin (BitString.greedyRowListLength B ψ.length) → Fin ψ.length × Bool}
    (h0 : A 0 = A₀) (hA : ∀ i, A (i + 1) = A i ++ [testRow (γ i)])
    (q : CNF.LeafCandidateQueryIndex V B ψ) :
    (CNF.candidateQueryRows A q).length ≤ 6 * Fintype.card V ∧
    ∀ r ∈ CNF.candidateQueryRows A q, weight r ≤ BitString.initialRowWeightBound B ψ.length := by
  have hstep : ∀ i, (A i).length ≤ 3 * Fintype.card V + i ∧
      ∀ r ∈ A i, weight r ≤ BitString.initialRowWeightBound B ψ.length := by
    intro i
    induction i with
    | zero =>
      exact ⟨by simpa [h0] using hlen0, fun r hr => hw0 r (h0 ▸ hr)⟩
    | succ i ih =>
      rw [hA i, List.length_append, List.length_singleton]
      refine ⟨by omega, fun r hr => ?_⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact ih.2 r hr
      · rw [List.mem_singleton.mp hr]
        exact (weight_testRow_le (γ i)).trans
          (greedyRowListLength_le_initialRowWeightBound B ψ.length)
  exact ⟨CNF.length_candidateQueryRows_le_of_step (fun i _ => (hstep i).1) q,
    CNF.weight_mem_candidateQueryRows_le_of_step (fun i _ => (hstep i).2) q⟩

/-- If `queryExam q ≤ M` (`0 ≤ M`) for every candidate and final query
`q : CNF.LeafCandidateQueryIndex V B ψ`, then the sum of `queryExam q` across all
`q : CNF.LeafCandidateQueryIndex V B ψ` (counting all `3 * Fintype.card V` rounds and all
ordered candidate lists `γ'` with multiplicity plus the final query) is at most
`(CNF.leafCandidateQueryBound B ψ : ℝ) * M`. -/
theorem CNF.sum_leafCandidateQueryIndex_le [Fintype V] (B : ℕ) (ψ : CNF V)
    (queryExam : CNF.LeafCandidateQueryIndex V B ψ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hq : ∀ q : CNF.LeafCandidateQueryIndex V B ψ, queryExam q ≤ M) :
    (∑ q : CNF.LeafCandidateQueryIndex V B ψ, queryExam q) ≤
      (CNF.leafCandidateQueryBound B ψ : ℝ) * M := by
  calc (∑ q : CNF.LeafCandidateQueryIndex V B ψ, queryExam q)
      ≤ ∑ _q : CNF.LeafCandidateQueryIndex V B ψ, M :=
        Finset.sum_le_sum fun q _ => hq q
    _ = (Fintype.card (CNF.LeafCandidateQueryIndex V B ψ) : ℝ) * M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (CNF.leafCandidateQueryBound B ψ : ℝ) * M :=
        mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr (CNF.card_leafCandidateQueryIndex_le B ψ)) hM

/-- **Section 6.3 eq. `(6.4)` candidate-query overhead absorption:**
For any `C_B β_B : ℕ` and any `ε > 0`, there exists `N_q : ℕ` such that for any finite variable
type `V` with `N_q ≤ Fintype.card V`, any CNF `ψ : CNF V`, and any `B : ℕ` satisfying
`ψ.length ≤ B * Fintype.card V` and `B ≤ C_B * (Nat.clog 2 (Fintype.card V)) ^ β_B`,
`(CNF.leafCandidateQueryBound B ψ : ℝ) ≤ (2 : ℝ) ^ (ε * interpolationScale (Fintype.card V))`. -/
theorem CNF.exists_leafCandidateQueryBound_le_interpolationScale
    (C_B β_B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N_q : ℕ, ∀ {V : Type*} [Fintype V] (ψ : CNF V) {B : ℕ},
      N_q ≤ Fintype.card V →
      ψ.length ≤ B * Fintype.card V →
      B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B →
      (CNF.leafCandidateQueryBound B ψ : ℝ) ≤
        (2 : ℝ) ^ (ε * interpolationScale (Fintype.card V)) := by
  obtain ⟨N_q, hN_q⟩ := eventually_atTop.mp
    (eventually_query_overhead_poly_le C_B β_B 20000 2 2 hε)
  refine ⟨N_q, fun {V _} ψ {B} hcard hm hB => ?_⟩
  have hP := CNF.greedyRowListLength_le_mul_pow_clog B ψ.length
  have hbound := hN_q (Fintype.card V) hcard ψ.length B
    (BitString.greedyRowListLength B ψ.length) hm hB hP
  unfold CNF.leafCandidateQueryBound
  exact_mod_cast hbound

/-- **Proposition 6.4 leaf candidate-query overhead bound (`ε = 1`):**
For any `k ≥ 2`, there exists `N_q ≥ 2` such that for any finite variable type `V` with
`N_q ≤ Fintype.card V` and any `ψ : CNF V` satisfying
`ψ.length ≤ CNF.prop64LeafClauseRatio k (Fintype.card V) * Fintype.card V`,
`(CNF.leafCandidateQueryBound (CNF.prop64LeafClauseRatio k (Fintype.card V)) ψ : ℝ) ≤`
`(2 : ℝ) ^ interpolationScale (Fintype.card V)`. -/
theorem CNF.exists_prop64_leafCandidateQueryBound_le_interpolationScale {k : ℕ} (hk : 2 ≤ k) :
    ∃ N_q : ℕ, 2 ≤ N_q ∧
      ∀ {V : Type*} [Fintype V] (ψ : CNF V),
        N_q ≤ Fintype.card V →
        ψ.length ≤ CNF.prop64LeafClauseRatio k (Fintype.card V) * Fintype.card V →
        (CNF.leafCandidateQueryBound (CNF.prop64LeafClauseRatio k (Fintype.card V)) ψ : ℝ) ≤
          (2 : ℝ) ^ interpolationScale (Fintype.card V) := by
  obtain ⟨C_B, _, hCB⟩ := CNF.exists_prop64LeafClauseRatio_le_mul_clog_pow hk
  obtain ⟨N_q, hN_q⟩ :=
    CNF.exists_leafCandidateQueryBound_le_interpolationScale C_B (2 * (k - 1)) one_pos
  refine ⟨max N_q 2, le_max_right _ _, fun {V _} ψ hcard hm => ?_⟩
  have hcard_q : N_q ≤ Fintype.card V := (le_max_left _ _).trans hcard
  have hn2 : 2 ≤ Fintype.card V := (le_max_right _ _).trans hcard
  have hB_le :
      CNF.prop64LeafClauseRatio k (Fintype.card V) ≤
        C_B * Nat.clog 2 (Fintype.card V) ^ (2 * (k - 1)) :=
    hCB (Fintype.card V) hn2
  simpa only [one_mul] using hN_q ψ hcard_q hm hB_le

private theorem list_sum_map_le_length_mul {α : Type*} (xs : List α) (f : α → ℝ) {M : ℝ}
    (hf : ∀ x ∈ xs, f x ≤ M) :
    (xs.map f).sum ≤ (xs.length : ℝ) * M := by
  simpa only [List.length_map, nsmul_eq_mul] using
    List.sum_le_length_nsmul (xs.map f) M (by simpa only [List.forall_mem_map] using hf)

/-- **Proposition 6.4 end-to-end normalized leaf-to-root greedy recovery,
leaf-count bound, and total candidate-indexed `interpolationScale` examination bounds
([OpenAI2026ETH], §6.4, pp. 43–44 & Appendix A, pp. 44–47):**
For any `k ≥ 2`, there exists `N₃ ≥ 2 ^ 640000` such that for any finite variable type `V` with
`N₃ ≤ Fintype.card V` and any width-`≤ k` CNF `φ : CNF V` (with no clause-count, occurrence, or
nontautology restriction on `φ`):
1. **Exact leaf-summed model-count conservation:**
   `((φ.prop64NormalizedLeaves k).map fun L => L.toCNF.modelCountOn Finset.univ).sum =`
   `φ.modelCountOn Finset.univ`.
2. **Sparsification tree leaf-count bounds:**
   `2 ≤ numGroups (Fintype.card V)`,
   `(φ.prop64NormalizedLeaves k).length ≤ 2 ^ (Fintype.card V / numGroups (Fintype.card V) + 1)`,
   and `((φ.prop64NormalizedLeaves k).length : ℝ) ≤`
   `(2 : ℝ) ^ (17 * interpolationScale (Fintype.card V))`.
3. **Per-leaf greedy parity-design recovery, degree, and candidate-indexed examination bounds:**
   For every leaf `L ∈ φ.prop64NormalizedLeaves k` (`ψ := L.toCNF`,
   `B := CNF.prop64LeafClauseRatio k (Fintype.card V)`):
   - `(CNF.leafCandidateQueryBound B ψ : ℝ) ≤ (2 : ℝ) ^ interpolationScale (Fintype.card V)`,
   - `ψ` admits Lemma 6.1 initial parity rows `A₀` such that for any `3 * n`-step greedy trajectory
     `(A, γ)`, `CNF.candidateQueryRows A (Sum.inr ()) = A (3 * Fintype.card V)` recovers
     `ψ.modelCountOn Finset.univ`, **every** evaluated query `q : CNF.LeafCandidateQueryIndex V B ψ`
     (including every discarded candidate `A i.1 ++ [testRow γ']` for `i < 3 * Fintype.card V` and
     `γ'` as well as the final query `Sum.inr ()`) has at most `6 * Fintype.card V` rows of weight
     `≤ D₀` and admits concrete per-branch `ReplacementDesign`s `D b` recovering
     `commonZeroCount univ (ψ.parityRowSystem (CNF.candidateQueryRows A q))` with branch-summed
     examination count at most
     `(2 : ℝ) ^ ((CNF.prop64BranchExamScaleCoeff k + 32) * interpolationScale (Fintype.card V))`,
     and any per-query examination family `queryExam : CNF.LeafCandidateQueryIndex V B ψ → ℝ`
     bounded by that single-query bound sums across all `q : CNF.LeafCandidateQueryIndex V B ψ` to
     at most
     `(2 : ℝ) ^ (CNF.prop64LeafQueryExamScaleCoeff k * interpolationScale (Fintype.card V))`.
4. **Tree-wide and total candidate-indexed examination bounds across `φ.prop64NormalizedLeaves k`:**
   - Any per-leaf examination family `leafExam : ClauseSet V → ℝ` bounded on every
     `L ∈ φ.prop64NormalizedLeaves k` by
     `(2 : ℝ) ^ ((CNF.prop64BranchExamScaleCoeff k + 32) * interpolationScale (Fintype.card V))`
     sums across `φ.prop64NormalizedLeaves k` to at most
     `(2 : ℝ) ^ (CNF.prop64TreeExamScaleCoeff k * interpolationScale (Fintype.card V))`.
   - Any candidate-indexed examination family
     `treeQueryExam : (L : ClauseSet V) → CNF.LeafCandidateQueryIndex V B L.toCNF → ℝ` bounded on
     every `L ∈ φ.prop64NormalizedLeaves k` and `q : CNF.LeafCandidateQueryIndex V B L.toCNF` by
     `(2 : ℝ) ^ ((CNF.prop64BranchExamScaleCoeff k + 32) * interpolationScale (Fintype.card V))`
     has total sum
     `((φ.prop64NormalizedLeaves k).map fun L =>`
     `∑ q : CNF.LeafCandidateQueryIndex V B L.toCNF, treeQueryExam L q).sum`
     at most `(2 : ℝ) ^ (CNF.prop64TotalExamScaleCoeff k * interpolationScale (Fintype.card V))`. -/
theorem CNF.exists_prop64NormalizedLeaves_greedy_total_recovery_and_examBound
    {k : ℕ} (hk : 2 ≤ k) :
    ∃ N₃ : ℕ, 2 ^ 640000 ≤ N₃ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (φ : CNF V),
        (∀ c ∈ φ, c.length ≤ k) →
        N₃ ≤ Fintype.card V →
        let B := CNF.prop64LeafClauseRatio k (Fintype.card V)
        ((φ.prop64NormalizedLeaves k).map fun L => L.toCNF.modelCountOn Finset.univ).sum =
          φ.modelCountOn Finset.univ ∧
        2 ≤ numGroups (Fintype.card V) ∧
        (φ.prop64NormalizedLeaves k).length ≤
          2 ^ (Fintype.card V / numGroups (Fintype.card V) + 1) ∧
        ((φ.prop64NormalizedLeaves k).length : ℝ) ≤
          (2 : ℝ) ^ (17 * interpolationScale (Fintype.card V)) ∧
        (∀ L ∈ φ.prop64NormalizedLeaves k,
          let ψ := L.toCNF
          let D₀ := BitString.initialRowWeightBound B ψ.length
          let P := BitString.greedyRowListLength B ψ.length
          let b₀ := CNF.parityBranchThreshold k D₀ (Fintype.card V)
          (∀ c ∈ ψ, c.length ≤ k) ∧
          ψ.length ≤ B * Fintype.card V ∧
          (CNF.leafCandidateQueryBound B ψ : ℝ) ≤
            (2 : ℝ) ^ interpolationScale (Fintype.card V) ∧
          ∃ A₀ : List (Fin ψ.length → Bool), A₀.length ≤ 3 * Fintype.card V ∧
            (∀ r ∈ A₀, weight r ≤ D₀) ∧
            ∀ (A : ℕ → List (Fin ψ.length → Bool))
              (γ : ℕ → Fin P → Fin ψ.length × Bool),
              A 0 = A₀ → (∀ i, A (i + 1) = A i ++ [testRow (γ i)]) →
              (∀ i (γ' : Fin P → Fin ψ.length × Bool),
                commonZeroCount univ (ψ.parityRowSystem (A i ++ [testRow (γ i)])) ≤
                  commonZeroCount univ (ψ.parityRowSystem (A i ++ [testRow γ']))) →
              commonZeroCount univ
                  (ψ.parityRowSystem (CNF.candidateQueryRows (B := B) A (Sum.inr ()))) =
                ψ.modelCountOn Finset.univ ∧
              (∀ q : CNF.LeafCandidateQueryIndex V B ψ,
                let rows := CNF.candidateQueryRows A q
                rows.length ≤ 6 * Fintype.card V ∧
                (∀ r ∈ rows, weight r ≤ D₀) ∧
                let S := heavyVars univ (univ : Finset (Fin rows.length))
                  (fun j => equationScope (ψ.parityRowSystem rows j)) b₀
                ∀ ⦃n' : ℕ⦄ (e : ↥(univ \ S) ≃ Fin n'),
                  (Fintype.card V ≤ 2 * n' ∧ n' ≤ Fintype.card V) ∧
                  (∃ (hF : ∀ b : V → Bool,
                        Feasible (CNF.prop64ScheduleExponent k) n' (b₀ + 1)
                          (max (k * (D₀ * 2 ^ k)) 1)
                          (∑ f : {j : Fin rows.length //
                              j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                            #(branchAugmentedScope S e univ (ψ.parityRowSystem rows) b f)))
                      (D : ∀ b : V → Bool,
                        ReplacementDesign
                          (branchAugmentedScope S e univ (ψ.parityRowSystem rows) b)
                          (numNodes n') (numGroups n')
                          (intervalStart (CNF.prop64ScheduleExponent k) n')
                          (rowBound (CNF.prop64ScheduleExponent k) n') (tauRat n')),
                      (commonZeroCount (univ : Finset (Fin rows.length))
                          (ψ.parityRowSystem rows) : ℤ) =
                        (∑ b ∈ branchAssignments S,
                          ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                            (ψ.branchParityRowSystem rows S e b)
                            (commonDenom (numNodes n')
                              (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k
                            (branchPrecision (Fintype.card V))
                            (designReplacementScaledIntMap (D b)
                              (fun j => Sum.inl ⟨j, mem_univ j⟩))).eval 0 /
                              clearedProductDenom
                                (commonDenom (numNodes n')
                                  (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k
                                (branchPrecision (Fintype.card V))
                                #(univ : Finset (Fin rows.length))) %
                                  ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
                      (∀ b : V → Bool,
                        (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                          (ψ.branchParityRowSystem rows S e b)
                          (commonDenom (numNodes n')
                            (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k
                          (branchPrecision (Fintype.card V))
                          (designReplacementScaledIntMap (D b)
                            (fun j => Sum.inl ⟨j, mem_univ j⟩))).natDegree ≤
                          (k * (rowBound (CNF.prop64ScheduleExponent k) n' - 1)) *
                            (8 * Fintype.card V)) ∧
                      ∀ (b : V → Bool)
                          (s_active : Finset
                            ({j : Fin rows.length //
                                j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n')),
                        let d := k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))
                        let q_ord := (d * rowBound (CNF.prop64ScheduleExponent k) n') / numNodes n'
                        let C := (hF b).toCountingDesign (D b) s_active
                        (∑ t : Fin (numNodes n'),
                            (#{p : Finset (Fin n') × Finset (Fin n') |
                                #p.1 ≤ q_ord ∧ p.2 ⊆ p.1} : ℝ) *
                              (2 * (#(C.measurementBox t) : ℝ) *
                                ∑ g : Fin (numGroups n'),
                                  (Fintype.card (C.LocalCube t g) : ℝ))) ≤
                          (2 : ℝ) ^ ((CNF.prop64BranchExamScaleCoeff k : ℝ) *
                            interpolationScale (Fintype.card V))) ∧
                  ∀ (examSum : (V → Bool) → ℝ),
                    (∀ b ∈ branchAssignments S,
                      examSum b ≤
                        (2 : ℝ) ^ ((CNF.prop64BranchExamScaleCoeff k : ℝ) *
                          interpolationScale (Fintype.card V))) →
                    (∑ b ∈ branchAssignments S, examSum b) ≤
                      (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                        interpolationScale (Fintype.card V))) ∧
              ∀ (queryExam : CNF.LeafCandidateQueryIndex V B ψ → ℝ),
                (∀ q : CNF.LeafCandidateQueryIndex V B ψ,
                  queryExam q ≤
                    (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                      interpolationScale (Fintype.card V))) →
                (∑ q : CNF.LeafCandidateQueryIndex V B ψ, queryExam q) ≤
                  (2 : ℝ) ^ ((CNF.prop64LeafQueryExamScaleCoeff k : ℝ) *
                    interpolationScale (Fintype.card V))) ∧
        (∀ (leafExam : ClauseSet V → ℝ),
          (∀ L ∈ φ.prop64NormalizedLeaves k,
            leafExam L ≤
              (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                interpolationScale (Fintype.card V))) →
          ((φ.prop64NormalizedLeaves k).map leafExam).sum ≤
            (2 : ℝ) ^ ((CNF.prop64TreeExamScaleCoeff k : ℝ) *
              interpolationScale (Fintype.card V))) ∧
        ∀ (treeQueryExam : (L : ClauseSet V) → CNF.LeafCandidateQueryIndex V B L.toCNF → ℝ),
          (∀ L ∈ φ.prop64NormalizedLeaves k, ∀ q : CNF.LeafCandidateQueryIndex V B L.toCNF,
            treeQueryExam L q ≤
              (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                interpolationScale (Fintype.card V))) →
          ((φ.prop64NormalizedLeaves k).map fun (L : ClauseSet V) =>
              ∑ q : CNF.LeafCandidateQueryIndex V B L.toCNF, treeQueryExam L q).sum ≤
            (2 : ℝ) ^ ((CNF.prop64TotalExamScaleCoeff k : ℝ) *
              interpolationScale (Fintype.card V)) := by
  obtain ⟨C_B, _, hCB⟩ := CNF.exists_prop64LeafClauseRatio_le_mul_clog_pow hk
  obtain ⟨N_row, hN_row16, hrow_rec⟩ :=
    CNF.exists_branch_schedule_recovery_and_examBound_parityRowSystem_of_le_clog_pow
      k C_B (2 * (k - 1))
  obtain ⟨N_gr, hN_gr16, hgreedy_rec⟩ :=
    CNF.exists_greedy_parityRowSystem_recovery_and_examBound_of_le_clog_pow k C_B (2 * (k - 1))
  obtain ⟨N_q, _, hquery⟩ := CNF.exists_prop64_leafCandidateQueryBound_le_interpolationScale hk
  refine ⟨max (2 ^ 640000) (max (max N_row N_gr) N_q), le_max_left _ _,
    fun {V _ _} φ hk_φ hcard => ?_⟩
  intro B
  have hpow_le : 2 ^ 640000 ≤ Fintype.card V := (le_max_left _ _).trans hcard
  have hN_row_le : N_row ≤ Fintype.card V :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hcard
  have hN_gr_le : N_gr ≤ Fintype.card V :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hcard
  have hNq_le : N_q ≤ Fintype.card V :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hcard
  have hs2 : 2 ≤ numGroups (Fintype.card V) := two_le_numGroups_of_pow_le hpow_le
  have hn1 : 1 ≤ Fintype.card V := le_trans (by decide : 1 ≤ 16384) (hN_row16.trans hN_row_le)
  have hn2 : 2 ≤ Fintype.card V := le_trans (by decide : 2 ≤ 16384) (hN_row16.trans hN_row_le)
  have hlen_two_pow :
      (φ.prop64NormalizedLeaves k).length ≤
        2 ^ (Fintype.card V / numGroups (Fintype.card V) + 1) :=
    CNF.length_prop64NormalizedLeaves_le_two_pow hk_φ (by omega)
  have hlen_scale :
      ((φ.prop64NormalizedLeaves k).length : ℝ) ≤
        (2 : ℝ) ^ (17 * interpolationScale (Fintype.card V)) :=
    CNF.length_prop64NormalizedLeaves_le_interpolationScale hk_φ hpow_le
  have hsum_leaf_queries : ∀ L ∈ φ.prop64NormalizedLeaves k,
      ∀ (queryExam : CNF.LeafCandidateQueryIndex V B L.toCNF → ℝ),
        (∀ q : CNF.LeafCandidateQueryIndex V B L.toCNF,
          queryExam q ≤
            (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
              interpolationScale (Fintype.card V))) →
        (∑ q : CNF.LeafCandidateQueryIndex V B L.toCNF, queryExam q) ≤
          (2 : ℝ) ^ ((CNF.prop64LeafQueryExamScaleCoeff k : ℝ) *
            interpolationScale (Fintype.card V)) := by
    intro L hL queryExam hq_bound
    obtain ⟨_, _, _, _, _, hlen_ψ⟩ := CNF.length_le_of_mem_prop64NormalizedLeaves hk_φ hL
    have hq_le := hquery L.toCNF hNq_le (hlen_ψ hn1)
    have hsum_q := CNF.sum_leafCandidateQueryIndex_le B L.toCNF queryExam (by positivity) hq_bound
    calc (∑ q : CNF.LeafCandidateQueryIndex V B L.toCNF, queryExam q)
        ≤ (CNF.leafCandidateQueryBound B L.toCNF : ℝ) *
            (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
              interpolationScale (Fintype.card V)) := hsum_q
      _ ≤ (2 : ℝ) ^ interpolationScale (Fintype.card V) *
            (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
              interpolationScale (Fintype.card V)) :=
          mul_le_mul_of_nonneg hq_le le_rfl (Nat.cast_nonneg _) (by positivity)
      _ = (2 : ℝ) ^ ((CNF.prop64LeafQueryExamScaleCoeff k : ℝ) *
            interpolationScale (Fintype.card V)) := by
          rw [← Real.rpow_add two_pos]
          unfold CNF.prop64LeafQueryExamScaleCoeff
          push_cast
          ring_nf
  refine ⟨CNF.sum_modelCountOn_prop64NormalizedLeaves k φ Finset.univ, hs2,
    hlen_two_pow, hlen_scale, fun L hL => ?_, fun leafExam hleaf => ?_,
    fun treeQueryExam htree => ?_⟩
  · intro ψ D₀ P b₀
    obtain ⟨_, _, _, hk_ψ, _, hlen_ψ⟩ := CNF.length_le_of_mem_prop64NormalizedLeaves hk_φ hL
    have hm_ψ : ψ.length ≤ B * Fintype.card V := hlen_ψ hn1
    have hB1 : 1 ≤ B := CNF.one_le_prop64LeafClauseRatio k (Fintype.card V)
    have hB_le : B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ (2 * (k - 1)) :=
      hCB (Fintype.card V) hn2
    have hq_le :
        (CNF.leafCandidateQueryBound B ψ : ℝ) ≤ (2 : ℝ) ^ interpolationScale (Fintype.card V) :=
      hquery ψ hNq_le hm_ψ
    obtain ⟨A₀, hlen0, hw0, hgreedy⟩ := hgreedy_rec ψ hk_ψ hN_gr_le hB1 hB_le hm_ψ
    refine ⟨hk_ψ, hm_ψ, hq_le, A₀, hlen0, hw0, fun A γ h0 hA hγ => ?_⟩
    obtain ⟨hcount, _⟩ := hgreedy A γ h0 hA hγ
    refine ⟨hcount, fun q => ?_, hsum_leaf_queries L hL⟩
    obtain ⟨hlen_q, hw_q⟩ := CNF.candidateQueryRows_length_and_weight_le hlen0 hw0 h0 hA q
    refine ⟨hlen_q, hw_q, fun {n'} e => ?_⟩
    exact hrow_rec hk_ψ hN_row_le hm_ψ hB_le le_rfl hw_q hlen_q e
  · calc ((φ.prop64NormalizedLeaves k).map leafExam).sum
        ≤ ((φ.prop64NormalizedLeaves k).length : ℝ) *
            (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
              interpolationScale (Fintype.card V)) :=
          list_sum_map_le_length_mul _ _ hleaf
      _ ≤ (2 : ℝ) ^ (17 * interpolationScale (Fintype.card V)) *
            (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
              interpolationScale (Fintype.card V)) :=
          mul_le_mul_of_nonneg_right hlen_scale (by positivity)
      _ = (2 : ℝ) ^ ((CNF.prop64TreeExamScaleCoeff k : ℝ) *
            interpolationScale (Fintype.card V)) := by
          rw [← Real.rpow_add two_pos]
          unfold CNF.prop64TreeExamScaleCoeff
          push_cast
          ring_nf
  · calc ((φ.prop64NormalizedLeaves k).map fun (L : ClauseSet V) =>
            ∑ q : CNF.LeafCandidateQueryIndex V B L.toCNF, treeQueryExam L q).sum
        ≤ ((φ.prop64NormalizedLeaves k).length : ℝ) *
            (2 : ℝ) ^ ((CNF.prop64LeafQueryExamScaleCoeff k : ℝ) *
              interpolationScale (Fintype.card V)) :=
          list_sum_map_le_length_mul _ _ fun L hL =>
            hsum_leaf_queries L hL (treeQueryExam L) (htree L hL)
      _ ≤ (2 : ℝ) ^ (17 * interpolationScale (Fintype.card V)) *
            (2 : ℝ) ^ ((CNF.prop64LeafQueryExamScaleCoeff k : ℝ) *
              interpolationScale (Fintype.card V)) :=
          mul_le_mul_of_nonneg_right hlen_scale (by positivity)
      _ = (2 : ℝ) ^ ((CNF.prop64TotalExamScaleCoeff k : ℝ) *
            interpolationScale (Fintype.card V)) := by
          rw [← Real.rpow_add two_pos]
          unfold CNF.prop64TotalExamScaleCoeff CNF.prop64LeafQueryExamScaleCoeff
          push_cast
          ring_nf

private noncomputable def nextGreedyStep [Fintype V] [DecidableEq V]
    (φ : CNF V) (P : ℕ) [Nonempty (Fin φ.length)]
    (L : List (Fin φ.length → Bool)) : Fin P → Fin φ.length × Bool :=
  (exists_min_image (univ : Finset (Fin P → Fin φ.length × Bool))
    (fun γ' => commonZeroCount univ (φ.parityRowSystem (L ++ [testRow γ'])))
    univ_nonempty).choose

private theorem nextGreedyStep_le [Fintype V] [DecidableEq V]
    (φ : CNF V) (P : ℕ) [Nonempty (Fin φ.length)]
    (L : List (Fin φ.length → Bool)) (γ' : Fin P → Fin φ.length × Bool) :
    commonZeroCount univ (φ.parityRowSystem (L ++ [testRow (nextGreedyStep φ P L)])) ≤
      commonZeroCount univ (φ.parityRowSystem (L ++ [testRow γ'])) :=
  (exists_min_image (univ : Finset (Fin P → Fin φ.length × Bool))
    (fun δ => commonZeroCount univ (φ.parityRowSystem (L ++ [testRow δ])))
    univ_nonempty).choose_spec.2 γ' (mem_univ γ')

private noncomputable def greedyTrajectory [Fintype V] [DecidableEq V]
    (φ : CNF V) (P : ℕ) [Nonempty (Fin φ.length)]
    (A₀ : List (Fin φ.length → Bool)) : ℕ → List (Fin φ.length → Bool)
  | 0 => A₀
  | i + 1 =>
    let L := greedyTrajectory φ P A₀ i
    L ++ [testRow (nextGreedyStep φ P L)]

/-- **Proposition 6.4 unconditional normalized leaf-to-root `modelCountOn` recovery
and total candidate-indexed `interpolationScale` examination bounds ([OpenAI2026ETH], §6.4,
pp. 43–44 & Appendix A, pp. 44–47):**
For any `k ≥ 2`, there exists `N₃ ≥ 2 ^ 640000` such that for any finite variable type `V` with
`N₃ ≤ Fintype.card V` and any width-`≤ k` CNF `φ : CNF V`:
1. `((φ.prop64NormalizedLeaves k).map fun L => L.toCNF.modelCountOn Finset.univ).sum =`
   `φ.modelCountOn Finset.univ`.
2. `2 ≤ numGroups (Fintype.card V)`,
   `(φ.prop64NormalizedLeaves k).length ≤ 2 ^ (Fintype.card V / numGroups (Fintype.card V) + 1)`,
   and `((φ.prop64NormalizedLeaves k).length : ℝ) ≤`
   `(2 : ℝ) ^ (17 * interpolationScale (Fintype.card V))`.
3. Every leaf `L ∈ φ.prop64NormalizedLeaves k` (`ψ := L.toCNF`) unconditionally admits a greedy
   parity-row trajectory `A : ℕ → List (Fin ψ.length → Bool)` such that:
   - at the final query `q = Sum.inr ()`,
     `commonZeroCount univ (ψ.parityRowSystem (CNF.candidateQueryRows A (Sum.inr ()))) =`
     `ψ.modelCountOn Finset.univ`,
   - at every greedy round `i : Fin (3 * Fintype.card V)` and every ordered candidate list
     `γ' : Fin P → Fin ψ.length × Bool`,
     `commonZeroCount univ (ψ.parityRowSystem (A (i.1 + 1))) ≤`
     `commonZeroCount univ (ψ.parityRowSystem (CNF.candidateQueryRows A (Sum.inl (i, γ'))))`,
   - for **every** evaluated query `q : CNF.LeafCandidateQueryIndex V B ψ` (including every
     discarded candidate `Sum.inl (i, γ')` as well as `Sum.inr ()`),
     `rows := CNF.candidateQueryRows A q` satisfies `rows.length ≤ 6 * Fintype.card V` and
     `∀ r ∈ rows, weight r ≤ D₀`, and for any free-variable equivalence `e : ↥(univ \ S) ≃ Fin n'`,
     there exist per-branch `hF b` and concrete `ReplacementDesign`s `D b` recovering
     `(commonZeroCount univ (ψ.parityRowSystem rows) : ℤ)` (and hence
     `(ψ.modelCountOn Finset.univ : ℤ)` at `q = Sum.inr ()`) via
     `univariateClearedParityTruncatedSum` with numerator degree
     `≤ (k * (rowBound (CNF.prop64ScheduleExponent k) n' - 1)) * (8 * Fintype.card V)` and
     single-branch / branch-summed `interpolationScale` examination bounds, and
   - any per-query examination family `queryExam : CNF.LeafCandidateQueryIndex V B ψ → ℝ` bounded
     by `(2 : ℝ) ^ ((CNF.prop64BranchExamScaleCoeff k + 32) * interpolationScale n)` sums across all
     `q : CNF.LeafCandidateQueryIndex V B ψ` to at most
     `(2 : ℝ) ^ (CNF.prop64LeafQueryExamScaleCoeff k * interpolationScale n)`.
4. Summing across all leaves in `φ.prop64NormalizedLeaves k` bounds the tree-wide examination count
   by `(2 : ℝ) ^ (CNF.prop64TreeExamScaleCoeff k * interpolationScale (Fintype.card V))` and the
   total candidate-indexed examination count by
   `(2 : ℝ) ^ (CNF.prop64TotalExamScaleCoeff k * interpolationScale (Fintype.card V))`. -/
theorem CNF.exists_prop64NormalizedLeaves_total_recovery_and_examBound
    {k : ℕ} (hk : 2 ≤ k) :
    ∃ N₃ : ℕ, 2 ^ 640000 ≤ N₃ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (φ : CNF V),
        (∀ c ∈ φ, c.length ≤ k) →
        N₃ ≤ Fintype.card V →
        let B := CNF.prop64LeafClauseRatio k (Fintype.card V)
        ((φ.prop64NormalizedLeaves k).map fun L => L.toCNF.modelCountOn Finset.univ).sum =
          φ.modelCountOn Finset.univ ∧
        2 ≤ numGroups (Fintype.card V) ∧
        (φ.prop64NormalizedLeaves k).length ≤
          2 ^ (Fintype.card V / numGroups (Fintype.card V) + 1) ∧
        ((φ.prop64NormalizedLeaves k).length : ℝ) ≤
          (2 : ℝ) ^ (17 * interpolationScale (Fintype.card V)) ∧
        (∀ L ∈ φ.prop64NormalizedLeaves k,
          let ψ := L.toCNF
          let D₀ := BitString.initialRowWeightBound B ψ.length
          let P := BitString.greedyRowListLength B ψ.length
          let b₀ := CNF.parityBranchThreshold k D₀ (Fintype.card V)
          (∀ c ∈ ψ, c.length ≤ k) ∧
          ψ.length ≤ B * Fintype.card V ∧
          (CNF.leafCandidateQueryBound B ψ : ℝ) ≤
            (2 : ℝ) ^ interpolationScale (Fintype.card V) ∧
          ∃ A : ℕ → List (Fin ψ.length → Bool),
            commonZeroCount univ
                (ψ.parityRowSystem (CNF.candidateQueryRows (B := B) A (Sum.inr ()))) =
              ψ.modelCountOn Finset.univ ∧
            (∀ (i : Fin (3 * Fintype.card V)) (γ' : Fin P → Fin ψ.length × Bool),
              commonZeroCount univ (ψ.parityRowSystem (A (i.1 + 1))) ≤
                commonZeroCount univ
                  (ψ.parityRowSystem (CNF.candidateQueryRows A (Sum.inl (i, γ'))))) ∧
            (∀ q : CNF.LeafCandidateQueryIndex V B ψ,
              let rows := CNF.candidateQueryRows A q
              rows.length ≤ 6 * Fintype.card V ∧
              (∀ r ∈ rows, weight r ≤ D₀) ∧
              let S := heavyVars univ (univ : Finset (Fin rows.length))
                (fun j => equationScope (ψ.parityRowSystem rows j)) b₀
              ∀ ⦃n' : ℕ⦄ (e : ↥(univ \ S) ≃ Fin n'),
                (Fintype.card V ≤ 2 * n' ∧ n' ≤ Fintype.card V) ∧
                (∃ (hF : ∀ b : V → Bool,
                      Feasible (CNF.prop64ScheduleExponent k) n' (b₀ + 1)
                        (max (k * (D₀ * 2 ^ k)) 1)
                        (∑ f : {j : Fin rows.length //
                            j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                          #(branchAugmentedScope S e univ (ψ.parityRowSystem rows) b f)))
                    (D : ∀ b : V → Bool,
                      ReplacementDesign
                        (branchAugmentedScope S e univ (ψ.parityRowSystem rows) b)
                        (numNodes n') (numGroups n')
                        (intervalStart (CNF.prop64ScheduleExponent k) n')
                        (rowBound (CNF.prop64ScheduleExponent k) n') (tauRat n')),
                    (commonZeroCount (univ : Finset (Fin rows.length))
                        (ψ.parityRowSystem rows) : ℤ) =
                      (∑ b ∈ branchAssignments S,
                        ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                          (ψ.branchParityRowSystem rows S e b)
                          (commonDenom (numNodes n')
                            (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k
                          (branchPrecision (Fintype.card V))
                          (designReplacementScaledIntMap (D b)
                            (fun j => Sum.inl ⟨j, mem_univ j⟩))).eval 0 /
                            clearedProductDenom
                              (commonDenom (numNodes n')
                                (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k
                              (branchPrecision (Fintype.card V))
                              #(univ : Finset (Fin rows.length))) %
                                ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
                    (∀ b : V → Bool,
                      (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                        (ψ.branchParityRowSystem rows S e b)
                        (commonDenom (numNodes n')
                          (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k
                        (branchPrecision (Fintype.card V))
                        (designReplacementScaledIntMap (D b)
                          (fun j => Sum.inl ⟨j, mem_univ j⟩))).natDegree ≤
                        (k * (rowBound (CNF.prop64ScheduleExponent k) n' - 1)) *
                          (8 * Fintype.card V)) ∧
                    ∀ (b : V → Bool)
                        (s_active : Finset
                          ({j : Fin rows.length //
                              j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n')),
                      let d := k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))
                      let q_ord := (d * rowBound (CNF.prop64ScheduleExponent k) n') / numNodes n'
                      let C := (hF b).toCountingDesign (D b) s_active
                      (∑ t : Fin (numNodes n'),
                          (#{p : Finset (Fin n') × Finset (Fin n') |
                              #p.1 ≤ q_ord ∧ p.2 ⊆ p.1} : ℝ) *
                            (2 * (#(C.measurementBox t) : ℝ) *
                              ∑ g : Fin (numGroups n'),
                                (Fintype.card (C.LocalCube t g) : ℝ))) ≤
                        (2 : ℝ) ^ ((CNF.prop64BranchExamScaleCoeff k : ℝ) *
                          interpolationScale (Fintype.card V))) ∧
                ∀ (examSum : (V → Bool) → ℝ),
                  (∀ b ∈ branchAssignments S,
                    examSum b ≤
                      (2 : ℝ) ^ ((CNF.prop64BranchExamScaleCoeff k : ℝ) *
                        interpolationScale (Fintype.card V))) →
                  (∑ b ∈ branchAssignments S, examSum b) ≤
                    (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                      interpolationScale (Fintype.card V))) ∧
            ∀ (queryExam : CNF.LeafCandidateQueryIndex V B ψ → ℝ),
              (∀ q : CNF.LeafCandidateQueryIndex V B ψ,
                queryExam q ≤
                  (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                    interpolationScale (Fintype.card V))) →
              (∑ q : CNF.LeafCandidateQueryIndex V B ψ, queryExam q) ≤
                (2 : ℝ) ^ ((CNF.prop64LeafQueryExamScaleCoeff k : ℝ) *
                  interpolationScale (Fintype.card V))) ∧
        (∀ (leafExam : ClauseSet V → ℝ),
          (∀ L ∈ φ.prop64NormalizedLeaves k,
            leafExam L ≤
              (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                interpolationScale (Fintype.card V))) →
          ((φ.prop64NormalizedLeaves k).map leafExam).sum ≤
            (2 : ℝ) ^ ((CNF.prop64TreeExamScaleCoeff k : ℝ) *
              interpolationScale (Fintype.card V))) ∧
        ∀ (treeQueryExam : (L : ClauseSet V) → CNF.LeafCandidateQueryIndex V B L.toCNF → ℝ),
          (∀ L ∈ φ.prop64NormalizedLeaves k, ∀ q : CNF.LeafCandidateQueryIndex V B L.toCNF,
            treeQueryExam L q ≤
              (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                interpolationScale (Fintype.card V))) →
          ((φ.prop64NormalizedLeaves k).map fun (L : ClauseSet V) =>
              ∑ q : CNF.LeafCandidateQueryIndex V B L.toCNF, treeQueryExam L q).sum ≤
            (2 : ℝ) ^ ((CNF.prop64TotalExamScaleCoeff k : ℝ) *
              interpolationScale (Fintype.card V)) := by
  obtain ⟨C_B, _, hCB⟩ := CNF.exists_prop64LeafClauseRatio_le_mul_clog_pow hk
  obtain ⟨N_row, hN_row16, hrow_rec⟩ :=
    CNF.exists_branch_schedule_recovery_and_examBound_parityRowSystem_of_le_clog_pow
      k C_B (2 * (k - 1))
  obtain ⟨N₃, hN₃, hgreedy_total⟩ :=
    CNF.exists_prop64NormalizedLeaves_greedy_total_recovery_and_examBound hk
  refine ⟨max N₃ N_row, le_trans hN₃ (le_max_left _ _),
    fun {V _ _} φ hk_φ hcard => ?_⟩
  intro B
  have hN₃_le : N₃ ≤ Fintype.card V := (le_max_left _ _).trans hcard
  have hN_row_le : N_row ≤ Fintype.card V := (le_max_right _ _).trans hcard
  have hn2 : 2 ≤ Fintype.card V := le_trans (by decide : 2 ≤ 16384) (hN_row16.trans hN_row_le)
  obtain ⟨hsum, hs2, hlen_pow, hlen_scale, hleaf, htree, htotal⟩ := hgreedy_total φ hk_φ hN₃_le
  refine ⟨hsum, hs2, hlen_pow, hlen_scale, fun L hL => ?_, htree, htotal⟩
  intro ψ D₀ P b₀
  obtain ⟨hk_ψ, hm_ψ, hq_le, A₀, hlen0, hw0, hgreedy⟩ := hleaf L hL
  refine ⟨hk_ψ, hm_ψ, hq_le, ?_⟩
  rcases Nat.eq_zero_or_pos ψ.length with hlen_zero | hlen_pos
  · have hnil : ψ = [] := List.eq_nil_of_length_eq_zero hlen_zero
    let A : ℕ → List (Fin ψ.length → Bool) := fun _ => []
    have hcount_nil :
        commonZeroCount univ (ψ.parityRowSystem (CNF.candidateQueryRows (B := B) A (Sum.inr ()))) =
          ψ.modelCountOn Finset.univ := by
      change commonZeroCount univ (ψ.parityRowSystem []) = ψ.modelCountOn Finset.univ
      rw [CNF.commonZeroCount_parityRowSystem_eq_modelCountOn_add]
      suffices #{σ : V → Bool | ψ.eval σ = false ∧ PassesTests ψ.violations [] σ} = 0 by omega
      rw [card_eq_zero, filter_eq_empty_iff]
      intro σ _ ⟨hev, _⟩
      rw [hnil] at hev
      exact Bool.noConfusion hev
    have hB1 : 1 ≤ B := CNF.one_le_prop64LeafClauseRatio k (Fintype.card V)
    have hP_pos : 0 < P := by
      change 0 < 20000 * B ^ 2 * (Nat.log 2 ψ.length + 1) ^ 2
      positivity
    have hmin_vac : ∀ (i : Fin (3 * Fintype.card V)) (γ' : Fin P → Fin ψ.length × Bool),
        commonZeroCount univ (ψ.parityRowSystem (A (i.1 + 1))) ≤
          commonZeroCount univ
            (ψ.parityRowSystem (CNF.candidateQueryRows A (Sum.inl (i, γ')))) := by
      intro _ γ'
      exact Fin.elim0 (hlen_zero ▸ (γ' ⟨0, hP_pos⟩).1)
    have hB_le : B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ (2 * (k - 1)) :=
      hCB (Fintype.card V) hn2
    refine ⟨A, hcount_nil, hmin_vac, fun q => ?_, fun queryExam hq_bound => ?_⟩
    · have hlen_q : (CNF.candidateQueryRows A q).length ≤ 6 * Fintype.card V :=
        CNF.length_candidateQueryRows_le_of_step (fun _ _ => Nat.zero_le _) q
      have hw_q : ∀ r ∈ CNF.candidateQueryRows A q, weight r ≤ D₀ :=
        CNF.weight_mem_candidateQueryRows_le_of_step (by intro _ _ _ hr; cases hr) q
      exact ⟨hlen_q, hw_q, fun {n'} e =>
        hrow_rec hk_ψ hN_row_le hm_ψ hB_le le_rfl hw_q hlen_q e⟩
    · have hsum_q := CNF.sum_leafCandidateQueryIndex_le B ψ queryExam (by positivity) hq_bound
      calc (∑ q : CNF.LeafCandidateQueryIndex V B ψ, queryExam q)
          ≤ (CNF.leafCandidateQueryBound B ψ : ℝ) *
              (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                interpolationScale (Fintype.card V)) := hsum_q
        _ ≤ (2 : ℝ) ^ interpolationScale (Fintype.card V) *
              (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                interpolationScale (Fintype.card V)) :=
            mul_le_mul_of_nonneg hq_le le_rfl (Nat.cast_nonneg _) (by positivity)
        _ = (2 : ℝ) ^ ((CNF.prop64LeafQueryExamScaleCoeff k : ℝ) *
              interpolationScale (Fintype.card V)) := by
            rw [← Real.rpow_add two_pos]
            unfold CNF.prop64LeafQueryExamScaleCoeff
            push_cast
            ring_nf
  · have : Nonempty (Fin ψ.length) := ⟨⟨0, hlen_pos⟩⟩
    let A := greedyTrajectory ψ P A₀
    let γ : ℕ → Fin P → Fin ψ.length × Bool := fun i => nextGreedyStep ψ P (A i)
    have hmin : ∀ i (γ' : Fin P → Fin ψ.length × Bool),
        commonZeroCount univ (ψ.parityRowSystem (A i ++ [testRow (γ i)])) ≤
          commonZeroCount univ (ψ.parityRowSystem (A i ++ [testRow γ'])) :=
      fun i γ' => nextGreedyStep_le ψ P (A i) γ'
    obtain ⟨hcount, hq_all, hq_sum⟩ := hgreedy A γ rfl (fun _ => rfl) hmin
    exact ⟨A, hcount, fun i γ' => hmin i.1 γ', hq_all, hq_sum⟩

end Cslib.Logic.PL
