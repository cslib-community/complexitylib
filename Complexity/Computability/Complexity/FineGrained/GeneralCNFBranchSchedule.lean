/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.SparseBranchAsymptotics
public import Complexity.Logics.Propositional.CNF.SparseDesignCounter
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Bounds
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingParameters
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingTree

/-!
# Section 6.4 Proposition 6.4 disjoint sparsification leaf-to-root schedule and recovery

This module connects the Section 6.4 disjoint counting-sparsification tree
(`Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingTree`,
`CountingParameters`, and `Bounds`) with the Section 6.3 compiled parity-row
`ReplacementDesign` recovery (`Complexity.Logics.Propositional.CNF.SparseDesignCounter`) and the
Section 5.5 / 6.3 `interpolationScale` domain-examination bounds
(`Complexity.Computability.Complexity.FineGrained.SparseBranchAsymptotics`) of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (printed pp. 38–47):

1. **Proposition 6.4 sparsification parameter and leaf clause-density bounds (§6.4, pp. 43–44)**:
   At `s = numGroups n = ⌊√⌈log₂ n⌉ / ⌈log₂ ⌈log₂ n⌉⌉²⌋`, `CNF.prop64ThresholdBase k n` selects
   the Appendix A.3 dyadic threshold base `M = countingThresholdBase k (numGroups n) ≥ 2`, and
   `CNF.prop64Leaves k φ = countingLeaves (fun j => M ^ j) (reduce φ.toClauseSet)` enumerates the
   disjoint counting-sparsification leaves of `φ`:
   - `CNF.sum_modelCountOn_prop64Leaves` and `CNF.countP_eval_toCNF_prop64Leaves`: exact leaf-summed
     model-count conservation `((φ.prop64Leaves k).map fun L => L.toCNF.modelCountOn declared).sum =
     φ.modelCountOn declared` and `0`/`1` assignment partition.
   - `CNF.length_le_of_mem_prop64Leaves`: for any width-`≤ k` CNF `φ : CNF V` and any leaf
     `L ∈ φ.prop64Leaves k`, `L.toCNF` has clause width `≤ k`, per-variable occurrence at most
     `2 * ∑ c ∈ range k, M ^ c`, and (when `1 ≤ Fintype.card V`) clause count
     `L.toCNF.length ≤ CNF.prop64LeafClauseRatio k (Fintype.card V) * Fintype.card V`, where
     `CNF.prop64LeafClauseRatio k n = 2 * (∑ c ∈ range k, M ^ c) + 1`.
   - `CNF.exists_prop64ThresholdBase_le_mul_clog_sq` and
     `CNF.exists_prop64LeafClauseRatio_le_mul_clog_pow`: for `k ≥ 2` and `n ≥ 2`,
     `CNF.prop64ThresholdBase k n ≤ C_M * (Nat.clog 2 n) ^ 2` and
     `CNF.prop64LeafClauseRatio k n ≤ C_B * (Nat.clog 2 n) ^ (2 * (k - 1))`, discharging the
     Section 6.3 polylogarithmic clause-density hypothesis with exponent `β_B = 2 * (k - 1)`.
2. **Unified Section 6.3 `ReplacementDesign` constant-term recovery and
   `2 ^ (A * interpolationScale n)` domain-examination bounds (§5.4–5.5 & §6.3, pp. 38–43)**:
   - `CNF.exists_branch_schedule_recovery_and_examBound_parityRowSystem_of_le_clog_pow` and
     `CNF.exists_greedy_parityRowSystem_recovery_and_examBound_of_le_clog_pow`: combine
     `SparseBranchAsymptotics` with `CNF.SparseDesignCounter` so that the same per-branch
     `ReplacementDesign` family `D b` simultaneously certifies exact branch-summed constant-term
     recovery of `commonZeroCount univ (φ.parityRowSystem rows)` (and `φ.modelCountOn Finset.univ`
     after `3 * n` greedy rounds) via `univariateClearedParityTruncatedSum`, numerator degree at
     most `(k * (rowBound (2 * β_B + 5) n' - 1)) * (8 * Fintype.card V)`, and per-branch /
     branch-summed `2 ^ (A * interpolationScale (Fintype.card V))` domain-examination bounds.
3. **End-to-end Proposition 6.4 leaf-to-root decomposition for arbitrary `k`-CNFs
   (§6.4, pp. 43–44)**:
   - `CNF.exists_prop64Leaves_greedy_recovery_and_examBound`: for any `k ≥ 2`, there exists
     `N₂ ≥ 16384` such that for any finite variable type `V` with `N₂ ≤ Fintype.card V` and any
     width-`≤ k` CNF `φ : CNF V` (with no clause-count or occurrence restriction on `φ`),
     `φ.modelCountOn Finset.univ` equals the sum of `L.toCNF.modelCountOn Finset.univ` across
     `L ∈ φ.prop64Leaves k`, and every leaf formula `L.toCNF` admits Lemma 6.1 initial parity rows
     and Lemma 6.2 greedy extensions whose `3 * n`-round `ReplacementDesign` family recovers
     `L.toCNF.modelCountOn Finset.univ` with univariate degree
     `≤ (k * (rowBound β n' - 1)) * (8 * n)` and branch-summed examination count
     `≤ (2 : ℝ) ^ ((CNF.prop64BranchExamScaleCoeff k + 32) * interpolationScale (Fintype.card V))`.

## Main definitions

* `Cslib.Logic.PL.CNF.prop64ThresholdBase`
* `Cslib.Logic.PL.CNF.prop64LeafClauseRatio`
* `Cslib.Logic.PL.CNF.prop64Leaves`
* `Cslib.Logic.PL.CNF.prop64ScheduleExponent`
* `Cslib.Logic.PL.CNF.prop64BranchExamScaleCoeff`

## Main results

* `CNF.two_le_prop64ThresholdBase`
* `CNF.one_le_prop64LeafClauseRatio`
* `CNF.sum_modelCountOn_prop64Leaves`
* `CNF.countP_eval_toCNF_prop64Leaves`
* `CNF.length_le_of_mem_prop64Leaves`
* `CNF.exists_prop64ThresholdBase_le_mul_clog_sq`
* `CNF.exists_prop64LeafClauseRatio_le_mul_clog_pow`
* `CNF.exists_branch_schedule_recovery_and_examBound_parityRowSystem_of_le_clog_pow`
* `CNF.exists_greedy_parityRowSystem_recovery_and_examBound_of_le_clog_pow`
* `CNF.exists_parityRowSystem_modelCountOn_recovery_and_examBound_of_le_clog_pow`
* `CNF.exists_prop64Leaves_greedy_recovery_and_examBound`
* `CNF.exists_prop64Leaves_modelCountOn_recovery_and_examBound`

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
  (Sections 5.4–5.5, pp. 38–39; Sections 6.1–6.4, pp. 39–44; Appendix A, pp. 44–47)
-/

public noncomputable section

namespace Cslib.Logic.PL

open Finset
open Cslib.BitString
open Cslib.LinearAlgebra
open Cslib.Logic.PL.ClauseSet.Sparsification
open Cslib.Complexity.SubexponentialSAT
open Cslib.Complexity.SubexponentialSAT.ReplacementParams

variable {V : Type*} {n' : ℕ}

/-! ### 1. Proposition 6.4 sparsification parameter and leaf clause-density bounds -/

/-- The Proposition 6.4 / Appendix A.3 dyadic threshold base
`M = countingThresholdBase k (numGroups n)` at sparsification parameter
`s = numGroups n = ⌊√⌈log₂ n⌉ / ⌈log₂ ⌈log₂ n⌉⌉²⌋`
([OpenAI2026ETH], Proposition 6.4, pp. 43–44). -/
@[expose] def CNF.prop64ThresholdBase (k n : ℕ) : ℕ :=
  countingThresholdBase k (numGroups n)

/-- The Proposition 6.4 leaf clause-to-variable ratio
`B_leaf = 2 * (∑ c ∈ range k, (prop64ThresholdBase k n) ^ c) + 1` bounding
`L.toCNF.length ≤ B_leaf * n` on every sparse leaf `L` over `n ≥ 1` variables. -/
@[expose] def CNF.prop64LeafClauseRatio (k n : ℕ) : ℕ :=
  2 * (∑ c ∈ range k, (CNF.prop64ThresholdBase k n) ^ c) + 1

/-- The Proposition 6.4 disjoint counting-sparsification leaf list of `φ : CNF V` at geometric
threshold schedule `θ j = (CNF.prop64ThresholdBase k (Fintype.card V)) ^ j`
([OpenAI2026ETH], Lemma 6.3 & Proposition 6.4, pp. 43–44). -/
@[expose] def CNF.prop64Leaves (k : ℕ) [Fintype V] [DecidableEq V] (φ : CNF V) :
    List (ClauseSet V) :=
  countingLeaves (fun j => (CNF.prop64ThresholdBase k (Fintype.card V)) ^ j)
    (reduce φ.toClauseSet)

/-- The Lemma 4.8 / Section 6.3 replacement schedule exponent `β = 2 * (2 * (k - 1)) + 5`
associated to the Proposition 6.4 leaf clause-density exponent `β_B = 2 * (k - 1)`. -/
@[expose] def CNF.prop64ScheduleExponent (k : ℕ) : ℕ :=
  2 * (2 * (k - 1)) + 5

/-- The single-branch `interpolationScale` exponent multiplier
`CNF.parityBranchExamScaleCoeff k (2 * (k - 1))` for Proposition 6.4 leaf formulas. -/
@[expose] def CNF.prop64BranchExamScaleCoeff (k : ℕ) : ℕ :=
  CNF.parityBranchExamScaleCoeff k (2 * (k - 1))

/-- `CNF.prop64ThresholdBase k n` is at least `2` for all `k, n : ℕ`. -/
theorem CNF.two_le_prop64ThresholdBase (k n : ℕ) : 2 ≤ CNF.prop64ThresholdBase k n :=
  two_le_countingThresholdBase k (numGroups n)

/-- `CNF.prop64LeafClauseRatio k n` is at least `1` for all `k, n : ℕ`. -/
theorem CNF.one_le_prop64LeafClauseRatio (k n : ℕ) : 1 ≤ CNF.prop64LeafClauseRatio k n :=
  Nat.succ_pos _

/-- **Proposition 6.4 additive model-count conservation:**
Summing `L.toCNF.modelCountOn declared` across all leaves `L ∈ φ.prop64Leaves k` recovers
`φ.modelCountOn declared`. -/
theorem CNF.sum_modelCountOn_prop64Leaves [Fintype V] [DecidableEq V]
    (k : ℕ) (φ : CNF V) (declared : Finset V) :
    ((φ.prop64Leaves k).map fun L => L.toCNF.modelCountOn declared).sum =
      φ.modelCountOn declared :=
  sum_modelCountOn_countingLeaves_reduce_toClauseSet
    (fun j => (CNF.prop64ThresholdBase k (Fintype.card V)) ^ j) φ declared

/-- **Proposition 6.4 exact assignment partition:**
For every assignment `x : V → Bool`, the number of leaf formulas `L.toCNF` (`L ∈ φ.prop64Leaves k`)
satisfied by `x` is `1` if `φ.eval x = true` and `0` otherwise. -/
theorem CNF.countP_eval_toCNF_prop64Leaves [Fintype V] [DecidableEq V]
    (k : ℕ) (φ : CNF V) (x : V → Bool) :
    ((φ.prop64Leaves k).map ClauseSet.toCNF).countP (fun F => F.eval x) =
      if φ.eval x then 1 else 0 := by
  unfold CNF.prop64Leaves
  rw [List.countP_map]
  have hcongr : (Function.comp (fun F : CNF V => F.eval x) ClauseSet.toCNF) =
      fun L : ClauseSet V => decide (L.Sat x) := by
    funext L
    exact Bool.eq_iff_iff.mpr
      ((ClauseSet.eval_toCNF_eq_true_iff L x).trans decide_eq_true_iff.symm)
  rw [hcongr, countP_sat_countingLeaves]
  by_cases hev : φ.eval x = true
  · have hsat : (reduce φ.toClauseSet).Sat x :=
      sat_reduce_iff.mpr ((CNF.sat_toClauseSet_iff φ x).mpr hev)
    rw [ite_eq_left hsat, ite_eq_left hev]
  · have hnsat : ¬ (reduce φ.toClauseSet).Sat x := fun hs =>
      hev ((CNF.sat_toClauseSet_iff φ x).mp (sat_reduce_iff.mp hs))
    rw [ite_eq_right hnsat, ite_eq_right hev]

/-- **Proposition 6.4 leaf width, variable-occurrence, and clause-density bounds:**
If `∀ c ∈ φ, c.length ≤ k`, then for every leaf `L ∈ φ.prop64Leaves k`:
1. Every clause `c ∈ L.toCNF` has width `c.length ≤ k`.
2. Every variable `v : V` occurs in at most
   `2 * ∑ c ∈ range k, (CNF.prop64ThresholdBase k (Fintype.card V)) ^ c` clauses of `L.toCNF`.
3. Whenever `1 ≤ Fintype.card V`,
   `L.toCNF.length ≤ CNF.prop64LeafClauseRatio k (Fintype.card V) * Fintype.card V`. -/
theorem CNF.length_le_of_mem_prop64Leaves [Fintype V] [DecidableEq V]
    {φ : CNF V} {k : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    {L : ClauseSet V} (hL : L ∈ φ.prop64Leaves k) :
    (∀ c ∈ L.toCNF, c.length ≤ k) ∧
    (∀ v : V, L.toCNF.occurrences v ≤
      2 * ∑ c ∈ range k, (CNF.prop64ThresholdBase k (Fintype.card V)) ^ c) ∧
    (1 ≤ Fintype.card V →
      L.toCNF.length ≤ CNF.prop64LeafClauseRatio k (Fintype.card V) * Fintype.card V) := by
  set M := CNF.prop64ThresholdBase k (Fintype.card V)
  have hM2 : 2 ≤ M := CNF.two_le_prop64ThresholdBase k (Fintype.card V)
  have hθ1 : ∀ j, 1 ≤ M ^ j := fun j => Nat.one_le_pow j M (by omega)
  have hsparse : Sparse (M ^ ·) L := sparse_of_mem_countingLeaves_pow hM2 hL
  have hroot_k : ∀ C ∈ reduce φ.toClauseSet, C.card ≤ k := by
    intro C hC
    obtain ⟨c, hc, hcard⟩ := CNF.exists_card_le_of_mem_toClauseSet (reduce_subset _ hC)
    exact hcard.trans (hk c hc)
  have hL_k : ∀ C ∈ L, C.card ≤ k := card_le_of_mem_countingLeaves hroot_k hL
  refine ⟨fun c hc => ClauseSet.length_le_of_mem_toCNF hL_k hc, fun v => ?_, fun hn1 => ?_⟩
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

/-- **Proposition 6.4 polylogarithmic threshold-base bound (printed pp. 43–44):**
For any `k ≥ 2`, there exists `C_M ≥ 1` such that for all `n ≥ 2`,
`CNF.prop64ThresholdBase k n ≤ C_M * (Nat.clog 2 n) ^ 2`. -/
theorem CNF.exists_prop64ThresholdBase_le_mul_clog_sq {k : ℕ} (hk : 2 ≤ k) :
    ∃ C_M : ℕ, 1 ≤ C_M ∧ ∀ n : ℕ, 2 ≤ n →
      CNF.prop64ThresholdBase k n ≤ C_M * (Nat.clog 2 n) ^ 2 := by
  obtain ⟨A, hA⟩ := exists_countingThresholdBase_le_mul_clog hk
  refine ⟨max (2 * A) 2, le_trans (by decide : 1 ≤ 2) (le_max_right _ _), fun n hn => ?_⟩
  unfold CNF.prop64ThresholdBase
  set lam := Nat.clog 2 n
  have hlam1 : 1 ≤ lam :=
    (Nat.lt_clog_iff_pow_lt one_lt_two).mpr (by omega : 2 ^ 0 < n)
  rcases Nat.eq_zero_or_pos (numGroups n) with hs0 | hs_pos
  · rw [hs0, countingThresholdBase_zero]
    have h1 : 2 ≤ max (2 * A) 2 := le_max_right _ _
    have h2 : 1 ≤ lam ^ 2 := Nat.one_le_pow 2 lam hlam1
    nlinarith
  · have hs_le_lam : numGroups n ≤ lam :=
      (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)
    have hclog_s : Nat.clog 2 (numGroups n) + 1 ≤ 2 * lam := by
      have hle : Nat.clog 2 (numGroups n) ≤ lam :=
        (Nat.clog_le_iff_le_pow one_lt_two).mpr
          (hs_le_lam.trans (Nat.lt_two_pow_self (n := lam)).le)
      omega
    have hM := hA (numGroups n) hs_pos
    calc countingThresholdBase k (numGroups n)
        ≤ A * numGroups n * (Nat.clog 2 (numGroups n) + 1) := hM
      _ ≤ A * lam * (2 * lam) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left A hs_le_lam) hclog_s
      _ = (2 * A) * lam ^ 2 := by ring
      _ ≤ max (2 * A) 2 * lam ^ 2 := Nat.mul_le_mul_right _ (le_max_left _ _)

/-- **Proposition 6.4 polylogarithmic leaf clause-density bound (`B = (log n)^{O_k(1)}`,
printed p. 44):**
For any `k ≥ 2`, there exists `C_B ≥ 1` such that for all `n ≥ 2`,
`CNF.prop64LeafClauseRatio k n ≤ C_B * (Nat.clog 2 n) ^ (2 * (k - 1))`. -/
theorem CNF.exists_prop64LeafClauseRatio_le_mul_clog_pow {k : ℕ} (hk : 2 ≤ k) :
    ∃ C_B : ℕ, 1 ≤ C_B ∧ ∀ n : ℕ, 2 ≤ n →
      CNF.prop64LeafClauseRatio k n ≤ C_B * (Nat.clog 2 n) ^ (2 * (k - 1)) := by
  obtain ⟨C_M, hCM1, hCM⟩ := CNF.exists_prop64ThresholdBase_le_mul_clog_sq hk
  refine ⟨2 * k * C_M ^ (k - 1) + 1, Nat.succ_pos _, fun n hn => ?_⟩
  set lam := Nat.clog 2 n
  set M := CNF.prop64ThresholdBase k n
  have hlam1 : 1 ≤ lam :=
    (Nat.lt_clog_iff_pow_lt one_lt_two).mpr (by omega : 2 ^ 0 < n)
  have hM1 : 1 ≤ M := le_trans (by decide : 1 ≤ 2) (CNF.two_le_prop64ThresholdBase k n)
  have hM_bound : M ≤ C_M * lam ^ 2 := hCM n hn
  have hsum_le :
      ∑ c ∈ range k, M ^ c ≤ k * (C_M ^ (k - 1) * lam ^ (2 * (k - 1))) := by
    calc ∑ c ∈ range k, M ^ c
        ≤ ∑ _c ∈ range k, M ^ (k - 1) := by
          refine sum_le_sum fun c hc => ?_
          have hc_lt : c < k := mem_range.mp hc
          exact Nat.pow_le_pow_right hM1 (by omega)
      _ = k * M ^ (k - 1) := by rw [sum_const, card_range, smul_eq_mul]
      _ ≤ k * (C_M * lam ^ 2) ^ (k - 1) :=
          Nat.mul_le_mul_left k (Nat.pow_le_pow_left hM_bound (k - 1))
      _ = k * (C_M ^ (k - 1) * lam ^ (2 * (k - 1))) := by
          rw [Nat.mul_pow, ← pow_mul]
  have hpow1 : 1 ≤ lam ^ (2 * (k - 1)) := Nat.one_le_pow _ lam hlam1
  unfold CNF.prop64LeafClauseRatio
  calc 2 * (∑ c ∈ range k, M ^ c) + 1
      ≤ 2 * (k * (C_M ^ (k - 1) * lam ^ (2 * (k - 1)))) + lam ^ (2 * (k - 1)) :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 hsum_le) hpow1
    _ = (2 * k * C_M ^ (k - 1) + 1) * lam ^ (2 * (k - 1)) := by ring

/-! ### 2. Unified Section 6.3 `ReplacementDesign` recovery and `interpolationScale` bounds -/

/-- **Unified Section 6.3 schedule feasibility, `ReplacementDesign` constant-term recovery,
degree bound, and `2 ^ (A * interpolationScale n)` examination bound for `CNF.parityRowSystem`:**
For any `k C_B β_B : ℕ`, at the threshold `N₁ ≥ 16384` of
`CNF.exists_branch_schedule_and_examBound_parityRowSystem_of_le_clog_pow k C_B β_B`, whenever
`∀ c ∈ φ, c.length ≤ k`, `N₁ ≤ Fintype.card V`, `φ.length ≤ B * Fintype.card V`,
`B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B`, `W ≤ initialRowWeightBound B φ.length`,
`∀ r ∈ rows, weight r ≤ W`, and `rows.length ≤ 6 * Fintype.card V`, at
`b₀ = CNF.parityBranchThreshold k W (Fintype.card V)` and `β = 2 * β_B + 5`, there exist
per-branch feasibility proofs `hF b` and concrete `ReplacementDesign`s `D b` such that:
1. `(commonZeroCount univ (φ.parityRowSystem rows) : ℤ) = (numPassing φ.violations rows : ℤ)` equals
   the branch-summed constant-term evaluation of `univariateClearedParityTruncatedSum`.
2. Every branch polynomial has
   `natDegree ≤ (k * (rowBound (2 * β_B + 5) n' - 1)) * (8 * Fintype.card V)`.
3. Every branch `b : V → Bool` has domain-examination count at most
   `(2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) * interpolationScale (Fintype.card V))`,
   and any per-branch examination family bounded by that quantity sums across `branchAssignments S`
   to at most `(2 : ℝ) ^ (((CNF.parityBranchExamScaleCoeff k β_B + 32 : ℕ) : ℝ) *`
   `interpolationScale (Fintype.card V))`. -/
theorem CNF.exists_branch_schedule_recovery_and_examBound_parityRowSystem_of_le_clog_pow
    (k C_B β_B : ℕ) :
    ∃ N₁ : ℕ, 16384 ≤ N₁ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        {φ : CNF V} ⦃n' B W : ℕ⦄,
        (∀ c ∈ φ, c.length ≤ k) →
        N₁ ≤ Fintype.card V →
        φ.length ≤ B * Fintype.card V →
        B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B →
        W ≤ initialRowWeightBound B φ.length →
        ∀ {rows : List (Fin φ.length → Bool)},
          (∀ r ∈ rows, weight r ≤ W) →
          rows.length ≤ 6 * Fintype.card V →
          let b₀ := CNF.parityBranchThreshold k W (Fintype.card V)
          let S := heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀
          ∀ (e : ↥(univ \ S) ≃ Fin n'),
            (Fintype.card V ≤ 2 * n' ∧ n' ≤ Fintype.card V) ∧
            (∃ (hF : ∀ b : V → Bool,
                  Feasible (2 * β_B + 5) n' (b₀ + 1) (max (k * (W * 2 ^ k)) 1)
                    (∑ f : {j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                      #(branchAugmentedScope S e univ (φ.parityRowSystem rows) b f)))
                (D : ∀ b : V → Bool,
                  ReplacementDesign
                    (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
                    (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
                    (rowBound (2 * β_B + 5) n') (tauRat n')),
                (commonZeroCount (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) : ℤ) =
                  (∑ b ∈ branchAssignments S,
                    ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                      (φ.branchParityRowSystem rows S e b)
                      (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                      (branchPrecision (Fintype.card V))
                      (designReplacementScaledIntMap (D b)
                        (fun j => Sum.inl ⟨j, mem_univ j⟩))).eval 0 /
                        clearedProductDenom
                          (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                          (branchPrecision (Fintype.card V))
                          #(univ : Finset (Fin rows.length))) %
                            ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
                (∀ b : V → Bool,
                  (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                    (φ.branchParityRowSystem rows S e b)
                    (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                    (branchPrecision (Fintype.card V))
                    (designReplacementScaledIntMap (D b)
                      (fun j => Sum.inl ⟨j, mem_univ j⟩))).natDegree ≤
                    (k * (rowBound (2 * β_B + 5) n' - 1)) * (8 * Fintype.card V)) ∧
                ∀ (b : V → Bool)
                    (s_active : Finset
                      ({j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n')),
                  let d := k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))
                  let q := (d * rowBound (2 * β_B + 5) n') / numNodes n'
                  let C := (hF b).toCountingDesign (D b) s_active
                  (∑ t : Fin (numNodes n'),
                      (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
                        (2 * (#(C.measurementBox t) : ℝ) *
                          ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
                    (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                      interpolationScale (Fintype.card V))) ∧
            ∀ (examSum : (V → Bool) → ℝ),
              (∀ b ∈ branchAssignments S,
                examSum b ≤
                  (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                    interpolationScale (Fintype.card V))) →
              (∑ b ∈ branchAssignments S, examSum b) ≤
                (2 : ℝ) ^ (((CNF.parityBranchExamScaleCoeff k β_B + 32 : ℕ) : ℝ) *
                  interpolationScale (Fintype.card V)) := by
  obtain ⟨N₁, hN₁, hsched⟩ :=
    CNF.exists_branch_schedule_and_examBound_parityRowSystem_of_le_clog_pow k C_B β_B
  refine ⟨N₁, hN₁, fun {V _ _ φ n' B W} hk hcard hm hB hW_bound {rows} hW hlen => ?_⟩
  intro b₀ S e
  obtain ⟨hn_bounds, hbranch, hsum⟩ := hsched hk hcard hm hB hW_bound hW hlen e
  choose hF D hexam using hbranch
  refine ⟨hn_bounds, ⟨hF, D, ?_, fun b => ?_, hexam⟩, hsum⟩
  · exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design hk rows S e
      (fun b => branchAugmentedScope S e univ (φ.parityRowSystem rows) b) D
      (fun _ j => Sum.inl ⟨j, mem_univ j⟩)
  · have hdeg :=
      CNF.natDegree_univariateClearedParityTruncatedSum_branchParityRowSystem_le hk rows S e b
        (D b) (fun j => Sum.inl ⟨j, mem_univ j⟩) (branchPrecision (Fintype.card V))
    refine hdeg.trans (Nat.mul_le_mul_left _ ?_)
    unfold branchPrecision
    omega

/-- **Unified Lemma 6.1 + Lemma 6.2 + Section 6.3 greedy parity-test schedule with
`ReplacementDesign` constant-term recovery and `2 ^ (A * interpolationScale n)` bounds:**
For any `k C_B β_B : ℕ`, at the threshold `N₁ ≥ 16384` of
`CNF.exists_greedy_parityRowSystem_branch_schedule_and_examBound_of_le_clog_pow k C_B β_B`, for
any width-`≤ k` CNF `φ : CNF V` with `N₁ ≤ Fintype.card V`, `1 ≤ B`,
`B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B`, and `φ.length ≤ B * Fintype.card V`, there exist
initial rows `A₀` (`A₀.length ≤ 3 * Fintype.card V`, weight `≤ D₀`) such that for any greedy
extension `A` up to stage `3 * Fintype.card V`:
1. `commonZeroCount univ (φ.parityRowSystem (A (3 * Fintype.card V))) = φ.modelCountOn univ`.
2. At every stage `i ≤ 3 * Fintype.card V`, `(A i).length ≤ 6 * Fintype.card V`, and for any
   `e : ↥(univ \ S_i) ≃ Fin n'`, there exist per-branch `hF b` and `D b` recovering
   `commonZeroCount univ (φ.parityRowSystem (A i))` (and `φ.modelCountOn Finset.univ` at stage
   `3 * Fintype.card V`) via `univariateClearedParityTruncatedSum` with numerator degree
   `≤ (k * (rowBound (2 * β_B + 5) n' - 1)) * (8 * Fintype.card V)` and per-branch / branch-summed
   `2 ^ (A * interpolationScale n)` domain-examination bounds. -/
theorem CNF.exists_greedy_parityRowSystem_recovery_and_examBound_of_le_clog_pow
    (k C_B β_B : ℕ) :
    ∃ N₁ : ℕ, 16384 ≤ N₁ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (φ : CNF V) {B : ℕ},
        (∀ c ∈ φ, c.length ≤ k) →
        N₁ ≤ Fintype.card V →
        1 ≤ B →
        B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B →
        φ.length ≤ B * Fintype.card V →
        let D₀ := initialRowWeightBound B φ.length
        let P := greedyRowListLength B φ.length
        let b₀ := CNF.parityBranchThreshold k D₀ (Fintype.card V)
        ∃ A₀ : List (Fin φ.length → Bool), A₀.length ≤ 3 * Fintype.card V ∧
          (∀ r ∈ A₀, weight r ≤ D₀) ∧
          ∀ (A : ℕ → List (Fin φ.length → Bool))
            (γ : ℕ → Fin P → Fin φ.length × Bool),
            A 0 = A₀ → (∀ i, A (i + 1) = A i ++ [testRow (γ i)]) →
            (∀ i (γ' : Fin P → Fin φ.length × Bool),
              commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow (γ i)])) ≤
                commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ']))) →
            commonZeroCount univ (φ.parityRowSystem (A (3 * Fintype.card V))) =
              φ.modelCountOn Finset.univ ∧
            ∀ i ≤ 3 * Fintype.card V,
              (A i).length ≤ 6 * Fintype.card V ∧
              let S := heavyVars univ (univ : Finset (Fin (A i).length))
                (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀
              ∀ ⦃n' : ℕ⦄ (e : ↥(univ \ S) ≃ Fin n'),
                (Fintype.card V ≤ 2 * n' ∧ n' ≤ Fintype.card V) ∧
                (∃ (hF : ∀ b : V → Bool,
                      Feasible (2 * β_B + 5) n' (b₀ + 1) (max (k * (D₀ * 2 ^ k)) 1)
                        (∑ f : {j : Fin (A i).length //
                            j ∈ (univ : Finset (Fin (A i).length))} ⊕ Fin n',
                          #(branchAugmentedScope S e univ (φ.parityRowSystem (A i)) b f)))
                    (D : ∀ b : V → Bool,
                      ReplacementDesign
                        (branchAugmentedScope S e univ (φ.parityRowSystem (A i)) b)
                        (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
                        (rowBound (2 * β_B + 5) n') (tauRat n')),
                    (commonZeroCount (univ : Finset (Fin (A i).length))
                        (φ.parityRowSystem (A i)) : ℤ) =
                      (∑ b ∈ branchAssignments S,
                        ((univariateClearedParityTruncatedSum (univ : Finset (Fin (A i).length))
                          (φ.branchParityRowSystem (A i) S e b)
                          (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                          (branchPrecision (Fintype.card V))
                          (designReplacementScaledIntMap (D b)
                            (fun j => Sum.inl ⟨j, mem_univ j⟩))).eval 0 /
                            clearedProductDenom
                              (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                              (branchPrecision (Fintype.card V))
                              #(univ : Finset (Fin (A i).length))) %
                                ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
                    (∀ b : V → Bool,
                      (univariateClearedParityTruncatedSum (univ : Finset (Fin (A i).length))
                        (φ.branchParityRowSystem (A i) S e b)
                        (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                        (branchPrecision (Fintype.card V))
                        (designReplacementScaledIntMap (D b)
                          (fun j => Sum.inl ⟨j, mem_univ j⟩))).natDegree ≤
                        (k * (rowBound (2 * β_B + 5) n' - 1)) * (8 * Fintype.card V)) ∧
                    ∀ (b : V → Bool)
                        (s_active : Finset
                          ({j : Fin (A i).length //
                              j ∈ (univ : Finset (Fin (A i).length))} ⊕ Fin n')),
                      let d := k * ((A i).length + 2 * (branchPrecision (Fintype.card V) - 1))
                      let q := (d * rowBound (2 * β_B + 5) n') / numNodes n'
                      let C := (hF b).toCountingDesign (D b) s_active
                      (∑ t : Fin (numNodes n'),
                          (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
                            (2 * (#(C.measurementBox t) : ℝ) *
                              ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
                        (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                          interpolationScale (Fintype.card V))) ∧
                ∀ (examSum : (V → Bool) → ℝ),
                  (∀ b ∈ branchAssignments S,
                    examSum b ≤
                      (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                        interpolationScale (Fintype.card V))) →
                  (∑ b ∈ branchAssignments S, examSum b) ≤
                    (2 : ℝ) ^ (((CNF.parityBranchExamScaleCoeff k β_B + 32 : ℕ) : ℝ) *
                      interpolationScale (Fintype.card V)) := by
  obtain ⟨N₁, hN₁, hgreedy_sched⟩ :=
    CNF.exists_greedy_parityRowSystem_branch_schedule_and_examBound_of_le_clog_pow k C_B β_B
  refine ⟨N₁, hN₁, fun {V _ _} φ {B} hk hcard hB1 hB_le hm => ?_⟩
  intro D₀ P b₀
  obtain ⟨A₀, hlen0, hw0, hgreedy⟩ := hgreedy_sched φ hk hcard hB1 hB_le hm
  refine ⟨A₀, hlen0, hw0, fun A γ h0 hA hγ => ?_⟩
  obtain ⟨hcount, hstage⟩ := hgreedy A γ h0 hA hγ
  refine ⟨hcount, fun i hi => ?_⟩
  obtain ⟨hlen_i, hstage_e⟩ := hstage i hi
  refine ⟨hlen_i, ?_⟩
  intro S n' e
  obtain ⟨hn_bounds, hbranch, hsum⟩ := hstage_e e
  choose hF D hexam using hbranch
  refine ⟨hn_bounds, ⟨hF, D, ?_, fun b => ?_, hexam⟩, hsum⟩
  · exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design hk (A i) S e
      (fun b => branchAugmentedScope S e univ (φ.parityRowSystem (A i)) b) D
      (fun _ j => Sum.inl ⟨j, mem_univ j⟩)
  · have hdeg :=
      CNF.natDegree_univariateClearedParityTruncatedSum_branchParityRowSystem_le hk (A i) S e b
        (D b) (fun j => Sum.inl ⟨j, mem_univ j⟩) (branchPrecision (Fintype.card V))
    refine hdeg.trans (Nat.mul_le_mul_left _ ?_)
    unfold branchPrecision
    omega

private noncomputable def nextGreedyStep [Fintype V] [DecidableEq V]
    (φ : CNF V) (P : ℕ) [Nonempty (Fin φ.length)]
    (L : List (Fin φ.length → Bool)) : Fin P → Fin φ.length × Bool :=
  (exists_min_image (univ : Finset (Fin P → Fin φ.length × Bool))
    (fun γ' => commonZeroCount univ (φ.parityRowSystem (L ++ [testRow γ'])))
    univ_nonempty).choose

private noncomputable def greedyTrajectory [Fintype V] [DecidableEq V]
    (φ : CNF V) (P : ℕ) [Nonempty (Fin φ.length)]
    (A₀ : List (Fin φ.length → Bool)) : ℕ → List (Fin φ.length → Bool)
  | 0 => A₀
  | i + 1 =>
    let L := greedyTrajectory φ P A₀ i
    L ++ [testRow (nextGreedyStep φ P L)]

/-- **Unconditional Section 6.3 parity-row system existence, `ReplacementDesign` recovery of
`φ.modelCountOn Finset.univ`, degree bound, and `2 ^ (A * interpolationScale n)` examination
bound:**
For any `k C_B β_B : ℕ`, there exists `N₁ ≥ 16384` such that for any width-`≤ k` CNF `φ : CNF V`
with `N₁ ≤ Fintype.card V`, `1 ≤ B`, `B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B`, and
`φ.length ≤ B * Fintype.card V` (including `φ = []`), at
`D₀ = initialRowWeightBound B φ.length` and
`b₀ = CNF.parityBranchThreshold k D₀ (Fintype.card V)`, there exists a parity-row list
`rows : List (Fin φ.length → Bool)` (`rows.length ≤ 6 * Fintype.card V`) such that:
1. `commonZeroCount univ (φ.parityRowSystem rows) = φ.modelCountOn Finset.univ`.
2. For any free-variable equivalence `e : ↥(univ \ S) ≃ Fin n'`, there exist per-branch `hF b` and
   concrete `ReplacementDesign`s `D b` such that `(φ.modelCountOn Finset.univ : ℤ)` equals the
   branch-summed constant-term evaluation of `univariateClearedParityTruncatedSum`, with numerator
   degree `≤ (k * (rowBound (2 * β_B + 5) n' - 1)) * (8 * Fintype.card V)` and single-branch /
   branch-summed `2 ^ (A * interpolationScale (Fintype.card V))` domain-examination bounds. -/
theorem CNF.exists_parityRowSystem_modelCountOn_recovery_and_examBound_of_le_clog_pow
    (k C_B β_B : ℕ) :
    ∃ N₁ : ℕ, 16384 ≤ N₁ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (φ : CNF V) {B : ℕ},
        (∀ c ∈ φ, c.length ≤ k) →
        N₁ ≤ Fintype.card V →
        1 ≤ B →
        B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B →
        φ.length ≤ B * Fintype.card V →
        let D₀ := initialRowWeightBound B φ.length
        let b₀ := CNF.parityBranchThreshold k D₀ (Fintype.card V)
        ∃ rows : List (Fin φ.length → Bool),
          rows.length ≤ 6 * Fintype.card V ∧
          commonZeroCount univ (φ.parityRowSystem rows) = φ.modelCountOn Finset.univ ∧
          let S := heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀
          ∀ ⦃n' : ℕ⦄ (e : ↥(univ \ S) ≃ Fin n'),
            (Fintype.card V ≤ 2 * n' ∧ n' ≤ Fintype.card V) ∧
            (∃ (hF : ∀ b : V → Bool,
                  Feasible (2 * β_B + 5) n' (b₀ + 1) (max (k * (D₀ * 2 ^ k)) 1)
                    (∑ f : {j : Fin rows.length //
                        j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                      #(branchAugmentedScope S e univ (φ.parityRowSystem rows) b f)))
                (D : ∀ b : V → Bool,
                  ReplacementDesign
                    (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
                    (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
                    (rowBound (2 * β_B + 5) n') (tauRat n')),
                (φ.modelCountOn Finset.univ : ℤ) =
                  (∑ b ∈ branchAssignments S,
                    ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                      (φ.branchParityRowSystem rows S e b)
                      (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                      (branchPrecision (Fintype.card V))
                      (designReplacementScaledIntMap (D b)
                        (fun j => Sum.inl ⟨j, mem_univ j⟩))).eval 0 /
                        clearedProductDenom
                          (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                          (branchPrecision (Fintype.card V))
                          #(univ : Finset (Fin rows.length))) %
                            ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
                (∀ b : V → Bool,
                  (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                    (φ.branchParityRowSystem rows S e b)
                    (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                    (branchPrecision (Fintype.card V))
                    (designReplacementScaledIntMap (D b)
                      (fun j => Sum.inl ⟨j, mem_univ j⟩))).natDegree ≤
                    (k * (rowBound (2 * β_B + 5) n' - 1)) * (8 * Fintype.card V)) ∧
                ∀ (b : V → Bool)
                    (s_active : Finset
                      ({j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n')),
                  let d := k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))
                  let q := (d * rowBound (2 * β_B + 5) n') / numNodes n'
                  let C := (hF b).toCountingDesign (D b) s_active
                  (∑ t : Fin (numNodes n'),
                      (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
                        (2 * (#(C.measurementBox t) : ℝ) *
                          ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
                    (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                      interpolationScale (Fintype.card V))) ∧
            ∀ (examSum : (V → Bool) → ℝ),
              (∀ b ∈ branchAssignments S,
                examSum b ≤
                  (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                    interpolationScale (Fintype.card V))) →
              (∑ b ∈ branchAssignments S, examSum b) ≤
                (2 : ℝ) ^ (((CNF.parityBranchExamScaleCoeff k β_B + 32 : ℕ) : ℝ) *
                  interpolationScale (Fintype.card V)) := by
  obtain ⟨N_row, hN_row16, hrow_rec⟩ :=
    CNF.exists_branch_schedule_recovery_and_examBound_parityRowSystem_of_le_clog_pow k C_B β_B
  obtain ⟨N_gr, hN_gr16, hgreedy_rec⟩ :=
    CNF.exists_greedy_parityRowSystem_recovery_and_examBound_of_le_clog_pow k C_B β_B
  refine ⟨max N_row N_gr, le_trans hN_row16 (le_max_left _ _),
    fun {V _ _} φ {B} hk hcard hB1 hB_le hm => ?_⟩
  intro D₀ b₀
  rcases Nat.eq_zero_or_pos φ.length with hlen0 | hlen_pos
  · have hnil : φ = [] := List.eq_nil_of_length_eq_zero hlen0
    have hcount_nil :
        commonZeroCount (univ : Finset (Fin ([] : List (Fin φ.length → Bool)).length))
          (φ.parityRowSystem []) = φ.modelCountOn Finset.univ := by
      rw [CNF.commonZeroCount_parityRowSystem_eq_modelCountOn_add]
      suffices #{σ : V → Bool | φ.eval σ = false ∧ PassesTests φ.violations [] σ} = 0 by omega
      rw [card_eq_zero, filter_eq_empty_iff]
      intro σ _ ⟨hev, _⟩
      rw [hnil] at hev
      exact Bool.noConfusion hev
    refine ⟨[], Nat.zero_le _, hcount_nil, ?_⟩
    intro S n' e
    have hN_row : N_row ≤ Fintype.card V := (le_max_left _ _).trans hcard
    have hW_nil : ∀ r ∈ ([] : List (Fin φ.length → Bool)), weight r ≤ D₀ := by
      intro r hr; cases hr
    have hlen_nil : ([] : List (Fin φ.length → Bool)).length ≤ 6 * Fintype.card V := Nat.zero_le _
    obtain ⟨hn_bounds, ⟨hF, D, hrec, hdeg, hexam⟩, hsum⟩ :=
      hrow_rec hk hN_row hm hB_le le_rfl hW_nil hlen_nil e
    rw [hcount_nil] at hrec
    exact ⟨hn_bounds, ⟨hF, D, hrec, hdeg, hexam⟩, hsum⟩
  · have : Nonempty (Fin φ.length) := ⟨⟨0, hlen_pos⟩⟩
    have hN_gr : N_gr ≤ Fintype.card V := (le_max_right _ _).trans hcard
    obtain ⟨A₀, _, _, hgreedy⟩ := hgreedy_rec φ hk hN_gr hB1 hB_le hm
    let P := greedyRowListLength B φ.length
    let A := greedyTrajectory φ P A₀
    let γ : ℕ → Fin P → Fin φ.length × Bool := fun i => nextGreedyStep φ P (A i)
    have hmin : ∀ i (γ' : Fin P → Fin φ.length × Bool),
        commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow (γ i)])) ≤
          commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ'])) :=
      fun i γ' =>
        (exists_min_image (univ : Finset (Fin P → Fin φ.length × Bool))
          (fun γ'' => commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ''])))
          univ_nonempty).choose_spec.2 γ' (mem_univ γ')
    obtain ⟨hcount, hstage⟩ := hgreedy A γ rfl (fun _ => rfl) hmin
    obtain ⟨hlen_final, hstage_final⟩ := hstage (3 * Fintype.card V) le_rfl
    refine ⟨A (3 * Fintype.card V), hlen_final, hcount, ?_⟩
    intro S n' e
    obtain ⟨hn_bounds, ⟨hF, D, hrec, hdeg, hexam⟩, hsum⟩ := hstage_final e
    rw [hcount] at hrec
    exact ⟨hn_bounds, ⟨hF, D, hrec, hdeg, hexam⟩, hsum⟩

/-! ### 3. Section 6.4 Proposition 6.4 leaf-to-root decomposition for arbitrary `k`-CNFs -/

/-- **Proposition 6.4 end-to-end disjoint sparsification leaf-to-root decomposition,
`ReplacementDesign` constant-term recovery, and `2 ^ (A * interpolationScale n)` examination
bounds for arbitrary `k`-CNFs ([OpenAI2026ETH], §6.4, pp. 43–44):**
For any `k ≥ 2`, there exists `N₂ ≥ 16384` such that for any finite variable type `V` with
`N₂ ≤ Fintype.card V` and any width-`≤ k` CNF `φ : CNF V` (with no clause-count or
variable-occurrence restriction on `φ`):
1. **Exact leaf-summed model-count conservation:**
   `((φ.prop64Leaves k).map fun L => L.toCNF.modelCountOn Finset.univ).sum =`
   `φ.modelCountOn Finset.univ`.
2. **Per-leaf greedy parity-design recovery and `interpolationScale` examination bounds:**
   For every leaf `L ∈ φ.prop64Leaves k`, setting `ψ := L.toCNF`,
   `B := CNF.prop64LeafClauseRatio k (Fintype.card V)`,
   `D₀ := initialRowWeightBound B ψ.length`,
   `P := greedyRowListLength B ψ.length`, and
   `b₀ := CNF.parityBranchThreshold k D₀ (Fintype.card V)`:
   - `(∀ c ∈ ψ, c.length ≤ k) ∧ ψ.length ≤ B * Fintype.card V`, and
   - `ψ` admits Lemma 6.1 initial parity rows `A₀` (`A₀.length ≤ 3 * Fintype.card V`, row weight
     `≤ D₀`) such that for any Lemma 6.2 greedy extension `A` up to stage `3 * Fintype.card V`:
     - `commonZeroCount univ (ψ.parityRowSystem (A (3 * Fintype.card V))) = ψ.modelCountOn univ`,
     - at every stage `i ≤ 3 * Fintype.card V`, `(A i).length ≤ 6 * Fintype.card V`, and for any
       free-variable equivalence `e : ↥(univ \ S_i) ≃ Fin n'`, there exist per-branch `hF b` and
       concrete `ReplacementDesign`s `D b` at schedule exponent `β = CNF.prop64ScheduleExponent k`
       recovering `commonZeroCount univ (ψ.parityRowSystem (A i))` (and `L.toCNF.modelCountOn univ`
       at stage `3 * Fintype.card V`) via `univariateClearedParityTruncatedSum` with numerator
       degree `≤ (k * (rowBound (CNF.prop64ScheduleExponent k) n' - 1)) * (8 * Fintype.card V)`,
       single-branch examination count at most
       `(2 : ℝ) ^ ((CNF.prop64BranchExamScaleCoeff k : ℝ) * interpolationScale (Fintype.card V))`,
       and branch-summed examination count at most
       `(2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *`
       `interpolationScale (Fintype.card V))`. -/
theorem CNF.exists_prop64Leaves_greedy_recovery_and_examBound {k : ℕ} (hk : 2 ≤ k) :
    ∃ N₂ : ℕ, 16384 ≤ N₂ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (φ : CNF V),
        (∀ c ∈ φ, c.length ≤ k) →
        N₂ ≤ Fintype.card V →
        ((φ.prop64Leaves k).map fun L => L.toCNF.modelCountOn Finset.univ).sum =
          φ.modelCountOn Finset.univ ∧
        ∀ L ∈ φ.prop64Leaves k,
          let ψ := L.toCNF
          let B := CNF.prop64LeafClauseRatio k (Fintype.card V)
          let D₀ := initialRowWeightBound B ψ.length
          let P := greedyRowListLength B ψ.length
          let b₀ := CNF.parityBranchThreshold k D₀ (Fintype.card V)
          (∀ c ∈ ψ, c.length ≤ k) ∧
          ψ.length ≤ B * Fintype.card V ∧
          ∃ A₀ : List (Fin ψ.length → Bool), A₀.length ≤ 3 * Fintype.card V ∧
            (∀ r ∈ A₀, weight r ≤ D₀) ∧
            ∀ (A : ℕ → List (Fin ψ.length → Bool))
              (γ : ℕ → Fin P → Fin ψ.length × Bool),
              A 0 = A₀ → (∀ i, A (i + 1) = A i ++ [testRow (γ i)]) →
              (∀ i (γ' : Fin P → Fin ψ.length × Bool),
                commonZeroCount univ (ψ.parityRowSystem (A i ++ [testRow (γ i)])) ≤
                  commonZeroCount univ (ψ.parityRowSystem (A i ++ [testRow γ']))) →
              commonZeroCount univ (ψ.parityRowSystem (A (3 * Fintype.card V))) =
                ψ.modelCountOn Finset.univ ∧
              ∀ i ≤ 3 * Fintype.card V,
                (A i).length ≤ 6 * Fintype.card V ∧
                let S := heavyVars univ (univ : Finset (Fin (A i).length))
                  (fun j => equationScope (ψ.parityRowSystem (A i) j)) b₀
                ∀ ⦃n' : ℕ⦄ (e : ↥(univ \ S) ≃ Fin n'),
                  (Fintype.card V ≤ 2 * n' ∧ n' ≤ Fintype.card V) ∧
                  (∃ (hF : ∀ b : V → Bool,
                        Feasible (CNF.prop64ScheduleExponent k) n' (b₀ + 1)
                          (max (k * (D₀ * 2 ^ k)) 1)
                          (∑ f : {j : Fin (A i).length //
                              j ∈ (univ : Finset (Fin (A i).length))} ⊕ Fin n',
                            #(branchAugmentedScope S e univ (ψ.parityRowSystem (A i)) b f)))
                      (D : ∀ b : V → Bool,
                        ReplacementDesign
                          (branchAugmentedScope S e univ (ψ.parityRowSystem (A i)) b)
                          (numNodes n') (numGroups n')
                          (intervalStart (CNF.prop64ScheduleExponent k) n')
                          (rowBound (CNF.prop64ScheduleExponent k) n') (tauRat n')),
                      (commonZeroCount (univ : Finset (Fin (A i).length))
                          (ψ.parityRowSystem (A i)) : ℤ) =
                        (∑ b ∈ branchAssignments S,
                          ((univariateClearedParityTruncatedSum (univ : Finset (Fin (A i).length))
                            (ψ.branchParityRowSystem (A i) S e b)
                            (commonDenom (numNodes n')
                              (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k
                            (branchPrecision (Fintype.card V))
                            (designReplacementScaledIntMap (D b)
                              (fun j => Sum.inl ⟨j, mem_univ j⟩))).eval 0 /
                              clearedProductDenom
                                (commonDenom (numNodes n')
                                  (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k
                                (branchPrecision (Fintype.card V))
                                #(univ : Finset (Fin (A i).length))) %
                                  ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
                      (∀ b : V → Bool,
                        (univariateClearedParityTruncatedSum (univ : Finset (Fin (A i).length))
                          (ψ.branchParityRowSystem (A i) S e b)
                          (commonDenom (numNodes n')
                            (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k
                          (branchPrecision (Fintype.card V))
                          (designReplacementScaledIntMap (D b)
                            (fun j => Sum.inl ⟨j, mem_univ j⟩))).natDegree ≤
                          (k * (rowBound (CNF.prop64ScheduleExponent k) n' - 1)) *
                            (8 * Fintype.card V)) ∧
                      ∀ (b : V → Bool)
                          (s_active : Finset
                            ({j : Fin (A i).length //
                                j ∈ (univ : Finset (Fin (A i).length))} ⊕ Fin n')),
                        let d := k * ((A i).length + 2 * (branchPrecision (Fintype.card V) - 1))
                        let q := (d * rowBound (CNF.prop64ScheduleExponent k) n') / numNodes n'
                        let C := (hF b).toCountingDesign (D b) s_active
                        (∑ t : Fin (numNodes n'),
                            (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
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
                        interpolationScale (Fintype.card V)) := by
  obtain ⟨C_B, _, hCB⟩ := CNF.exists_prop64LeafClauseRatio_le_mul_clog_pow hk
  obtain ⟨N₁, hN₁, hgreedy_rec⟩ :=
    CNF.exists_greedy_parityRowSystem_recovery_and_examBound_of_le_clog_pow k C_B (2 * (k - 1))
  refine ⟨N₁, hN₁, fun {V _ _} φ hk_φ hcard => ?_⟩
  refine ⟨CNF.sum_modelCountOn_prop64Leaves k φ Finset.univ, fun L hL => ?_⟩
  intro ψ B D₀ P b₀
  have hn1 : 1 ≤ Fintype.card V := by omega
  have hn2 : 2 ≤ Fintype.card V := by omega
  obtain ⟨hk_ψ, _, hlen_ψ⟩ := CNF.length_le_of_mem_prop64Leaves hk_φ hL
  have hm_ψ : ψ.length ≤ B * Fintype.card V := hlen_ψ hn1
  have hB1 : 1 ≤ B := CNF.one_le_prop64LeafClauseRatio k (Fintype.card V)
  have hB_le : B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ (2 * (k - 1)) := hCB (Fintype.card V) hn2
  refine ⟨hk_ψ, hm_ψ, ?_⟩
  exact hgreedy_rec ψ hk_ψ hcard hB1 hB_le hm_ψ

/-- **Proposition 6.4 unconditional leaf-to-root `modelCountOn` recovery and
`2 ^ (A * interpolationScale n)` examination bounds for arbitrary `k`-CNFs
([OpenAI2026ETH], §6.4, pp. 43–44):**
For any `k ≥ 2`, there exists `N₂ ≥ 16384` such that for any finite variable type `V` with
`N₂ ≤ Fintype.card V` and any width-`≤ k` CNF `φ : CNF V` (with no clause-count, occurrence, or
nonemptiness restriction on `φ` or its leaves):
1. `((φ.prop64Leaves k).map fun L => L.toCNF.modelCountOn Finset.univ).sum =`
   `φ.modelCountOn Finset.univ`.
2. For every leaf `L ∈ φ.prop64Leaves k` (`ψ := L.toCNF`), there unconditionally exists a parity-row
   list `rows : List (Fin ψ.length → Bool)` (`rows.length ≤ 6 * Fintype.card V`) such that
   `commonZeroCount univ (ψ.parityRowSystem rows) = ψ.modelCountOn Finset.univ`, and for any
   free-variable equivalence `e : ↥(univ \ S) ≃ Fin n'`, there exist per-branch `hF b` and concrete
   `ReplacementDesign`s `D b` at schedule exponent `β = CNF.prop64ScheduleExponent k` recovering
   `(L.toCNF.modelCountOn Finset.univ : ℤ)` via `univariateClearedParityTruncatedSum` with
   numerator degree
   `≤ (k * (rowBound (CNF.prop64ScheduleExponent k) n' - 1)) * (8 * Fintype.card V)`
   and single-branch / branch-summed `2 ^ (A * interpolationScale (Fintype.card V))`
   domain-examination bounds. -/
theorem CNF.exists_prop64Leaves_modelCountOn_recovery_and_examBound {k : ℕ} (hk : 2 ≤ k) :
    ∃ N₂ : ℕ, 16384 ≤ N₂ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (φ : CNF V),
        (∀ c ∈ φ, c.length ≤ k) →
        N₂ ≤ Fintype.card V →
        ((φ.prop64Leaves k).map fun L => L.toCNF.modelCountOn Finset.univ).sum =
          φ.modelCountOn Finset.univ ∧
        ∀ L ∈ φ.prop64Leaves k,
          let ψ := L.toCNF
          let B := CNF.prop64LeafClauseRatio k (Fintype.card V)
          let D₀ := initialRowWeightBound B ψ.length
          let b₀ := CNF.parityBranchThreshold k D₀ (Fintype.card V)
          (∀ c ∈ ψ, c.length ≤ k) ∧
          ψ.length ≤ B * Fintype.card V ∧
          ∃ rows : List (Fin ψ.length → Bool),
            rows.length ≤ 6 * Fintype.card V ∧
            commonZeroCount univ (ψ.parityRowSystem rows) = ψ.modelCountOn Finset.univ ∧
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
                  (ψ.modelCountOn Finset.univ : ℤ) =
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
                    let q := (d * rowBound (CNF.prop64ScheduleExponent k) n') / numNodes n'
                    let C := (hF b).toCountingDesign (D b) s_active
                    (∑ t : Fin (numNodes n'),
                        (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
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
                    interpolationScale (Fintype.card V)) := by
  obtain ⟨C_B, _, hCB⟩ := CNF.exists_prop64LeafClauseRatio_le_mul_clog_pow hk
  obtain ⟨N₁, hN₁, hmodel_rec⟩ :=
    CNF.exists_parityRowSystem_modelCountOn_recovery_and_examBound_of_le_clog_pow
      k C_B (2 * (k - 1))
  refine ⟨N₁, hN₁, fun {V _ _} φ hk_φ hcard => ?_⟩
  refine ⟨CNF.sum_modelCountOn_prop64Leaves k φ Finset.univ, fun L hL => ?_⟩
  intro ψ B D₀ b₀
  have hn1 : 1 ≤ Fintype.card V := by omega
  have hn2 : 2 ≤ Fintype.card V := by omega
  obtain ⟨hk_ψ, _, hlen_ψ⟩ := CNF.length_le_of_mem_prop64Leaves hk_φ hL
  have hm_ψ : ψ.length ≤ B * Fintype.card V := hlen_ψ hn1
  have hB1 : 1 ≤ B := CNF.one_le_prop64LeafClauseRatio k (Fintype.card V)
  have hB_le : B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ (2 * (k - 1)) := hCB (Fintype.card V) hn2
  refine ⟨hk_ψ, hm_ψ, ?_⟩
  exact hmodel_rec ψ hk_ψ hcard hB1 hB_le hm_ψ

end Cslib.Logic.PL
