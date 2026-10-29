/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.SparseBranchSchedule
public import Complexity.Logics.Propositional.CNF.SparseParityCounter

/-!
# Section 6.3 compiled CNF parity-row schedule feasibility and domain-examination bounds

This module connects the compiled CNF parity-row systems and greedy model-counting reduction of
`Complexity.Logics.Propositional.CNF.SparseParityCounter` (Sections 6.1–6.3, Lemmas 6.1–6.2,
printed pp. 39–43 of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]) with the
per-branch schedule feasibility, `ReplacementDesign` existence, and domain-examination bounds of
`Complexity.Computability.Complexity.FineGrained.SparseBranchSchedule` (Section 5.5, Proof of
Theorem 2.2, printed pp. 38–39):

1. **Incidence, free-variable, and scope-width bounds for `CNF.parityRowSystem` (§6.3, p. 43)**:
   In Lemma 6.2 and Section 6.3, every candidate parity-row list `rows : List (Fin φ.length → Bool)`
   (as well as the final list `A (3 * n)`) has at most `6 * Fintype.card V` equations, giving
   equation-count ratio `6`, and row Hamming weight at most `W` (with `W = max D₀ P`). Theorem 2.2
   uses a sufficiently large `c = c(k)` to bound both the equation count and monomial sparsity.
   For any width-`≤ k` CNF
   `φ : CNF V`:
   - `CNF.totalIncidence_parityRowSystem_le_six_mul`: when `rows.length ≤ 6 * Fintype.card V` and
     `∀ r ∈ rows, weight r ≤ W`, total variable-equation incidence across `φ.parityRowSystem rows`
     is at most `(6 * (k * (W * 2 ^ k))) * Fintype.card V`.
   - `CNF.card_le_two_mul_freeVar_parityRowSystem`: when `1 ≤ b₀`, `2 ≤ s_div`, and
     `(6 * (k * (W * 2 ^ k))) * s_div ≤ b₀`, removing the heavy variables
     `S = heavyVars univ univ (fun j => equationScope (φ.parityRowSystem rows j)) b₀` leaves
     `Fintype.card V ≤ 2 * n'`, `Fintype.card V / 2 ≤ n'`, and at most
     `2 ^ (Fintype.card V / s_div)` branches in `branchAssignments S`.
   - `CNF.card_branchAugmentedScope_parityRowSystem_le`: every factor in
     `branchAugmentedScope S e univ (φ.parityRowSystem rows) b` has scope width at most
     `max (k * (W * 2 ^ k)) 1`.
2. **Per-branch and uniform `ReplacementDesign` existence and `(16 * k + 4)` domain-examination
   bounds for `CNF.parityRowSystem` (§6.3, p. 43)**:
   - `CNF.exists_branch_replacementDesign_parityRowSystem` and
     `CNF.exists_branch_schedule_parityRowSystem`: instantiate
     `Feasible.exists_branch_replacementDesign` and `exists_branch_schedule_replacementDesign`
     directly on `φ.parityRowSystem rows` with scope width bound `w = k * (W * 2 ^ k)`.
   - `CNF.branch_domainExaminationBound_parityRowSystem_le` and
     `CNF.sum_branch_domainExaminationBound_parityRowSystem_le`: specialize
     `Feasible.branch_domainExaminationBound_le` and `sum_branch_domainExaminationBound_le` at the
     Lemma 6.2 equation-count ratio `c = 6` (`rows.length ≤ 6 * Fintype.card V`), yielding the
     explicit single-branch examination bound
     `2 * numNodes n' * numGroups n' * exp (((16 * k + 4) : ℝ) * n' * rowCost β n')` (since
     `k * (2 * 6 + 4) + 4 = 16 * k + 4`) and the branch-summed bound
     `2 ^ (Fintype.card V / s_div) * (2 * numNodes n' * numGroups n' *`
     `exp (((16 * k + 4) : ℝ) * n' * rowCost β n'))`.
3. **End-to-end Lemma 6.1 + Lemma 6.2 + Section 6.3 greedy parity-test schedule theorems**:
   - `CNF.exists_greedy_parityRowSystem_branch_schedule`: combines
     `CNF.exists_initialTests_commonZeroCount_greedy` with
     `CNF.exists_branch_schedule_parityRowSystem`, establishing that at every greedy stage
     `i ≤ 3 * Fintype.card V` (with `W = max D₀ P`), `(A i).length ≤ 6 * Fintype.card V`, every
     branch of `φ.parityRowSystem (A i)` is `Feasible` and admits a concrete `ReplacementDesign` in
     the polylogarithmic regime, and at stage `3 * Fintype.card V`,
     `commonZeroCount univ (φ.parityRowSystem (A (3 * Fintype.card V))) =`
     `φ.modelCountOn Finset.univ`.
   - `CNF.initialRowWeightBound_le_mul_pow_clog`,
     `CNF.exists_branch_schedule_parityRowSystem_of_le_clog_pow`, and
     `CNF.exists_greedy_parityRowSystem_branch_schedule_of_le_clog_pow`: discharge the free-variable
     polylogarithmic schedule hypotheses `n₀ ≤ n'`, `b₀ + 1 ≤ (Nat.clog 2 n') ^ β`, and
     `max (k * (W * 2 ^ k)) 1 ≤ (Nat.clog 2 n') ^ β` unconditionally at the canonical Section 5.5 /
     Section 6.3 heavy-variable branching schedule `s_div = (Nat.clog 2 n).sqrt`,
     `b₀ = CNF.parityBranchThreshold k W n`, and `β = 2 * β_B + 5` whenever
     `B ≤ C_B * (Nat.clog 2 n) ^ β_B` and `N₀ ≤ n`.

## Main definitions

* `Cslib.Logic.PL.CNF.initialRowWeightCoeff`
* `Cslib.Logic.PL.CNF.parityBranchThreshold`
* `Cslib.Logic.PL.CNF.parityScheduleCoeff`

## Main results

* `Cslib.Logic.PL.CNF.totalIncidence_parityRowSystem_le_six_mul`
* `Cslib.Logic.PL.CNF.card_le_two_mul_freeVar_parityRowSystem`
* `Cslib.Logic.PL.CNF.card_branchAugmentedScope_parityRowSystem_le`
* `Cslib.Logic.PL.CNF.exists_branch_replacementDesign_parityRowSystem`
* `Cslib.Logic.PL.CNF.exists_branch_schedule_parityRowSystem`
* `Cslib.Logic.PL.CNF.branch_domainExaminationBound_parityRowSystem_le`
* `Cslib.Logic.PL.CNF.sum_branch_domainExaminationBound_parityRowSystem_le`
* `Cslib.Logic.PL.CNF.exists_greedy_parityRowSystem_branch_schedule`
* `Cslib.Logic.PL.CNF.initialRowWeightBound_le_mul_pow_clog`
* `Cslib.Logic.PL.CNF.exists_branch_schedule_parityRowSystem_of_le_clog_pow`
* `Cslib.Logic.PL.CNF.exists_greedy_parityRowSystem_branch_schedule_of_le_clog_pow`

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
  (Section 5.5, pp. 38–39; Sections 6.1–6.3, pp. 39–43)
-/

public section

namespace Cslib.Logic.PL

open Finset
open Cslib.BitString
open Cslib.LinearAlgebra
open Cslib.Complexity.SubexponentialSAT.ReplacementParams

variable {V : Type*} {n' : ℕ}

/-! ### 1. Incidence, free-variable, and scope-width bounds for `CNF.parityRowSystem` -/

/-- **Section 6.2 & 6.3 ($M \le 6 k W 2^k n$ for candidate parity-row systems):**
when every clause of `φ` has width at most `k`, every row in `rows` has Hamming weight at most `W`,
and `rows.length ≤ 6 * Fintype.card V`, the total variable-equation incidence of
`φ.parityRowSystem rows` is at most `(6 * (k * (W * 2 ^ k))) * Fintype.card V`. -/
theorem CNF.totalIncidence_parityRowSystem_le_six_mul [Fintype V] [DecidableEq V]
    {φ : CNF V} {k W : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    {rows : List (Fin φ.length → Bool)} (hW : ∀ r ∈ rows, weight r ≤ W)
    (hlen : rows.length ≤ 6 * Fintype.card V) :
    totalIncidence (univ : Finset (Fin rows.length))
        (fun j => equationScope (φ.parityRowSystem rows j)) ≤
      (6 * (k * (W * 2 ^ k))) * Fintype.card V := by
  calc totalIncidence (univ : Finset (Fin rows.length))
        (fun j => equationScope (φ.parityRowSystem rows j))
      ≤ (k * (W * 2 ^ k)) * rows.length := CNF.totalIncidence_parityRowSystem_le hk hW
    _ ≤ (k * (W * 2 ^ k)) * (6 * Fintype.card V) := Nat.mul_le_mul_left _ hlen
    _ = (6 * (k * (W * 2 ^ k))) * Fintype.card V := by ring

/-- **Section 5.5 & 6.3 ($n \le 2n'$ and branch count $\le 2^{n / s}$ for `CNF.parityRowSystem`):**
when `∀ c ∈ φ, c.length ≤ k`, `∀ r ∈ rows, weight r ≤ W`, `rows.length ≤ 6 * Fintype.card V`,
`1 ≤ b₀`, `2 ≤ s_div`, and `(6 * (k * (W * 2 ^ k))) * s_div ≤ b₀`, removing the heavy variables
`S = heavyVars univ univ (fun j => equationScope (φ.parityRowSystem rows j)) b₀` leaves
`Fintype.card V ≤ 2 * n'`, `Fintype.card V / 2 ≤ n'`, and at most `2 ^ (Fintype.card V / s_div)`
branches in `branchAssignments S`. -/
theorem CNF.card_le_two_mul_freeVar_parityRowSystem [Fintype V] [DecidableEq V]
    {φ : CNF V} {k W b₀ s_div : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    {rows : List (Fin φ.length → Bool)} (hW : ∀ r ∈ rows, weight r ≤ W)
    (hlen : rows.length ≤ 6 * Fintype.card V)
    (hb₀ : 1 ≤ b₀) (hs_div : 2 ≤ s_div)
    (h_thresh : (6 * (k * (W * 2 ^ k))) * s_div ≤ b₀)
    (e : ↥(univ \ heavyVars univ (univ : Finset (Fin rows.length))
      (fun j => equationScope (φ.parityRowSystem rows j)) b₀) ≃ Fin n') :
    (Fintype.card V ≤ 2 * n' ∧ Fintype.card V / 2 ≤ n') ∧
    #(branchAssignments
        (heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀)) ≤
      2 ^ (Fintype.card V / s_div) := by
  have hM :
      totalIncidence (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) * s_div ≤
        b₀ * Fintype.card V := by
    calc totalIncidence (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) * s_div
        ≤ ((6 * (k * (W * 2 ^ k))) * Fintype.card V) * s_div :=
          Nat.mul_le_mul_right s_div (CNF.totalIncidence_parityRowSystem_le_six_mul hk hW hlen)
      _ = ((6 * (k * (W * 2 ^ k))) * s_div) * Fintype.card V := by ring
      _ ≤ b₀ * Fintype.card V := Nat.mul_le_mul_right _ h_thresh
  exact ⟨card_le_two_mul_freeVar_of_heavyVars univ
      (fun j => equationScope (φ.parityRowSystem rows j)) hb₀ hs_div hM e,
    card_branchAssignments_heavyVars_le_two_pow_div univ
      (fun j => equationScope (φ.parityRowSystem rows j)) hb₀ (by omega) hM⟩

/-- **Section 5.5 & 6.3 (per-factor scope width $\le \max(k W 2^k, 1)$ for `CNF.parityRowSystem`):**
when `∀ c ∈ φ, c.length ≤ k` and `∀ r ∈ rows, weight r ≤ W`, every factor `f` of
`branchAugmentedScope S e univ (φ.parityRowSystem rows) b` has scope cardinality at most
`max (k * (W * 2 ^ k)) 1`. -/
theorem CNF.card_branchAugmentedScope_parityRowSystem_le [Fintype V] [DecidableEq V]
    {φ : CNF V} {k W : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    {rows : List (Fin φ.length → Bool)} (hW : ∀ r ∈ rows, weight r ≤ W)
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n') (b : V → Bool)
    (f : {j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n') :
    #(branchAugmentedScope S e univ (φ.parityRowSystem rows) b f) ≤
      max (k * (W * 2 ^ k)) 1 :=
  card_branchAugmentedScope_le S e univ (φ.parityRowSystem rows) b
    (fun j _ => CNF.card_equationScope_parityRowSystem_le hk hW j) f

/-! ### 2. Per-branch and uniform `ReplacementDesign` and domain-examination bounds -/

/-- **Section 6.3 per-branch `ReplacementDesign` existence for `CNF.parityRowSystem`**:
Given a width-`≤ k` CNF `φ : CNF V`, a parity-row list `rows : List (Fin φ.length → Bool)` with
`∀ r ∈ rows, weight r ≤ W`,
`S = heavyVars univ univ (fun j => equationScope (φ.parityRowSystem rows j)) b₀`,
`e : ↥(univ \ S) ≃ Fin n'`, and
`hF : Feasible β n' (b₀ + 1) (max (k * (W * 2 ^ k)) 1)`
`(∑ f, #(branchAugmentedScope S e univ (φ.parityRowSystem rows) b f))`,
there exists a concrete Section 4 `ReplacementDesign` for
`branchAugmentedScope S e univ (φ.parityRowSystem rows) b` at the Lemma 4.8 schedule. -/
theorem CNF.exists_branch_replacementDesign_parityRowSystem [Fintype V] [DecidableEq V]
    {φ : CNF V} {β k W b₀ : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    {rows : List (Fin φ.length → Bool)} (hW : ∀ r ∈ rows, weight r ≤ W)
    (e : ↥(univ \ heavyVars univ (univ : Finset (Fin rows.length))
      (fun j => equationScope (φ.parityRowSystem rows j)) b₀) ≃ Fin n')
    (b : V → Bool)
    (hF : Feasible β n' (b₀ + 1) (max (k * (W * 2 ^ k)) 1)
      (∑ f : {j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
        #(branchAugmentedScope
          (heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
          e univ (φ.parityRowSystem rows) b f))) :
    Nonempty
      (ReplacementDesign
        (branchAugmentedScope
          (heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
          e univ (φ.parityRowSystem rows) b)
        (numNodes n') (numGroups n') (intervalStart β n') (rowBound β n') (tauRat n')) :=
  hF.exists_branch_replacementDesign univ univ (φ.parityRowSystem rows) (Subset.refl _) e b
    (fun j _ => CNF.card_equationScope_parityRowSystem_le hk hW j)

/-- **Uniform Section 6.3 schedule feasibility and `ReplacementDesign` existence for
`CNF.parityRowSystem`**:
For every `1 ≤ β`, there exists `n₀ ≥ 20` such that for any width-`≤ k` CNF `φ : CNF V` and
parity-row list `rows : List (Fin φ.length → Bool)` with `∀ r ∈ rows, weight r ≤ W`, whenever the
free-variable count `n'` after removing
`S = heavyVars univ univ (fun j => equationScope (φ.parityRowSystem rows j)) b₀` satisfies
`n₀ ≤ n'`, `b₀ + 1 ≤ (Nat.clog 2 n') ^ β`, and `max (k * (W * 2 ^ k)) 1 ≤ (Nat.clog 2 n') ^ β`,
**every** branch assignment `b : V → Bool` simultaneously satisfies `Feasible` and admits a
concrete `ReplacementDesign`. -/
theorem CNF.exists_branch_schedule_parityRowSystem {β : ℕ} (hβ : 1 ≤ β) :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        {φ : CNF V} ⦃n' k W b₀ : ℕ⦄,
        (∀ c ∈ φ, c.length ≤ k) →
        ∀ {rows : List (Fin φ.length → Bool)},
          (∀ r ∈ rows, weight r ≤ W) →
          ∀ (e : ↥(univ \ heavyVars univ (univ : Finset (Fin rows.length))
              (fun j => equationScope (φ.parityRowSystem rows j)) b₀) ≃ Fin n'),
            n₀ ≤ n' →
            b₀ + 1 ≤ Nat.clog 2 n' ^ β →
            max (k * (W * 2 ^ k)) 1 ≤ Nat.clog 2 n' ^ β →
            ∀ b : V → Bool,
              Feasible β n' (b₀ + 1) (max (k * (W * 2 ^ k)) 1)
                (∑ f : {j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                  #(branchAugmentedScope
                    (heavyVars univ (univ : Finset (Fin rows.length))
                      (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
                    e univ (φ.parityRowSystem rows) b f)) ∧
                Nonempty
                  (ReplacementDesign
                    (branchAugmentedScope
                      (heavyVars univ (univ : Finset (Fin rows.length))
                        (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
                      e univ (φ.parityRowSystem rows) b)
                    (numNodes n') (numGroups n') (intervalStart β n')
                    (rowBound β n') (tauRat n')) := by
  obtain ⟨n₀, hn₀20, hsched⟩ := exists_branch_schedule_replacementDesign hβ
  refine ⟨n₀, hn₀20,
    fun {V _ _ φ n' k W b₀} hk {rows} hW e hn' hb₀ hw_pow b => ?_⟩
  exact hsched univ univ (φ.parityRowSystem rows) (Subset.refl _) e hn' hb₀ hw_pow
    (fun j _ => CNF.card_equationScope_parityRowSystem_le hk hW j) b

/-- **Section 6.3 single-branch domain-examination bound for `CNF.parityRowSystem` ($c = 6$):**
For any parity-row list `rows : List (Fin φ.length → Bool)` with `rows.length ≤ 6 * Fintype.card V`
and `Fintype.card V ≤ 2 * n'`, and any branch `b` with `hF : Feasible β n' b_occ w_width M'` and
concrete schedule design `D`, at the Section 5.3 / 6.3 degree budget
`d = k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))` and canonical truncation order
`q = (d * rowBound β n') / numNodes n'`, the induced Section 3 counting design
`C := hF.toCountingDesign D s` satisfies
`(∑ t : Fin (numNodes n'), (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
  (2 * (#(C.measurementBox t) : ℝ) *
    ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ)))
  ≤ 2 * numNodes n' * numGroups n' * exp (((16 * k + 4 : ℕ) : ℝ) * n' * rowCost β n')`. -/
theorem CNF.branch_domainExaminationBound_parityRowSystem_le [Fintype V]
    {F_idx : Type*} [Fintype F_idx] {scope : F_idx → Finset (Fin n')}
    {φ : CNF V} {β b_occ w_width M' k : ℕ}
    (rows : List (Fin φ.length → Bool))
    (hF : Feasible β n' b_occ w_width M')
    (D : ReplacementDesign scope (numNodes n') (numGroups n') (intervalStart β n')
      (rowBound β n') (tauRat n'))
    (s : Finset F_idx) (hlen : rows.length ≤ 6 * Fintype.card V) (hn : Fintype.card V ≤ 2 * n') :
    let d := k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))
    let q := (d * rowBound β n') / numNodes n'
    let C := hF.toCountingDesign D s
    (∑ t : Fin (numNodes n'),
        (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
          (2 * (#(C.measurementBox t) : ℝ) *
            ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
      2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
        Real.exp (((16 * k + 4 : ℕ) : ℝ) * (n' : ℝ) * rowCost β n') ∧
    2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
        Real.exp (((16 * k + 4 : ℕ) : ℝ) * (n' : ℝ) * rowCost β n') ≤
      2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
        Real.exp (((16 * k + 4 : ℕ) : ℝ) * (n' : ℝ) *
          (1028 * ((β : ℝ) + 3) * (Nat.clog 2 (Nat.clog 2 n') : ℝ) ^ 2 /
            Real.sqrt (Nat.clog 2 n'))) := by
  intro d q C
  have hcard : #(univ : Finset (Fin rows.length)) ≤ 6 * Fintype.card V := by
    simpa only [card_univ, Fintype.card_fin] using hlen
  have hbound := hF.branch_domainExaminationBound_le (ι := V) (k := k) (c := 6)
    (univ : Finset (Fin rows.length)) D s hcard hn
  have h16 : k * (2 * 6 + 4) + 4 = 16 * k + 4 := by ring
  simpa only [card_univ, Fintype.card_fin, h16] using hbound

/-- **Section 6.3 multi-branch domain-examination bound across `branchAssignments` for
`CNF.parityRowSystem`**:
When `∀ c ∈ φ, c.length ≤ k`, `∀ r ∈ rows, weight r ≤ W`, `rows.length ≤ 6 * Fintype.card V`,
`1 ≤ b₀`, `2 ≤ s_div`, `(6 * (k * (W * 2 ^ k))) * s_div ≤ b₀`, and `e : ↥(univ \ S) ≃ Fin n'`,
the free-variable dimension satisfies `Fintype.card V ≤ 2 * n'`, and if each branch
`b ∈ branchAssignments S` has its real examination sum bounded via
`CNF.branch_domainExaminationBound_parityRowSystem_le`, then the sum of those examination bounds
across all `b ∈ branchAssignments S` is at most
`(2 : ℝ) ^ (Fintype.card V / s_div) * (2 * numNodes n' * numGroups n' *
  exp (((16 * k + 4 : ℕ) : ℝ) * n' * rowCost β n'))`. -/
theorem CNF.sum_branch_domainExaminationBound_parityRowSystem_le [Fintype V] [DecidableEq V]
    {φ : CNF V} {β k W b₀ s_div : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    {rows : List (Fin φ.length → Bool)} (hW : ∀ r ∈ rows, weight r ≤ W)
    (hlen : rows.length ≤ 6 * Fintype.card V)
    (hb₀ : 1 ≤ b₀) (hs_div : 2 ≤ s_div)
    (h_thresh : (6 * (k * (W * 2 ^ k))) * s_div ≤ b₀)
    (e : ↥(univ \ heavyVars univ (univ : Finset (Fin rows.length))
      (fun j => equationScope (φ.parityRowSystem rows j)) b₀) ≃ Fin n')
    (examSum : (V → Bool) → ℝ)
    (hexam : ∀ b ∈ branchAssignments
        (heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀),
      examSum b ≤
        2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
          Real.exp (((16 * k + 4 : ℕ) : ℝ) * (n' : ℝ) * rowCost β n')) :
    Fintype.card V ≤ 2 * n' ∧
    (∑ b ∈ branchAssignments
        (heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀),
        examSum b) ≤
      (2 : ℝ) ^ (Fintype.card V / s_div) *
        (2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
          Real.exp (((16 * k + 4 : ℕ) : ℝ) * (n' : ℝ) * rowCost β n')) := by
  have hM :
      totalIncidence (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) * s_div ≤
        b₀ * Fintype.card V := by
    calc totalIncidence (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) * s_div
        ≤ ((6 * (k * (W * 2 ^ k))) * Fintype.card V) * s_div :=
          Nat.mul_le_mul_right s_div (CNF.totalIncidence_parityRowSystem_le_six_mul hk hW hlen)
      _ = ((6 * (k * (W * 2 ^ k))) * s_div) * Fintype.card V := by ring
      _ ≤ b₀ * Fintype.card V := Nat.mul_le_mul_right _ h_thresh
  have h16 : k * (2 * 6 + 4) + 4 = 16 * k + 4 := by ring
  simpa only [h16] using
    sum_branch_domainExaminationBound_le (β := β) (k := k) (c := 6)
      (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) hb₀ hs_div hM e examSum
      (by simpa only [h16] using hexam)

/-! ### 3. End-to-end Lemma 6.1 + Lemma 6.2 + Section 6.3 greedy parity-test schedule theorem -/

private theorem greedyRowListLength_le_initialRowWeightBound (B m : ℕ) :
    greedyRowListLength B m ≤ initialRowWeightBound B m := by
  unfold greedyRowListLength initialRowWeightBound
  have h1 : 20000 * B ^ 2 ≤ 320000 * B ^ 2 := Nat.mul_le_mul_right _ (by decide)
  have h2 : (Nat.log 2 m + 1) ^ 2 ≤ (Nat.log 2 m + 1) ^ 3 :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  exact Nat.mul_le_mul h1 h2

private theorem max_initialRowWeightBound_greedyRowListLength (B m : ℕ) :
    max (initialRowWeightBound B m) (greedyRowListLength B m) =
      initialRowWeightBound B m :=
  max_eq_left (greedyRowListLength_le_initialRowWeightBound B m)

/-- **Lemmas 6.1–6.2 & Section 6.3 (greedy parity-row selection with uniform per-branch
`Feasible` and `ReplacementDesign` guarantees at every stage `i ≤ 3 * n`)**:
For any `1 ≤ β`, there exists `n₀ ≥ 20` such that for any width-`≤ k` CNF `φ : CNF V` on
`n = Fintype.card V ≥ 1` variables with `φ.length ≤ B * n` (`1 ≤ B`), there exist initial parity
rows `A₀` (`A₀.length ≤ 3 * n`, each of weight at most `D₀ = initialRowWeightBound B φ.length`)
such that for any `3 * n`-step greedy sequence `A (i + 1) = A i ++ [testRow (γ i)]` with `A 0 = A₀`
minimizing `commonZeroCount` over candidate rows of list length
`P = greedyRowListLength B φ.length`:
1. After `3 * n` rounds,
   `commonZeroCount univ (φ.parityRowSystem (A (3 * n))) = φ.modelCountOn Finset.univ`.
2. At every stage `i ≤ 3 * n`, `(A i).length ≤ 6 * n`, and whenever the free-variable count `n'`
   after removing
   `S_i = heavyVars univ univ (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀` satisfies
   `n₀ ≤ n'`, `b₀ + 1 ≤ (Nat.clog 2 n') ^ β`, and
   `max (k * (max D₀ P * 2 ^ k)) 1 ≤ (Nat.clog 2 n') ^ β`, every branch `b : V → Bool` of
   `φ.parityRowSystem (A i)` satisfies
   `Feasible β n' (b₀ + 1) (max (k * (max D₀ P * 2 ^ k)) 1) M'_b`
   and admits a concrete `ReplacementDesign`. -/
theorem CNF.exists_greedy_parityRowSystem_branch_schedule {β : ℕ} (hβ : 1 ≤ β) :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (φ : CNF V) {k B : ℕ},
        (∀ c ∈ φ, c.length ≤ k) →
        1 ≤ Fintype.card V →
        1 ≤ B →
        φ.length ≤ B * Fintype.card V →
        let D₀ := initialRowWeightBound B φ.length
        let P := greedyRowListLength B φ.length
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
              ∀ ⦃n' b₀ : ℕ⦄
                (e : ↥(univ \ heavyVars univ (univ : Finset (Fin (A i).length))
                  (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀) ≃ Fin n'),
                n₀ ≤ n' →
                b₀ + 1 ≤ Nat.clog 2 n' ^ β →
                max (k * (max D₀ P * 2 ^ k)) 1 ≤ Nat.clog 2 n' ^ β →
                ∀ b : V → Bool,
                  Feasible β n' (b₀ + 1) (max (k * (max D₀ P * 2 ^ k)) 1)
                    (∑ f : {j : Fin (A i).length //
                        j ∈ (univ : Finset (Fin (A i).length))} ⊕ Fin n',
                      #(branchAugmentedScope
                        (heavyVars univ (univ : Finset (Fin (A i).length))
                          (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀)
                        e univ (φ.parityRowSystem (A i)) b f)) ∧
                    Nonempty
                      (ReplacementDesign
                        (branchAugmentedScope
                          (heavyVars univ (univ : Finset (Fin (A i).length))
                            (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀)
                          e univ (φ.parityRowSystem (A i)) b)
                        (numNodes n') (numGroups n') (intervalStart β n')
                        (rowBound β n') (tauRat n')) := by
  obtain ⟨n₀, hn₀20, hsched⟩ := exists_branch_schedule_replacementDesign hβ
  refine ⟨n₀, hn₀20, fun {V _ _} φ {k B} hk hn hB hm => ?_⟩
  intro D₀ P
  obtain ⟨A₀, hlen0, hw0, hgreedy⟩ := φ.exists_initialTests_commonZeroCount_greedy hk hn hB hm
  refine ⟨A₀, hlen0, hw0, fun A γ h0 hA hγ => ?_⟩
  obtain ⟨hcount, hstage⟩ := hgreedy A γ h0 hA hγ
  refine ⟨hcount, fun i hi => ?_⟩
  obtain ⟨hlen_i, hscope_i⟩ := hstage i hi
  refine ⟨hlen_i, fun {n' b₀} e hn' hb₀ hw_pow b => ?_⟩
  exact hsched univ univ (φ.parityRowSystem (A i)) (Subset.refl _) e hn' hb₀ hw_pow
    (fun j _ => (hscope_i j).2.2) b

/-! ### 4. Unconditional polylogarithmic schedule discharge for `B ≤ C_B * (Nat.clog 2 n) ^ β_B` -/

/-- When `n ≤ 2 * n'` and `2 ≤ n'`, `Nat.clog 2 n ≤ 2 * Nat.clog 2 n'`. -/
theorem clog_two_le_two_mul_of_le_two_mul {n n' : ℕ} (hn : n ≤ 2 * n') (hn' : 2 ≤ n') :
    Nat.clog 2 n ≤ 2 * Nat.clog 2 n' := by
  have h1 : 1 ≤ Nat.clog 2 n' :=
    (Nat.lt_clog_iff_pow_lt one_lt_two).mpr (by omega : 2 ^ 0 < n')
  have h2 : n ≤ 2 ^ (Nat.clog 2 n' + 1) := by
    calc n ≤ 2 * n' := hn
      _ ≤ 2 * 2 ^ Nat.clog 2 n' := Nat.mul_le_mul_left 2 (Nat.le_pow_clog one_lt_two n')
      _ = 2 ^ (Nat.clog 2 n' + 1) := (pow_succ' 2 _).symm
  have h3 : Nat.clog 2 n ≤ Nat.clog 2 n' + 1 :=
    (Nat.clog_le_iff_le_pow one_lt_two).mpr h2
  omega

/-- Coefficient for the polynomial bound on `initialRowWeightBound B m` when
`B ≤ C_B * (Nat.clog 2 n) ^ β_B` and `m ≤ B * n`. -/
def CNF.initialRowWeightCoeff (C_B β_B : ℕ) : ℕ :=
  320000 * C_B ^ 2 * (C_B + β_B + 2) ^ 3

/-- **Section 6.1 & 6.3 ($D_0 \le C \cdot (\lceil \log_2 n \rceil)^{2\beta_B + 3}$):**
when `2 ≤ n`, `m ≤ B * n`, and `B ≤ C_B * (Nat.clog 2 n) ^ β_B`, the initial parity-row weight bound
`initialRowWeightBound B m` is at most
`CNF.initialRowWeightCoeff C_B β_B * (Nat.clog 2 n) ^ (2 * β_B + 3)`. -/
theorem CNF.initialRowWeightBound_le_mul_pow_clog {n m B C_B β_B : ℕ}
    (hn : 2 ≤ n) (hm : m ≤ B * n) (hB : B ≤ C_B * Nat.clog 2 n ^ β_B) :
    initialRowWeightBound B m ≤
      CNF.initialRowWeightCoeff C_B β_B * Nat.clog 2 n ^ (2 * β_B + 3) := by
  set lam := Nat.clog 2 n
  have hlam1 : 1 ≤ lam :=
    (Nat.lt_clog_iff_pow_lt one_lt_two).mpr (by omega : 2 ^ 0 < n)
  have hn_pow : n ≤ 2 ^ lam := Nat.le_pow_clog one_lt_two n
  have hlam_pow : lam ^ β_B ≤ 2 ^ (lam * β_B) := by
    calc lam ^ β_B ≤ (2 ^ lam) ^ β_B := Nat.pow_le_pow_left lam.lt_two_pow_self.le β_B
      _ = 2 ^ (lam * β_B) := (pow_mul 2 lam β_B).symm
  have hCB_pow : C_B ≤ 2 ^ (C_B * lam) := by
    calc C_B ≤ 2 ^ C_B := C_B.lt_two_pow_self.le
      _ ≤ 2 ^ (C_B * lam) := Nat.pow_le_pow_right two_pos (Nat.le_mul_of_pos_right C_B hlam1)
  have hm_pow : m ≤ 2 ^ ((C_B + β_B + 1) * lam) := by
    calc m ≤ B * n := hm
      _ ≤ C_B * lam ^ β_B * n := Nat.mul_le_mul_right n hB
      _ ≤ 2 ^ (C_B * lam) * 2 ^ (lam * β_B) * 2 ^ lam :=
          Nat.mul_le_mul (Nat.mul_le_mul hCB_pow hlam_pow) hn_pow
      _ = 2 ^ ((C_B + β_B + 1) * lam) := by rw [← pow_add, ← pow_add]; ring_nf
  have hlog : Nat.log 2 m + 1 ≤ (C_B + β_B + 2) * lam := by
    have hlog_le : Nat.log 2 m ≤ (C_B + β_B + 1) * lam := by
      calc Nat.log 2 m ≤ Nat.log 2 (2 ^ ((C_B + β_B + 1) * lam)) := Nat.log_mono_right hm_pow
        _ = (C_B + β_B + 1) * lam := Nat.log_pow one_lt_two _
    nlinarith
  have hB2 : B ^ 2 ≤ C_B ^ 2 * lam ^ (2 * β_B) := by
    calc B ^ 2 ≤ (C_B * lam ^ β_B) ^ 2 := Nat.pow_le_pow_left hB 2
      _ = C_B ^ 2 * lam ^ (2 * β_B) := by rw [mul_pow, ← pow_mul]; ring
  have hlog3 : (Nat.log 2 m + 1) ^ 3 ≤ (C_B + β_B + 2) ^ 3 * lam ^ 3 := by
    calc (Nat.log 2 m + 1) ^ 3 ≤ ((C_B + β_B + 2) * lam) ^ 3 := Nat.pow_le_pow_left hlog 3
      _ = (C_B + β_B + 2) ^ 3 * lam ^ 3 := mul_pow _ _ 3
  unfold initialRowWeightBound CNF.initialRowWeightCoeff
  calc 320000 * B ^ 2 * (Nat.log 2 m + 1) ^ 3
      ≤ 320000 * (C_B ^ 2 * lam ^ (2 * β_B)) * ((C_B + β_B + 2) ^ 3 * lam ^ 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 320000 hB2) hlog3
    _ = 320000 * C_B ^ 2 * (C_B + β_B + 2) ^ 3 * lam ^ (2 * β_B + 3) := by
        rw [pow_add]; ring

/-- Canonical Section 5.5 & 6.3 heavy-variable branching threshold
`b₀ = (6 * (k * (W * 2 ^ k))) * (Nat.clog 2 n).sqrt + 1` for a width-`≤ k` CNF with row-weight
bound `W` on `n` variables. -/
def CNF.parityBranchThreshold (k W n : ℕ) : ℕ :=
  (6 * (k * (W * 2 ^ k))) * (Nat.clog 2 n).sqrt + 1

/-- Schedule coefficient bounding `CNF.parityBranchThreshold k W n + 1` and
`max (k * (W * 2 ^ k)) 1` against `(Nat.clog 2 n') ^ (2 * β_B + 4)` when `n ≤ 2 * n'`. -/
def CNF.parityScheduleCoeff (k C_B β_B : ℕ) : ℕ :=
  (6 * k * 2 ^ k * CNF.initialRowWeightCoeff C_B β_B + 2) * 2 ^ (2 * β_B + 4)

private theorem parityBranchThreshold_succ_and_width_le_clog_pow {n n' m B W k C_B β_B : ℕ}
    (hn : 2 ≤ n) (hn_le : n ≤ 2 * n') (hn' : 2 ≤ n')
    (hm : m ≤ B * n) (hB : B ≤ C_B * Nat.clog 2 n ^ β_B)
    (hW : W ≤ initialRowWeightBound B m)
    (hcoeff : CNF.parityScheduleCoeff k C_B β_B ≤ Nat.clog 2 n') :
    CNF.parityBranchThreshold k W n + 1 ≤ Nat.clog 2 n' ^ (2 * β_B + 5) ∧
    max (k * (W * 2 ^ k)) 1 ≤ Nat.clog 2 n' ^ (2 * β_B + 5) := by
  set lam := Nat.clog 2 n
  set lam' := Nat.clog 2 n'
  have hlam1 : 1 ≤ lam :=
    (Nat.lt_clog_iff_pow_lt one_lt_two).mpr (by omega : 2 ^ 0 < n)
  have hsqrt1 : 1 ≤ lam.sqrt := Nat.le_sqrt.mpr (by omega)
  have hmax_le : max (k * (W * 2 ^ k)) 1 ≤ CNF.parityBranchThreshold k W n + 1 := by
    unfold CNF.parityBranchThreshold
    have hmul : k * (W * 2 ^ k) ≤ (6 * (k * (W * 2 ^ k))) * (Nat.clog 2 n).sqrt := by
      calc k * (W * 2 ^ k) = (k * (W * 2 ^ k)) * 1 := (mul_one _).symm
        _ ≤ (6 * (k * (W * 2 ^ k))) * (Nat.clog 2 n).sqrt :=
            Nat.mul_le_mul (Nat.le_mul_of_pos_left _ (by decide)) hsqrt1
    omega
  have hW_le : W ≤ CNF.initialRowWeightCoeff C_B β_B * lam ^ (2 * β_B + 3) :=
    hW.trans (CNF.initialRowWeightBound_le_mul_pow_clog hn hm hB)
  have hterm :
      (6 * (k * (W * 2 ^ k))) * lam.sqrt ≤
        (6 * k * 2 ^ k * CNF.initialRowWeightCoeff C_B β_B) * lam ^ (2 * β_B + 4) := by
    calc (6 * (k * (W * 2 ^ k))) * lam.sqrt
        = (6 * k * 2 ^ k) * W * lam.sqrt := by ring
      _ ≤ (6 * k * 2 ^ k) * (CNF.initialRowWeightCoeff C_B β_B * lam ^ (2 * β_B + 3)) * lam :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hW_le) (Nat.sqrt_le_self lam)
      _ = (6 * k * 2 ^ k * CNF.initialRowWeightCoeff C_B β_B) * lam ^ (2 * β_B + 4) := by
          rw [pow_succ]; ring
  have h1_pow : 1 ≤ lam ^ (2 * β_B + 4) := Nat.one_le_pow _ lam hlam1
  have hthresh_lam :
      CNF.parityBranchThreshold k W n + 1 ≤
        (6 * k * 2 ^ k * CNF.initialRowWeightCoeff C_B β_B + 2) * lam ^ (2 * β_B + 4) := by
    unfold CNF.parityBranchThreshold
    calc (6 * (k * (W * 2 ^ k))) * lam.sqrt + 1 + 1
        ≤ (6 * k * 2 ^ k * CNF.initialRowWeightCoeff C_B β_B) * lam ^ (2 * β_B + 4) +
            2 * lam ^ (2 * β_B + 4) := by linarith
      _ = (6 * k * 2 ^ k * CNF.initialRowWeightCoeff C_B β_B + 2) * lam ^ (2 * β_B + 4) := by
          ring
  have hlam_pow : lam ^ (2 * β_B + 4) ≤ 2 ^ (2 * β_B + 4) * lam' ^ (2 * β_B + 4) := by
    calc lam ^ (2 * β_B + 4) ≤ (2 * lam') ^ (2 * β_B + 4) :=
          Nat.pow_le_pow_left (clog_two_le_two_mul_of_le_two_mul hn_le hn') _
      _ = 2 ^ (2 * β_B + 4) * lam' ^ (2 * β_B + 4) := mul_pow 2 lam' _
  have hthresh_lam' :
      CNF.parityBranchThreshold k W n + 1 ≤ Nat.clog 2 n' ^ (2 * β_B + 5) := by
    calc CNF.parityBranchThreshold k W n + 1
        ≤ (6 * k * 2 ^ k * CNF.initialRowWeightCoeff C_B β_B + 2) *
            (2 ^ (2 * β_B + 4) * lam' ^ (2 * β_B + 4)) :=
          hthresh_lam.trans (Nat.mul_le_mul_left _ hlam_pow)
      _ = CNF.parityScheduleCoeff k C_B β_B * lam' ^ (2 * β_B + 4) := by
          unfold CNF.parityScheduleCoeff; ring
      _ ≤ lam' * lam' ^ (2 * β_B + 4) := Nat.mul_le_mul_right _ hcoeff
      _ = lam' ^ (2 * β_B + 5) := (pow_succ' lam' (2 * β_B + 4)).symm
  exact ⟨hthresh_lam', hmax_le.trans hthresh_lam'⟩

/-- **Unconditional Section 6.3 branch-schedule feasibility and `ReplacementDesign` existence for
`CNF.parityRowSystem` with `B ≤ C_B * (Nat.clog 2 n) ^ β_B`**:
For any `k C_B β_B : ℕ`, there exists an explicit threshold `N₀ ≥ 20` such that for any width-`≤ k`
CNF `φ : CNF V` with `N₀ ≤ Fintype.card V`, `φ.length ≤ B * Fintype.card V`, and
`B ≤ C_B * (Nat.clog 2 (Fintype.card V)) ^ β_B`, and any parity-row list
`rows : List (Fin φ.length → Bool)` with `rows.length ≤ 6 * Fintype.card V`,
`∀ r ∈ rows, weight r ≤ W`, and `W ≤ initialRowWeightBound B φ.length`, at the canonical
threshold `b₀ = CNF.parityBranchThreshold k W (Fintype.card V)` and exponent `β = 2 * β_B + 5`:
1. `2 ≤ (Nat.clog 2 (Fintype.card V)).sqrt`,
2. `Fintype.card V ≤ 2 * n'` and `Fintype.card V / 2 ≤ n'`,
3. `#(branchAssignments S) ≤ 2 ^ (Fintype.card V / (Nat.clog 2 (Fintype.card V)).sqrt)`, and
4. **every** branch `b : V → Bool` unconditionally satisfies `Feasible (2 * β_B + 5) n' (b₀ + 1)`
   `(max (k * (W * 2 ^ k)) 1) M'_b` and admits a concrete `ReplacementDesign`. -/
theorem CNF.exists_branch_schedule_parityRowSystem_of_le_clog_pow (k C_B β_B : ℕ) :
    ∃ N₀ : ℕ, 20 ≤ N₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        {φ : CNF V} ⦃n' B W : ℕ⦄,
        (∀ c ∈ φ, c.length ≤ k) →
        N₀ ≤ Fintype.card V →
        φ.length ≤ B * Fintype.card V →
        B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B →
        W ≤ initialRowWeightBound B φ.length →
        ∀ {rows : List (Fin φ.length → Bool)},
          (∀ r ∈ rows, weight r ≤ W) →
          rows.length ≤ 6 * Fintype.card V →
          let b₀ := CNF.parityBranchThreshold k W (Fintype.card V)
          ∀ (e : ↥(univ \ heavyVars univ (univ : Finset (Fin rows.length))
              (fun j => equationScope (φ.parityRowSystem rows j)) b₀) ≃ Fin n'),
            2 ≤ (Nat.clog 2 (Fintype.card V)).sqrt ∧
            (Fintype.card V ≤ 2 * n' ∧ Fintype.card V / 2 ≤ n') ∧
            #(branchAssignments
                (heavyVars univ (univ : Finset (Fin rows.length))
                  (fun j => equationScope (φ.parityRowSystem rows j)) b₀)) ≤
              2 ^ (Fintype.card V / (Nat.clog 2 (Fintype.card V)).sqrt) ∧
            ∀ b : V → Bool,
              Feasible (2 * β_B + 5) n' (b₀ + 1) (max (k * (W * 2 ^ k)) 1)
                (∑ f : {j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                  #(branchAugmentedScope
                    (heavyVars univ (univ : Finset (Fin rows.length))
                      (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
                    e univ (φ.parityRowSystem rows) b f)) ∧
                Nonempty
                  (ReplacementDesign
                    (branchAugmentedScope
                      (heavyVars univ (univ : Finset (Fin rows.length))
                        (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
                      e univ (φ.parityRowSystem rows) b)
                    (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
                    (rowBound (2 * β_B + 5) n') (tauRat n')) := by
  obtain ⟨n₀, hn₀20, hsched⟩ :=
    CNF.exists_branch_schedule_parityRowSystem (β := 2 * β_B + 5) (by omega)
  set C := CNF.parityScheduleCoeff k C_B β_B
  refine ⟨max (2 * n₀) (2 ^ (C + 1)), by omega,
    fun {V _ _ φ n' B W} hk hN₀ hm hB hW_bound {rows} hW hlen => ?_⟩
  intro b₀ e
  have hn20 : 20 ≤ Fintype.card V := by
    have : 2 * n₀ ≤ Fintype.card V := (le_max_left _ _).trans hN₀
    omega
  have hsqrt : 2 ≤ (Nat.clog 2 (Fintype.card V)).sqrt := by
    refine Nat.le_sqrt.mpr ?_
    have h4 : 2 ^ 3 < Fintype.card V := by omega
    have hclog : 3 < Nat.clog 2 (Fintype.card V) := (Nat.lt_clog_iff_pow_lt one_lt_two).mpr h4
    omega
  have hb₀_pos : 1 ≤ b₀ := Nat.succ_pos _
  have hthresh : (6 * (k * (W * 2 ^ k))) * (Nat.clog 2 (Fintype.card V)).sqrt ≤ b₀ :=
    Nat.le_succ _
  obtain ⟨⟨hn_le, hn_div⟩, hbranches⟩ :=
    CNF.card_le_two_mul_freeVar_parityRowSystem hk hW hlen hb₀_pos hsqrt hthresh e
  have hn₀_le : n₀ ≤ n' := by
    have : 2 * n₀ ≤ Fintype.card V := (le_max_left _ _).trans hN₀
    omega
  have hcoeff : C ≤ Nat.clog 2 n' := by
    have hpow : 2 ^ (C + 1) ≤ 2 * n' := ((le_max_right _ _).trans hN₀).trans hn_le
    have hpow' : 2 ^ C ≤ n' := by rw [pow_succ'] at hpow; omega
    exact (Nat.clog_pow 2 C one_lt_two).symm.le.trans (Nat.clog_mono_right 2 hpow')
  obtain ⟨hb₀_pow, hw_pow⟩ :=
    parityBranchThreshold_succ_and_width_le_clog_pow (by omega) hn_le (by omega) hm hB hW_bound
      hcoeff
  exact ⟨hsqrt, ⟨hn_le, hn_div⟩, hbranches,
    fun b => hsched hk hW e hn₀_le hb₀_pow hw_pow b⟩

/-- **Unconditional Section 6.3 greedy parity-test schedule theorem for
`B ≤ C_B * (Nat.clog 2 n) ^ β_B`**:
For any `k C_B β_B : ℕ`, there exists `N₀ ≥ 20` such that for any width-`≤ k` CNF `φ : CNF V` with
`N₀ ≤ Fintype.card V`, `1 ≤ B ≤ C_B * (Nat.clog 2 (Fintype.card V)) ^ β_B`, and
`φ.length ≤ B * Fintype.card V`, there exist initial parity rows `A₀` (`A₀.length ≤ 3 * n`, each of
weight at most `D₀ = initialRowWeightBound B φ.length`) such that for any `3 * n`-step greedy
sequence `A (i + 1) = A i ++ [testRow (γ i)]` with `A 0 = A₀` minimizing `commonZeroCount`:
1. `commonZeroCount univ (φ.parityRowSystem (A (3 * Fintype.card V))) = φ.modelCountOn Finset.univ`.
2. At every stage `i ≤ 3 * Fintype.card V`, `(A i).length ≤ 6 * Fintype.card V`, and at the
   canonical threshold `b₀ = CNF.parityBranchThreshold k D₀ (Fintype.card V)`:
   - `Fintype.card V ≤ 2 * n'` and `Fintype.card V / 2 ≤ n'`,
   - `#(branchAssignments S_i) ≤ 2 ^ (Fintype.card V / (Nat.clog 2 (Fintype.card V)).sqrt)`, and
   - **every** branch `b : V → Bool` unconditionally satisfies
     `Feasible (2 * β_B + 5) n' (b₀ + 1) (max (k * (D₀ * 2 ^ k)) 1) M'_b` and admits a concrete
     `ReplacementDesign`. -/
theorem CNF.exists_greedy_parityRowSystem_branch_schedule_of_le_clog_pow (k C_B β_B : ℕ) :
    ∃ N₀ : ℕ, 20 ≤ N₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (φ : CNF V) {B : ℕ},
        (∀ c ∈ φ, c.length ≤ k) →
        N₀ ≤ Fintype.card V →
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
              ∀ ⦃n' : ℕ⦄
                (e : ↥(univ \ heavyVars univ (univ : Finset (Fin (A i).length))
                  (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀) ≃ Fin n'),
                (Fintype.card V ≤ 2 * n' ∧ Fintype.card V / 2 ≤ n') ∧
                #(branchAssignments
                    (heavyVars univ (univ : Finset (Fin (A i).length))
                      (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀)) ≤
                  2 ^ (Fintype.card V / (Nat.clog 2 (Fintype.card V)).sqrt) ∧
                ∀ b : V → Bool,
                  Feasible (2 * β_B + 5) n' (b₀ + 1) (max (k * (D₀ * 2 ^ k)) 1)
                    (∑ f : {j : Fin (A i).length //
                        j ∈ (univ : Finset (Fin (A i).length))} ⊕ Fin n',
                      #(branchAugmentedScope
                        (heavyVars univ (univ : Finset (Fin (A i).length))
                          (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀)
                        e univ (φ.parityRowSystem (A i)) b f)) ∧
                    Nonempty
                      (ReplacementDesign
                        (branchAugmentedScope
                          (heavyVars univ (univ : Finset (Fin (A i).length))
                            (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀)
                          e univ (φ.parityRowSystem (A i)) b)
                        (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
                        (rowBound (2 * β_B + 5) n') (tauRat n')) := by
  obtain ⟨n₀, hn₀20, hsched⟩ :=
    exists_branch_schedule_replacementDesign (β := 2 * β_B + 5) (by omega)
  set C := CNF.parityScheduleCoeff k C_B β_B
  refine ⟨max (2 * n₀) (2 ^ (C + 1)), by omega,
    fun {V _ _} φ {B} hk hN₀ hB1 hB_le hm => ?_⟩
  intro D₀ P b₀
  obtain ⟨A₀, hlen0, hw0, hgreedy⟩ :=
    φ.exists_initialTests_commonZeroCount_greedy hk (by omega) hB1 hm
  refine ⟨A₀, hlen0, hw0, fun A γ h0 hA hγ => ?_⟩
  obtain ⟨hcount, hstage⟩ := hgreedy A γ h0 hA hγ
  refine ⟨hcount, fun i hi => ?_⟩
  obtain ⟨hlen_i, hscope_i⟩ := hstage i hi
  refine ⟨hlen_i, fun {n'} e => ?_⟩
  have hscope_D₀ : ∀ j : Fin (A i).length,
      #(equationScope (φ.parityRowSystem (A i) j)) ≤ k * (D₀ * 2 ^ k) := fun j => by
    simpa only [D₀, P, max_initialRowWeightBound_greedyRowListLength] using (hscope_i j).2.2
  have hn20 : 20 ≤ Fintype.card V := by
    have : 2 * n₀ ≤ Fintype.card V := (le_max_left _ _).trans hN₀
    omega
  have hsqrt : 2 ≤ (Nat.clog 2 (Fintype.card V)).sqrt := by
    refine Nat.le_sqrt.mpr ?_
    have h4 : 2 ^ 3 < Fintype.card V := by omega
    have hclog : 3 < Nat.clog 2 (Fintype.card V) := (Nat.lt_clog_iff_pow_lt one_lt_two).mpr h4
    omega
  have hM_le :
      totalIncidence (univ : Finset (Fin (A i).length))
          (fun j => equationScope (φ.parityRowSystem (A i) j)) *
        (Nat.clog 2 (Fintype.card V)).sqrt ≤
      b₀ * Fintype.card V := by
    have htot :
        totalIncidence (univ : Finset (Fin (A i).length))
            (fun j => equationScope (φ.parityRowSystem (A i) j)) ≤
          (6 * (k * (D₀ * 2 ^ k))) * Fintype.card V := by
      calc totalIncidence (univ : Finset (Fin (A i).length))
              (fun j => equationScope (φ.parityRowSystem (A i) j))
          ≤ ∑ _j ∈ (univ : Finset (Fin (A i).length)), (k * (D₀ * 2 ^ k)) :=
            sum_le_sum fun j _ => hscope_D₀ j
        _ = (A i).length * (k * (D₀ * 2 ^ k)) := by
            simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
        _ ≤ (6 * Fintype.card V) * (k * (D₀ * 2 ^ k)) := Nat.mul_le_mul_right _ hlen_i
        _ = (6 * (k * (D₀ * 2 ^ k))) * Fintype.card V := by ring
    calc totalIncidence (univ : Finset (Fin (A i).length))
            (fun j => equationScope (φ.parityRowSystem (A i) j)) *
          (Nat.clog 2 (Fintype.card V)).sqrt
        ≤ ((6 * (k * (D₀ * 2 ^ k))) * Fintype.card V) *
            (Nat.clog 2 (Fintype.card V)).sqrt := Nat.mul_le_mul_right _ htot
      _ = ((6 * (k * (D₀ * 2 ^ k))) * (Nat.clog 2 (Fintype.card V)).sqrt) *
            Fintype.card V := by ring
      _ ≤ b₀ * Fintype.card V := Nat.mul_le_mul_right _ (Nat.le_succ _)
  have hb₀_pos : 1 ≤ b₀ := Nat.succ_pos _
  have hcard : Fintype.card V ≤ 2 * n' ∧ Fintype.card V / 2 ≤ n' :=
    card_le_two_mul_freeVar_of_heavyVars univ
      (fun j => equationScope (φ.parityRowSystem (A i) j)) hb₀_pos hsqrt hM_le e
  have hbr :
      #(branchAssignments
          (heavyVars univ (univ : Finset (Fin (A i).length))
            (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀)) ≤
        2 ^ (Fintype.card V / (Nat.clog 2 (Fintype.card V)).sqrt) :=
    card_branchAssignments_heavyVars_le_two_pow_div univ
      (fun j => equationScope (φ.parityRowSystem (A i) j)) hb₀_pos (by omega) hM_le
  have hn₀_le : n₀ ≤ n' := by
    have : 2 * n₀ ≤ Fintype.card V := (le_max_left _ _).trans hN₀
    omega
  have hcoeff : C ≤ Nat.clog 2 n' := by
    have hpow : 2 ^ (C + 1) ≤ 2 * n' := ((le_max_right _ _).trans hN₀).trans hcard.1
    have hpow' : 2 ^ C ≤ n' := by rw [pow_succ'] at hpow; omega
    exact (Nat.clog_pow 2 C one_lt_two).symm.le.trans (Nat.clog_mono_right 2 hpow')
  obtain ⟨hb₀_pow, hw_pow⟩ :=
    parityBranchThreshold_succ_and_width_le_clog_pow (by omega) hcard.1 (by omega) hm hB_le
      le_rfl hcoeff
  refine ⟨hcard, hbr, fun b => ?_⟩
  exact hsched univ univ (φ.parityRowSystem (A i)) (Subset.refl _) e hn₀_le hb₀_pow hw_pow
    (fun j _ => hscope_D₀ j) b

end Cslib.Logic.PL
