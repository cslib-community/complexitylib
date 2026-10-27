/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.ReplacementScheduleDesign
public import Complexity.Logics.Propositional.CNF.SparseDesignCounter

/-!
# Section 6.3 Lemma 4.8 schedule instantiation for compiled CNF sparse parity-design counters

This module bridges the compiled CNF sparse parity-design counter of
`Complexity.Logics.Propositional.CNF.SparseDesignCounter` (Sections 5.4–5.5 and 6.1–6.3 of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]) with the concrete Lemma 4.7 /
Lemma 4.8 parameter schedule `(numNodes n', numGroups n', intervalStart β n', rowBound β n',
tauRat n')` and Proposition 3.4 domain-examination bounds of
`Complexity.Computability.Complexity.FineGrained.ReplacementScheduleDesign` (Sections 3.5 and
4.6–4.7):

1. **Per-branch and uniform Lemma 4.7 + Lemma 4.8 `ReplacementDesign` existence on
   `CNF.branchParityRowNeutralScope` (§5.5 & §6.3, pp. 38–39, 43):**
   - `Feasible.exists_branchParityRow_replacementDesign`: on any heavy-variable branch
     `b : V → Bool` of `S = heavyVars univ univ (fun j => equationScope (φ.parityRowSystem rows j))
     b₀` with free-variable relabeling `e : ↥(univ \ S) ≃ Fin n'`, if every clause of `φ` has width
     at most `k`, every row in `rows` has Hamming weight at most `W`, and
     `hF : Feasible β n' (b₀ + 1) (max 1 (k * (W * 2 ^ k))) M'_b` holds, then there exists a
     concrete Section 4
     `ReplacementDesign (φ.branchParityRowNeutralScope rows S e b) (numNodes n') (numGroups n')
     (intervalStart β n') (rowBound β n') (tauRat n')`.
   - `exists_schedule_branchParityRow_replacementDesign`: uniformly for any `1 ≤ β`, produces
     `n₀ ≥ 20` (via `exists_schedule_replacementDesign`) such that whenever `n₀ ≤ n'`,
     `b₀ + 1 ≤ (Nat.clog 2 n') ^ β`, `max 1 (k * (W * 2 ^ k)) ≤ (Nat.clog 2 n') ^ β`,
     `∀ c ∈ φ, c.length ≤ k`, and `∀ r_row ∈ rows, weight r_row ≤ W`, **every** branch
     `b : V → Bool` simultaneously satisfies
     `Feasible β n' (b₀ + 1) (max 1 (k * (W * 2 ^ k))) M'_b` and admits a concrete schedule
     `ReplacementDesign`, with all per-branch incidence bounds (`n' ≤ M'_b`,
     `M'_b ≤ (b₀ + 1) * n'`, per-variable occurrence `≤ b₀ + 1`, and per-factor width
     `≤ max 1 (k * (W * 2 ^ k))`) discharged automatically.

2. **Schedule-instantiated `commonZeroCount`, `numPassing`, and greedy `modelCountOn` recovery
   (§§5.4–5.5, 6.1–6.3, pp. 38–43):**
   - `exists_schedule_design_commonZeroCount_parityRowSystem_eq` and
     `exists_schedule_design_numPassing_eq`: under the uniform polylogarithmic schedule hypotheses,
     exhibits a concrete family `D` of Lemma 4.8 schedule `ReplacementDesign`s across all branches
     `b : V → Bool` whose branch-summed constant-term evaluation of
     `univariateClearedParityTruncatedSum` recovers `commonZeroCount univ (φ.parityRowSystem rows)`
     and `numPassing φ.violations rows`, with each branch numerator of degree at most
     `(k * (rowBound β n' - 1)) * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))`.
   - `exists_schedule_design_modelCountOn_eq_greedy` and
     `exists_initialTests_and_schedule_design_modelCountOn_eq`: combines Lemma 6.1 (initial parity
     tests of weight `≤ D₀`), Lemma 6.2 (`3 * n` greedy rounds of list length `P ≤ D₀`), and the
     uniform Lemma 4.8 schedule threshold `n₀ ≤ n'` to recover `φ.modelCountOn Finset.univ` from
     concrete Lemma 4.8 schedule `ReplacementDesign`s with numerator degree at most
     `(k * (rowBound β n' - 1)) * (8 * Fintype.card V)`.

3. **Section 6.3 (`c = 6`) candidate/final degree budgets and Proposition 3.4 / Lemma 4.8
   domain-examination bounds (§5.5 & §6.3, pp. 38–39, 43):**
   - `branchParityRowDegreeBudget_le` and `greedyCandidateDegreeBudget_le`: when
     `rows.length ≤ c * Fintype.card V` (in particular `c = 6` for every Lemma 6.2 candidate and
     final system) and `Fintype.card V ≤ 2 * n'`, the pre-replacement degree factor
     `d = k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))` is at most
     `(k * (2 * c + 4)) * n'` (and `(16 * k) * n'` when `c = 6`).
   - `Feasible.branchParityRow_domainExaminationBound_le`,
     `Feasible.greedyCandidate_domainExaminationBound_le`, and
     `sum_branchParityRow_domainExaminationBound_le`: bounds the per-branch and branch-summed
     Proposition 3.4 local Boolean assignment examination counts on compiled CNF parity systems by
     `2 * numNodes n' * numGroups n' * exp (((k * (2 * c + 4) + 4) : ℝ) * n' * rowCost β n')` per
     branch and `2 ^ (Fintype.card V / s_div)` times that bound across all `branchAssignments S`.

## Main results

* `Feasible.exists_branchParityRow_replacementDesign`
* `exists_schedule_branchParityRow_replacementDesign`
* `exists_schedule_design_commonZeroCount_parityRowSystem_eq`
* `exists_schedule_design_numPassing_eq`
* `exists_schedule_design_modelCountOn_eq_greedy`
* `exists_initialTests_and_schedule_design_modelCountOn_eq`
* `branchParityRowDegreeBudget_le`
* `greedyCandidateDegreeBudget_le`
* `Feasible.branchParityRow_domainExaminationBound_le`
* `Feasible.greedyCandidate_domainExaminationBound_le`
* `sum_branchParityRow_domainExaminationBound_le`

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (Section 3.5, pp. 25–26;
  Section 4.6–4.7, pp. 33–35; Section 5.4–5.5, pp. 38–39; Section 6.1–6.3, pp. 40–43)
-/

@[expose] public noncomputable section

namespace Cslib.Complexity.SubexponentialSAT.ReplacementParams

open Finset Polynomial Cslib.BitString Cslib.BalancedSchedules Cslib.LinearAlgebra
  Cslib.ReplacementCounting Cslib.Logic.PL
open scoped BigOperators

variable {V : Type*} {n' : ℕ}

/-! ### 1. Per-branch and uniform Lemma 4.8 schedule `ReplacementDesign` existence -/

section BranchScheduleExistence

variable [Fintype V] [DecidableEq V]

/-- **§5.5 & §6.3 (per-branch Lemma 4.7 + Lemma 4.8 schedule `ReplacementDesign` existence on
`CNF.branchParityRowNeutralScope`)**: if every clause of `φ` has width at most `k`, every row in
`rows` has Hamming weight at most `W`, and at `S = heavyVars univ univ (fun j => equationScope
(φ.parityRowSystem rows j)) b₀` with free-variable relabeling `e : ↥(univ \ S) ≃ Fin n'` the
schedule parameters satisfy `Feasible β n' (b₀ + 1) (max 1 (k * (W * 2 ^ k))) M'_b`, then branch `b`
admits a concrete Section 4
`ReplacementDesign (φ.branchParityRowNeutralScope rows S e b) (numNodes n') (numGroups n')
(intervalStart β n') (rowBound β n') (tauRat n')`. -/
theorem Feasible.exists_branchParityRow_replacementDesign {φ : CNF V} {β k W b₀ : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) {rows : List (Fin φ.length → Bool)}
    (hW : ∀ r_row ∈ rows, weight r_row ≤ W)
    (e : ↥(univ \ heavyVars univ (univ : Finset (Fin rows.length))
      (fun j => equationScope (φ.parityRowSystem rows j)) b₀) ≃ Fin n')
    (b : V → Bool)
    (hF : Feasible β n' (b₀ + 1) (max 1 (k * (W * 2 ^ k)))
      (totalIncidence (univ : Finset (Fin rows.length ⊕ Fin n'))
        (φ.branchParityRowNeutralScope rows
          (heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
          e b))) :
    Nonempty
      (ReplacementDesign
        (φ.branchParityRowNeutralScope rows
          (heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
          e b)
        (numNodes n') (numGroups n') (intervalStart β n') (rowBound β n') (tauRat n')) :=
  hF.exists_replacementDesign _ (Nat.succ_pos b₀) (le_max_left 1 _)
    (CNF.varIncidence_branchParityRowNeutralScope_heavyVars_le φ rows b₀ e b)
    (CNF.card_branchParityRowNeutralScope_le hk hW _ e b)
    (CNF.totalIncidence_branchParityRowNeutralScope_heavyVars_le φ rows b₀ e b)

/-- **§5.5 & §6.3 (uniform Lemma 4.7 + Lemma 4.8 schedule `ReplacementDesign` existence across all
heavy-variable branches of `φ.parityRowSystem rows`)**: for every integer `1 ≤ β`, there exists
`n₀ ≥ 20` such that whenever the free-variable count `n'` satisfies `n₀ ≤ n'`, the heavy-variable
threshold satisfies `b₀ + 1 ≤ (Nat.clog 2 n') ^ β`, the neutral-augmented scope width bound
satisfies `max 1 (k * (W * 2 ^ k)) ≤ (Nat.clog 2 n') ^ β`, every clause of `φ` has width at most
`k`, and every row in `rows` has Hamming weight at most `W`, **every** branch assignment
`b : V → Bool` simultaneously satisfies `Feasible` and admits a concrete Lemma 4.8 schedule
`ReplacementDesign`. -/
theorem exists_schedule_branchParityRow_replacementDesign {β : ℕ} (hβ : 1 ≤ β) :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] {φ : CNF V} {k W b₀ n' : ℕ}
        {rows : List (Fin φ.length → Bool)}
        (e : ↥(univ \ heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀) ≃ Fin n'),
        n₀ ≤ n' →
        b₀ + 1 ≤ Nat.clog 2 n' ^ β →
        max 1 (k * (W * 2 ^ k)) ≤ Nat.clog 2 n' ^ β →
        (∀ c ∈ φ, c.length ≤ k) →
        (∀ r_row ∈ rows, weight r_row ≤ W) →
        ∀ b : V → Bool,
          Feasible β n' (b₀ + 1) (max 1 (k * (W * 2 ^ k)))
            (totalIncidence (univ : Finset (Fin rows.length ⊕ Fin n'))
              (φ.branchParityRowNeutralScope rows
                (heavyVars univ (univ : Finset (Fin rows.length))
                  (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
                e b)) ∧
          Nonempty
            (ReplacementDesign
              (φ.branchParityRowNeutralScope rows
                (heavyVars univ (univ : Finset (Fin rows.length))
                  (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
                e b)
              (numNodes n') (numGroups n') (intervalStart β n') (rowBound β n') (tauRat n')) := by
  obtain ⟨n₀, hn₀20, hsched⟩ := exists_schedule_replacementDesign hβ
  refine ⟨n₀, hn₀20, fun {V _ _ φ k W b₀ n' rows} e hn' hb hw hk hW b => ?_⟩
  exact hsched
    (φ.branchParityRowNeutralScope rows
      (heavyVars univ (univ : Finset (Fin rows.length))
        (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
      e b)
    hn' (Nat.succ_pos b₀) hb (le_max_left 1 _) hw
    (CNF.le_totalIncidence_branchParityRowNeutralScope φ rows _ e b)
    (CNF.totalIncidence_branchParityRowNeutralScope_heavyVars_le φ rows b₀ e b)
    (CNF.varIncidence_branchParityRowNeutralScope_heavyVars_le φ rows b₀ e b)
    (CNF.card_branchParityRowNeutralScope_le hk hW _ e b)

end BranchScheduleExistence

/-! ### 2. End-to-end Lemma 4.8 schedule `ReplacementDesign` recovery of `numPassing` and `#F` -/

section ScheduleDesignRecovery

variable [Fintype V] [DecidableEq V]

/-- **§5.4–5.5 & §6.3 (schedule-instantiated `commonZeroCount` recovery on `φ.parityRowSystem`)**:
for every `1 ≤ β`, there exists `n₀ ≥ 20` such that whenever `n₀ ≤ n'`,
`b₀ + 1 ≤ (Nat.clog 2 n') ^ β`, `max 1 (k * (W * 2 ^ k)) ≤ (Nat.clog 2 n') ^ β`,
`∀ c ∈ φ, c.length ≤ k`, and `∀ r_row ∈ rows, weight r_row ≤ W`, there exists a family `D` of
concrete Lemma 4.8 schedule `ReplacementDesign`s across all branches `b : V → Bool` whose
branch-summed constant-term evaluation recovers
`(commonZeroCount univ (φ.parityRowSystem rows) : ℤ)` and whose univariate numerators have degree at
most `(k * (rowBound β n' - 1)) * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))`. -/
theorem exists_schedule_design_commonZeroCount_parityRowSystem_eq {β : ℕ} (hβ : 1 ≤ β) :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] {φ : CNF V} {k W b₀ n' : ℕ}
        {rows : List (Fin φ.length → Bool)}
        (e : ↥(univ \ heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀) ≃ Fin n'),
        n₀ ≤ n' →
        b₀ + 1 ≤ Nat.clog 2 n' ^ β →
        max 1 (k * (W * 2 ^ k)) ≤ Nat.clog 2 n' ^ β →
        (∀ c ∈ φ, c.length ≤ k) →
        (∀ r_row ∈ rows, weight r_row ≤ W) →
        let S := heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀
        (∀ b : V → Bool,
          Feasible β n' (b₀ + 1) (max 1 (k * (W * 2 ^ k)))
            (totalIncidence (univ : Finset (Fin rows.length ⊕ Fin n'))
              (φ.branchParityRowNeutralScope rows S e b))) ∧
        ∃ D : (b : V → Bool) →
            ReplacementDesign (φ.branchParityRowNeutralScope rows S e b)
              (numNodes n') (numGroups n') (intervalStart β n') (rowBound β n') (tauRat n'),
          (commonZeroCount (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) : ℤ) =
            (∑ b ∈ branchAssignments S,
              ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                (φ.branchParityRowSystem rows S e b)
                (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                (branchPrecision (Fintype.card V))
                (designReplacementScaledIntMap (D b) Sum.inl)).eval 0 /
                  clearedProductDenom (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                    (branchPrecision (Fintype.card V))
                    #(univ : Finset (Fin rows.length))) %
                      ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
          ∀ b : V → Bool,
            (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
              (φ.branchParityRowSystem rows S e b)
              (commonDenom (numNodes n') (rowBound β n') : ℤ) k
              (branchPrecision (Fintype.card V))
              (designReplacementScaledIntMap (D b) Sum.inl)).natDegree ≤
                (k * (rowBound β n' - 1)) *
                  (rows.length + 2 * (branchPrecision (Fintype.card V) - 1)) := by
  obtain ⟨n₀, hn₀20, hsched⟩ := exists_schedule_branchParityRow_replacementDesign hβ
  refine ⟨n₀, hn₀20, fun {V _ _ φ k W b₀ n' rows} e hn' hb hw hk hW => ?_⟩
  intro S
  have hbranch := hsched e hn' hb hw hk hW
  refine ⟨fun b => (hbranch b).1, ?_⟩
  let D : (b : V → Bool) →
      ReplacementDesign (φ.branchParityRowNeutralScope rows S e b)
        (numNodes n') (numGroups n') (intervalStart β n') (rowBound β n') (tauRat n') :=
    fun b => Classical.choice (hbranch b).2
  refine ⟨D, ?_, ?_⟩
  · exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design hk rows S e
      (φ.branchParityRowNeutralScope rows S e) D (fun _ => Sum.inl)
  · intro b
    exact CNF.natDegree_univariateClearedParityTruncatedSum_branchParityRowSystem_le hk rows S e b
      (D b) Sum.inl (branchPrecision (Fintype.card V))

/-- **§5.4–5.5 & §6.3 (schedule-instantiated `numPassing` recovery on `φ.violations`)**: under the
same polylogarithmic schedule hypotheses, there exists a family `D` of concrete Lemma 4.8 schedule
`ReplacementDesign`s across all branches `b : V → Bool` whose branch-summed constant-term evaluation
recovers `(numPassing φ.violations rows : ℤ)`. -/
theorem exists_schedule_design_numPassing_eq {β : ℕ} (hβ : 1 ≤ β) :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] {φ : CNF V} {k W b₀ n' : ℕ}
        {rows : List (Fin φ.length → Bool)}
        (e : ↥(univ \ heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀) ≃ Fin n'),
        n₀ ≤ n' →
        b₀ + 1 ≤ Nat.clog 2 n' ^ β →
        max 1 (k * (W * 2 ^ k)) ≤ Nat.clog 2 n' ^ β →
        (∀ c ∈ φ, c.length ≤ k) →
        (∀ r_row ∈ rows, weight r_row ≤ W) →
        let S := heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀
        (∀ b : V → Bool,
          Feasible β n' (b₀ + 1) (max 1 (k * (W * 2 ^ k)))
            (totalIncidence (univ : Finset (Fin rows.length ⊕ Fin n'))
              (φ.branchParityRowNeutralScope rows S e b))) ∧
        ∃ D : (b : V → Bool) →
            ReplacementDesign (φ.branchParityRowNeutralScope rows S e b)
              (numNodes n') (numGroups n') (intervalStart β n') (rowBound β n') (tauRat n'),
          (numPassing φ.violations rows : ℤ) =
            (∑ b ∈ branchAssignments S,
              ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                (φ.branchParityRowSystem rows S e b)
                (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                (branchPrecision (Fintype.card V))
                (designReplacementScaledIntMap (D b) Sum.inl)).eval 0 /
                  clearedProductDenom (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                    (branchPrecision (Fintype.card V))
                    #(univ : Finset (Fin rows.length))) %
                      ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
          ∀ b : V → Bool,
            (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
              (φ.branchParityRowSystem rows S e b)
              (commonDenom (numNodes n') (rowBound β n') : ℤ) k
              (branchPrecision (Fintype.card V))
              (designReplacementScaledIntMap (D b) Sum.inl)).natDegree ≤
                (k * (rowBound β n' - 1)) *
                  (rows.length + 2 * (branchPrecision (Fintype.card V) - 1)) := by
  obtain ⟨n₀, hn₀20, hsched⟩ := exists_schedule_design_commonZeroCount_parityRowSystem_eq hβ
  refine ⟨n₀, hn₀20, fun {V _ _ φ k W b₀ n' rows} e hn' hb hw hk hW => ?_⟩
  obtain ⟨hF, D, hcount, hdeg⟩ := hsched e hn' hb hw hk hW
  rw [CNF.commonZeroCount_parityRowSystem] at hcount
  exact ⟨hF, D, hcount, hdeg⟩

/-- If every row in `A 0` has Hamming weight at most `D₀` and each step appends `testRow (γ i)` of
list length `P`, then at every stage `j` every row in `A j` has Hamming weight at most
`max D₀ P`. -/
theorem weight_le_max_of_append_testRow {m D₀ P : ℕ}
    (A : ℕ → List (Fin m → Bool)) (hA₀ : ∀ r_row ∈ A 0, weight r_row ≤ D₀)
    (γ : ℕ → Fin P → Fin m × Bool) (hA : ∀ i, A (i + 1) = A i ++ [testRow (γ i)]) :
    ∀ (j : ℕ) (r_row : Fin m → Bool), r_row ∈ A j → weight r_row ≤ max D₀ P := by
  intro j
  induction j with
  | zero =>
    exact fun r_row hr => (hA₀ r_row hr).trans (le_max_left D₀ P)
  | succ j ih =>
    intro r_row hr
    rw [hA j] at hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ih r_row hr
    · rw [List.mem_singleton.mp hr]
      exact (weight_testRow_le (γ j)).trans (le_max_right D₀ P)

/-- **§§5.4–5.5 & 6.2–6.3 (schedule-instantiated greedy `modelCountOn` recovery)**: for every
`1 ≤ β`, there exists `n₀ ≥ 20` such that under the hypotheses of
`CNF.commonZeroCount_parityRowSystem_greedy`, if every row of `A 0` has weight at most `D₀` and at
stage `3 * Fintype.card V` the free-variable count `n'` satisfies `n₀ ≤ n'`,
`b₀ + 1 ≤ (Nat.clog 2 n') ^ β`, and `max 1 (k * (max D₀ P * 2 ^ k)) ≤ (Nat.clog 2 n') ^ β`, then
there exists a concrete family `D` of Lemma 4.8 schedule `ReplacementDesign`s across all branches of
`A (3 * Fintype.card V)` whose branch-summed constant-term evaluation recovers
`(φ.modelCountOn Finset.univ : ℤ)`. -/
theorem exists_schedule_design_modelCountOn_eq_greedy {β : ℕ} (hβ : 1 ≤ β) :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (φ : CNF V) {k D₀ P b₀ n' : ℕ},
        (∀ c ∈ φ, c.length ≤ k) →
        1 ≤ Fintype.card V →
        1 ≤ P →
        ∀ (A : ℕ → List (Fin φ.length → Bool)),
        (∀ r_row ∈ A 0, weight r_row ≤ D₀) →
        (∀ σ, PassesTests φ.violations (A 0) σ → φ.eval σ = false →
          φ.length ≤ P * weight (φ.violations σ)) →
        ∀ (γ : ℕ → Fin P → Fin φ.length × Bool),
        (∀ i, A (i + 1) = A i ++ [testRow (γ i)]) →
        (∀ i (γ' : Fin P → Fin φ.length × Bool),
          commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow (γ i)])) ≤
            commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ']))) →
        ∀ (e : ↥(univ \ heavyVars univ (univ : Finset (Fin (A (3 * Fintype.card V)).length))
          (fun j => equationScope (φ.parityRowSystem (A (3 * Fintype.card V)) j)) b₀) ≃ Fin n'),
        n₀ ≤ n' →
        b₀ + 1 ≤ Nat.clog 2 n' ^ β →
        max 1 (k * (max D₀ P * 2 ^ k)) ≤ Nat.clog 2 n' ^ β →
        let rows := A (3 * Fintype.card V)
        let S := heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀
        (∀ b : V → Bool,
          Feasible β n' (b₀ + 1) (max 1 (k * (max D₀ P * 2 ^ k)))
            (totalIncidence (univ : Finset (Fin rows.length ⊕ Fin n'))
              (φ.branchParityRowNeutralScope rows S e b))) ∧
        ∃ D : (b : V → Bool) →
            ReplacementDesign (φ.branchParityRowNeutralScope rows S e b)
              (numNodes n') (numGroups n') (intervalStart β n') (rowBound β n') (tauRat n'),
          (φ.modelCountOn Finset.univ : ℤ) =
            (∑ b ∈ branchAssignments S,
              ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                (φ.branchParityRowSystem rows S e b)
                (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                (branchPrecision (Fintype.card V))
                (designReplacementScaledIntMap (D b) Sum.inl)).eval 0 /
                  clearedProductDenom (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                    (branchPrecision (Fintype.card V))
                    #(univ : Finset (Fin rows.length))) %
                      ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
          ∀ b : V → Bool,
            (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
              (φ.branchParityRowSystem rows S e b)
              (commonDenom (numNodes n') (rowBound β n') : ℤ) k
              (branchPrecision (Fintype.card V))
              (designReplacementScaledIntMap (D b) Sum.inl)).natDegree ≤
                (k * (rowBound β n' - 1)) *
                  (rows.length + 2 * (branchPrecision (Fintype.card V) - 1)) := by
  obtain ⟨n₀, hn₀20, hsched⟩ := exists_schedule_design_commonZeroCount_parityRowSystem_eq hβ
  refine ⟨n₀, hn₀20,
    fun {V _ _} φ {k D₀ P b₀ n'} hk hn hP A hA₀_wt hinit γ hA hγ e hn' hb hw => ?_⟩
  have hW : ∀ r_row ∈ A (3 * Fintype.card V), weight r_row ≤ max D₀ P :=
    weight_le_max_of_append_testRow A hA₀_wt γ hA (3 * Fintype.card V)
  obtain ⟨hF, D, hcount, hdeg⟩ := hsched e hn' hb hw hk hW
  rw [CNF.commonZeroCount_parityRowSystem_greedy φ hn hP A hinit γ hA hγ] at hcount
  exact ⟨hF, D, hcount, hdeg⟩

/-- **Lemmas 6.1–6.2, Lemma 4.7–4.8, & §§5.4–5.5, 6.3 (end-to-end initial + greedy parity-test
compilation and Lemma 4.8 schedule `ReplacementDesign` recovery of `φ.modelCountOn Finset.univ`)**:
for every `1 ≤ β`, there exists `n₀ ≥ 20` such that for any width-`≤ k` CNF `φ` on
`n = Fintype.card V ≥ 1` variables with `φ.length ≤ B * n` (`B ≥ 1`), there exist initial parity
rows `A_init` (`A_init.length ≤ 3 * n`, each of weight at most
`D₀ = CNF.initialRowWeightBound B φ.length`) such that for any greedy sequence
`A (i + 1) = A i ++ [testRow (γ i)]` with `A 0 = A_init` minimizing
`commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ']))` over candidate rows of list length
`P = CNF.greedyRowListLength B φ.length`, whenever at stage `3 * n` the free-variable count `n'`
satisfies `n₀ ≤ n'`, `b₀ + 1 ≤ (Nat.clog 2 n') ^ β`, and
`max 1 (k * (D₀ * 2 ^ k)) ≤ (Nat.clog 2 n') ^ β`:
1. Every branch `b : V → Bool` satisfies
   `Feasible β n' (b₀ + 1) (max 1 (k * (D₀ * 2 ^ k))) M'_b`,
2. There exists a family `D` of concrete Lemma 4.8 schedule `ReplacementDesign`s across all
   branches whose branch-summed constant-term evaluation recovers
   `(φ.modelCountOn Finset.univ : ℤ)`,
3. Every branch numerator has `natDegree ≤ (k * (rowBound β n' - 1)) * (8 * Fintype.card V)`. -/
theorem exists_initialTests_and_schedule_design_modelCountOn_eq {β : ℕ} (hβ : 1 ≤ β) :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (φ : CNF V) {k B : ℕ},
        (∀ c ∈ φ, c.length ≤ k) →
        1 ≤ Fintype.card V →
        1 ≤ B →
        φ.length ≤ B * Fintype.card V →
        let D₀ := CNF.initialRowWeightBound B φ.length
        let P := CNF.greedyRowListLength B φ.length
        ∃ A_init : List (Fin φ.length → Bool), A_init.length ≤ 3 * Fintype.card V ∧
          (∀ r_row ∈ A_init, weight r_row ≤ D₀) ∧
          ∀ (A : ℕ → List (Fin φ.length → Bool))
            (γ : ℕ → Fin P → Fin φ.length × Bool),
            A 0 = A_init → (∀ i, A (i + 1) = A i ++ [testRow (γ i)]) →
            (∀ i (γ' : Fin P → Fin φ.length × Bool),
              commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow (γ i)])) ≤
                commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ']))) →
            (∀ i ≤ 3 * Fintype.card V,
              (A i).length ≤ 6 * Fintype.card V ∧
              ∀ j : Fin (A i).length,
                (∀ M ∈ φ.parityRowSystem (A i) j, M ⊆ φ.vars.toFinset ∧ #M ≤ k) ∧
                #(φ.parityRowSystem (A i) j) ≤ D₀ * 2 ^ k ∧
                #(equationScope (φ.parityRowSystem (A i) j)) ≤ k * (D₀ * 2 ^ k)) ∧
            ∀ {b₀ n' : ℕ}
              (e : ↥(univ \ heavyVars univ (univ : Finset (Fin (A (3 * Fintype.card V)).length))
                (fun j => equationScope (φ.parityRowSystem (A (3 * Fintype.card V)) j)) b₀) ≃
                  Fin n'),
              n₀ ≤ n' →
              b₀ + 1 ≤ Nat.clog 2 n' ^ β →
              max 1 (k * (D₀ * 2 ^ k)) ≤ Nat.clog 2 n' ^ β →
              let rows := A (3 * Fintype.card V)
              let S := heavyVars univ (univ : Finset (Fin rows.length))
                (fun j => equationScope (φ.parityRowSystem rows j)) b₀
              (∀ b : V → Bool,
                Feasible β n' (b₀ + 1) (max 1 (k * (D₀ * 2 ^ k)))
                  (totalIncidence (univ : Finset (Fin rows.length ⊕ Fin n'))
                    (φ.branchParityRowNeutralScope rows S e b))) ∧
              ∃ D : (b : V → Bool) →
                  ReplacementDesign (φ.branchParityRowNeutralScope rows S e b)
                    (numNodes n') (numGroups n') (intervalStart β n') (rowBound β n') (tauRat n'),
                (φ.modelCountOn Finset.univ : ℤ) =
                  (∑ b ∈ branchAssignments S,
                    ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                      (φ.branchParityRowSystem rows S e b)
                      (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                      (branchPrecision (Fintype.card V))
                      (designReplacementScaledIntMap (D b) Sum.inl)).eval 0 /
                        clearedProductDenom (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                          (branchPrecision (Fintype.card V))
                          #(univ : Finset (Fin rows.length))) %
                            ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
                ∀ b : V → Bool,
                  (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                    (φ.branchParityRowSystem rows S e b)
                    (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                    (branchPrecision (Fintype.card V))
                    (designReplacementScaledIntMap (D b) Sum.inl)).natDegree ≤
                      (k * (rowBound β n' - 1)) * (8 * Fintype.card V) := by
  obtain ⟨n₀, hn₀20, hsched⟩ := exists_schedule_branchParityRow_replacementDesign hβ
  refine ⟨n₀, hn₀20, fun {V _ _} φ {k B} hk hn hB hm => ?_⟩
  obtain ⟨A_init, hlen, hw, hgreedy⟩ := CNF.exists_initialTests_commonZeroCount_greedy φ hk hn hB hm
  refine ⟨A_init, hlen, hw, fun A γ h0 hA hγ => ?_⟩
  obtain ⟨hcount, hbounds⟩ := hgreedy A γ h0 hA hγ
  have hstage :
      ∀ i ≤ 3 * Fintype.card V,
        (A i).length ≤ 6 * Fintype.card V ∧
        ∀ j : Fin (A i).length,
          (∀ M ∈ φ.parityRowSystem (A i) j, M ⊆ φ.vars.toFinset ∧ #M ≤ k) ∧
          #(φ.parityRowSystem (A i) j) ≤ CNF.initialRowWeightBound B φ.length * 2 ^ k ∧
          #(equationScope (φ.parityRowSystem (A i) j)) ≤
            k * (CNF.initialRowWeightBound B φ.length * 2 ^ k) := by
    intro i hi
    obtain ⟨hlen_i, hj⟩ := hbounds i hi
    refine ⟨hlen_i, fun j => ?_⟩
    obtain ⟨hM, hcard, hscope⟩ := hj j
    rw [CNF.max_initialRowWeightBound_greedyRowListLength] at hcard hscope
    exact ⟨hM, hcard, hscope⟩
  refine ⟨hstage, fun {b₀ n'} e hn' hb hw_width => ?_⟩
  intro rows S
  have hW_rows : ∀ r_row ∈ rows, weight r_row ≤ CNF.initialRowWeightBound B φ.length := by
    intro r_row hr
    have hmax := weight_le_max_of_append_testRow A (h0 ▸ hw) γ hA (3 * Fintype.card V) r_row hr
    rwa [CNF.max_initialRowWeightBound_greedyRowListLength] at hmax
  have hbranch := hsched e hn' hb hw_width hk hW_rows
  refine ⟨fun b => (hbranch b).1, ?_⟩
  let D : (b : V → Bool) →
      ReplacementDesign (φ.branchParityRowNeutralScope rows S e b)
        (numNodes n') (numGroups n') (intervalStart β n') (rowBound β n') (tauRat n') :=
    fun b => Classical.choice (hbranch b).2
  refine ⟨D, ?_, ?_⟩
  · rw [← hcount]
    exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design hk rows S e
      (φ.branchParityRowNeutralScope rows S e) D (fun _ => Sum.inl)
  · intro b
    have hdeg := CNF.natDegree_univariateClearedParityTruncatedSum_branchParityRowSystem_le hk rows
      S e b (D b) Sum.inl (branchPrecision (Fintype.card V))
    have hrows_len : rows.length ≤ 6 * Fintype.card V := (hstage (3 * Fintype.card V) le_rfl).1
    have h8 : rows.length + 2 * (branchPrecision (Fintype.card V) - 1) ≤ 8 * Fintype.card V := by
      unfold branchPrecision
      omega
    exact hdeg.trans (Nat.mul_le_mul_left (k * (rowBound β n' - 1)) h8)

end ScheduleDesignRecovery

/-! ### 3. Section 6.3 (`c = 6`) degree budgets and Proposition 3.4 domain-examination bounds -/

section DomainExaminationBounds

/-- **Section 5.5 & Section 6.3 degree budget**: when `rows.length ≤ c * Fintype.card V` and
`Fintype.card V ≤ 2 * n'`, the pre-replacement degree factor
`k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))` at original precision
`branchPrecision (Fintype.card V) = Fintype.card V + 1` is at most `(k * (2 * c + 4)) * n'`. -/
theorem branchParityRowDegreeBudget_le {k c n n' m : ℕ}
    (hm : m ≤ c * n) (hn : n ≤ 2 * n') :
    k * (m + 2 * (branchPrecision n - 1)) ≤ (k * (2 * c + 4)) * n' := by
  unfold branchPrecision
  have h1 : m + 2 * (n + 1 - 1) ≤ (2 * c + 4) * n' := by
    calc m + 2 * (n + 1 - 1)
        = m + 2 * n := by omega
      _ ≤ c * n + 2 * n := Nat.add_le_add_right hm (2 * n)
      _ = (c + 2) * n := by ring
      _ ≤ (c + 2) * (2 * n') := Nat.mul_le_mul_left (c + 2) hn
      _ = (2 * c + 4) * n' := by ring
  calc k * (m + 2 * (n + 1 - 1))
      ≤ k * ((2 * c + 4) * n') := Nat.mul_le_mul_left k h1
    _ = (k * (2 * c + 4)) * n' := (mul_assoc k (2 * c + 4) n').symm

/-- **Section 6.3 (`c = 6`) Lemma 6.2 candidate/final degree budget**: for any candidate or final
system with `rows.length ≤ 6 * Fintype.card V` and `Fintype.card V ≤ 2 * n'`, the pre-replacement
degree factor `k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))` is at most
`(16 * k) * n'`. -/
theorem greedyCandidateDegreeBudget_le {k n n' m : ℕ}
    (hm : m ≤ 6 * n) (hn : n ≤ 2 * n') :
    k * (m + 2 * (branchPrecision n - 1)) ≤ (16 * k) * n' := by
  have h := branchParityRowDegreeBudget_le (k := k) hm hn
  rwa [show k * (2 * 6 + 4) = 16 * k by ring] at h

/-- **Section 5.5 (`n ≤ 2 * n'` after branching on `heavyVars` of `φ.parityRowSystem rows`)**: when
`1 ≤ b₀`, `2 ≤ s_div`, `totalIncidence univ (fun j => equationScope (φ.parityRowSystem rows j)) *
s_div ≤ b₀ * Fintype.card V`, and `e : ↥(univ \ heavyVars ...) ≃ Fin n'`, the free-variable count
`n'` satisfies `Fintype.card V ≤ 2 * n'` and `Fintype.card V / 2 ≤ n'`. -/
theorem card_le_two_mul_freeVar_of_heavyVars_parityRowSystem [Fintype V] [DecidableEq V]
    (φ : CNF V) (rows : List (Fin φ.length → Bool)) {b₀ s_div : ℕ}
    (hb₀ : 1 ≤ b₀) (hs_div : 2 ≤ s_div)
    (hM :
      totalIncidence (univ : Finset (Fin rows.length))
        (fun j => equationScope (φ.parityRowSystem rows j)) * s_div ≤
          b₀ * Fintype.card V)
    (e : ↥(univ \ heavyVars univ (univ : Finset (Fin rows.length))
      (fun j => equationScope (φ.parityRowSystem rows j)) b₀) ≃ Fin n') :
    Fintype.card V ≤ 2 * n' ∧ Fintype.card V / 2 ≤ n' := by
  have hhalf := card_sdiff_heavyVars_ge_half (univ : Finset V)
    (univ : Finset (Fin rows.length))
    (fun j => equationScope (φ.parityRowSystem rows j)) hb₀ hs_div
    (fun _ _ => subset_univ _) (by simpa only [card_univ] using hM)
  have hcard : #(univ \ heavyVars univ (univ : Finset (Fin rows.length))
      (fun j => equationScope (φ.parityRowSystem rows j)) b₀) = n' := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr e
  simpa only [card_univ, hcard] using hhalf

/-- **Section 5.5 & Section 6.3 single-branch Proposition 3.4 / Lemma 4.8 domain-examination bound
for `φ.parityRowSystem rows`**: for any branch with `hF : Feasible β n' b_occ w_width M'` and
concrete schedule design `D` on `Fin n'`, if `rows.length ≤ c * Fintype.card V` and
`Fintype.card V ≤ 2 * n'`, then at
`d = k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))` and canonical truncation order
`q = (d * rowBound β n') / numNodes n'`, the induced Section 3 counting design
`C := hF.toCountingDesign D s` examines at most
`2 * numNodes n' * numGroups n' * exp (((k * (2 * c + 4) + 4) : ℝ) * n' * rowCost β n')` local
Boolean assignments. -/
theorem Feasible.branchParityRow_domainExaminationBound_le [Fintype V] {F_idx : Type*}
    [Fintype F_idx] {scope : F_idx → Finset (Fin n')} {β b_occ w_width M' k c : ℕ}
    (φ : CNF V) (rows : List (Fin φ.length → Bool))
    (hF : Feasible β n' b_occ w_width M')
    (D : ReplacementDesign scope (numNodes n') (numGroups n') (intervalStart β n')
      (rowBound β n') (tauRat n'))
    (s : Finset F_idx) (hm : rows.length ≤ c * Fintype.card V) (hn : Fintype.card V ≤ 2 * n') :
    let d := k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))
    let q := (d * rowBound β n') / numNodes n'
    let C := hF.toCountingDesign D s
    (∑ t : Fin (numNodes n'),
        (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
          (2 * (#(C.measurementBox t) : ℝ) *
            ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
      2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
        Real.exp (((k * (2 * c + 4) + 4 : ℕ) : ℝ) * (n' : ℝ) * rowCost β n') ∧
    2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
        Real.exp (((k * (2 * c + 4) + 4 : ℕ) : ℝ) * (n' : ℝ) * rowCost β n') ≤
      2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
        Real.exp (((k * (2 * c + 4) + 4 : ℕ) : ℝ) * (n' : ℝ) *
          (1028 * ((β : ℝ) + 3) * (Nat.clog 2 (Nat.clog 2 n') : ℝ) ^ 2 /
            Real.sqrt (Nat.clog 2 n'))) := by
  intro d q C
  have hd_le : (d : ℝ) ≤ ((k * (2 * c + 4) : ℕ) : ℝ) * (n' : ℝ) := by
    exact_mod_cast branchParityRowDegreeBudget_le (k := k) hm hn
  have hq :
      (q : ℝ) ≤ ((k * (2 * c + 4) : ℕ) : ℝ) * (n' : ℝ) *
        ((rowBound β n' : ℝ) / numNodes n') := by
    calc (q : ℝ)
        ≤ ((d * rowBound β n' : ℕ) : ℝ) / numNodes n' := Nat.cast_div_le
      _ = (d : ℝ) * ((rowBound β n' : ℝ) / numNodes n') := by push_cast; ring
      _ ≤ (((k * (2 * c + 4) : ℕ) : ℝ) * (n' : ℝ)) *
            ((rowBound β n' : ℝ) / numNodes n') :=
          mul_le_mul_of_nonneg_right hd_le (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hc_nn : (0 : ℝ) ≤ ((k * (2 * c + 4) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hbound := hF.domainExaminationBound_le_mul_exp_rowCost D s hc_nn hq
  have hcast :
      (((k * (2 * c + 4) : ℕ) : ℝ) + 4) = ((k * (2 * c + 4) + 4 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hcast] at hbound
  exact hbound

/-- **Section 6.3 (`c = 6`) single-branch domain-examination bound for any Lemma 6.2 candidate or
final system (`rows.length ≤ 6 * Fintype.card V`)**: specializes
`Feasible.branchParityRow_domainExaminationBound_le` to `c = 6`, giving the exponent multiplier
`16 * k + 4`. -/
theorem Feasible.greedyCandidate_domainExaminationBound_le [Fintype V] {F_idx : Type*}
    [Fintype F_idx] {scope : F_idx → Finset (Fin n')} {β b_occ w_width M' k : ℕ}
    (φ : CNF V) (rows : List (Fin φ.length → Bool))
    (hF : Feasible β n' b_occ w_width M')
    (D : ReplacementDesign scope (numNodes n') (numGroups n') (intervalStart β n')
      (rowBound β n') (tauRat n'))
    (s : Finset F_idx) (hm : rows.length ≤ 6 * Fintype.card V) (hn : Fintype.card V ≤ 2 * n') :
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
  have h := hF.branchParityRow_domainExaminationBound_le (k := k) (c := 6) φ rows D s hm hn
  rwa [show k * (2 * 6 + 4) + 4 = 16 * k + 4 by ring] at h

/-- **Section 5.5 & Section 6.3 multi-branch domain-examination bound across all
`branchAssignments S` of `φ.parityRowSystem rows`**: when
`S = heavyVars univ univ (fun j => equationScope (φ.parityRowSystem rows j)) b₀` with `1 ≤ b₀`,
`2 ≤ s_div`, `totalIncidence univ (fun j => equationScope (φ.parityRowSystem rows j)) * s_div ≤
b₀ * Fintype.card V`, and `e : ↥(univ \ S) ≃ Fin n'`, the free-variable dimension satisfies
`Fintype.card V ≤ 2 * n'`, and if each branch `b ∈ branchAssignments S` has its real examination sum
bounded via `Feasible.branchParityRow_domainExaminationBound_le`, then the sum across all
`b ∈ branchAssignments S` is at most
`(2 : ℝ) ^ (Fintype.card V / s_div) * (2 * numNodes n' * numGroups n' *
  exp (((k * (2 * c + 4) + 4 : ℕ) : ℝ) * n' * rowCost β n'))`. -/
theorem sum_branchParityRow_domainExaminationBound_le [Fintype V] [DecidableEq V]
    (φ : CNF V) (rows : List (Fin φ.length → Bool)) {β b₀ s_div k c : ℕ}
    (hb₀ : 1 ≤ b₀) (hs_div : 2 ≤ s_div)
    (hM :
      totalIncidence (univ : Finset (Fin rows.length))
        (fun j => equationScope (φ.parityRowSystem rows j)) * s_div ≤
          b₀ * Fintype.card V)
    (e : ↥(univ \ heavyVars univ (univ : Finset (Fin rows.length))
      (fun j => equationScope (φ.parityRowSystem rows j)) b₀) ≃ Fin n')
    (examSum : (V → Bool) → ℝ)
    (hexam : ∀ b ∈ branchAssignments
        (heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀),
      examSum b ≤
        2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
          Real.exp (((k * (2 * c + 4) + 4 : ℕ) : ℝ) * (n' : ℝ) * rowCost β n')) :
    Fintype.card V ≤ 2 * n' ∧
    (∑ b ∈ branchAssignments
        (heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀),
      examSum b) ≤
      (2 : ℝ) ^ (Fintype.card V / s_div) *
        (2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
          Real.exp (((k * (2 * c + 4) + 4 : ℕ) : ℝ) * (n' : ℝ) * rowCost β n')) := by
  have hn :=
    (card_le_two_mul_freeVar_of_heavyVars_parityRowSystem φ rows hb₀ hs_div hM e).1
  refine ⟨hn, ?_⟩
  let S := heavyVars univ (univ : Finset (Fin rows.length))
    (fun j => equationScope (φ.parityRowSystem rows j)) b₀
  let B := 2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
    Real.exp (((k * (2 * c + 4) + 4 : ℕ) : ℝ) * (n' : ℝ) * rowCost β n')
  have hB_nn : 0 ≤ B := by positivity
  have hcard : (#(branchAssignments S) : ℝ) ≤ (2 : ℝ) ^ (Fintype.card V / s_div) := by
    exact_mod_cast card_branchAssignments_heavyVars_le_two_pow_div
      (univ : Finset (Fin rows.length))
      (fun j => equationScope (φ.parityRowSystem rows j)) hb₀ (by omega) hM
  calc ∑ b ∈ branchAssignments S, examSum b
      ≤ ∑ _b ∈ branchAssignments S, B := sum_le_sum hexam
    _ = (#(branchAssignments S) : ℝ) * B := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ (Fintype.card V / s_div) * B := mul_le_mul_of_nonneg_right hcard hB_nn

end DomainExaminationBounds

end Cslib.Complexity.SubexponentialSAT.ReplacementParams
