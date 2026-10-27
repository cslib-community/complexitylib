/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.ReplacementScheduleDesign
public import Complexity.Foundations.BooleanAnalysis.SparseBranching

/-!
# Section 5.5 per-branch schedule feasibility and multi-branch domain-examination bounds

This module connects the heavy-variable branch reduction and neutral singleton scope augmentation of
`Complexity.Foundations.BooleanAnalysis.SparseBranching` (Section 5.5, Proof of Theorem 2.2,
printed pp. 38–39 of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]) with the
Lemma 4.7 / Lemma 4.8 schedule replacement design bridge of
`Complexity.Computability.Complexity.FineGrained.ReplacementScheduleDesign` (Sections 3.5 and
4.6–4.7, printed pp. 25–26, 33–35):

1. **Per-branch neutral-augmented scope family on `{i : κ // i ∈ I} ⊕ Fin n'`**:
   Given an active equation set `I : Finset κ`, a sparse polynomial system
   `P : κ → Finset (Finset ι)` on `ι`, a heavy-variable subset `S : Finset ι`, and an equivalence
   `e : ↥(univ \ S) ≃ Fin n'` identifying the free variables with `Fin n'`,
   `branchEquationScope S e P b` maps each equation `i` to the variable scope of
   `relabelRestrictedMonomials S e b (P i)`, and
   `branchAugmentedScope S e I P b : {i : κ // i ∈ I} ⊕ Fin n' → Finset (Fin n')` applies
   `Cslib.BitString.withNeutralScope` on the subtype `{i : κ // i ∈ I}` of active equations.
   Because `(univ : Finset ({i : κ // i ∈ I} ⊕ Fin n'))` coincides with
   `withNeutralFactors (univ : Finset {i : κ // i ∈ I})`, this directly inherits the incidence
   identities of `SparseBranching.lean`:
   - `sum_card_branchAugmentedScope`:
     `∑ f, #(branchAugmentedScope S e I P b f) =`
     `totalIncidence I (branchEquationScope S e P b) + n'`.
   - `le_sum_card_branchAugmentedScope`:
     `n' ≤ ∑ f, #(branchAugmentedScope S e I P b f)` ($M' \ge n'$).
   - `varIncidence_branchAugmentedScope_le`: for
     `S = heavyVars univ F (fun i => equationScope (P i)) b₀` and `I ⊆ F`, every free variable
     `v : Fin n'` appears in at most `b₀ + 1` scopes of `branchAugmentedScope S e I P b`.
   - `sum_card_branchAugmentedScope_le`: for `S = heavyVars ... b₀` and `I ⊆ F`, total
     branch incidence satisfies `∑ f, #(branchAugmentedScope S e I P b f) ≤ (b₀ + 1) * n'`.
   - `card_branchAugmentedScope_le`: when every active equation `i ∈ I` has scope width at most `w`,
     every factor in `branchAugmentedScope S e I P b` has scope width at most `max w 1`.
2. **Per-branch and uniform Lemma 4.7 + Lemma 4.8 `ReplacementDesign` existence**:
   - `Feasible.exists_branch_replacementDesign`: whenever the schedule parameters at free-variable
     dimension `n'` satisfy `Feasible β n' (b₀ + 1) (max w 1) M'_b`, there exists a concrete
     Section 4 `ReplacementDesign` (and via `Feasible.toCountingDesign`, a Section 3
     `Cslib.ReplacementCounting.Design`) for `branchAugmentedScope S e I P b`.
   - `exists_branch_schedule_replacementDesign`: uniformly for any `1 ≤ β`, there exists `n₀ ≥ 20`
     (from `exists_schedule_replacementDesign`) such that whenever `n' ≥ n₀`,
     `b₀ + 1 ≤ (Nat.clog 2 n') ^ β`, and `max w 1 ≤ (Nat.clog 2 n') ^ β`, **every** branch
     assignment `b : ι → Bool` simultaneously satisfies `Feasible` and admits a concrete
     `ReplacementDesign`, with all four per-branch incidence hypotheses (`n' ≤ M'_b`,
     `M'_b ≤ (b₀ + 1) * n'`, per-variable occurrence `≤ b₀ + 1`, and per-factor width `≤ max w 1`)
     discharged automatically.
3. **Per-branch and branch-summed domain-examination bounds**:
   - `branchDegreeBudget_le`: when `#I ≤ c * Fintype.card ι` and `Fintype.card ι ≤ 2 * n'`, the
     Section 5.3 / 5.5 degree budget `k * (#I + 2 * (branchPrecision (Fintype.card ι) - 1))` is at
     most `(k * (2 * c + 4)) * n'`.
   - `Feasible.branch_domainExaminationBound_le`: bounds the single-branch real domain-examination
     sum at canonical truncation order
     `q = (k * (#I + 2 * (branchPrecision (Fintype.card ι) - 1)) * rowBound β n') / numNodes n'` by
     `2 * numNodes n' * numGroups n' * exp (((k * (2 * c + 4) + 4) : ℝ) * n' * rowCost β n')`.
   - `sum_branch_domainExaminationBound_le`: when
     `S = heavyVars univ F (fun i => equationScope (P i)) b₀` with `1 ≤ b₀`, `2 ≤ s_div`, and
     `totalIncidence F (fun i => equationScope (P i)) * s_div ≤ b₀ * Fintype.card ι` (which holds
     in particular for `paperHeavyThreshold` and `heavyThreshold`), `Fintype.card ι ≤ 2 * n'` holds
     automatically and the sum of the real domain-examination bounds across all
     `b ∈ branchAssignments S` is at most
     `2 ^ (Fintype.card ι / s_div) * (2 * numNodes n' * numGroups n' *`
     `exp (((k * (2 * c + 4) + 4) : ℝ) * n' * rowCost β n'))`.

## Main definitions

* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.branchEquationScope`: variable scope on
  `Fin n'` of a relabeled restricted branch equation.
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.branchAugmentedScope`: neutral-augmented
  scope family on `{i : κ // i ∈ I} ⊕ Fin n'` via `Cslib.BitString.withNeutralScope`.

## Main results

* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.sum_card_branchAugmentedScope`
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.le_sum_card_branchAugmentedScope`
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.varIncidence_branchAugmentedScope_le`
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.sum_card_branchAugmentedScope_le`
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.card_branchAugmentedScope_le`
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.Feasible.exists_branch_replacementDesign`
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.exists_branch_schedule_replacementDesign`
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.Feasible.branch_domainExaminationBound_le`
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.sum_branch_domainExaminationBound_le`

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
  (Section 3.5, pp. 25–26; Section 4.6–4.7, pp. 33–35; Section 5.3 & 5.5, pp. 37–39)
-/

public section

namespace Cslib.Complexity.SubexponentialSAT.ReplacementParams

open Finset
open Cslib.BitString
open Cslib.LinearAlgebra

variable {ι κ : Type*} {n' : ℕ}

/-! ### 1. Per-branch neutral-augmented scope family on `{i : κ // i ∈ I} ⊕ Fin n'` -/

/-- The variable scope on `Fin n'` of equation `i : κ` after specializing `S` to `b` and relabeling
the free variables `univ \ S` along `e : ↥(univ \ S) ≃ Fin n'`. -/
def branchEquationScope [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (e : ↥(univ \ S) ≃ Fin n') (P : κ → Finset (Finset ι)) (b : ι → Bool) (i : κ) :
    Finset (Fin n') :=
  equationScope (relabelRestrictedMonomials S e b (P i))

/-- The Section 5.5 neutral-augmented scope family on `{i : κ // i ∈ I} ⊕ Fin n'`, defined by
applying `Cslib.BitString.withNeutralScope` to `branchEquationScope` on the subtype
`{i : κ // i ∈ I}` of active equations. -/
def branchAugmentedScope [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (e : ↥(univ \ S) ≃ Fin n') (I : Finset κ) (P : κ → Finset (Finset ι))
    (b : ι → Bool) : {i : κ // i ∈ I} ⊕ Fin n' → Finset (Fin n') :=
  withNeutralScope fun i : {i : κ // i ∈ I} => branchEquationScope S e P b i.1

@[simp]
theorem branchAugmentedScope_inl [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (e : ↥(univ \ S) ≃ Fin n') (I : Finset κ) (P : κ → Finset (Finset ι))
    (b : ι → Bool) (i : {i : κ // i ∈ I}) :
    branchAugmentedScope S e I P b (Sum.inl i) = branchEquationScope S e P b i.1 := by
  unfold branchAugmentedScope withNeutralScope
  rfl

@[simp]
theorem branchAugmentedScope_inr [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (e : ↥(univ \ S) ≃ Fin n') (I : Finset κ) (P : κ → Finset (Finset ι))
    (b : ι → Bool) (v : Fin n') :
    branchAugmentedScope S e I P b (Sum.inr v) = {v} := by
  unfold branchAugmentedScope withNeutralScope
  rfl

/-- Subtype-sum bridge: `totalIncidence` on `univ : Finset {i : κ // i ∈ I}` equals
`totalIncidence` on `I`. -/
private theorem totalIncidence_univ_subtype (I : Finset κ) (scope : κ → Finset (Fin n')) :
    totalIncidence (univ : Finset {i : κ // i ∈ I}) (fun i => scope i.1) =
      totalIncidence I scope := by
  unfold totalIncidence
  rw [← sum_coe_sort I (fun i => #(scope i))]

/-- Subtype-filter bridge: `varIncidence` on `univ : Finset {i : κ // i ∈ I}` equals
`varIncidence` on `I`. -/
private theorem varIncidence_univ_subtype (I : Finset κ) (scope : κ → Finset (Fin n'))
    (v : Fin n') :
    varIncidence (univ : Finset {i : κ // i ∈ I}) (fun i => scope i.1) v =
      varIncidence I scope v := by
  unfold varIncidence
  rw [card_eq_sum_ones, card_eq_sum_ones, sum_filter, sum_filter,
    ← sum_coe_sort I (fun i => if v ∈ scope i then 1 else 0)]

/-- The full `Fintype` finset `univ : Finset ({i : κ // i ∈ I} ⊕ Fin n')` coincides with
`withNeutralFactors (univ : Finset {i : κ // i ∈ I})`. -/
private theorem univ_sum_eq_withNeutralFactors (I : Finset κ) (n' : ℕ) :
    (univ : Finset ({i : κ // i ∈ I} ⊕ Fin n')) =
      withNeutralFactors (univ : Finset {i : κ // i ∈ I}) := by
  ext f
  simp only [withNeutralFactors, mem_disjSum, mem_univ, true_and, true_iff]
  cases f with
  | inl i => exact Or.inl ⟨i, rfl⟩
  | inr v => exact Or.inr ⟨v, rfl⟩

/-- **Section 5.5 ($M' = \sum_{i \in I} |I'_i| + n'$):** the total factor-variable incidence of
`branchAugmentedScope` equals `totalIncidence I (branchEquationScope S e P b) + n'`. -/
theorem sum_card_branchAugmentedScope [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (e : ↥(univ \ S) ≃ Fin n') (I : Finset κ) (P : κ → Finset (Finset ι)) (b : ι → Bool) :
    (∑ f : {i : κ // i ∈ I} ⊕ Fin n', #(branchAugmentedScope S e I P b f)) =
      totalIncidence I (branchEquationScope S e P b) + n' := by
  change totalIncidence (univ : Finset ({i : κ // i ∈ I} ⊕ Fin n'))
      (branchAugmentedScope S e I P b) =
    totalIncidence I (branchEquationScope S e P b) + n'
  rw [univ_sum_eq_withNeutralFactors, branchAugmentedScope, totalIncidence_withNeutralFactors,
    totalIncidence_univ_subtype, Fintype.card_fin]

/-- **Section 5.5 ($M' \ge n'$):** adjoining the neutral singleton scopes ensures that total branch
incidence is at least `n'`. -/
theorem le_sum_card_branchAugmentedScope [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (e : ↥(univ \ S) ≃ Fin n') (I : Finset κ) (P : κ → Finset (Finset ι)) (b : ι → Bool) :
    n' ≤ ∑ f : {i : κ // i ∈ I} ⊕ Fin n', #(branchAugmentedScope S e I P b f) := by
  rw [sum_card_branchAugmentedScope]
  exact Nat.le_add_left _ _

/-- The number of factors in `branchAugmentedScope S e I P b` containing `v : Fin n'` equals
`varIncidence I (branchEquationScope S e P b) v + 1`. -/
theorem varIncidence_branchAugmentedScope [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (e : ↥(univ \ S) ≃ Fin n') (I : Finset κ) (P : κ → Finset (Finset ι)) (b : ι → Bool)
    (v : Fin n') :
    #{f : {i : κ // i ∈ I} ⊕ Fin n' | v ∈ branchAugmentedScope S e I P b f} =
      varIncidence I (branchEquationScope S e P b) v + 1 := by
  change varIncidence (univ : Finset ({i : κ // i ∈ I} ⊕ Fin n'))
      (branchAugmentedScope S e I P b) v =
    varIncidence I (branchEquationScope S e P b) v + 1
  rw [univ_sum_eq_withNeutralFactors, branchAugmentedScope, varIncidence_withNeutralFactors,
    varIncidence_univ_subtype]

/-- **Section 5.5 (free-variable occurrence $\le b_0 + 1$ after branching on `heavyVars`):**
for `S = heavyVars univ F (fun i => equationScope (P i)) b₀` and `I ⊆ F`, every free variable
`v : Fin n'` belongs to at most `b₀ + 1` scopes of `branchAugmentedScope S e I P b`. -/
theorem varIncidence_branchAugmentedScope_le [Fintype ι] [DecidableEq ι]
    (F I : Finset κ) (P : κ → Finset (Finset ι)) (b₀ : ℕ) (hIF : I ⊆ F)
    (e : ↥(univ \ heavyVars univ F (fun i => equationScope (P i)) b₀) ≃ Fin n')
    (b : ι → Bool) (v : Fin n') :
    #{f : {i : κ // i ∈ I} ⊕ Fin n' |
        v ∈ branchAugmentedScope (heavyVars univ F (fun i => equationScope (P i)) b₀)
          e I P b f} ≤ b₀ + 1 := by
  rw [varIncidence_branchAugmentedScope]
  exact Nat.add_le_add_right
    (varIncidence_relabelRestrictedMonomials_heavyVars_le F I P b₀ hIF e b v) 1

/-- **Section 5.5 ($M' \le (b_0 + 1) n'$ after branching on `heavyVars`):**
for `S = heavyVars univ F (fun i => equationScope (P i)) b₀` and `I ⊆ F`, the total incidence of
`branchAugmentedScope S e I P b` is at most `(b₀ + 1) * n'`. -/
theorem sum_card_branchAugmentedScope_le [Fintype ι] [DecidableEq ι]
    (F I : Finset κ) (P : κ → Finset (Finset ι)) (b₀ : ℕ) (hIF : I ⊆ F)
    (e : ↥(univ \ heavyVars univ F (fun i => equationScope (P i)) b₀) ≃ Fin n')
    (b : ι → Bool) :
    (∑ f : {i : κ // i ∈ I} ⊕ Fin n',
        #(branchAugmentedScope (heavyVars univ F (fun i => equationScope (P i)) b₀)
          e I P b f)) ≤ (b₀ + 1) * n' := by
  let scope := branchAugmentedScope (heavyVars univ F (fun i => equationScope (P i)) b₀) e I P b
  have hdouble :
      (∑ f : {i : κ // i ∈ I} ⊕ Fin n', #(scope f)) =
        ∑ v : Fin n', #{f : {i : κ // i ∈ I} ⊕ Fin n' | v ∈ scope f} := by
    simpa only [totalIncidence, varIncidence] using
      (sum_varIncidence_eq_totalIncidence (univ : Finset (Fin n'))
        (univ : Finset ({i : κ // i ∈ I} ⊕ Fin n')) scope (fun _ _ => subset_univ _)).symm
  rw [hdouble]
  calc ∑ v : Fin n', #{f : {i : κ // i ∈ I} ⊕ Fin n' | v ∈ scope f}
      ≤ ∑ _v : Fin n', (b₀ + 1) :=
        sum_le_sum fun v _ =>
          varIncidence_branchAugmentedScope_le F I P b₀ hIF e b v
    _ = (b₀ + 1) * n' := by
        rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

/-- Specializing `S` and relabeling along `e` never increases the scope cardinality of an equation:
`#(branchEquationScope S e P b i) ≤ #(equationScope (P i))`. -/
theorem card_branchEquationScope_le [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (e : ↥(univ \ S) ≃ Fin n') (P : κ → Finset (Finset ι)) (b : ι → Bool) (i : κ) :
    #(branchEquationScope S e P b i) ≤ #(equationScope (P i)) := by
  unfold branchEquationScope
  calc #(equationScope (relabelRestrictedMonomials S e b (P i)))
      ≤ #(((equationScope (P i) \ S).subtype (· ∈ univ \ S)).image e) :=
        card_le_card (equationScope_relabelRestrictedMonomials_subset S e b (P i))
    _ ≤ #((equationScope (P i) \ S).subtype (· ∈ univ \ S)) := card_image_le
    _ = #((equationScope (P i) \ S).filter (· ∈ univ \ S)) := card_subtype _ _
    _ ≤ #(equationScope (P i) \ S) := card_filter_le _ _
    _ ≤ #(equationScope (P i)) := card_le_card sdiff_subset

/-- **Section 5.5 (per-factor scope width $\le \max(w, 1)$):** if every active equation `i ∈ I` has
`#(equationScope (P i)) ≤ w`, then every factor `f` of `branchAugmentedScope S e I P b` has scope
cardinality at most `max w 1`. -/
theorem card_branchAugmentedScope_le [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (e : ↥(univ \ S) ≃ Fin n') (I : Finset κ) (P : κ → Finset (Finset ι)) (b : ι → Bool)
    {w : ℕ} (hw : ∀ i ∈ I, #(equationScope (P i)) ≤ w)
    (f : {i : κ // i ∈ I} ⊕ Fin n') :
    #(branchAugmentedScope S e I P b f) ≤ max w 1 := by
  cases f with
  | inl i =>
    rw [branchAugmentedScope_inl]
    exact ((card_branchEquationScope_le S e P b i.1).trans (hw i.1 i.2)).trans (le_max_left w 1)
  | inr v =>
    rw [branchAugmentedScope_inr, card_singleton]
    exact le_max_right w 1

/-! ### 2. Per-branch and uniform Lemma 4.7 + Lemma 4.8 `ReplacementDesign` existence -/

/-- **Section 5.5 per-branch `ReplacementDesign` existence**:
Given `S = heavyVars univ F (fun i => equationScope (P i)) b₀`, `I ⊆ F`,
`e : ↥(univ \ S) ≃ Fin n'`, `∀ i ∈ I, #(equationScope (P i)) ≤ w`, and
`hF : Feasible β n' (b₀ + 1) (max w 1) (∑ f, #(branchAugmentedScope S e I P b f))`, there exists a
concrete Section 4 `ReplacementDesign` for `branchAugmentedScope S e I P b` at the Lemma 4.8
parameter schedule `(numNodes n', numGroups n', intervalStart β n', rowBound β n', tauRat n')`. -/
theorem Feasible.exists_branch_replacementDesign [Fintype ι] [DecidableEq ι]
    {β b₀ w : ℕ} (F I : Finset κ) (P : κ → Finset (Finset ι)) (hIF : I ⊆ F)
    (e : ↥(univ \ heavyVars univ F (fun i => equationScope (P i)) b₀) ≃ Fin n')
    (b : ι → Bool) (hw : ∀ i ∈ I, #(equationScope (P i)) ≤ w)
    (hF : Feasible β n' (b₀ + 1) (max w 1)
      (∑ f : {i : κ // i ∈ I} ⊕ Fin n',
        #(branchAugmentedScope (heavyVars univ F (fun i => equationScope (P i)) b₀)
          e I P b f))) :
    Nonempty
      (ReplacementDesign
        (branchAugmentedScope (heavyVars univ F (fun i => equationScope (P i)) b₀) e I P b)
        (numNodes n') (numGroups n') (intervalStart β n') (rowBound β n') (tauRat n')) :=
  Feasible.exists_replacementDesign
    (branchAugmentedScope (heavyVars univ F (fun i => equationScope (P i)) b₀) e I P b)
    hF (Nat.succ_pos b₀) (le_max_right w 1)
    (varIncidence_branchAugmentedScope_le F I P b₀ hIF e b)
    (card_branchAugmentedScope_le _ e I P b hw)
    (sum_card_branchAugmentedScope_le F I P b₀ hIF e b)

/-- **Uniform Section 5.5 Theorem 2.2 per-branch schedule feasibility and design existence**:
For every integer `1 ≤ β`, there exists `n₀ ≥ 20` such that whenever the free-variable count
`n'` after removing `S = heavyVars univ F (fun i => equationScope (P i)) b₀` satisfies `n₀ ≤ n'`,
`b₀ + 1 ≤ (Nat.clog 2 n') ^ β`, `max w 1 ≤ (Nat.clog 2 n') ^ β`, `I ⊆ F`, and
`∀ i ∈ I, #(equationScope (P i)) ≤ w`, **every** branch assignment `b : ι → Bool` simultaneously
satisfies `Feasible` and admits a concrete `ReplacementDesign` for `branchAugmentedScope S e I P b`
(with all per-branch incidence bounds `n' ≤ M'_b ≤ (b₀ + 1) * n'` discharged automatically). -/
theorem exists_branch_schedule_replacementDesign {β : ℕ} (hβ : 1 ≤ β) :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧
      ∀ {ι κ : Type*} [Fintype ι] [DecidableEq ι]
        ⦃n' b₀ w : ℕ⦄ (F I : Finset κ) (P : κ → Finset (Finset ι)), I ⊆ F →
        ∀ (e : ↥(univ \ heavyVars univ F (fun i => equationScope (P i)) b₀) ≃ Fin n'),
          n₀ ≤ n' →
          b₀ + 1 ≤ Nat.clog 2 n' ^ β →
          max w 1 ≤ Nat.clog 2 n' ^ β →
          (∀ i ∈ I, #(equationScope (P i)) ≤ w) →
          ∀ b : ι → Bool,
            Feasible β n' (b₀ + 1) (max w 1)
              (∑ f : {i : κ // i ∈ I} ⊕ Fin n',
                #(branchAugmentedScope
                  (heavyVars univ F (fun i => equationScope (P i)) b₀) e I P b f)) ∧
              Nonempty
                (ReplacementDesign
                  (branchAugmentedScope
                    (heavyVars univ F (fun i => equationScope (P i)) b₀) e I P b)
                  (numNodes n') (numGroups n') (intervalStart β n')
                  (rowBound β n') (tauRat n')) := by
  obtain ⟨n₀, hn₀20, hsched⟩ := exists_schedule_replacementDesign hβ
  refine ⟨n₀, hn₀20,
    fun {ι κ _ _ n' b₀ w} F I P hIF e hn' hb₀ hw_pow hw b => ?_⟩
  exact @hsched n' (b₀ + 1) (max w 1) ({i : κ // i ∈ I} ⊕ Fin n') _
    (branchAugmentedScope (heavyVars univ F (fun i => equationScope (P i)) b₀) e I P b)
    hn' (Nat.succ_pos b₀) hb₀ (le_max_right w 1) hw_pow
    (le_sum_card_branchAugmentedScope _ e I P b)
    (sum_card_branchAugmentedScope_le F I P b₀ hIF e b)
    (varIncidence_branchAugmentedScope_le F I P b₀ hIF e b)
    (card_branchAugmentedScope_le _ e I P b hw)

/-! ### 3. Section 5.5 per-branch and multi-branch domain-examination bounds -/

/-- **Section 5.3 & 5.5 ($d = k(m_{\mathrm{test}} + 2(\ell - 1)) \le k(2c + 4)n'$):**
when `m ≤ c * n` and `n ≤ 2 * n'`, the equation-product degree budget
`k * (m + 2 * (branchPrecision n - 1))` at original precision `branchPrecision n = n + 1` is at
most `(k * (2 * c + 4)) * n'`. -/
theorem branchDegreeBudget_le {k m c n : ℕ} (hm : m ≤ c * n) (hn : n ≤ 2 * n') :
    k * (m + 2 * (branchPrecision n - 1)) ≤ (k * (2 * c + 4)) * n' := by
  calc k * (m + 2 * (branchPrecision n - 1))
      ≤ k * ((2 * c + 4) * n') := Nat.mul_le_mul_left k (branchEquationBudget_le hm hn)
    _ = (k * (2 * c + 4)) * n' := (Nat.mul_assoc k (2 * c + 4) n').symm

/-- **Section 5.5 ($n \le 2n'$ from heavy-variable branching with $s \ge 2$):**
whenever `1 ≤ b₀`, `2 ≤ s_div`, `totalIncidence F scope * s_div ≤ b₀ * Fintype.card ι`, and
`e : ↥(univ \ heavyVars univ F scope b₀) ≃ Fin n'`, the original variable count satisfies
`Fintype.card ι ≤ 2 * n'` and `Fintype.card ι / 2 ≤ n'`. -/
theorem card_le_two_mul_freeVar_of_heavyVars [Fintype ι] [DecidableEq ι]
    (F : Finset κ) (scope : κ → Finset ι) {b₀ s_div : ℕ}
    (hb₀ : 1 ≤ b₀) (hs : 2 ≤ s_div)
    (hM : totalIncidence F scope * s_div ≤ b₀ * Fintype.card ι)
    (e : ↥(univ \ heavyVars univ F scope b₀) ≃ Fin n') :
    Fintype.card ι ≤ 2 * n' ∧ Fintype.card ι / 2 ≤ n' := by
  have hcard : #(univ \ heavyVars univ F scope b₀) = n' := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hhalf := card_sdiff_heavyVars_ge_half univ F scope hb₀ hs
    (fun _ _ => subset_univ _) (by simpa only [card_univ] using hM)
  rw [card_univ, hcard] at hhalf
  exact hhalf

/-- **Section 5.5 single-branch domain-examination bound**:
For any branch `b` with `hF : Feasible β n' b_occ w_width M'` and concrete schedule design `D`, if
`#I ≤ c * Fintype.card ι` and `Fintype.card ι ≤ 2 * n'`, then at the Section 5.3 / 5.5 degree
budget `d = k * (#I + 2 * (branchPrecision (Fintype.card ι) - 1))` and canonical truncation order
`q = (d * rowBound β n') / numNodes n'`, the induced Section 3 counting design
`C := hF.toCountingDesign D s` satisfies
`(∑ t : Fin (numNodes n'), (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
  (2 * (#(C.measurementBox t) : ℝ) *
    ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ)))
  ≤ 2 * numNodes n' * numGroups n' * exp (((k * (2 * c + 4) + 4 : ℕ) : ℝ) * n' * rowCost β n')`. -/
theorem Feasible.branch_domainExaminationBound_le [Fintype ι]
    {F_idx : Type*} [Fintype F_idx] {scope : F_idx → Finset (Fin n')}
    {β b_occ w_width M' k c : ℕ} (I : Finset κ)
    (hF : Feasible β n' b_occ w_width M')
    (D : ReplacementDesign scope (numNodes n') (numGroups n') (intervalStart β n')
      (rowBound β n') (tauRat n'))
    (s : Finset F_idx) (hm : #I ≤ c * Fintype.card ι) (hn : Fintype.card ι ≤ 2 * n') :
    let d := k * (#I + 2 * (branchPrecision (Fintype.card ι) - 1))
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
    exact_mod_cast branchDegreeBudget_le (k := k) hm hn
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

/-- **Section 5.5 Theorem 2.2 multi-branch domain-examination bound across `branchAssignments S`**:
When `S = heavyVars univ F (fun i => equationScope (P i)) b₀` with `1 ≤ b₀`, `2 ≤ s_div`,
`totalIncidence F (fun i => equationScope (P i)) * s_div ≤ b₀ * Fintype.card ι`, and
`e : ↥(univ \ S) ≃ Fin n'`, the free-variable dimension satisfies `Fintype.card ι ≤ 2 * n'`, there
are at most `2 ^ (Fintype.card ι / s_div)` branches in `branchAssignments S`, and if each branch
`b ∈ branchAssignments S` has its real examination sum bounded via
`Feasible.branch_domainExaminationBound_le`, then the sum of those examination bounds across all
`b ∈ branchAssignments S` is at most
`(2 : ℝ) ^ (Fintype.card ι / s_div) * (2 * numNodes n' * numGroups n' *
  exp (((k * (2 * c + 4) + 4 : ℕ) : ℝ) * n' * rowCost β n'))`. -/
theorem sum_branch_domainExaminationBound_le [Fintype ι] [DecidableEq ι]
    (F : Finset κ) (P : κ → Finset (Finset ι)) {β b₀ s_div k c : ℕ}
    (hb₀ : 1 ≤ b₀) (hs_div : 2 ≤ s_div)
    (hM : totalIncidence F (fun i => equationScope (P i)) * s_div ≤ b₀ * Fintype.card ι)
    (e : ↥(univ \ heavyVars univ F (fun i => equationScope (P i)) b₀) ≃ Fin n')
    (examSum : (ι → Bool) → ℝ)
    (hexam : ∀ b ∈ branchAssignments (heavyVars univ F (fun i => equationScope (P i)) b₀),
      examSum b ≤
        2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
          Real.exp (((k * (2 * c + 4) + 4 : ℕ) : ℝ) * (n' : ℝ) * rowCost β n')) :
    Fintype.card ι ≤ 2 * n' ∧
    (∑ b ∈ branchAssignments (heavyVars univ F (fun i => equationScope (P i)) b₀), examSum b) ≤
      (2 : ℝ) ^ (Fintype.card ι / s_div) *
        (2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
          Real.exp (((k * (2 * c + 4) + 4 : ℕ) : ℝ) * (n' : ℝ) * rowCost β n')) := by
  have hn :=
    (card_le_two_mul_freeVar_of_heavyVars F (fun i => equationScope (P i)) hb₀ hs_div hM e).1
  refine ⟨hn, ?_⟩
  let S := heavyVars univ F (fun i => equationScope (P i)) b₀
  let B := 2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
    Real.exp (((k * (2 * c + 4) + 4 : ℕ) : ℝ) * (n' : ℝ) * rowCost β n')
  have hB_nn : 0 ≤ B := by positivity
  have hcard : (#(branchAssignments S) : ℝ) ≤ (2 : ℝ) ^ (Fintype.card ι / s_div) := by
    exact_mod_cast card_branchAssignments_heavyVars_le_two_pow_div F
      (fun i => equationScope (P i)) hb₀ (by omega) hM
  calc ∑ b ∈ branchAssignments S, examSum b
      ≤ ∑ _b ∈ branchAssignments S, B := sum_le_sum hexam
    _ = (#(branchAssignments S) : ℝ) * B := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ (Fintype.card ι / s_div) * B := mul_le_mul_of_nonneg_right hcard hB_nn

end Cslib.Complexity.SubexponentialSAT.ReplacementParams
