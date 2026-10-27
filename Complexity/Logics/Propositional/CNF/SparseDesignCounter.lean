/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.SparseReplacementDesign
public import Complexity.Logics.Propositional.CNF.SparseParityCounter

/-!
# Replacement-Design Specialization of Sparse Parity Model Counting for CNF Formulas

This module connects the compiled CNF parity-test equation systems and greedy zero-counting
reduction of Sections 6.1–6.3 (`Complexity.Logics.Propositional.CNF.SparseParityCounter`) directly
with the Section 4 algebraic replacement design specialization of Sections 5.3–5.5 and Appendix B.2
(`Complexity.Foundations.BooleanAnalysis.SparseReplacementDesign`) of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (printed pp. 37–43, 48–50):

1. **Branch-restricted CNF parity systems and neutral singleton scopes (§5.5 & §6.2–6.3)**:
   Given `φ : CNF V`, parity-check rows `rows : List (Fin φ.length → Bool)`, a heavy-variable subset
   `S : Finset V`, a free-variable equivalence `e : ↥(univ \ S) ≃ Fin n'`, and a branch assignment
   `b : V → Bool`:
   - `CNF.branchParityRowSystem φ rows S e b : Fin rows.length → Finset (Finset (Fin n'))` restricts
     each compiled parity equation `φ.parityRowSystem rows j` to `S` under `b` (cancelling duplicate
     monomials modulo `2`) and relabels the remaining free variables along `e`.
   - `CNF.branchParityRowScope φ rows S e b` is its variable-scope family on `Fin n'`, and
     `CNF.branchParityRowNeutralScope φ rows S e b : Fin rows.length ⊕ Fin n' → Finset (Fin n')`
     augments those scopes with one neutral singleton scope `{v}` per free variable `v : Fin n'` via
     `withNeutralScope`.
   - When every clause of `φ` has width at most `k` and every row in `rows` has Hamming weight at
     most `W`, each branch equation has degree at most `k`, at most `W * 2 ^ k` monomials, and
     scope size at most `k * (W * 2 ^ k)`. On the canonical heavy-variable set
     `S = heavyVars univ univ (fun j => equationScope (φ.parityRowSystem rows j)) b₀`, every free
     variable `v : Fin n'` belongs to at most `b₀ + 1` scopes of `branchParityRowNeutralScope`,
     total branch incidence satisfies `n' ≤ M'_b ≤ (b₀ + 1) * n'`, and Lemma 4.7 supplies a
     concrete `ReplacementDesign` (`CNF.exists_replacementDesign_branchParityRowNeutralScope`).

2. **Per-branch factor locality, polynomial degree, and coordinate `coeffNorm1` bounds (§5.3–5.4 &
   Appendix B.2)**:
   For any `D : ReplacementDesign (φ.branchParityRowNeutralScope rows S e b) Q r A₀ R τ`,
   instantiating `SparseReplacementDesign` with `emb = Sum.inl` automatically discharges the
   monomial-degree (`#M ≤ k`), monomial-count (`#(P j) ≤ W * 2 ^ k`), and scope-containment
   (`equationScope (P j) ⊆ scope (Sum.inl j)`) premises from `∀ c ∈ φ, c.length ≤ k` and
   `∀ r ∈ rows, weight r ≤ W`, yielding:
   - node-point factor locality
     (`CNF.eval_univariateMonomialSumPoly_branchParityRowSystem_nodePoint_eq`),
   - the equation (5.5) degree bound `(k * (R - 1)) * (rows.length + 2 * (ℓ - 1))`
     (`CNF.natDegree_univariateClearedParityCoord_branchParityRowSystem_le`,
     `CNF.natDegree_univariateClearedParityTruncatedSum_branchParityRowSystem_le`), and
   - the Appendix B.2 coordinate `ℓ₁`-norm bound with `S_mon = W * 2 ^ k`
     (`CNF.coeffNorm1_univariateClearedParityCoord_branchParityRowSystem_le`).

3. **Exact branch-summed `ReplacementDesign` recovery of `commonZeroCount`, `numPassing`, and
   `φ.modelCountOn Finset.univ` (§5.4–5.5 & §6.2–6.3)**:
   Eliminating the abstract replacement-map hypotheses `d_den`, `θ`, and `hθ` of
   `SparseParityCounter`, any per-branch family of replacement designs `D b` recovers
   `commonZeroCount univ (φ.parityRowSystem rows) = numPassing φ.violations rows` via
   branch-summed evaluation at `T = 0`
   (`CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design`,
   `CNF.numPassing_eq_sum_branch_emod_ediv_design`), and recovers `φ.modelCountOn Finset.univ` on
   the nose after `3 * Fintype.card V` greedy rounds
   (`CNF.modelCountOn_eq_sum_branch_emod_ediv_design_greedy`,
   `CNF.exists_initialTests_modelCountOn_eq_sum_branch_emod_ediv_design_greedy`), with
   `max D₀ P` simplified unconditionally to `D₀ = initialRowWeightBound B φ.length`
   (`CNF.max_initialRowWeightBound_greedyRowListLength`).

## Main definitions

* `Cslib.Logic.PL.CNF.branchParityRowSystem`: branch-restricted and relabeled `𝔽₂` polynomial system
  `fun j => relabelRestrictedMonomials S e b (φ.parityRowSystem rows j)`.
* `Cslib.Logic.PL.CNF.branchParityRowScope`: variable-scope family of `branchParityRowSystem`.
* `Cslib.Logic.PL.CNF.branchParityRowNeutralScope`: neutral-singleton augmented scope family
  `withNeutralScope (φ.branchParityRowScope rows S e b)`.

## Main results

* `Cslib.Logic.PL.CNF.card_mem_branchParityRowSystem_le`,
  `Cslib.Logic.PL.CNF.card_branchParityRowSystem_le`,
  `Cslib.Logic.PL.CNF.card_branchParityRowScope_le`,
  `Cslib.Logic.PL.CNF.card_branchParityRowNeutralScope_le`: per-branch monomial degree, sparsity,
  and scope-width bounds from clause width `≤ k` and row weight `≤ W`.
* `Cslib.Logic.PL.CNF.varIncidence_branchParityRowNeutralScope_heavyVars_le`,
  `Cslib.Logic.PL.CNF.totalIncidence_branchParityRowNeutralScope_heavyVars_le`,
  `Cslib.Logic.PL.CNF.exists_replacementDesign_branchParityRowNeutralScope`: post-branching
  free-variable incidence bounds and Lemma 4.7 `ReplacementDesign` existence on each branch.
* `Cslib.Logic.PL.CNF.eval_univariateMonomialSumPoly_branchParityRowSystem_nodePoint_eq`,
  `Cslib.Logic.PL.CNF.natDegree_univariateClearedParityCoord_branchParityRowSystem_le`,
  `Cslib.Logic.PL.CNF.natDegree_univariateClearedParityTruncatedSum_branchParityRowSystem_le`,
  `Cslib.Logic.PL.CNF.coeffNorm1_univariateClearedParityCoord_branchParityRowSystem_le`: per-branch
  locality, degree, and `coeffNorm1` bounds for a `ReplacementDesign`.
* `Cslib.Logic.PL.CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design`,
  `Cslib.Logic.PL.CNF.numPassing_eq_sum_branch_emod_ediv_design`,
  `Cslib.Logic.PL.CNF.modelCountOn_eq_sum_branch_emod_ediv_design_greedy`,
  `Cslib.Logic.PL.CNF.max_initialRowWeightBound_greedyRowListLength`,
  `Cslib.Logic.PL.CNF.exists_initialTests_modelCountOn_eq_sum_branch_emod_ediv_design_greedy`:
  end-to-end `ReplacementDesign` recovery of `commonZeroCount`, `numPassing`, and
  `φ.modelCountOn Finset.univ`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (Sections 5.3–5.5 and 6.1–6.3,
  printed pp. 37–43, 48–50)
-/

@[expose] public noncomputable section

namespace Cslib.Logic.PL

open Finset Polynomial Cslib.BitString Cslib.BalancedSchedules Cslib.LinearAlgebra
open scoped BigOperators

variable {V : Type*}

/-! ### 1. Branch-restricted CNF parity systems and neutral singleton scopes -/

section BranchParityRowSystem

variable [Fintype V] [DecidableEq V] {n' : ℕ}

/-- The `Fin rows.length`-indexed sparse `𝔽₂` polynomial system on `Fin n'` obtained from
`φ.parityRowSystem rows` by fixing `S : Finset V` to `b : V → Bool` (cancelling duplicate
monomials modulo `2`) and relabeling `univ \ S ≃ Fin n'` along `e`
([OpenAI2026ETH], §5.5 & §6.3, pp. 38–39, 43). -/
def CNF.branchParityRowSystem (φ : CNF V) (rows : List (Fin φ.length → Bool))
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n') (b : V → Bool)
    (j : Fin rows.length) : Finset (Finset (Fin n')) :=
  relabelRestrictedMonomials S e b (φ.parityRowSystem rows j)

/-- The variable scope `equationScope (φ.branchParityRowSystem rows S e b j) : Finset (Fin n')` of
restricted parity equation `j` on branch `b`. -/
def CNF.branchParityRowScope (φ : CNF V) (rows : List (Fin φ.length → Bool))
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n') (b : V → Bool)
    (j : Fin rows.length) : Finset (Fin n') :=
  equationScope (φ.branchParityRowSystem rows S e b j)

/-- The neutral-singleton augmented scope family on `Fin rows.length ⊕ Fin n'` associated to
`φ.branchParityRowScope rows S e b` ([OpenAI2026ETH], §5.3 & §5.5, pp. 37–38). -/
def CNF.branchParityRowNeutralScope (φ : CNF V) (rows : List (Fin φ.length → Bool))
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n') (b : V → Bool) :
    Fin rows.length ⊕ Fin n' → Finset (Fin n') :=
  withNeutralScope (φ.branchParityRowScope rows S e b)

/-- Every monomial in `φ.branchParityRowSystem rows S e b j` has degree at most `k` whenever every
clause of `φ` has width at most `k`. -/
theorem CNF.card_mem_branchParityRowSystem_le {φ : CNF V} {k : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (rows : List (Fin φ.length → Bool))
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n') (b : V → Bool)
    (j : Fin rows.length) {M : Finset (Fin n')}
    (hM : M ∈ φ.branchParityRowSystem rows S e b j) :
    #M ≤ k :=
  card_mem_relabelRestrictedMonomials_le
    (fun _M₀ hM₀ => CNF.card_mem_parityRowSystem_le hk rows j hM₀) M hM

/-- Every branch equation `φ.branchParityRowSystem rows S e b j` contains at most `W * 2 ^ k`
monomials whenever every clause of `φ` has width at most `k` and every row in `rows` has Hamming
weight at most `W`. -/
theorem CNF.card_branchParityRowSystem_le {φ : CNF V} {k W : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) {rows : List (Fin φ.length → Bool)}
    (hW : ∀ r ∈ rows, weight r ≤ W) (S : Finset V) (e : ↥(univ \ S) ≃ Fin n')
    (b : V → Bool) (j : Fin rows.length) :
    #(φ.branchParityRowSystem rows S e b j) ≤ W * 2 ^ k :=
  (card_relabelRestrictedMonomials_le S e b (φ.parityRowSystem rows j)).trans
    (CNF.card_parityRowSystem_le hk hW j)

/-- Every branch equation scope `φ.branchParityRowScope rows S e b j` has size at most
`k * (W * 2 ^ k)` whenever every clause of `φ` has width at most `k` and every row in `rows` has
Hamming weight at most `W`. -/
theorem CNF.card_branchParityRowScope_le {φ : CNF V} {k W : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) {rows : List (Fin φ.length → Bool)}
    (hW : ∀ r ∈ rows, weight r ≤ W) (S : Finset V) (e : ↥(univ \ S) ≃ Fin n')
    (b : V → Bool) (j : Fin rows.length) :
    #(φ.branchParityRowScope rows S e b j) ≤ k * (W * 2 ^ k) :=
  (card_equationScope_le (fun _ hM =>
    CNF.card_mem_branchParityRowSystem_le hk rows S e b j hM)).trans
    (Nat.mul_le_mul_left k (CNF.card_branchParityRowSystem_le hk hW S e b j))

/-- Every factor in `φ.branchParityRowNeutralScope rows S e b` has scope width at most
`max 1 (k * (W * 2 ^ k))` whenever every clause of `φ` has width at most `k` and every row in
`rows` has Hamming weight at most `W`. -/
theorem CNF.card_branchParityRowNeutralScope_le {φ : CNF V} {k W : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) {rows : List (Fin φ.length → Bool)}
    (hW : ∀ r ∈ rows, weight r ≤ W) (S : Finset V) (e : ↥(univ \ S) ≃ Fin n')
    (b : V → Bool) (f : Fin rows.length ⊕ Fin n') :
    #(φ.branchParityRowNeutralScope rows S e b f) ≤ max 1 (k * (W * 2 ^ k)) :=
  card_withNeutralScope_le (le_max_left 1 _)
    (fun j => (CNF.card_branchParityRowScope_le hk hW S e b j).trans (le_max_right 1 _)) f

/-- Total factor–variable incidence of `φ.branchParityRowNeutralScope rows S e b` equals
`totalIncidence univ (φ.branchParityRowScope rows S e b) + n'`. -/
theorem CNF.totalIncidence_branchParityRowNeutralScope_eq (φ : CNF V)
    (rows : List (Fin φ.length → Bool)) (S : Finset V) (e : ↥(univ \ S) ≃ Fin n')
    (b : V → Bool) :
    totalIncidence (univ : Finset (Fin rows.length ⊕ Fin n'))
        (φ.branchParityRowNeutralScope rows S e b) =
      totalIncidence (univ : Finset (Fin rows.length))
        (φ.branchParityRowScope rows S e b) + n' := by
  rw [CNF.branchParityRowNeutralScope, ← withNeutralFactors_univ,
    totalIncidence_withNeutralFactors, Fintype.card_fin]

/-- Neutral singleton factors ensure `n' ≤ M'_b` on every branch `b` ([OpenAI2026ETH], §5.5,
p. 38). -/
theorem CNF.le_totalIncidence_branchParityRowNeutralScope (φ : CNF V)
    (rows : List (Fin φ.length → Bool)) (S : Finset V) (e : ↥(univ \ S) ≃ Fin n')
    (b : V → Bool) :
    n' ≤ totalIncidence (univ : Finset (Fin rows.length ⊕ Fin n'))
      (φ.branchParityRowNeutralScope rows S e b) := by
  rw [CNF.totalIncidence_branchParityRowNeutralScope_eq]
  exact Nat.le_add_left n' _

/-- When `S = heavyVars univ univ (fun j => equationScope (φ.parityRowSystem rows j)) b₀`, every
free variable `v : Fin n'` occurs in at most `b₀` restricted equation scopes of
`φ.branchParityRowScope rows S e b`. -/
theorem CNF.varIncidence_branchParityRowScope_heavyVars_le (φ : CNF V)
    (rows : List (Fin φ.length → Bool)) (b₀ : ℕ)
    (e : ↥(univ \ heavyVars univ (univ : Finset (Fin rows.length))
      (fun j => equationScope (φ.parityRowSystem rows j)) b₀) ≃ Fin n')
    (b : V → Bool) (v : Fin n') :
    varIncidence (univ : Finset (Fin rows.length))
      (φ.branchParityRowScope rows
        (heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
        e b) v ≤ b₀ :=
  varIncidence_relabelRestrictedMonomials_heavyVars_le univ univ
    (φ.parityRowSystem rows) b₀ subset_rfl e b v

/-- When `S = heavyVars univ univ (fun j => equationScope (φ.parityRowSystem rows j)) b₀`, every
free variable `v : Fin n'` occurs in at most `b₀ + 1` scopes of
`φ.branchParityRowNeutralScope rows S e b`. -/
theorem CNF.varIncidence_branchParityRowNeutralScope_heavyVars_le (φ : CNF V)
    (rows : List (Fin φ.length → Bool)) (b₀ : ℕ)
    (e : ↥(univ \ heavyVars univ (univ : Finset (Fin rows.length))
      (fun j => equationScope (φ.parityRowSystem rows j)) b₀) ≃ Fin n')
    (b : V → Bool) (v : Fin n') :
    varIncidence (univ : Finset (Fin rows.length ⊕ Fin n'))
      (φ.branchParityRowNeutralScope rows
        (heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
        e b) v ≤ b₀ + 1 := by
  rw [CNF.branchParityRowNeutralScope, ← withNeutralFactors_univ]
  exact varIncidence_withNeutralFactors_le
    (CNF.varIncidence_branchParityRowScope_heavyVars_le φ rows b₀ e b v)

/-- When `S = heavyVars univ univ (fun j => equationScope (φ.parityRowSystem rows j)) b₀`, total
branch incidence of `φ.branchParityRowNeutralScope rows S e b` is at most `(b₀ + 1) * n'`. -/
theorem CNF.totalIncidence_branchParityRowNeutralScope_heavyVars_le (φ : CNF V)
    (rows : List (Fin φ.length → Bool)) (b₀ : ℕ)
    (e : ↥(univ \ heavyVars univ (univ : Finset (Fin rows.length))
      (fun j => equationScope (φ.parityRowSystem rows j)) b₀) ≃ Fin n')
    (b : V → Bool) :
    totalIncidence (univ : Finset (Fin rows.length ⊕ Fin n'))
      (φ.branchParityRowNeutralScope rows
        (heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
        e b) ≤ (b₀ + 1) * n' := by
  rw [CNF.branchParityRowNeutralScope, ← withNeutralFactors_univ]
  simpa only [Fintype.card_fin] using
    totalIncidence_withNeutralFactors_le
      (CNF.varIncidence_branchParityRowScope_heavyVars_le φ rows b₀ e b)

/-- **§5.5 & §6.3 (Lemma 4.7 `ReplacementDesign` existence on each heavy-variable branch of a
compiled CNF parity system)**: if every clause of `φ` has width at most `k` and every row in `rows`
has Hamming weight at most `W`, then on every branch `b : V → Bool` of
`S = heavyVars univ univ (fun j => equationScope (φ.parityRowSystem rows j)) b₀` with free-variable
relabeling `e : ↥(univ \ S) ≃ Fin n'`, the neutral-augmented scope family
`φ.branchParityRowNeutralScope rows S e b` admits a Section 4
`ReplacementDesign _ Q r A₀ R τ` whenever the numerical balance and binomial-tail hypotheses of
Lemma 4.7 hold for `b_occ = b₀ + 1` and `w_width = max 1 (k * (W * 2 ^ k))`. -/
theorem CNF.exists_replacementDesign_branchParityRowNeutralScope {φ : CNF V}
    {k W b₀ Q r A₀ R : ℕ} {τ : ℚ} (hk : ∀ c ∈ φ, c.length ≤ k)
    {rows : List (Fin φ.length → Bool)} (hW : ∀ r_row ∈ rows, weight r_row ≤ W)
    (e : ↥(univ \ heavyVars univ (univ : Finset (Fin rows.length))
      (fun j => equationScope (φ.parityRowSystem rows j)) b₀) ≃ Fin n')
    (b : V → Bool) (hn' : 1 ≤ n') (hr : 2 ≤ r) (hR : 1 ≤ R) (hRQ : R < Q) (hτ : 0 ≤ τ)
    (hI : ∀ a < R - 1, A₀ + a ≤ Q)
    (hbal₁ :
      2 * (b₀ + 1 + max 1 (k * (W * 2 ^ k))) * (r ^ (2 * Q)) ^ 2 ≤
        totalIncidence (univ : Finset (Fin rows.length))
          (φ.branchParityRowScope rows
            (heavyVars univ (univ : Finset (Fin rows.length))
              (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
            e b) + n')
    (hbal₂ : 2 * Q * r ^ 2 ≤ n')
    (htail : binomTailProb Q r A₀ R ≤ τ / ((r : ℚ) * ((b₀ + 1 : ℕ) : ℚ))) :
    Nonempty
      (ReplacementDesign
        (φ.branchParityRowNeutralScope rows
          (heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
          e b) Q r A₀ R τ) :=
  exists_replacementDesign_withNeutralScope _ hn' (le_max_left 1 _) hr hR hRQ hτ hI
    (CNF.varIncidence_branchParityRowScope_heavyVars_le φ rows b₀ e b)
    (fun j => (CNF.card_branchParityRowScope_le hk hW _ e b j).trans (le_max_right 1 _))
    hbal₁ hbal₂ htail

end BranchParityRowSystem

/-! ### 2. Per-branch locality, degree, and `coeffNorm1` bounds under a `ReplacementDesign` -/

section BranchDesignBounds

variable [Fintype V] [DecidableEq V] {n' Q r A₀ R : ℕ} {τ : ℚ}

/-- **§5.3 factor-level locality on a branch-restricted CNF parity equation**: for any
`D : ReplacementDesign (φ.branchParityRowNeutralScope rows S e b) Q r A₀ R τ`, the substituted
branch equation factor `(univariateMonomialSumPoly ℚ (designReplacementMap D Sum.inl x j)
(φ.branchParityRowSystem rows S e b j)).eval (nodePoint t)` depends only on `x` restricted to
`varGroup D.varAssign t (D.factorAssign (Sum.inl j) t)` and the measurement vector
`(varMeasurementMatrix Q r A₀ R ℚ D.place
(scopeVarOf (φ.branchParityRowNeutralScope rows S e b))).mulVec (fun u => bitVal ℚ (x u))`. -/
theorem CNF.eval_univariateMonomialSumPoly_branchParityRowSystem_nodePoint_eq
    (φ : CNF V) (rows : List (Fin φ.length → Bool))
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n') (b : V → Bool)
    (D : ReplacementDesign (φ.branchParityRowNeutralScope rows S e b) Q r A₀ R τ)
    (j : Fin rows.length) (t : Fin Q) (x x' : Fin n' → Bool)
    (hgrp : ∀ u ∈ varGroup D.varAssign t (D.factorAssign (Sum.inl j) t), x u = x' u)
    (hmeas :
      (varMeasurementMatrix Q r A₀ R ℚ D.place
          (scopeVarOf (φ.branchParityRowNeutralScope rows S e b))).mulVec
            (fun u => bitVal ℚ (x u)) =
        (varMeasurementMatrix Q r A₀ R ℚ D.place
          (scopeVarOf (φ.branchParityRowNeutralScope rows S e b))).mulVec
            (fun u => bitVal ℚ (x' u))) :
    (univariateMonomialSumPoly ℚ (designReplacementMap D Sum.inl x j)
        (φ.branchParityRowSystem rows S e b j)).eval (nodePoint t) =
      (univariateMonomialSumPoly ℚ (designReplacementMap D Sum.inl x' j)
        (φ.branchParityRowSystem rows S e b j)).eval (nodePoint t) :=
  eval_univariateMonomialSumPoly_designReplacementMap_nodePoint_eq D Sum.inl
    (φ.branchParityRowSystem rows S e b) subset_rfl t x x' hgrp hmeas

/-- **Equation (5.5) degree bound on a branch-restricted CNF parity system**: if every clause of `φ`
has width at most `k`, then for any replacement design `D` on branch `b` (with factor embedding
`emb : Fin rows.length → F`) and `s < ℓ`, the cleared parity coordinate `s` on
`φ.branchParityRowSystem rows S e b` has
`natDegree ≤ (k * (R - 1)) * (rows.length + 2 * (ℓ - 1))` (strengthening the manuscript's coarser
`k * R * (rows.length + 2 * (ℓ - 1))` display in (5.5) via `natDegree ≤ R - 1` from Lemma 4.3 and
§4.5 (4.14)). -/
theorem CNF.natDegree_univariateClearedParityCoord_branchParityRowSystem_le
    {F : Type*} [Fintype F] {scope : F → Finset (Fin n')} {φ : CNF V} {k ℓ s : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (rows : List (Fin φ.length → Bool))
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n') (b : V → Bool)
    (D : ReplacementDesign scope Q r A₀ R τ) (emb : Fin rows.length → F)
    (hs : s < ℓ) :
    (univariateClearedParityCoord (univ : Finset (Fin rows.length))
        (φ.branchParityRowSystem rows S e b) (commonDenom Q R : ℤ) k ℓ
        (designReplacementScaledIntMap D emb) s).natDegree ≤
      (k * (R - 1)) * (rows.length + 2 * (ℓ - 1)) := by
  have hdeg := natDegree_univariateClearedParityCoord_design_le D emb
    (univ : Finset (Fin rows.length)) (φ.branchParityRowSystem rows S e b)
    (fun j _ _M hM => CNF.card_mem_branchParityRowSystem_le hk rows S e b j hM) hs
  simpa only [card_univ, Fintype.card_fin] using hdeg

/-- **Equation (5.5) degree bound for `univariateClearedParityTruncatedSum` on a branch-restricted
CNF parity system**: under `∀ c ∈ φ, c.length ≤ k`, the truncated sum has
`natDegree ≤ (k * (R - 1)) * (rows.length + 2 * (ℓ - 1))` (strengthening the manuscript's coarser
`k * R * (rows.length + 2 * (ℓ - 1))` display in (5.5) via `natDegree ≤ R - 1` from Lemma 4.3 and
§4.5 (4.14)). -/
theorem CNF.natDegree_univariateClearedParityTruncatedSum_branchParityRowSystem_le
    {F : Type*} [Fintype F] {scope : F → Finset (Fin n')} {φ : CNF V} {k : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (rows : List (Fin φ.length → Bool))
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n') (b : V → Bool)
    (D : ReplacementDesign scope Q r A₀ R τ) (emb : Fin rows.length → F)
    (ℓ : ℕ) :
    (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
        (φ.branchParityRowSystem rows S e b) (commonDenom Q R : ℤ) k ℓ
        (designReplacementScaledIntMap D emb)).natDegree ≤
      (k * (R - 1)) * (rows.length + 2 * (ℓ - 1)) := by
  have hdeg := natDegree_univariateClearedParityTruncatedSum_design_le D emb
    (univ : Finset (Fin rows.length)) (φ.branchParityRowSystem rows S e b) k ℓ
    (fun j _ _M hM => CNF.card_mem_branchParityRowSystem_le hk rows S e b j hM)
  simpa only [card_univ, Fintype.card_fin] using hdeg

/-- **Appendix B.2 coordinate `coeffNorm1` bound on a branch-restricted CNF parity system**: if
every clause of `φ` has width at most `k` and every row in `rows` has Hamming weight at most `W`,
then for any replacement design `D` on branch `b`, every cleared parity coordinate `s` on
`φ.branchParityRowSystem rows S e b` satisfies the Appendix B.2 `ℓ₁`-norm bound with
`S_mon = W * 2 ^ k`. -/
theorem CNF.coeffNorm1_univariateClearedParityCoord_branchParityRowSystem_le
    {F : Type*} [Fintype F] {scope : F → Finset (Fin n')} {φ : CNF V} {k W ℓ E_ℓ : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) {rows : List (Fin φ.length → Bool)}
    (hW : ∀ r_row ∈ rows, weight r_row ≤ W) (S : Finset V) (e : ↥(univ \ S) ≃ Fin n')
    (b : V → Bool) (D : ReplacementDesign scope Q r A₀ R τ)
    (emb : Fin rows.length → F)
    (hE : ∀ j < ℓ, (Polynomial.parityBaseDigit ℓ j).coeffNorm1 ≤ E_ℓ) (s : ℕ) :
    (univariateClearedParityCoord (univ : Finset (Fin rows.length))
        (φ.branchParityRowSystem rows S e b) (commonDenom Q R : ℤ) k ℓ
        (designReplacementScaledIntMap D emb) s).coeffNorm1 ≤
      2 ^ n' *
        (ℓ * E_ℓ *
          ((W * 2 ^ k) * designRowNormBound Q R ^ k + commonDenom Q R ^ k) ^ (2 * ℓ - 1)) ^
            rows.length := by
  have hnorm := coeffNorm1_univariateClearedParityCoord_design_le D emb
    (univ : Finset (Fin rows.length)) (φ.branchParityRowSystem rows S e b) k ℓ
    (S_mon := W * 2 ^ k)
    (fun j _ _M hM => CNF.card_mem_branchParityRowSystem_le hk rows S e b j hM)
    (fun j _ => CNF.card_branchParityRowSystem_le hk hW S e b j)
    hE s
  simpa only [card_univ, Fintype.card_fin] using hnorm

end BranchDesignBounds

/-! ### 3. End-to-end `ReplacementDesign` recovery of `commonZeroCount`, `numPassing`, and `#F` -/

section DesignRecovery

variable [Fintype V] [DecidableEq V] {n' Q r A₀ R : ℕ} {τ : ℚ}

/-- **§5.4–5.5 single-branch `ReplacementDesign` recovery for `φ.branchParityRowSystem`**: when
`∀ c ∈ φ, c.length ≤ k` and `n' < ℓ`, evaluating `univariateClearedParityTruncatedSum` at `T = 0`,
dividing by `clearedProductDenom`, and reducing modulo `2 ^ ℓ` recovers the branch common-zero count
`commonZeroCount univ (φ.branchParityRowSystem rows S e b)`. -/
theorem CNF.emod_ediv_eval_zero_branchParityRowSystem_design_eq_commonZeroCount
    {F : Type*} [Fintype F] {scope : F → Finset (Fin n')} {φ : CNF V} {k ℓ : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (rows : List (Fin φ.length → Bool))
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n') (b : V → Bool)
    (D : ReplacementDesign scope Q r A₀ R τ) (emb : Fin rows.length → F)
    (hℓ : n' < ℓ) :
    ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
        (φ.branchParityRowSystem rows S e b) (commonDenom Q R : ℤ) k ℓ
        (designReplacementScaledIntMap D emb)).eval 0 /
          clearedProductDenom (commonDenom Q R : ℤ) k ℓ
            #(univ : Finset (Fin rows.length))) % ((2 : ℤ) ^ ℓ) =
      (commonZeroCount (univ : Finset (Fin rows.length))
        (φ.branchParityRowSystem rows S e b) : ℤ) :=
  emod_ediv_eval_zero_clearedParityTruncatedSum_design_eq_commonZeroCount D emb
    (univ : Finset (Fin rows.length)) (φ.branchParityRowSystem rows S e b) hℓ
    (fun j _ _M hM => CNF.card_mem_branchParityRowSystem_le hk rows S e b j hM)

/-- **§5.4–5.5 & §6 (branch-summed `ReplacementDesign` recovery of `commonZeroCount` on
`φ.parityRowSystem rows`)**: when every clause of `φ` has width at most `k`, summing the per-branch
`ReplacementDesign` modular residues of `univariateClearedParityTruncatedSum` at shared precision
`branchPrecision (Fintype.card V)` across all `b ∈ branchAssignments S` recovers
`commonZeroCount univ (φ.parityRowSystem rows)`. -/
theorem CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design
    {F : (V → Bool) → Type*} [∀ b, Fintype (F b)] {φ : CNF V} {k : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (rows : List (Fin φ.length → Bool))
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n')
    (scope : (b : V → Bool) → F b → Finset (Fin n'))
    (D : (b : V → Bool) → ReplacementDesign (scope b) Q r A₀ R τ)
    (emb : (b : V → Bool) → Fin rows.length → F b) :
    (commonZeroCount (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) : ℤ) =
      ∑ b ∈ branchAssignments S,
        ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
          (φ.branchParityRowSystem rows S e b) (commonDenom Q R : ℤ) k
          (branchPrecision (Fintype.card V))
          (designReplacementScaledIntMap (D b) (emb b))).eval 0 /
            clearedProductDenom (commonDenom Q R : ℤ) k
              (branchPrecision (Fintype.card V)) #(univ : Finset (Fin rows.length))) %
                ((2 : ℤ) ^ branchPrecision (Fintype.card V)) :=
  commonZeroCount_eq_sum_branch_emod_ediv_cleared S e (univ : Finset (Fin rows.length))
    (φ.parityRowSystem rows) (commonDenom_intCast_ne_zero Q R)
    (fun b => designReplacementScaledIntMap (D b) (emb b))
    (fun j _ _M hM => CNF.card_mem_parityRowSystem_le hk rows j hM)
    (fun b _ x j _ _ _ v _ => eval_zero_designReplacementScaledIntMap (D b) (emb b) x j v)

/-- **§5.4–5.5 & §6 (branch-summed `ReplacementDesign` recovery of
`numPassing φ.violations rows`)**: when every clause of `φ` has width at most `k`, the
branch-summed `ReplacementDesign` evaluation at `T = 0` equals
`(numPassing φ.violations rows : ℤ)`. -/
theorem CNF.numPassing_eq_sum_branch_emod_ediv_design
    {F : (V → Bool) → Type*} [∀ b, Fintype (F b)] {φ : CNF V} {k : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (rows : List (Fin φ.length → Bool))
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n')
    (scope : (b : V → Bool) → F b → Finset (Fin n'))
    (D : (b : V → Bool) → ReplacementDesign (scope b) Q r A₀ R τ)
    (emb : (b : V → Bool) → Fin rows.length → F b) :
    (numPassing φ.violations rows : ℤ) =
      ∑ b ∈ branchAssignments S,
        ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
          (φ.branchParityRowSystem rows S e b) (commonDenom Q R : ℤ) k
          (branchPrecision (Fintype.card V))
          (designReplacementScaledIntMap (D b) (emb b))).eval 0 /
            clearedProductDenom (commonDenom Q R : ℤ) k
              (branchPrecision (Fintype.card V)) #(univ : Finset (Fin rows.length))) %
                ((2 : ℤ) ^ branchPrecision (Fintype.card V)) := by
  rw [← CNF.commonZeroCount_parityRowSystem]
  exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design hk rows S e scope D emb

/-- **§5.4–5.5 & §6.2–6.3 (branch-summed `ReplacementDesign` recovery of
`φ.modelCountOn Finset.univ` after `3 * n` greedy rounds)**: under the hypotheses of
`CNF.commonZeroCount_parityRowSystem_greedy`, for any heavy-variable set `S : Finset V`,
free-variable relabeling `e : ↥(univ \ S) ≃ Fin n'`, and per-branch replacement design family
`D b`, summing the branch modular residues of `univariateClearedParityTruncatedSum` at `T = 0`
across `b ∈ branchAssignments S` recovers `(φ.modelCountOn Finset.univ : ℤ)` without any auxiliary
replacement hypotheses. -/
theorem CNF.modelCountOn_eq_sum_branch_emod_ediv_design_greedy
    {F : (V → Bool) → Type*} [∀ b, Fintype (F b)] (φ : CNF V) {k P : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (hn : 1 ≤ Fintype.card V) (hP : 1 ≤ P)
    (A : ℕ → List (Fin φ.length → Bool))
    (hinit : ∀ σ, PassesTests φ.violations (A 0) σ → φ.eval σ = false →
      φ.length ≤ P * weight (φ.violations σ))
    (γ : ℕ → Fin P → Fin φ.length × Bool) (hA : ∀ i, A (i + 1) = A i ++ [testRow (γ i)])
    (hγ : ∀ i (γ' : Fin P → Fin φ.length × Bool),
      commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow (γ i)])) ≤
        commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ'])))
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n')
    (scope : (b : V → Bool) → F b → Finset (Fin n'))
    (D : (b : V → Bool) → ReplacementDesign (scope b) Q r A₀ R τ)
    (emb : (b : V → Bool) → Fin (A (3 * Fintype.card V)).length → F b) :
    (φ.modelCountOn Finset.univ : ℤ) =
      ∑ b ∈ branchAssignments S,
        ((univariateClearedParityTruncatedSum
          (univ : Finset (Fin (A (3 * Fintype.card V)).length))
          (φ.branchParityRowSystem (A (3 * Fintype.card V)) S e b)
          (commonDenom Q R : ℤ) k (branchPrecision (Fintype.card V))
          (designReplacementScaledIntMap (D b) (emb b))).eval 0 /
            clearedProductDenom (commonDenom Q R : ℤ) k
              (branchPrecision (Fintype.card V))
              #(univ : Finset (Fin (A (3 * Fintype.card V)).length))) %
                ((2 : ℤ) ^ branchPrecision (Fintype.card V)) := by
  rw [← CNF.commonZeroCount_parityRowSystem_greedy φ hn hP A hinit γ hA hγ]
  exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design hk
    (A (3 * Fintype.card V)) S e scope D emb

/-- For all `B, m : ℕ`, the Lemma 6.2 greedy list length
`P = 20000 * B ^ 2 * (Nat.log 2 m + 1) ^ 2` is at most the Lemma 6.1 initial row weight bound
`D₀ = 320000 * B ^ 2 * (Nat.log 2 m + 1) ^ 3`. -/
theorem CNF.greedyRowListLength_le_initialRowWeightBound (B m : ℕ) :
    greedyRowListLength B m ≤ initialRowWeightBound B m := by
  unfold greedyRowListLength initialRowWeightBound
  have h1 : 20000 * B ^ 2 ≤ 320000 * B ^ 2 :=
    Nat.mul_le_mul_right (B ^ 2) (by decide)
  have h2 : (Nat.log 2 m + 1) ^ 2 ≤ (Nat.log 2 m + 1) ^ 3 :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  exact Nat.mul_le_mul h1 h2

/-- Consequently `max (initialRowWeightBound B m) (greedyRowListLength B m)` simplifies to
`initialRowWeightBound B m`. -/
@[simp]
theorem CNF.max_initialRowWeightBound_greedyRowListLength (B m : ℕ) :
    max (initialRowWeightBound B m) (greedyRowListLength B m) =
      initialRowWeightBound B m :=
  max_eq_left (CNF.greedyRowListLength_le_initialRowWeightBound B m)

/-- **Lemmas 6.1–6.2 & §§5.4–5.5, 6.3 (end-to-end initial + greedy parity-test compilation and
branch-summed `ReplacementDesign` recovery of `φ.modelCountOn Finset.univ`)**: for any width-`≤ k`
CNF `φ` on `n = Fintype.card V ≥ 1` variables with `φ.length ≤ B * n` (`B ≥ 1`), there exist
initial parity rows `A_init` (`A_init.length ≤ 3 * n`, each of weight at most
`D₀ = initialRowWeightBound B φ.length`) such that for any greedy sequence
`A (i + 1) = A i ++ [testRow (γ i)]` with `A 0 = A_init` minimizing
`commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ']))` over candidate rows of list length
`P = greedyRowListLength B φ.length`:
1. At every stage `i ≤ 3 * n`, `(A i).length ≤ 6 * n`, and every compiled equation
   `φ.parityRowSystem (A i) j` has degree at most `k`, at most `D₀ * 2 ^ k` monomials, and
   variable-scope size `#(equationScope (φ.parityRowSystem (A i) j)) ≤ k * (D₀ * 2 ^ k)`.
2. After `3 * n` rounds, for any heavy-variable set `S : Finset V`, free-variable relabeling
   `e : ↥(univ \ S) ≃ Fin n'`, and per-branch replacement design family `D b`, the branch-summed
   `ReplacementDesign` evaluation at `T = 0` equals `(φ.modelCountOn Finset.univ : ℤ)`. -/
theorem CNF.exists_initialTests_modelCountOn_eq_sum_branch_emod_ediv_design_greedy
    {F : (V → Bool) → Type*} [∀ b, Fintype (F b)] (φ : CNF V) {k B : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (hn : 1 ≤ Fintype.card V) (hB : 1 ≤ B)
    (hm : φ.length ≤ B * Fintype.card V) :
    let D₀ := initialRowWeightBound B φ.length
    let P := greedyRowListLength B φ.length
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
        ∀ (S : Finset V) (e : ↥(univ \ S) ≃ Fin n')
          (scope : (b : V → Bool) → F b → Finset (Fin n'))
          (D : (b : V → Bool) → ReplacementDesign (scope b) Q r A₀ R τ)
          (emb : (b : V → Bool) → Fin (A (3 * Fintype.card V)).length → F b),
          (φ.modelCountOn Finset.univ : ℤ) =
            ∑ b ∈ branchAssignments S,
              ((univariateClearedParityTruncatedSum
                (univ : Finset (Fin (A (3 * Fintype.card V)).length))
                (φ.branchParityRowSystem (A (3 * Fintype.card V)) S e b)
                (commonDenom Q R : ℤ) k (branchPrecision (Fintype.card V))
                (designReplacementScaledIntMap (D b) (emb b))).eval 0 /
                  clearedProductDenom (commonDenom Q R : ℤ) k
                    (branchPrecision (Fintype.card V))
                    #(univ : Finset (Fin (A (3 * Fintype.card V)).length))) %
                      ((2 : ℤ) ^ branchPrecision (Fintype.card V)) := by
  obtain ⟨A_init, hlen, hw, hgreedy⟩ := CNF.exists_initialTests_commonZeroCount_greedy φ hk hn hB hm
  refine ⟨A_init, hlen, hw, fun A γ h0 hA hγ => ?_⟩
  obtain ⟨hcount, hbounds⟩ := hgreedy A γ h0 hA hγ
  refine ⟨fun i hi => ?_, fun S e scope D emb => ?_⟩
  · obtain ⟨hlen_i, hj⟩ := hbounds i hi
    refine ⟨hlen_i, fun j => ?_⟩
    obtain ⟨hM, hcard, hscope⟩ := hj j
    rw [CNF.max_initialRowWeightBound_greedyRowListLength] at hcard hscope
    exact ⟨hM, hcard, hscope⟩
  · rw [← hcount]
    exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design hk
      (A (3 * Fintype.card V)) S e scope D emb

end DesignRecovery

end Cslib.Logic.PL
