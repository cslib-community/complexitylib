/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.SparseClearedSpecialization
public import Complexity.Foundations.Data.BitString.ParityTestBounds
public import Complexity.Logics.Propositional.CNF.ExactTests
public import Complexity.Logics.Propositional.CNF.PolynomialTests

/-!
# Sparse `𝔽₂` Polynomial Systems and Branch-Reduced Parity Counting for CNF Formulas

This module connects the sparse CNF parity-test compilation of Sections 6.1–6.3
(`Complexity.Logics.Propositional.CNF.ExactTests` and
`Complexity.Logics.Propositional.CNF.PolynomialTests`) with the sparse `𝔽₂` polynomial system,
heavy-variable branching, and cleared-denominator parity-amplifier counter of Section 5 and
Appendix B.2–B.3 (`Complexity.Foundations.BooleanAnalysis.SparseEquations`,
`Complexity.Foundations.BooleanAnalysis.SparseBranching`, and
`Complexity.Foundations.BooleanAnalysis.SparseClearedSpecialization`) of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (printed pp. 37–43, 48–50):

1. **Indexed sparse `𝔽₂` polynomial system of parity-check rows (`CNF.parityRowSystem`)**:
   For any `φ : CNF V` and list `rows : List (Fin φ.length → Bool)` of parity-check rows on the
   clause-violation vector, `φ.parityRowSystem rows : Fin rows.length → Finset (Finset V)` indexes
   the compiled `𝔽₂` equations `φ.parityRowMonomials (rows.get i)`. Its `Cslib.BitString` common
   zero predicate `IsCommonZero univ (φ.parityRowSystem rows)` is equivalent to
   `PassesTests φ.violations rows`, and its common-zero count
   `commonZeroCount univ (φ.parityRowSystem rows)` equals `numPassing φ.violations rows`.
2. **Degree, sparsity, variable-scope, and heavy-variable branch bounds (§5.5 & Lemma 6.2)**:
   When every clause of `φ` has width at most `k` and every row in `rows` has Hamming weight at most
   `W`, each equation `φ.parityRowSystem rows i` has degree at most `k`, at most `W * 2 ^ k`
   monomials, and variable scope `equationScope (φ.parityRowSystem rows i)` of size at most
   `k * (W * 2 ^ k)` contained in `φ.vars.toFinset`. Consequently, branching on the heavy variables
   `heavyVars univ univ (fun i => equationScope (φ.parityRowSystem rows i)) b₀` produces at most
   `2 ^ ((rows.length * (k * (W * 2 ^ k))) / b₀)` branches, each with post-branching free-variable
   incidence at most `b₀`.
3. **End-to-end greedy parity-test model counting via `commonZeroCount` and cleared-denominator
   branch evaluation (§6.1–6.3 & §5.4–5.5)**:
   Combining `CNF.numPassing_greedy_initial` (Lemmas 6.1–6.2) with
   `CNF.commonZeroCount_parityRowSystem` and `commonZeroCount_eq_sum_branch_emod_ediv_cleared`
   shows that for any width-`≤ k` formula `φ` on `n = Fintype.card V ≥ 1` variables with
   `φ.length ≤ B * n` (`B ≥ 1`), there exist at most `3 * n` initial rows `A₀` of weight at most
   `D₀ = 320000 * B ^ 2 * (Nat.log 2 φ.length + 1) ^ 3` such that any `3 * n`-step greedy sequence
   minimizing `commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ']))` over candidate rows
   of list length `P = 20000 * B ^ 2 * (Nat.log 2 φ.length + 1) ^ 2` satisfies
   `commonZeroCount univ (φ.parityRowSystem (A (3 * n))) = φ.modelCountOn Finset.univ`, and its
   branch-summed cleared-denominator parity-product evaluation at `T = 0` recovers
   `φ.modelCountOn Finset.univ` on the nose.

## Main definitions

* `Cslib.Logic.PL.CNF.parityRowSystem`: the `Fin rows.length`-indexed sparse `𝔽₂` polynomial system
  `fun i => φ.parityRowMonomials (rows.get i)`.

## Main results

* `Cslib.Logic.PL.CNF.isCommonZero_parityRowSystem_iff`,
  `Cslib.Logic.PL.CNF.commonZeroCount_parityRowSystem`: equivalence between `IsCommonZero` /
  `commonZeroCount` of `φ.parityRowSystem rows` and `PassesTests` / `numPassing`.
* `Cslib.Logic.PL.CNF.card_equationScope_parityRowSystem_le`,
  `Cslib.Logic.PL.CNF.totalIncidence_parityRowSystem_le`,
  `Cslib.Logic.PL.CNF.card_branchAssignments_heavyVars_parityRowSystem_le`,
  `Cslib.Logic.PL.CNF.varIncidence_restrictMonomials_heavyVars_parityRowSystem_le`: variable-scope,
  total-incidence, and heavy-variable branching bounds for compiled parity-row systems.
* `Cslib.Logic.PL.CNF.commonZeroCount_parityRowSystem_greedy`,
  `Cslib.Logic.PL.CNF.exists_initialTests_commonZeroCount_greedy`,
  `Cslib.Logic.PL.CNF.modelCountOn_eq_sum_branch_emod_ediv_cleared_greedy`: exact recovery of
  `φ.modelCountOn Finset.univ` after `3 * Fintype.card V` greedy rounds via `commonZeroCount` and
  cleared-denominator branch evaluation.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (Sections 5.4–5.5 and 6.1–6.3)
-/

@[expose] public noncomputable section

namespace Cslib.Logic.PL

open Finset Cslib.BitString

variable {V : Type*}

/-! ### 1. Indexed sparse `𝔽₂` polynomial system of parity-check rows -/

section ParityRowSystem

variable [DecidableEq V]

/-- The `Fin rows.length`-indexed sparse `𝔽₂` polynomial system compiled from a list
`rows : List (Fin φ.length → Bool)` of parity-check rows on the clause-violation bits of `φ`
([OpenAI2026ETH], eq. 6.1, p. 39). -/
def CNF.parityRowSystem (φ : CNF V) (rows : List (Fin φ.length → Bool))
    (i : Fin rows.length) : Finset (Finset V) :=
  φ.parityRowMonomials (rows.get i)

/-- **§6 (eq. 6.1 common-zero equivalence)**: `σ : V → Bool` is a common zero of
`φ.parityRowSystem rows` if and only if `PassesTests φ.violations rows σ`. -/
theorem CNF.isCommonZero_parityRowSystem_iff (φ : CNF V)
    (rows : List (Fin φ.length → Bool)) (σ : V → Bool) :
    IsCommonZero univ (φ.parityRowSystem rows) σ ↔ PassesTests φ.violations rows σ := by
  rw [IsCommonZero, ← CNF.commonZero_parityRowMonomials_iff_passesTests]
  constructor
  · intro h r hr
    rcases List.mem_iff_get.mp hr with ⟨i, rfl⟩
    exact h i (mem_univ i)
  · intro h i _
    exact h (rows.get i) (List.get_mem rows i)

/-- If every clause of `φ` has width at most `k`, then every monomial in
`φ.parityRowSystem rows i` has size at most `k`. -/
theorem CNF.card_mem_parityRowSystem_le {φ : CNF V} {k : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    (rows : List (Fin φ.length → Bool)) (i : Fin rows.length) {M : Finset V}
    (hM : M ∈ φ.parityRowSystem rows i) :
    #M ≤ k :=
  CNF.card_le_of_mem_parityRowMonomials hk hM

/-- If every clause of `φ` has width at most `k` and every row in `rows` has Hamming weight at most
`W`, then every equation `φ.parityRowSystem rows i` contains at most `W * 2 ^ k` monomials. -/
theorem CNF.card_parityRowSystem_le {φ : CNF V} {k W : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    {rows : List (Fin φ.length → Bool)} (hW : ∀ r ∈ rows, weight r ≤ W)
    (i : Fin rows.length) :
    #(φ.parityRowSystem rows i) ≤ W * 2 ^ k :=
  (CNF.card_parityRowMonomials_le hk (rows.get i)).trans
    (Nat.mul_le_mul_right (2 ^ k) (hW (rows.get i) (List.get_mem rows i)))

/-- If every clause of `φ` has width at most `k` and every row in `rows` has Hamming weight at most
`W`, then the variable scope `equationScope (φ.parityRowSystem rows i)` has size at most
`k * (W * 2 ^ k)`. -/
theorem CNF.card_equationScope_parityRowSystem_le {φ : CNF V} {k W : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) {rows : List (Fin φ.length → Bool)}
    (hW : ∀ r ∈ rows, weight r ≤ W) (i : Fin rows.length) :
    #(equationScope (φ.parityRowSystem rows i)) ≤ k * (W * 2 ^ k) :=
  (card_equationScope_le (fun _ hM => CNF.card_mem_parityRowSystem_le hk rows i hM)).trans
    (Nat.mul_le_mul_left k (CNF.card_parityRowSystem_le hk hW i))

/-- Under the same hypotheses, the total variable-equation incidence across all `rows.length`
compiled equations is at most `(k * (W * 2 ^ k)) * rows.length`. -/
theorem CNF.totalIncidence_parityRowSystem_le {φ : CNF V} {k W : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) {rows : List (Fin φ.length → Bool)}
    (hW : ∀ r ∈ rows, weight r ≤ W) :
    totalIncidence (univ : Finset (Fin rows.length))
        (fun i => equationScope (φ.parityRowSystem rows i)) ≤
      (k * (W * 2 ^ k)) * rows.length := by
  have hle := totalIncidence_le_mul_card (univ : Finset (Fin rows.length))
    (fun i => equationScope (φ.parityRowSystem rows i))
    (fun i _ => CNF.card_equationScope_parityRowSystem_le hk hW i)
  simpa only [card_univ, Fintype.card_fin] using hle

end ParityRowSystem

/-! ### 2. Common-zero counts, heavy-variable branching, and greedy parity recovery -/

section GreedyParityCounter

variable [Fintype V] [DecidableEq V]

/-- **§6 (common-zero count identity)**: `commonZeroCount univ (φ.parityRowSystem rows)` equals
`numPassing φ.violations rows`. -/
theorem CNF.commonZeroCount_parityRowSystem (φ : CNF V)
    (rows : List (Fin φ.length → Bool)) :
    commonZeroCount univ (φ.parityRowSystem rows) = numPassing φ.violations rows := by
  unfold commonZeroCount numPassing
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and, CNF.isCommonZero_parityRowSystem_iff]

/-- **`N(P_A) = #F + D(A)` in `commonZeroCount` form** ([OpenAI2026ETH], §6, p. 40). -/
theorem CNF.commonZeroCount_parityRowSystem_eq_modelCountOn_add (φ : CNF V)
    (rows : List (Fin φ.length → Bool)) :
    commonZeroCount univ (φ.parityRowSystem rows) =
      φ.modelCountOn Finset.univ +
        #{σ : V → Bool | φ.eval σ = false ∧ PassesTests φ.violations rows σ} := by
  rw [CNF.commonZeroCount_parityRowSystem, CNF.numPassing_violations_eq_modelCountOn_add]

/-- **§5.5 & §6.3 (heavy-variable branch count bound on compiled parity systems)**: if every clause
of `φ` has width at most `k`, every row in `rows` has Hamming weight at most `W`, and `0 < b₀`, then
branching on `heavyVars univ univ (fun i => equationScope (φ.parityRowSystem rows i)) b₀` produces
at most `2 ^ (((k * (W * 2 ^ k)) * rows.length) / b₀)` canonical branches. -/
theorem CNF.card_branchAssignments_heavyVars_parityRowSystem_le {φ : CNF V} {k W b₀ : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) {rows : List (Fin φ.length → Bool)}
    (hW : ∀ r ∈ rows, weight r ≤ W) (hb₀ : 0 < b₀) :
    #(branchAssignments
        (heavyVars univ (univ : Finset (Fin rows.length))
          (fun i => equationScope (φ.parityRowSystem rows i)) b₀)) ≤
      2 ^ (((k * (W * 2 ^ k)) * rows.length) / b₀) := by
  refine (card_branchAssignments_heavyVars_le univ univ
    (fun i => equationScope (φ.parityRowSystem rows i)) hb₀
    (fun _ _ => subset_univ _)).trans ?_
  exact Nat.pow_le_pow_right (by omega)
    (Nat.div_le_div_right (CNF.totalIncidence_parityRowSystem_le hk hW))

/-- **§5.5 & §6.3 (post-branching free-variable incidence bound on compiled parity systems)**:
after branching on `heavyVars univ univ (fun i => equationScope (φ.parityRowSystem rows i)) b₀`,
every variable `v : V` appears in at most `b₀` restricted equations. -/
theorem CNF.varIncidence_restrictMonomials_heavyVars_parityRowSystem_le (φ : CNF V)
    (rows : List (Fin φ.length → Bool)) (b₀ : ℕ) (b : V → Bool) (v : V) :
    varIncidence (univ : Finset (Fin rows.length))
      (fun i => equationScope
        (restrictMonomials
          (heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀)
          b (φ.parityRowSystem rows i))) v ≤
      b₀ :=
  varIncidence_equationScope_restrictMonomials_heavyVars_le univ univ
    (φ.parityRowSystem rows) b₀ (fun _ _ => subset_univ _) b v

/-- **Lemma 6.2 & §6.3 (`commonZeroCount` greedy recovery of `φ.modelCountOn Finset.univ`)**:
under the initial-residual hypothesis `hinit`, if each greedy step `i` chooses `γ i` minimizing
`commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ']))`, then after `3 * Fintype.card V`
rounds the common-zero count of `φ.parityRowSystem (A (3 * Fintype.card V))` equals
`φ.modelCountOn Finset.univ` (`#F`). -/
theorem CNF.commonZeroCount_parityRowSystem_greedy (φ : CNF V) {P : ℕ}
    (hn : 1 ≤ Fintype.card V) (hP : 1 ≤ P) (A : ℕ → List (Fin φ.length → Bool))
    (hinit : ∀ σ, PassesTests φ.violations (A 0) σ → φ.eval σ = false →
      φ.length ≤ P * weight (φ.violations σ))
    (γ : ℕ → Fin P → Fin φ.length × Bool) (hA : ∀ i, A (i + 1) = A i ++ [testRow (γ i)])
    (hγ : ∀ i (γ' : Fin P → Fin φ.length × Bool),
      commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow (γ i)])) ≤
        commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ']))) :
    commonZeroCount univ (φ.parityRowSystem (A (3 * Fintype.card V))) =
      φ.modelCountOn Finset.univ := by
  rw [CNF.commonZeroCount_parityRowSystem]
  have hγ_pass : ∀ i (γ' : Fin P → Fin φ.length × Bool),
      numPassing φ.violations (A i ++ [testRow (γ i)]) ≤
        numPassing φ.violations (A i ++ [testRow γ']) := by
    intro i γ'
    simpa only [CNF.commonZeroCount_parityRowSystem] using hγ i γ'
  rw [CNF.numPassing_greedy φ hn hP A hinit γ hA hγ_pass, CNF.modelCountOn_univ]

/-- **Lemmas 6.1–6.2 & §6.3 (initial + greedy parity tests via `commonZeroCount` with system
sparsity and scope bounds)**: for any width-`≤ k` CNF `φ` on `n = Fintype.card V ≥ 1` variables with
`φ.length ≤ B * n` (`B ≥ 1`), there exist initial parity rows `A₀` (`A₀.length ≤ 3 * n`, each of
weight at most `D₀ = initialRowWeightBound B φ.length`) such that for any greedy sequence
`A (i + 1) = A i ++ [testRow (γ i)]` with `A 0 = A₀` minimizing
`commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ']))` over candidate rows of list length
`P = greedyRowListLength B φ.length`:
1. After `3 * n` rounds, `commonZeroCount univ (φ.parityRowSystem (A (3 * n))) =
   φ.modelCountOn Finset.univ`.
2. At every stage `i ≤ 3 * n`, `(A i).length ≤ 6 * n`, and every compiled equation
   `φ.parityRowSystem (A i) j` has degree at most `k`, at most `max D₀ P * 2 ^ k` monomials, and
   variable-scope size `#(equationScope (φ.parityRowSystem (A i) j)) ≤ k * (max D₀ P * 2 ^ k)`. -/
theorem CNF.exists_initialTests_commonZeroCount_greedy (φ : CNF V) {k B : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (hn : 1 ≤ Fintype.card V) (hB : 1 ≤ B)
    (hm : φ.length ≤ B * Fintype.card V) :
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
          ∀ j : Fin (A i).length,
            (∀ M ∈ φ.parityRowSystem (A i) j, M ⊆ φ.vars.toFinset ∧ #M ≤ k) ∧
            #(φ.parityRowSystem (A i) j) ≤ max D₀ P * 2 ^ k ∧
            #(equationScope (φ.parityRowSystem (A i) j)) ≤ k * (max D₀ P * 2 ^ k) := by
  dsimp only [initialRowWeightBound, greedyRowListLength]
  obtain ⟨A₀, hlen, hw, hgreedy⟩ := φ.numPassing_greedy_initial hn hB hm
  refine ⟨A₀, hlen, hw, fun A γ h0 hA hγ => ⟨?_, fun i hi => ?_⟩⟩
  · rw [CNF.commonZeroCount_parityRowSystem, CNF.modelCountOn_univ]
    refine hgreedy A γ h0 hA fun i γ' => ?_
    simpa only [CNF.commonZeroCount_parityRowSystem] using hγ i γ'
  · have hbounds := φ.greedy_system_bounds hk A (h0 ▸ hlen) (h0 ▸ hw) γ hA hi
    have hlen_i : (A i).length ≤ 6 * Fintype.card V := by
      simpa only [List.length_map] using hbounds.1
    refine ⟨hlen_i, fun j => ?_⟩
    have hj_mem : φ.parityRowSystem (A i) j ∈ (A i).map φ.parityRowMonomials :=
      List.mem_map.mpr ⟨(A i).get j, List.get_mem (A i) j, rfl⟩
    obtain ⟨hM_bounds, hcard_le⟩ := hbounds.2 (φ.parityRowSystem (A i) j) hj_mem
    refine ⟨hM_bounds, hcard_le, ?_⟩
    exact (card_equationScope_le fun M hM => (hM_bounds M hM).2).trans
      (Nat.mul_le_mul_left k hcard_le)

/-- **§5.4–5.5 & §6.3 (branch-summed cleared-denominator recovery of `φ.modelCountOn Finset.univ`
after `3 * n` greedy rounds)**: under the hypotheses of
`CNF.commonZeroCount_parityRowSystem_greedy`, for any heavy-variable set `S : Finset V`,
free-variable relabeling `e : ↥(univ \ S) ≃ ι'`, nonzero common denominator `d_den ≠ 0`, and
cleared-denominator replacement family `θ` evaluating at `T = 0` to `d_den * bitVal ℤ (x v)`,
summing the branch modular residues of `univariateClearedParityTruncatedSum` divided by
`clearedProductDenom` at shared precision `branchPrecision (Fintype.card V)` across all
`b ∈ branchAssignments S` recovers `φ.modelCountOn Finset.univ`. -/
theorem CNF.modelCountOn_eq_sum_branch_emod_ediv_cleared_greedy {ι' : Type*}
    [Fintype ι'] [DecidableEq ι'] (φ : CNF V) {k P : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (hn : 1 ≤ Fintype.card V) (hP : 1 ≤ P)
    (A : ℕ → List (Fin φ.length → Bool))
    (hinit : ∀ σ, PassesTests φ.violations (A 0) σ → φ.eval σ = false →
      φ.length ≤ P * weight (φ.violations σ))
    (γ : ℕ → Fin P → Fin φ.length × Bool) (hA : ∀ i, A (i + 1) = A i ++ [testRow (γ i)])
    (hγ : ∀ i (γ' : Fin P → Fin φ.length × Bool),
      commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow (γ i)])) ≤
        commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ'])))
    (S : Finset V) (e : ↥(univ \ S) ≃ ι') {d_den : ℤ} (hd : d_den ≠ 0)
    (θ : (V → Bool) → (ι' → Bool) → Fin (A (3 * Fintype.card V)).length → ι' → Polynomial ℤ)
    (hθ : ∀ b ∈ branchAssignments S, ∀ x : ι' → Bool,
      ∀ j ∈ (univ : Finset (Fin (A (3 * Fintype.card V)).length)),
      ∀ M ∈ relabelRestrictedMonomials S e b (φ.parityRowSystem (A (3 * Fintype.card V)) j),
      ∀ v ∈ M, (θ b x j v).eval 0 = d_den * bitVal ℤ (x v)) :
    (φ.modelCountOn Finset.univ : ℤ) =
      ∑ b ∈ branchAssignments S,
        ((univariateClearedParityTruncatedSum
          (univ : Finset (Fin (A (3 * Fintype.card V)).length))
          (fun j => relabelRestrictedMonomials S e b (φ.parityRowSystem (A (3 * Fintype.card V)) j))
          d_den k (branchPrecision (Fintype.card V)) (θ b)).eval 0 /
            clearedProductDenom d_den k (branchPrecision (Fintype.card V))
              #(univ : Finset (Fin (A (3 * Fintype.card V)).length))) %
                ((2 : ℤ) ^ branchPrecision (Fintype.card V)) := by
  rw [← CNF.commonZeroCount_parityRowSystem_greedy φ hn hP A hinit γ hA hγ]
  exact commonZeroCount_eq_sum_branch_emod_ediv_cleared S e univ
    (φ.parityRowSystem (A (3 * Fintype.card V))) hd θ
    (fun j _ M hM => CNF.card_mem_parityRowSystem_le hk (A (3 * Fintype.card V)) j hM) hθ

end GreedyParityCounter

end Cslib.Logic.PL
