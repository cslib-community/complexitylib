/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.Exponents
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Search
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.PolyTime
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Logics.Propositional.ClauseSet.Sparsification
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Algorithmic sparsification

The sparsification lemma of Impagliazzo, Paturi and Zane [ImpagliazzoPaturiZane2001] on the native
machines: a depth-first search of the sparsification tree, with a decider applied at its leaves,
runs within time `2 ^ (ε n)` times the sum of a polynomial and the time of the decider on formulas
with at most `c n + 1` clauses, on formulas with `n` variables. Hence a decider for `k`-SAT within
time `2 ^ (δ m)` times a polynomial, on formulas with `m` clauses, gives one within time
`2 ^ ((ε + c δ) n)` times a polynomial, on formulas with `n` variables
(`Cslib.Complexity.exists_decidableInExpTime_numVars_of_length`), and the exponential time
hypothesis says that 3SAT is not decidable in subexponential time in the number of clauses
(`Cslib.Complexity.ETH_iff_not_decidableInSubexpTime_length`).

The search (`Cslib.Complexity.Sparsify.search`) keeps a stack of formulas and an accumulator
(`Cslib.Complexity.Sparsify.step`). It starts from the normal form of the formula
(`Cslib.Logic.PL.CNF.Sparsification.normalize`); at a sparse formula on top of the stack it runs
the decider, and at any other formula it pushes the two children of the list-level step
(`Cslib.Logic.PL.CNF.Sparsification.next`), which is polynomial-time. This is the depth-first
search of the branching tree of the list-level rule
(`Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule.exists_iterate_searchStep`), so it visits
every leaf within twice the number of leaves of steps, which is at most `2 ^ (ε n)` up to a
constant for the thresholds given by
`Cslib.Logic.PL.ClauseSet.Sparsification.exists_sum_choose_le`. Meanwhile the stack holds at most
`O(n)` formulas of the tree, each with `O(n + m)` clauses, and the leaves, being sparse, have at
most `c n + 1` clauses (`Cslib.Logic.PL.ClauseSet.Sparsification.card_le_of_sparse`). The search
runs a fixed number `2 ^ (n / M + 2)` of rounds, the last ones on the empty stack, for `ε = 1 / M`.

## Main definitions

* `Cslib.Complexity.Sparsify.step`, `Cslib.Complexity.Sparsify.search`: the search.

## Main results

* `Cslib.Complexity.Sparsify.search_eq_true_iff`: the search decides satisfiability.
* `Cslib.Complexity.Sparsify.decidableInExpTime_search`: the time of the search.
* `Cslib.Complexity.exists_decidableInExpTime_numVars_of_length`: from clauses to variables.
* `Cslib.Complexity.DecidableInSubexpTime.numVars_of_length`: subexponential time in the number of
  clauses gives subexponential time in the number of variables.
* `Cslib.Complexity.ETH_iff_not_decidableInSubexpTime_length`: the exponential time hypothesis in
  terms of clauses.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification Turing.MultiTapeTM
open scoped List

namespace Sparsify

open ClauseSet.Sparsification (threshold base one_le_threshold BranchingRule)

/-! ### The search -/

/-- The states of the search: a stack of formulas and an accumulator. -/
abbrev State : Type := List (CNF ℕ) × Bool

/-- States encoded as framed tuples. -/
private abbrev encState : State ↪ List Bool := encPair (encList encCNF) encBool

/-- One step of the depth-first search of the sparsification tree, for width `K` and the
thresholds `threshold K α`: a sparse formula on top of the stack is popped and the decider `g` is
run on it; any other formula on top is replaced by its two children. -/
def step (K α : ℕ) (g : CNF ℕ → Bool) (s : State) : State :=
  if s.1.isEmpty then s
  else if isSparse (threshold K α) K (s.1.headD []) then (s.1.tail, s.2 || g (s.1.headD []))
  else (next (threshold K α) K (s.1.headD []) false ::
    next (threshold K α) K (s.1.headD []) true :: s.1.tail, s.2)

/-- The root of the search: the normal form of a formula of width `k`, and the formula without
clauses otherwise. -/
def root (k : ℕ) (φ : CNF ℕ) : CNF ℕ :=
  if φ.all fun c => decide (c.length ≤ k) then normalize φ else []

/-- The number of rounds of the search, `2 ^ (n / M + 2)` on formulas with `n` variables. -/
def rounds (M : ℕ) (φ : CNF ℕ) : ℕ := 2 ^ (φ.distinctVars.length / M + 2)

/-- **The sparsification search**: run the search for the given number of rounds from the root,
and report the accumulator. -/
def search (K α k M : ℕ) (g : CNF ℕ → Bool) (φ : CNF ℕ) : Bool :=
  ((step K α g)^[rounds M φ] ([root k φ], false)).2

/-! ### The search is the depth-first search of the tree -/

variable {K α : ℕ} (hK : 1 ≤ K) (hα : 1 ≤ α)

/-- The list-level branching rule for width `K` and the thresholds `threshold K α`. -/
private abbrev rule : BranchingRule (threshold K α) ℕ {ψ : CNF ℕ // Normalized K ψ} :=
  CNF.Sparsification.rule (one_le_threshold hK hα) K

include hK hα in
private theorem step_map (g : CNF ℕ → Bool) (stk : List {ψ : CNF ℕ // Normalized K ψ})
    (acc : Bool) :
    step K α g (stk.map Subtype.val, acc) =
      Prod.map (List.map Subtype.val) id
        ((rule hK hα).searchStep (g ∘ Subtype.val) (stk, acc)) := by
  cases stk with
  | nil => rfl
  | cons s rest =>
    have hiff := isSparse_eq_true_iff (one_le_threshold hK hα) s.2
    by_cases hs : ClauseSet.Sparsification.Sparse (threshold K α) s.1.toClauseSet
    · have hs' : isSparse (threshold K α) K s.1 = true := hiff.mpr hs
      simp [step, BranchingRule.searchStep, hs, hs', CNF.Sparsification.rule]
    · have hs' : isSparse (threshold K α) K s.1 = false := by
        simpa using fun h => hs (hiff.mp h)
      simp [step, BranchingRule.searchStep, hs, hs', rule, CNF.Sparsification.rule]

include hK hα in
private theorem iterate_step_map (g : CNF ℕ → Bool) (n : ℕ)
    (stk : List {ψ : CNF ℕ // Normalized K ψ})
    (acc : Bool) :
    (step K α g)^[n] (stk.map Subtype.val, acc) =
      Prod.map (List.map Subtype.val) id
        (((rule hK hα).searchStep (g ∘ Subtype.val))^[n] (stk, acc)) := by
  induction n generalizing stk acc with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, step_map hK hα]
    obtain ⟨stk', acc'⟩ := (rule hK hα).searchStep (g ∘ Subtype.val) (stk, acc)
    exact ih stk' acc'

private theorem step_nil (g : CNF ℕ → Bool) (acc : Bool) : step K α g ([], acc) = ([], acc) := rfl

private theorem iterate_step_nil (g : CNF ℕ → Bool) (n : ℕ) (acc : Bool) :
    (step K α g)^[n] ([], acc) = ([], acc) :=
  Function.iterate_fixed (step_nil g acc) n

/-! ### The root -/

private theorem normalized_root {k : ℕ} (hkK : k ≤ K) (φ : CNF ℕ) : Normalized K (root k φ) := by
  unfold root
  split_ifs with h
  · simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact normalized_normalize fun C hC => (h C hC).trans hkK
  · exact ⟨by simp, by simp, by simp, by simp [CNF.toClauseSet, ClauseSet.Sparsification.Reduced]⟩

/-- Every clause of the root has the literals of a clause of the formula. -/
private theorem exists_of_mem_root {k : ℕ} {φ : CNF ℕ} {C : Clause ℕ} (hC : C ∈ root k φ) :
    ∃ D ∈ φ, C.toFinset = D.toFinset := by
  unfold root at hC
  split_ifs at hC
  · have hsub : normalize φ <+ φ.map dedup :=
      (reduce_sublist _).trans (dedupClauses_sublist _)
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (hsub.subset hC)
    exact ⟨D, hD, toFinset_dedup D⟩
  · simp at hC

private theorem length_root_le (k : ℕ) (φ : CNF ℕ) : (root k φ).length ≤ φ.length := by
  unfold root
  split_ifs
  · exact ((reduce_sublist _).trans (dedupClauses_sublist _)).length_le.trans
      (List.length_map _).le
  · exact Nat.zero_le _

/-- The root as a state of the list-level rule. -/
private def rootState {k : ℕ} (hkK : k ≤ K) (φ : CNF ℕ) : {ψ : CNF ℕ // Normalized K ψ} :=
  ⟨root k φ, normalized_root hkK φ⟩

private theorem mem_vars_of_mem_root {k : ℕ} {φ : CNF ℕ} :
    ∀ C ∈ (root k φ).toClauseSet, ∀ l ∈ C, l.1 ∈ φ.vars.toFinset := by
  intro C hC l hl
  obtain ⟨C', hC', rfl⟩ := mem_toClauseSet.mp hC
  obtain ⟨D, hD, hDeq⟩ := exists_of_mem_root hC'
  rw [hDeq, List.mem_toFinset] at hl
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨D, hD, hl⟩, rfl⟩)

/-! ### The states of the tree -/

/-- The bound `2 ∑_{j < K} θ j` on the occurrences of a variable in a sparse formula. -/
def occBound (K α : ℕ) : ℕ := 2 * ∑ j ∈ Finset.range K, threshold K α j

section Tree

variable {k : ℕ} (hkK : k ≤ K) {φ : CNF ℕ} {w : List Bool}
include hK hα hkK

/-- Every clause of a state of the tree has its literals in a clause of the formula. -/
private theorem exists_of_mem_walk (hw : (rule hK hα).IsNodeWord (rootState hkK φ) w) {C : Clause ℕ}
    (hC : C ∈ ((rule hK hα).walk (rootState hkK φ) w).1) :
    ∃ D ∈ φ, C.toFinset ⊆ D.toFinset := by
  obtain ⟨D', hD', hCD'⟩ := BranchingRule.IsNodeWord.refines_walk (one_le_threshold hK hα) hw
    C.toFinset (mem_toClauseSet.mpr ⟨C, hC, rfl⟩)
  obtain ⟨D'', hD'', rfl⟩ := mem_toClauseSet.mp hD'
  obtain ⟨D, hD, hDeq⟩ := exists_of_mem_root hD''
  exact ⟨D, hD, hDeq ▸ hCD'⟩

/-- The states of the tree have at most `m + n K X ^ (2 K)` clauses. -/
private theorem length_walk_le (hw : (rule hK hα).IsNodeWord (rootState hkK φ) w) :
    ((rule hK hα).walk (rootState hkK φ) w).1.length ≤
      φ.length + φ.numVars * (K * base K α ^ (2 * K)) := by
  have h : (((rule hK hα).walk (rootState hkK φ) w).1.toClauseSet).card ≤
      (rootState hkK φ).1.toClauseSet.card + φ.vars.toFinset.card * (K * base K α ^ (2 * K)) :=
    BranchingRule.IsNodeWord.card_walk_le hK hα (rootState hkK φ).2.reduced
      (rootState hkK φ).2.card_le φ.vars.toFinset mem_vars_of_mem_root hw
  rw [Normalized.card_toClauseSet ((rule hK hα).walk (rootState hkK φ) w).2] at h
  refine h.trans (Nat.add_le_add_right ?_ _)
  rw [Normalized.card_toClauseSet (rootState hkK φ).2]
  exact length_root_le k φ

/-- **The leaves are small.** The sparse states of the tree have at most `c n + 1` clauses, for
`c = occBound K α`. -/
private theorem length_walk_le_of_isSparse (hw : (rule hK hα).IsNodeWord (rootState hkK φ) w)
    (hs : isSparse (threshold K α) K ((rule hK hα).walk (rootState hkK φ) w).1 = true) :
    ((rule hK hα).walk (rootState hkK φ) w).1.length ≤ occBound K α * φ.numVars + 1 := by
  set ψ := (rule hK hα).walk (rootState hkK φ) w
  have hsparse := (isSparse_eq_true_iff (one_le_threshold hK hα) ψ.2).mp hs
  rw [← Normalized.card_toClauseSet ψ.2]
  refine ClauseSet.Sparsification.card_le_of_sparse (one_le_threshold hK hα) hsparse ψ.2.card_le
    φ.vars.toFinset fun C' hC' l hl => ?_
  obtain ⟨C, hC, rfl⟩ := mem_toClauseSet.mp hC'
  obtain ⟨D, hD, hCD⟩ := exists_of_mem_walk hK hα hkK hw hC
  have hl' := List.mem_toFinset.mp (hCD hl)
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨D, hD, hl'⟩, rfl⟩)

/-- The states of the tree from a formula of width `k` have width `k`. -/
private theorem length_le_of_mem_walk (hφ : ∀ c ∈ φ, c.length ≤ k)
    (hw : (rule hK hα).IsNodeWord (rootState hkK φ) w) {C : Clause ℕ}
    (hC : C ∈ ((rule hK hα).walk (rootState hkK φ) w).1) : C.length ≤ k := by
  obtain ⟨D, hD, hCD⟩ := exists_of_mem_walk hK hα hkK hw hC
  rw [← List.toFinset_card_of_nodup (((rule hK hα).walk (rootState hkK φ) w).2.nodup C hC)]
  exact (Finset.card_le_card hCD).trans ((List.toFinset_card_le D).trans (hφ D hD))

end Tree

/-! ### The run of the search -/

/-- The number of leaves is within the number of rounds: the bound on the binomial tail that
`Cslib.Logic.PL.ClauseSet.Sparsification.exists_sum_choose_le` provides for `ε = 1 / M`. -/
def LeafBound (K α M : ℕ) : Prop :=
  ∀ N : ℕ, ∑ j ∈ Finset.range ((K - 1) * N / α + 1),
    (N * (K * base K α ^ (2 * K))).choose j ≤ 2 ^ (N / M + 1)

open Classical in
/-- **The run of the search.** After the rounds, the stack is empty and the accumulator records
whether the decider accepts a leaf of the tree. Meanwhile the stack holds at most
`n K X ^ (2 K) + 1` states of the tree. -/
private theorem iterate_step {k M : ℕ} (hkK : k ≤ K) (hM : LeafBound K α M) (g : CNF ℕ → Bool)
    (φ : CNF ℕ) :
    (step K α g)^[rounds M φ] ([root k φ], false) =
      ([], decide (∃ w, (rule hK hα).IsLeafWord (rootState hkK φ) w ∧
        g ((rule hK hα).walk (rootState hkK φ) w).1 = true)) ∧
    ∀ i, ∃ (stk : List {ψ : CNF ℕ // Normalized K ψ}) (acc : Bool),
      (step K α g)^[i] ([root k φ], false) = (stk.map Subtype.val, acc) ∧
      stk.length ≤ φ.numVars * (K * base K α ^ (2 * K)) + 1 ∧
      ∀ t ∈ stk, ∃ w, (rule hK hα).IsNodeWord (rootState hkK φ) w ∧
        (rule hK hα).walk (rootState hkK φ) w = t := by
  set R := rule hK hα
  set s₀ := rootState hkK φ
  have hred := s₀.2.reduced
  have hk0 := s₀.2.card_le
  have hlen : ∀ w, R.IsLeafWord s₀ w → w.length ≤ φ.numVars * (K * base K α ^ (2 * K)) :=
    fun w hw => hw.length_le hK hα hred hk0 φ.vars.toFinset mem_vars_of_mem_root
  obtain ⟨W, hW, N, hN, h⟩ := BranchingRule.exists_iterate_searchStep (R := R)
    (one_le_threshold hK hα) (g ∘ Subtype.val) s₀ hlen
  have hWcard : W.card ≤ 2 ^ (φ.numVars / M + 1) :=
    (BranchingRule.card_le_of_isLeafWord hK hα hred hk0 φ.vars.toFinset mem_vars_of_mem_root W
      hW).trans (hM φ.numVars)
  have hNr : N ≤ rounds M φ := by
    rw [rounds, CNF.length_distinctVars, pow_succ]
    omega
  have hinit : ([root k φ], false) = ([s₀].map Subtype.val, false) := rfl
  obtain ⟨hfin, hmid⟩ := h [] false
  have hN' : (step K α g)^[N] ([root k φ], false) = ([], decide (∃ w, R.IsLeafWord s₀ w ∧
      g (R.walk s₀ w).1 = true)) := by
    rw [hinit, iterate_step_map hK hα, hfin]
    simp
  refine ⟨?_, fun i => ?_⟩
  · rw [show rounds M φ = (rounds M φ - N) + N by omega, Function.iterate_add_apply, hN',
      iterate_step_nil]
  · by_cases hi : i ≤ N
    · obtain ⟨stk, acc', heq, hstk, hmem⟩ := hmid i hi
      refine ⟨stk, acc', ?_, hstk, hmem⟩
      rw [hinit, iterate_step_map hK hα, heq]
      simp
    · refine ⟨[], decide (∃ w, R.IsLeafWord s₀ w ∧ g (R.walk s₀ w).1 = true), ?_, by simp,
        by simp⟩
      rw [show i = (i - N) + N by omega, Function.iterate_add_apply, hN', iterate_step_nil]
      rfl

include hK hα in
/-- **The search decides satisfiability.** If the decider decides satisfiability on formulas of
width `k`, the search decides satisfiability on formulas of width `k`. -/
theorem search_eq_true_iff {k M : ℕ} (hkK : k ≤ K) (hM : LeafBound K α M) {g : CNF ℕ → Bool}
    (hg : ∀ ψ : CNF ℕ, (∀ c ∈ ψ, c.length ≤ k) → (g ψ = true ↔ ψ.Satisfiable)) {φ : CNF ℕ}
    (hφ : ∀ c ∈ φ, c.length ≤ k) : search K α k M g φ = true ↔ φ.Satisfiable := by
  classical
  set R := rule hK hα
  set s₀ := rootState hkK φ
  rw [search, (iterate_step hK hα hkK hM g φ).1, decide_eq_true_iff]
  have hroot : (root k φ) = normalize φ := by
    rw [root, ite_eq_left (List.all_eq_true.mpr fun c hc => decide_eq_true (hφ c hc))]
  constructor
  · rintro ⟨w, hw, hgw⟩
    obtain ⟨x, hx⟩ := (hg _ fun c hc => length_le_of_mem_walk hK hα hkK hφ hw.isNodeWord hc).mp
      hgw
    refine ⟨x, ?_⟩
    have hsat : (R.toClauseSet (R.walk s₀ w)).Sat x := (CNF.sat_toClauseSet_iff _ x).mpr hx
    have := (BranchingRule.exists_isLeafWord_sat_iff (one_le_threshold hK hα) s₀ x).mp
      ⟨w, hw, hsat⟩
    change (root k φ).toClauseSet.Sat x at this
    rwa [hroot, sat_toClauseSet_normalize_iff] at this
  · rintro ⟨x, hx⟩
    have hsat : (R.toClauseSet s₀).Sat x := by
      change (root k φ).toClauseSet.Sat x
      rwa [hroot, sat_toClauseSet_normalize_iff]
    obtain ⟨w, hw, hwx⟩ :=
      (BranchingRule.exists_isLeafWord_sat_iff (one_le_threshold hK hα) s₀ x).mpr hsat
    refine ⟨w, hw, (hg _ fun c hc => length_le_of_mem_walk hK hα hkK hφ hw.isNodeWord hc).mpr
      ⟨x, (CNF.sat_toClauseSet_iff _ x).mp hwx⟩⟩

/-! ### Polynomial-time parts -/

section PolyTime

open ComputableInPolyTime

@[local fun_prop]
private theorem computableInPolyTime_listIsEmpty {β : Type} (enc : β ↪ List Bool) :
    ComputableInPolyTime List.isEmpty (encList enc) encBool := by
  have heq : (List.isEmpty : List β → Bool) = fun l => decide (l.length = 0) := by
    funext l; cases l <;> simp
  rw [heq]
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_listTail {β : Type} (enc : β ↪ List Bool) :
    ComputableInPolyTime List.tail (encList enc) (encList enc) := by
  have heq : (List.tail : List β → List β) = fun l => l.drop 1 := by
    funext l; cases l <;> rfl
  rw [heq]
  exact (dropUnary (encA := enc)).comp (id'.prod (const 1))

private theorem computableInPolyTime_isSparse_head (K α : ℕ) :
    ComputableInPolyTime (fun s : State => isSparse (threshold K α) K (s.1.headD []))
      encState encBool := by
  have h := computableInPolyTime_isSparse encNat
    (ClauseSet.Sparsification.computableInPolyTime_threshold_le K α) K
  have hH : ComputableInPolyTime (fun s : State => s.1.headD []) encState encCNF := by
    unfold encState
    fun_prop
  exact h.comp hH

private theorem computableInPolyTime_inner (K α : ℕ) :
    ComputableInPolyTime (fun s : State => (next (threshold K α) K (s.1.headD []) false ::
      next (threshold K α) K (s.1.headD []) true :: s.1.tail, s.2)) encState encState := by
  have h := computableInPolyTime_next encNat
    (ClauseSet.Sparsification.computableInPolyTime_threshold_le K α) K
  unfold encState encCNF
  fun_prop

private theorem computableInPolyTime_root (k : ℕ) :
    ComputableInPolyTime (fun φ : CNF ℕ => (([root k φ], false) : State)) encCNF
      encState := by
  have h := computableInPolyTime_normalize encNat
  unfold root encState encCNF
  fun_prop

private theorem computableInPolyTime_rounds (M : ℕ) :
    ComputableInPolyTime (rounds M) encCNF encNat := by
  have hvars := SAT.computableInPolyTime_distinctVars
  have h := unary_div_const M
  unfold rounds
  fun_prop

/-- **The time of a step**: a polynomial in the length of the encoded state, plus the time of the
decider when it runs on the formula on top of the stack. -/
private theorem exists_computableInO_step (K α : ℕ) {g : CNF ℕ → Bool} {t : CNF ℕ → ℕ}
    (hg : ComputableInO g encCNF encBool t t) :
    ∃ d, ComputableInO (step K α g) encState encState
      (fun s => ((encState s).length + 1) ^ d +
        if s.1.isEmpty = false ∧ isSparse (threshold K α) K (s.1.headD []) = true then
          t (s.1.headD []) else 0)
      (fun s => ((encState s).length + 1) ^ d +
        if s.1.isEmpty = false ∧ isSparse (threshold K α) K (s.1.headD []) = true then
          t (s.1.headD []) else 0) := by
  obtain ⟨dE, eE, hE⟩ := (show ComputableInPolyTime (fun s : State => s.1.isEmpty) encState
    encBool by unfold encState; fun_prop).exists_degree
  obtain ⟨dI, eI, hI⟩ := (id' (encIn := encState)).exists_degree
  obtain ⟨dS, eS, hS⟩ := (computableInPolyTime_isSparse_head K α).exists_degree
  obtain ⟨dH, eH, hH⟩ := (show ComputableInPolyTime (fun s : State => s.1.headD []) encState
    encCNF by unfold encState; fun_prop).exists_degree
  obtain ⟨dB, eB, hB⟩ := (show ComputableInPolyTime (fun s : State => s.2) encState
    encBool by unfold encState; fun_prop).exists_degree
  obtain ⟨dT, eT, hT⟩ := (show ComputableInPolyTime (fun s : State => s.1.tail) encState
    (encList encCNF) by unfold encState; fun_prop).exists_degree
  obtain ⟨dN, eN, hN⟩ := (computableInPolyTime_inner K α).exists_degree
  obtain ⟨dO, eO, hO⟩ := bool_or.exists_degree
  set D := dE + dI + dS + dH + dB + dT + dN
  have hE' := (hE.mono (d' := D) (e' := eE) (by omega) le_rfl).inO
  have hI' := (hI.mono (d' := D) (e' := eI) (by omega) le_rfl).inO
  have hS' := (hS.mono (d' := D) (e' := eS) (by omega) le_rfl).inO
  have hH' := (hH.mono (d' := D) (e' := eH) (by omega) le_rfl).inO
  have hB' := (hB.mono (d' := D) (e' := eB) (by omega) le_rfl).inO
  have hT' := (hT.mono (d' := D) (e' := eT) (by omega) le_rfl).inO
  have hN' := (hN.mono (d' := D) (e' := eN) (by omega) le_rfl).inO
  have hleaf := hT'.prod (hO.inO.comp (hB'.prod (hg.comp hH')))
  have h := hE'.ite hI' (hS'.ite hleaf hN')
  have h4 (p : Bool × Bool) : (encPair encBool encBool p).length = 4 := by simp
  refine ⟨D, (h.mono (5 ^ dO + 7) (fun s => ?_) (fun s => ?_))⟩ <;>
  · simp only [Function.comp_apply, h4]
    generalize ((encState s).length + 1) ^ D = P
    generalize t (s.1.headD []) = T
    have hF : 1 ≤ (4 + 1) ^ dO := Nat.one_le_pow _ _ (by norm_num)
    generalize (4 + 1) ^ dO = F at hF ⊢
    cases s.1.isEmpty <;> cases isSparse (threshold K α) K (s.1.headD []) <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, and_true, and_false,
        Bool.true_eq_false] <;> nlinarith

end PolyTime

/-! ### Sizes -/

/-- A bound on the length of the encoded states of the tree. -/
private def nodeBound (K α : ℕ) (φ : CNF ℕ) : ℕ :=
  (φ.length + φ.numVars * (K * base K α ^ (2 * K))) *
    (2 * (K * (2 * (encCNF φ).length + 1)) + 1)

/-- A bound on the length of the encoded states of the search. -/
private def stateBound (K α : ℕ) (φ : CNF ℕ) : ℕ :=
  2 * ((φ.numVars * (K * base K α ^ (2 * K)) + 1) * (2 * nodeBound K α φ + 1)) + 2

private theorem length_encLiteral_le {φ : CNF ℕ} {D : Clause ℕ} (hD : D ∈ φ) {l : Literal ℕ}
    (hl : l ∈ D) : (encPair encNat encBool l).length ≤ (encCNF φ).length :=
  (length_le_encList_of_mem _ hl).trans (length_le_encList_of_mem _ hD)

section Sizes

variable {k : ℕ} (hkK : k ≤ K) {φ : CNF ℕ}
include hK hα hkK

private theorem length_encCNF_walk_le {w : List Bool}
    (hw : (rule hK hα).IsNodeWord (rootState hkK φ) w) :
    (encCNF ((rule hK hα).walk (rootState hkK φ) w).1).length ≤ nodeBound K α φ := by
  set ψ := (rule hK hα).walk (rootState hkK φ) w
  refine (length_encList_le _ ψ.1 (b := K * (2 * (encCNF φ).length + 1)) fun C hC => ?_).trans
    (Nat.mul_le_mul_right _ (length_walk_le hK hα hkK hw))
  refine (length_encList_le _ C (b := (encCNF φ).length) fun l hl => ?_).trans
    (Nat.mul_le_mul_right _ (ψ.2.length_le C hC))
  obtain ⟨D, hD, hCD⟩ := exists_of_mem_walk hK hα hkK hw hC
  exact length_encLiteral_le hD (List.mem_toFinset.mp (hCD (List.mem_toFinset.mpr hl)))

private theorem length_encState_le {stk : List {ψ : CNF ℕ // Normalized K ψ}} {acc : Bool}
    (hstk : stk.length ≤ φ.numVars * (K * base K α ^ (2 * K)) + 1)
    (hmem : ∀ t ∈ stk, ∃ w, (rule hK hα).IsNodeWord (rootState hkK φ) w ∧
      (rule hK hα).walk (rootState hkK φ) w = t) :
    (encState (stk.map Subtype.val, acc)).length ≤ stateBound K α φ := by
  have h := length_encList_le encCNF (stk.map Subtype.val) (b := nodeBound K α φ) fun ψ hψ => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hψ
    obtain ⟨w, hw, rfl⟩ := hmem t ht
    exact length_encCNF_walk_le hK hα hkK hw
  rw [List.length_map] at h
  have h' := h.trans (Nat.mul_le_mul_right _ hstk)
  simp only [encState, length_encPair, encBool_apply, List.length_singleton, stateBound]
  omega

end Sizes

/-! ### The time of the search -/

/-- The time bound of the decider on the leaves of the tree. -/
private noncomputable def leafTime (K α : ℕ) (δ : ℝ) (c e : ℕ) (φ : CNF ℕ) : ℕ :=
  ⌈(c : ℝ) * (2 ^ (δ * ((occBound K α * φ.numVars + 1 : ℕ) : ℝ)) *
    ((nodeBound K α φ : ℝ) + 1) ^ e) + c⌉₊

include hK hα in
/-- **The time of the rounds.** The search is computed within `rounds M φ + 1` times the bound on
a round: a polynomial in the length of the encoded states (`stateBound`), plus the time bound of
the decider on the leaves (`leafTime`), plus the cost of the counter; and within polynomial time
for the start. -/
private theorem exists_computableInO_search {k M : ℕ} (hkK : k ≤ K) (hM : LeafBound K α M)
    {g : CNF ℕ → Bool} {t : CNF ℕ → ℕ} (hg : ComputableInO g encCNF encBool t t)
    {δ : ℝ} (hδ : 0 ≤ δ) {c e : ℕ}
    (ht : ∀ ψ : CNF ℕ, (t ψ : ℝ) ≤ c * (2 ^ (δ * ψ.length) * ((encCNF ψ).length + 1) ^ e) + c) :
    ∃ d dn di, ComputableInO (search K α k M g) encCNF encBool
      (fun φ => ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
        (rounds M φ + 1) * ((stateBound K α φ + 1) ^ d + leafTime K α δ c e φ +
          stateBound K α φ + ((encNat (rounds M φ)).length + 1) ^ 2))
      (fun φ => ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
        ((stateBound K α φ + 1) ^ d + leafTime K α δ c e φ) + stateBound K α φ +
          (encNat (rounds M φ)).length) := by
  obtain ⟨d, hstep⟩ := exists_computableInO_step K α hg
  obtain ⟨dn, en, hn⟩ := (computableInPolyTime_rounds M).exists_degree
  obtain ⟨di, ei, hi⟩ := (computableInPolyTime_root k).exists_degree
  have hround : ∀ φ, ∀ i ≤ rounds M φ,
      (fun s : State => ((encState s).length + 1) ^ d +
        if s.1.isEmpty = false ∧ isSparse (threshold K α) K (s.1.headD []) = true then
          t (s.1.headD []) else 0) ((step K α g)^[i] ([root k φ], false)) ≤
        (stateBound K α φ + 1) ^ d + leafTime K α δ c e φ := by
    intro φ i _
    obtain ⟨stk, acc, heq, hstk, hmem⟩ := (iterate_step hK hα hkK hM g φ).2 i
    rw [heq]
    have hS := length_encState_le hK hα hkK hstk hmem (acc := acc)
    refine Nat.add_le_add (Nat.pow_le_pow_left (by omega) d) ?_
    split_ifs with hc
    · cases stk with
      | nil => simp at hc
      | cons s rest =>
        obtain ⟨w, hw, rfl⟩ := hmem s List.mem_cons_self
        simp only [List.map_cons, List.headD_cons] at hc ⊢
        have hlen := length_walk_le_of_isSparse hK hα hkK hw hc.2
        have henc := length_encCNF_walk_le hK hα hkK hw
        set ψ := ((rule hK hα).walk (rootState hkK φ) w).1
        have h₁ : (2 : ℝ) ^ (δ * ψ.length) ≤
            2 ^ (δ * ((occBound K α * φ.numVars + 1 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (mul_le_mul_of_nonneg_left (by exact_mod_cast hlen) hδ)
        have h₂ : (((encCNF ψ).length : ℝ) + 1) ^ e ≤ ((nodeBound K α φ : ℝ) + 1) ^ e :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right henc 1) e
        have h₃ := mul_le_mul h₁ h₂ (by positivity) (by positivity)
        have h₄ := mul_le_mul_of_nonneg_left h₃ (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
        have h₅ := (ht ψ).trans (add_le_add h₄ le_rfl)
        exact Nat.cast_le.mp (h₅.trans (Nat.le_ceil _))
    · exact Nat.zero_le _
  have hstate : ∀ φ, ∀ i ≤ rounds M φ,
      (encState ((step K α g)^[i] ([root k φ], false))).length ≤ stateBound K α φ := by
    intro φ i _
    obtain ⟨stk, acc, heq, hstk, hmem⟩ := (iterate_step hK hα hkK hM g φ).2 i
    rw [heq]
    exact length_encState_le hK hα hkK hstk hmem
  exact ⟨d, dn, di, (ComputableInO.iterate hn.inO hi.inO
    hstep hround hround hstate).snd'⟩

include hK hα in
/-- **The time of the search.** With a decider within time `2 ^ (δ m)` times a polynomial, on
formulas with `m` clauses, the formulas accepted by the search are decidable within time
`2 ^ ((1 / M + c δ) n)` times a polynomial, on formulas with `n` variables, for
`c = occBound K α`. -/
theorem decidableInExpTime_search {k M : ℕ} (hkK : k ≤ K) (hM : LeafBound K α M)
    {g : CNF ℕ → Bool} {t : CNF ℕ → ℕ} (hg : ComputableInO g encCNF encBool t t)
    {δ : ℝ} (hδ : 0 ≤ δ) {c e : ℕ}
    (ht : ∀ ψ : CNF ℕ, (t ψ : ℝ) ≤ c * (2 ^ (δ * ψ.length) * ((encCNF ψ).length + 1) ^ e) + c) :
    DecidableInExpTime {φ | search K α k M g φ = true} encCNF CNF.numVars
      (1 / M + occBound K α * δ) := by
  obtain ⟨d, dn, di, h⟩ := exists_computableInO_search hK hα hkK hM hg hδ ht
  set Kx := K * base K α ^ (2 * K)
  set c₁ := (1 + Kx) * (6 * K + 1)
  set c₂ := 2 * (Kx + 1) * (2 * c₁ + 1) + 2
  set C₁ := (c₂ + 1) ^ d + c₂ + 16
  set E := dn + di + 3 * d + 2 * e + 3
  set C₂ : ℝ := c * 2 ^ δ * ((c₁ : ℝ) + 1) ^ e + c + 1
  set C₀ : ℝ := 2 + 5 * (C₁ + C₂)
  refine DecidableInExpTime.of_computableInO h (fun φ => Iff.rfl) ⌈C₀⌉₊ E fun φ => ?_
  set L := (encCNF φ).length
  set N := φ.numVars
  set P := (L + 1) ^ E
  have hNL : N ≤ L := φ.numVars_le_length_vars.trans (SAT.length_vars_le φ)
  have hmL : φ.length ≤ L := length_le_length_encList _ φ
  have hP (a : ℕ) (ha : a ≤ E) : (L + 1) ^ a ≤ P := Nat.pow_le_pow_right (Nat.succ_pos L) ha
  -- the sizes of the states
  have hnb : nodeBound K α φ ≤ c₁ * (L + 1) ^ 2 := by
    have h₁ : φ.length + N * Kx ≤ (1 + Kx) * (L + 1) := by nlinarith
    have h₂ : 2 * (K * (2 * L + 1)) + 1 ≤ (6 * K + 1) * (L + 1) := by nlinarith
    calc nodeBound K α φ ≤ ((1 + Kx) * (L + 1)) * ((6 * K + 1) * (L + 1)) :=
          Nat.mul_le_mul h₁ h₂
      _ = c₁ * (L + 1) ^ 2 := by ring
  have hsb : stateBound K α φ ≤ c₂ * (L + 1) ^ 3 := by
    have h₁ : N * Kx + 1 ≤ (Kx + 1) * (L + 1) := by nlinarith
    have h₂ : 2 * nodeBound K α φ + 1 ≤ (2 * c₁ + 1) * (L + 1) ^ 2 := by
      have : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos L)
      nlinarith
    have h₃ : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_pos L)
    have h₄ := Nat.mul_le_mul h₁ h₂
    have hdef : stateBound K α φ = 2 * ((N * Kx + 1) * (2 * nodeBound K α φ + 1)) + 2 := rfl
    have e₁ : 2 * (((Kx + 1) * (L + 1)) * ((2 * c₁ + 1) * (L + 1) ^ 2)) + 2 * (L + 1) ^ 3 =
        c₂ * (L + 1) ^ 3 := by simp only [c₂]; ring
    omega
  have henc : (encNat (rounds M φ)).length = N / M + 3 := by
    rw [rounds, CNF.length_distinctVars, encNat_two_pow, List.length_append,
      List.length_replicate, List.length_singleton]
  have hr : rounds M φ + 1 ≤ 5 * 2 ^ (N / M) := by
    have : rounds M φ = 4 * 2 ^ (N / M) := by
      rw [rounds, CNF.length_distinctVars, pow_add]
      ring
    have : 1 ≤ 2 ^ (N / M) := Nat.one_le_two_pow
    omega
  -- the polynomial parts
  have hpoly : (L + 1) ^ dn + (L + 1) ^ di ≤ 2 * P := by
    have := hP dn (by omega)
    have := hP di (by omega)
    omega
  have hrnd : (stateBound K α φ + 1) ^ d + stateBound K α φ +
      ((encNat (rounds M φ)).length + 1) ^ 2 ≤ C₁ * P := by
    have h₁ : (stateBound K α φ + 1) ^ d ≤ (c₂ + 1) ^ d * (L + 1) ^ (3 * d) := by
      rw [pow_mul, ← mul_pow]
      refine Nat.pow_le_pow_left ?_ d
      have : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_pos L)
      have e₁ : (c₂ + 1) * (L + 1) ^ 3 = c₂ * (L + 1) ^ 3 + (L + 1) ^ 3 := by ring
      omega
    have h₂ : ((encNat (rounds M φ)).length + 1) ^ 2 ≤ 16 * (L + 1) ^ 2 := by
      rw [henc]
      have : N / M + 3 + 1 ≤ 4 * (L + 1) := by
        have := (Nat.div_le_self N M).trans hNL
        omega
      calc (N / M + 3 + 1) ^ 2 ≤ (4 * (L + 1)) ^ 2 := Nat.pow_le_pow_left this 2
        _ = 16 * (L + 1) ^ 2 := by ring
    have h₃ := hP (3 * d) (by omega)
    have h₄ := hP 3 (by omega)
    have h₅ := hP 2 (by omega)
    have h₆ := Nat.mul_le_mul_left ((c₂ + 1) ^ d) h₃
    have h₇ := Nat.mul_le_mul_left c₂ (hsb.trans (Nat.mul_le_mul_left c₂ h₄) |>.trans le_rfl)
    calc (stateBound K α φ + 1) ^ d + stateBound K α φ + ((encNat (rounds M φ)).length + 1) ^ 2
        ≤ (c₂ + 1) ^ d * P + c₂ * P + 16 * P := by
          have := hsb.trans (Nat.mul_le_mul_left c₂ h₄)
          have := h₂.trans (Nat.mul_le_mul_left 16 h₅)
          omega
      _ = C₁ * P := by ring
  -- the leaves
  set Y : ℝ := 2 ^ ((occBound K α * δ) * N)
  have hY : 1 ≤ Y := Real.one_le_rpow (by norm_num) (by positivity)
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast Nat.one_le_pow _ _ (Nat.succ_pos L)
  have hleaf : (leafTime K α δ c e φ : ℝ) ≤ C₂ * Y * P := by
    have h₁ : (2 : ℝ) ^ (δ * ((occBound K α * N + 1 : ℕ) : ℝ)) = 2 ^ δ * Y := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    have h₂ : ((nodeBound K α φ : ℝ) + 1) ^ e ≤ ((c₁ : ℝ) + 1) ^ e * P := by
      have : ((nodeBound K α φ : ℝ) + 1) ≤ ((c₁ : ℝ) + 1) * ((L : ℝ) + 1) ^ 2 := by
        have h₁ : (nodeBound K α φ : ℝ) ≤ c₁ * ((L : ℝ) + 1) ^ 2 := by exact_mod_cast hnb
        have h₂ : (1 : ℝ) ≤ ((L : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith [(L.cast_nonneg :
          (0 : ℝ) ≤ L)])
        have e₁ : ((c₁ : ℝ) + 1) * ((L : ℝ) + 1) ^ 2 = c₁ * ((L : ℝ) + 1) ^ 2 +
          ((L : ℝ) + 1) ^ 2 := by ring
        linarith only [h₁, h₂, e₁]
      calc ((nodeBound K α φ : ℝ) + 1) ^ e ≤ (((c₁ : ℝ) + 1) * ((L : ℝ) + 1) ^ 2) ^ e :=
            pow_le_pow_left₀ (by positivity) this e
        _ = ((c₁ : ℝ) + 1) ^ e * ((L : ℝ) + 1) ^ (2 * e) := by rw [mul_pow, ← pow_mul]
        _ ≤ ((c₁ : ℝ) + 1) ^ e * P := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact_mod_cast hP (2 * e) (by omega)
    have h₃ := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (c : ℝ) * (2 ^ (δ * ((occBound K α * N + 1 : ℕ) :
      ℝ)) * ((nodeBound K α φ : ℝ) + 1) ^ e) + c by positivity)
    unfold leafTime
    rw [h₁] at h₃ ⊢
    have h₄ : (c : ℝ) * (2 ^ δ * Y * ((nodeBound K α φ : ℝ) + 1) ^ e) ≤
        c * 2 ^ δ * ((c₁ : ℝ) + 1) ^ e * Y * P := by
      have := mul_le_mul_of_nonneg_left h₂ (by positivity : (0 : ℝ) ≤ c * 2 ^ δ * Y)
      linarith only [this]
    have h₅ : (c : ℝ) + 1 ≤ ((c : ℝ) + 1) * Y * P := by
      rw [mul_assoc]
      exact le_mul_of_one_le_right (by positivity)
        (one_le_mul_of_one_le_of_one_le hY hP1)
    calc (⌈(c : ℝ) * (2 ^ δ * Y * ((nodeBound K α φ : ℝ) + 1) ^ e) + c⌉₊ : ℝ)
        ≤ (c : ℝ) * (2 ^ δ * Y * ((nodeBound K α φ : ℝ) + 1) ^ e) + c + 1 := h₃.le
      _ ≤ C₂ * Y * P := by simp only [C₂]; linarith only [h₄, h₅]
  -- together
  set X : ℝ := 2 ^ ((1 / M : ℝ) * N)
  have hX : ((2 ^ (N / M) : ℕ) : ℝ) ≤ X := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [one_div_mul_eq_div]
    exact Nat.cast_div_le
  have hX1 : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
  have hXY : X * Y = 2 ^ ((1 / M + occBound K α * δ) * N) := by
    rw [← Real.rpow_add (by norm_num)]
    ring_nf
  have hT : ((L + 1) ^ dn + (L + 1) ^ di +
      (rounds M φ + 1) * ((stateBound K α φ + 1) ^ d + leafTime K α δ c e φ +
        stateBound K α φ + ((encNat (rounds M φ)).length + 1) ^ 2) : ℝ) ≤
      2 * P + 5 * X * (C₁ * P + C₂ * Y * P) := by
    have h₁ : ((L + 1) ^ dn + (L + 1) ^ di : ℝ) ≤ 2 * P := by exact_mod_cast hpoly
    have h₂ : ((rounds M φ + 1 : ℕ) : ℝ) ≤ 5 * X := by
      have : ((rounds M φ + 1 : ℕ) : ℝ) ≤ ((5 * 2 ^ (N / M) : ℕ) : ℝ) := by exact_mod_cast hr
      rw [Nat.cast_mul] at this
      push_cast at this hX ⊢
      linarith only [this, hX]
    have h₃ : (((stateBound K α φ + 1) ^ d + stateBound K α φ +
        ((encNat (rounds M φ)).length + 1) ^ 2 : ℕ) : ℝ) ≤ C₁ * P := by exact_mod_cast hrnd
    have h₄ : (((stateBound K α φ + 1) ^ d + leafTime K α δ c e φ + stateBound K α φ +
        ((encNat (rounds M φ)).length + 1) ^ 2 : ℕ) : ℝ) ≤ C₁ * P + C₂ * Y * P := by
      push_cast at h₃ ⊢
      linarith only [h₃, hleaf]
    have h₅ := mul_le_mul h₂ h₄ (by positivity) (by positivity)
    push_cast at h₁ h₅ ⊢
    linarith only [h₁, h₅]
  calc _ ≤ 2 * P + 5 * X * (C₁ * P + C₂ * Y * P) := by exact_mod_cast hT
    _ ≤ C₀ * (X * Y * P) := by
        have hXY1 : 1 ≤ X * Y := one_le_mul_of_one_le_of_one_le hX1 hY
        have hC₁ : (0 : ℝ) ≤ C₁ := by positivity
        have hP0 : (0 : ℝ) ≤ P := by positivity
        have a₁ : (P : ℝ) ≤ X * Y * P := le_mul_of_one_le_left hP0 hXY1
        have a₂ : X * P ≤ X * Y * P := by
          have := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ X * P)
          linarith only [this, show X * P * Y = X * Y * P by ring]
        have a₃ := mul_le_mul_of_nonneg_left a₂ hC₁
        simp only [C₀]
        linarith only [a₁, a₃]
    _ ≤ ⌈C₀⌉₊ * (2 ^ ((1 / M + occBound K α * δ) * N) * ((L : ℝ) + 1) ^ E) := by
        rw [← hXY]
        push_cast [P]
        exact mul_le_mul_of_nonneg_right (Nat.le_ceil C₀) (by positivity)

end Sparsify

/-! ### From clauses to variables -/

/-- **Sparsification on the native machines** [ImpagliazzoPaturiZane2001]. For every width `k` and
every `ε > 0` there is a constant `c` such that, for every `δ ≥ 0`, a decider for `k`-SAT within
time `2 ^ (δ m)` times a polynomial in the length of the encoded formula, on formulas with `m`
clauses, gives a decider for `k`-SAT within time `2 ^ ((ε + c δ) n)` times a polynomial, on
formulas with `n` variables. -/
theorem exists_decidableInExpTime_numVars_of_length (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ δ : ℝ, 0 ≤ δ → DecidableInExpTime (KSAT k) encCNF List.length δ →
      DecidableInExpTime (KSAT k) encCNF CNF.numVars (ε + c * δ) := by
  set K := max k 1
  have hK : 1 ≤ K := le_max_right _ _
  have hkK : k ≤ K := le_max_left _ _
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  have hMpos : (0 : ℝ) < M := lt_trans (by positivity) hM
  have hMε : 1 / (M : ℝ) < ε := by
    rw [div_lt_iff₀ hMpos]
    rw [div_lt_iff₀ hε] at hM
    linarith
  obtain ⟨α, hα, hcount⟩ :=
    ClauseSet.Sparsification.exists_sum_choose_le hK (ε := 1 / M) (by positivity)
  have hLB : Sparsify.LeafBound K α M := fun N => by
    have h₁ := hcount N
    have h₂ : (1 / M : ℝ) * N ≤ ((N / M + 1 : ℕ) : ℝ) := by
      have hlt : N < M * (N / M + 1) := by
        have := Nat.mod_lt N (show 0 < M by exact_mod_cast hMpos)
        have := Nat.div_add_mod N M
        nlinarith
      have : (N : ℝ) < M * ((N / M + 1 : ℕ) : ℝ) := by exact_mod_cast hlt
      rw [one_div_mul_eq_div, div_le_iff₀ hMpos]
      linarith
    have h₃ : (2 : ℝ) ^ ((1 / M : ℝ) * N) ≤ 2 ^ (N / M + 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h₂
    exact_mod_cast h₁.trans h₃
  refine ⟨Sparsify.occBound K α, fun δ hδ h => ?_⟩
  obtain ⟨e, h⟩ := h
  obtain ⟨g, t, c, hg, hgA, ht⟩ := h.exists_computableInO
  have hgsat : ∀ ψ : CNF ℕ, (∀ c ∈ ψ, c.length ≤ k) → (g ψ = true ↔ ψ.Satisfiable) :=
    fun ψ hψ => by
      rw [← hgA]
      exact ⟨fun h => h.2, fun h => ⟨hψ, h⟩⟩
  have hsearch := Sparsify.decidableInExpTime_search hK hα hkK hLB hg hδ ht
  have heq : KSAT k = {φ : CNF ℕ | (φ.all fun c => decide (c.length ≤ k)) = true} ∩
      {φ | Sparsify.search K α k M g φ = true} := by
    ext φ
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.all_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hw, hs⟩
      exact ⟨hw, (Sparsify.search_eq_true_iff hK hα hkK hLB hgsat hw).mpr hs⟩
    · rintro ⟨hw, hs⟩
      exact ⟨hw, (Sparsify.search_eq_true_iff hK hα hkK hLB hgsat hw).mp hs⟩
  rw [heq]
  exact (hsearch.inter (computableInPolyTime_all_length_le k) (by positivity)).mono
    (by linarith)

/-- **Subexponential time in the clauses gives subexponential time in the variables**
[ImpagliazzoPaturiZane2001]: if `k`-SAT is decidable within time `2 ^ (δ m)` times a polynomial
for every `δ > 0`, on formulas with `m` clauses, it is decidable within time `2 ^ (δ n)` times a
polynomial for every `δ > 0`, on formulas with `n` variables. -/
theorem DecidableInSubexpTime.numVars_of_length {k : ℕ}
    (h : DecidableInSubexpTime (KSAT k) encCNF List.length) :
    DecidableInSubexpTime (KSAT k) encCNF CNF.numVars := by
  intro δ hδ
  obtain ⟨c, hc⟩ := exists_decidableInExpTime_numVars_of_length k (half_pos hδ)
  have hδ' : 0 < δ / 2 / (c + 1) := by positivity
  refine (hc _ hδ'.le (h _ hδ')).mono ?_
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have : (c : ℝ) * (δ / 2 / (c + 1)) ≤ δ / 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **The exponential time hypothesis in terms of clauses** [ImpagliazzoPaturiZane2001]: `ETH`
holds exactly when 3SAT is not decidable in subexponential time in the number of clauses. -/
theorem ETH_iff_not_decidableInSubexpTime_length :
    ETH ↔ ¬DecidableInSubexpTime ThreeSAT encCNF List.length := by
  refine ⟨fun h h' => ETH_iff_not_decidableInSubexpTime.mp h ?_,
    ETH_of_not_decidableInSubexpTime_length⟩
  rw [← KSAT_three] at h' ⊢
  exact h'.numVars_of_length

end Cslib.Complexity
