/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.Exponents
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingSearch
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingPolyTime
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# Algorithmic counting sparsification on native machines

Implements the depth-first counting-sparsification search
(`Cslib.Complexity.CountingSparsify.search`) for Lemma 6.3, Proposition 6.4, and Appendix A
[OpenAI2026ETH] on the native multi-tape Turing machines, parallel to the decision sparsifier
`Cslib.Complexity.Sparsify.search`
(`Complexity/Computability/Complexity/FineGrained/Sparsification.lean`). In Lemma 6.3 (Section 6.4,
printed p. 43), *"The input count is the sum of the leaf counts"*, obtained in Appendix A (printed
p. 44) by *"repeatedly splitting a formula into two cases. Both children use the same n variables,
and every satisfying assignment of the parent satisfies exactly one child."*

Given a formula `φ : CNF ℕ` with `n = φ.numVars` occurring variables, the search maintains a state
`(n, (stk, acc))` (`CountingSparsify.State`, with `n` in unary and `acc` in binary capped at
`2 ^ n`):
* Starting from `init k φ = (φ.distinctVars.length, ([root k φ], 0))` (where `root k φ` is
  `countingNormalize φ` if `φ` has clause width at most `k` and `[[]]` otherwise), each step
  (`CountingSparsify.step`) inspects the top formula `ψ` of `stk`.
* If `ψ` is sparse (`isSparse (countingThreshold M) K ψ = true`), it pops `ψ`, runs a leaf model
  counter `g : CNF ℕ → ℕ` on `ψ`, weights the result by `leafWeight n ψ (g ψ) =
  2 ^ (n - ψ.distinctVars.length) * g ψ` to account for the `n - ψ.numVars` declared variables of
  `φ` not occurring in `ψ` (`CNF.modelCountOn_eq_mul_modelCount`), and adds the weighted count into
  `acc` capped at `2 ^ n`.
* If `ψ` is not sparse (using the heavy-heart branching condition of Appendix A.1, equation (A.1),
  p. 44, with the unnumbered threshold schedule `countingThreshold M j = M ^ j`), it pushes the two
  disjoint counting children `countingNext (countingThreshold M) K ψ false` and
  `countingNext (countingThreshold M) K ψ true` (Appendix A.1, equation (A.2), pp. 44–45).

To mirror `Sparsify`, this module packages the quantitative tree depth (`w.length ≤ L_coeff * N`)
and fixed-parameter leaf-count (`W.card ≤ 2 ^ (N / B + 1)`) hypotheses into `CountingTreeBound`, a
library adaptation of Appendix A.2–A.3 (Lemmas A.2–A.3, pp. 46–47) that remains an open
quantitative obligation for `K ≥ 2` (unit insertion accounting and finite recursive leaf partition
are prerequisites, with higher-width occurrence, deletion, survival, and leaf-recurrence bounds
handled separately). Under `CountingTreeBound`, running `step M K g` for
`rounds B φ = 2 ^ (n / B + 2)` steps visits every leaf of the counting-sparsification tree and
returns `φ.modelCount` (`CountingSparsify.search_eq_modelCount`). Given a total leaf routine `g`
with `hg : ComputableInO g encCNF encNat t t` and a global bound `ht` holding for every
`ψ : CNF ℕ` (`(t ψ : ℝ) ≤ c * (2 ^ (δ * ψ.length) * (|encCNF ψ| + 1) ^ e) + c`),
`CountingSparsify.exists_computableInO_search` yields a combined time-and-space certificate
`ComputableInO (search M K k B g) encCNF encNat T T` with the fixed-parameter library-adaptation
transfer bound `T φ ≤ C₀ * (2 ^ ((1 / B + occBound K M * δ) * n) * (|encCNF φ| + 1) ^ E) + C₀`.
Because `hg` bounds both time and space of `g` by `t` (which may be exponential) and the step space
bound includes `leafTime`, no separate polynomial leaf-workspace certificate is claimed here.

## Main definitions

* `Cslib.Complexity.CountingSparsify.State`, `Cslib.Complexity.CountingSparsify.leafWeight`,
  `Cslib.Complexity.CountingSparsify.leafUpdate`, `Cslib.Complexity.CountingSparsify.step`,
  `Cslib.Complexity.CountingSparsify.root`, `Cslib.Complexity.CountingSparsify.init`,
  `Cslib.Complexity.CountingSparsify.rounds`, `Cslib.Complexity.CountingSparsify.search`: the
  counting-sparsification search.
* `Cslib.Complexity.CountingSparsify.occBound`: the sparse leaf clause-density bound
  `2 * ∑ j ∈ Finset.range K, countingThreshold M j`.
* `Cslib.Complexity.CountingSparsify.CountingTreeBound`: the fixed-parameter depth and leaf-count
  hypotheses for `countingRule` (a library adaptation of Appendix A.2–A.3).

## Main results

* `Cslib.Complexity.CountingSparsify.search_eq_modelCount`,
  `Cslib.Complexity.CountingSparsify.search_eq_ite_modelCount`: the search computes `φ.modelCount`
  on formulas of width `≤ k` (and `0` otherwise).
* `Cslib.Complexity.CountingSparsify.exists_computableInO_search`: native `ComputableInO ... T T`
  time-and-space transfer certificate for `CountingSparsify.search`.
* `Cslib.Complexity.CountingSparsify.stepWith`,
  `Cslib.Complexity.CountingSparsify.iterate_stepWith_fst`,
  `Cslib.Complexity.CountingSparsify.iterate_stepWith_countingThreshold`: the step with a captured
  runtime context, which keeps the context and agrees with `step` at the context's base.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 6.4,
  Lemma 6.3 and Proposition 6.4 (pp. 43–44) and Appendix A (pp. 44–47).
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification Turing.MultiTapeTM
open scoped List

namespace CountingSparsify

open ClauseSet.Sparsification (CountingBranchingRule)

/-! ### Auxiliary model-count and binary-encoding bounds -/

/-- The number of satisfying assignments of `ψ` on its occurring variables is at most
`2 ^ ψ.numVars`. -/
theorem modelCount_le_two_pow_numVars {V : Type*} [DecidableEq V] (ψ : CNF V) :
    ψ.modelCount ≤ 2 ^ ψ.numVars := by
  rw [CNF.modelCount, CNF.numVars]
  refine (Finset.card_filter_le _ _).trans ?_
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, le_rfl]

private theorem length_encNat_le_of_le_two_pow {acc n : ℕ} (h : acc ≤ 2 ^ n) :
    (encNat acc).length ≤ n + 1 := by
  refine (ComputableTidilyInO.length_encNat_mono h).trans ?_
  rw [encNat_two_pow, List.length_append, List.length_replicate, List.length_singleton]

/-! ### The counting-sparsification search -/

/-- The states of the counting-sparsification search: the declared variable count `n` (in unary),
a stack of formulas, and a binary accumulator capped at `2 ^ n`. -/
abbrev State : Type := ℕ × (List (CNF ℕ) × ℕ)

/-- States encoded as framed tuples, with the declared variable count in unary and the accumulator
in binary. -/
private abbrev encState : State ↪ List Bool :=
  encPair encUnary (encPair (encList encCNF) encNat)

/-- Weight a leaf's occurring-variable model count `c` by `2 ^ (n - ψ.numVars)` for the unused
declared variables. -/
def leafWeight (n : ℕ) (ψ : CNF ℕ) (c : ℕ) : ℕ :=
  2 ^ (n - ψ.distinctVars.length) * c

/-- Update the search state when the top of the stack is a sparse leaf with occurring-variable
count `c`, popping the leaf and adding its weighted count (capped at `2 ^ s.1`). -/
def leafUpdate (s : State) (c : ℕ) : State :=
  (s.1, (s.2.1.tail, min (2 ^ s.1) (s.2.2 + leafWeight s.1 (s.2.1.headD []) c)))

/-- One step of the depth-first search of the counting-sparsification tree, for threshold base `M`
and width `K`: a sparse formula on top of the stack is popped and weighted by `leafWeight` applied
to the leaf counter `g`; any other formula on top is replaced by its two counting children
(`countingNext`). -/
def step (M K : ℕ) (g : CNF ℕ → ℕ) (s : State) : State :=
  if s.2.1.isEmpty then s
  else if isSparse (countingThreshold M) K (s.2.1.headD []) then
    leafUpdate s (g (s.2.1.headD []))
  else
    (s.1, (countingNext (countingThreshold M) K (s.2.1.headD []) false ::
      countingNext (countingThreshold M) K (s.2.1.headD []) true :: s.2.1.tail, s.2.2))

/-- The root of the counting-sparsification search: the nontautological normal form
(`countingNormalize`) of a formula of width `k`, and the unsatisfiable formula `[[]]` otherwise. -/
def root (k : ℕ) (φ : CNF ℕ) : CNF ℕ :=
  if φ.all fun c => decide (c.length ≤ k) then countingNormalize φ else [[]]

/-- The initial state of the counting-sparsification search on `φ`. -/
def init (k : ℕ) (φ : CNF ℕ) : State :=
  (φ.distinctVars.length, ([root k φ], 0))

/-- The number of rounds of the search, `2 ^ (n / B + 2)` on formulas with `n` occurring
variables. -/
def rounds (B : ℕ) (φ : CNF ℕ) : ℕ := 2 ^ (φ.distinctVars.length / B + 2)

/-- **The counting-sparsification search**: run `step M K g` for `rounds B φ` rounds from
`init k φ`, and report the accumulated model count. -/
def search (M K k B : ℕ) (g : CNF ℕ → ℕ) (φ : CNF ℕ) : ℕ :=
  ((step M K g)^[rounds B φ] (init k φ)).2.2

/-! ### Agreement with the depth-first tree search -/

variable {M K : ℕ} (hM : 1 ≤ M) (hK : 1 ≤ K)

/-- The list-level counting branching rule for width `K` and thresholds `countingThreshold M`. -/
abbrev rule : CountingBranchingRule (countingThreshold M) ℕ {ψ : CNF ℕ // CountingNormalized K ψ} :=
  CNF.Sparsification.countingRule (one_le_countingThreshold hM) hK

include hM hK in
private theorem step_map (g : CNF ℕ → ℕ) (n : ℕ)
    (stk : List {ψ : CNF ℕ // CountingNormalized K ψ}) (acc : ℕ) :
    step M K g (n, (stk.map Subtype.val, acc)) =
      (n, Prod.map (List.map Subtype.val) id
        ((rule hM hK).searchStep (2 ^ n) (fun t => leafWeight n t.1 (g t.1)) (stk, acc))) := by
  cases stk with
  | nil => rfl
  | cons s rest =>
    have hiff := isSparse_eq_true_iff (one_le_countingThreshold hM) s.2.toNormalized
    by_cases hs : ClauseSet.Sparsification.Sparse (countingThreshold M) s.1.toClauseSet
    · have hs' : isSparse (countingThreshold M) K s.1 = true := hiff.mpr hs
      simp [step, leafUpdate, CountingBranchingRule.searchStep, hs, hs', rule,
        CNF.Sparsification.countingRule]
    · have hs' : isSparse (countingThreshold M) K s.1 = false := by
        simpa using fun h => hs (hiff.mp h)
      simp [step, CountingBranchingRule.searchStep, hs, hs', rule,
        CNF.Sparsification.countingRule]

include hM hK in
private theorem iterate_step_map (g : CNF ℕ → ℕ) (r n : ℕ)
    (stk : List {ψ : CNF ℕ // CountingNormalized K ψ}) (acc : ℕ) :
    (step M K g)^[r] (n, (stk.map Subtype.val, acc)) =
      (n, Prod.map (List.map Subtype.val) id
        (((rule hM hK).searchStep (2 ^ n)
          (fun t => leafWeight n t.1 (g t.1)))^[r] (stk, acc))) := by
  induction r generalizing stk acc with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, step_map hM hK]
    obtain ⟨stk', acc'⟩ :=
      (rule hM hK).searchStep (2 ^ n) (fun t => leafWeight n t.1 (g t.1)) (stk, acc)
    exact ih stk' acc'

private theorem step_nil (g : CNF ℕ → ℕ) (n acc : ℕ) :
    step M K g (n, ([], acc)) = (n, ([], acc)) := rfl

private theorem iterate_step_nil (g : CNF ℕ → ℕ) (r n acc : ℕ) :
    (step M K g)^[r] (n, ([], acc)) = (n, ([], acc)) :=
  Function.iterate_fixed (step_nil g n acc) r

/-! ### The root -/

theorem countingNormalized_root {k : ℕ} (hkK : k ≤ K) (φ : CNF ℕ) :
    CountingNormalized K (root k φ) := by
  unfold root
  split_ifs with h
  · simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact countingNormalized_countingNormalize fun C hC => (h C hC).trans hkK
  · exact ⟨⟨by simp, by simp, by simp,
      by simp [CNF.toClauseSet, ClauseSet.Sparsification.Reduced]⟩,
      by simp [Nontautological]⟩

private theorem length_le_of_mem_root (k : ℕ) (φ : CNF ℕ) {C : Clause ℕ} (hC : C ∈ root k φ) :
    C.length ≤ k := by
  unfold root at hC
  split_ifs at hC with h
  · simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact (countingNormalized_countingNormalize h).length_le C hC
  · simp only [List.mem_singleton] at hC
    subst hC
    exact Nat.zero_le k

private theorem length_root_le (k : ℕ) (φ : CNF ℕ) : (root k φ).length ≤ φ.length + 1 := by
  unfold root
  split_ifs
  · exact (length_countingNormalize_le φ).trans (Nat.le_succ _)
  · simp

/-- The root as a state of the list-level counting branching rule. -/
def rootState {k : ℕ} (hkK : k ≤ K) (φ : CNF ℕ) : {ψ : CNF ℕ // CountingNormalized K ψ} :=
  ⟨root k φ, countingNormalized_root hkK φ⟩

private theorem mem_vars_of_mem_root {k : ℕ} {φ : CNF ℕ} :
    ∀ C ∈ root k φ, ∀ l ∈ C, l.1 ∈ φ.vars.toFinset := by
  intro C hC l hl
  unfold root at hC
  split_ifs at hC with h
  · exact mem_vars_of_mem_countingNormalize C.toFinset (mem_toClauseSet.mpr ⟨C, hC, rfl⟩)
      l (List.mem_toFinset.mpr hl)
  · simp only [List.mem_singleton] at hC
    subst hC
    simp at hl

/-! ### The states of the tree -/

/-- The bound `2 ∑_{j < K} countingThreshold M j` on the occurrences of a variable in a sparse
formula. -/
def occBound (K M : ℕ) : ℕ := 2 * ∑ j ∈ Finset.range K, countingThreshold M j

section Tree

variable {k : ℕ} (hkK : k ≤ K) {φ : CNF ℕ} {w : List Bool}
include hM hK hkK

private theorem mem_vars_of_mem_walk (w : List Bool) :
    ∀ C ∈ ((rule hM hK).walk (rootState hkK φ) w).1, ∀ l ∈ C, l.1 ∈ φ.vars.toFinset :=
  support_walk_countingRule (one_le_countingThreshold hM) hK mem_vars_of_mem_root w

private theorem vars_walk_subset (w : List Bool) :
    ((rule hM hK).walk (rootState hkK φ) w).1.vars.toFinset ⊆ φ.vars.toFinset := by
  intro v hv
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
  obtain ⟨C, hC, hlC⟩ := List.mem_flatten.mp hl
  exact mem_vars_of_mem_walk hM hK hkK w C hC l hlC

private theorem numVars_walk_le (w : List Bool) :
    ((rule hM hK).walk (rootState hkK φ) w).1.numVars ≤ φ.numVars :=
  Finset.card_le_card (vars_walk_subset hM hK hkK w)

/-- Every state reached along a node word of length at most `h` has at most `φ.length + 1 + K * h`
clauses. -/
private theorem length_walk_le (hw : (rule hM hK).IsNodeWord (rootState hkK φ) w)
    {h : ℕ} (hwlen : w.length ≤ h) :
    ((rule hM hK).walk (rootState hkK φ) w).1.length ≤ φ.length + 1 + K * h := by
  have hcard : (((rule hM hK).walk (rootState hkK φ) w).1.toClauseSet).card ≤
      (rootState hkK φ).1.toClauseSet.card + K * w.length :=
    CountingBranchingRule.IsNodeWord.card_walk_le (one_le_countingThreshold hM) hK
      (rootState hkK φ).2.card_le hw
  rw [((rule hM hK).walk (rootState hkK φ) w).2.card_toClauseSet,
    (rootState hkK φ).2.card_toClauseSet] at hcard
  exact hcard.trans (Nat.add_le_add (length_root_le k φ) (Nat.mul_le_mul_left K hwlen))

/-- **Sparse leaves are small.** The sparse states of the counting-sparsification tree have at most
`occBound K M * φ.numVars + 1` clauses. -/
private theorem length_walk_le_of_isSparse
    (hs : isSparse (countingThreshold M) K ((rule hM hK).walk (rootState hkK φ) w).1 = true) :
    ((rule hM hK).walk (rootState hkK φ) w).1.length ≤ occBound K M * φ.numVars + 1 := by
  set ψ := (rule hM hK).walk (rootState hkK φ) w
  have hsparse := (isSparse_eq_true_iff (one_le_countingThreshold hM) ψ.2.toNormalized).mp hs
  rw [← ψ.2.card_toClauseSet]
  refine ClauseSet.Sparsification.card_le_of_sparse (one_le_countingThreshold hM) hsparse
    ψ.2.card_le φ.vars.toFinset fun C' hC' l hl => ?_
  obtain ⟨C, hC, rfl⟩ := mem_toClauseSet.mp hC'
  exact mem_vars_of_mem_walk hM hK hkK w C hC l (List.mem_toFinset.mp hl)

/-- Every state of the tree has clause width at most `k` (for every `φ : CNF ℕ` and every `k : ℕ`,
including `k = 0`). -/
private theorem length_le_of_mem_walk (hw : (rule hM hK).IsNodeWord (rootState hkK φ) w)
    {C : Clause ℕ} (hC : C ∈ ((rule hM hK).walk (rootState hkK φ) w).1) : C.length ≤ k := by
  set ψ := (rule hM hK).walk (rootState hkK φ) w
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hsparse : ClauseSet.Sparsification.Sparse (countingThreshold M)
        (rootState hkK φ).1.toClauseSet := by
      intro c H hH
      obtain ⟨D', hD'⟩ := hH.flower_nonempty (one_le_countingThreshold hM)
      obtain ⟨hD'root, rfl, -⟩ := ClauseSet.Sparsification.mem_flower.mp hD'
      obtain ⟨D, hD, rfl⟩ := mem_toClauseSet.mp hD'root
      have hD0 : D.toFinset.card ≤ 0 :=
        (List.toFinset_card_le D).trans (length_le_of_mem_root 0 φ hD)
      have := hH.1
      have := hH.2.1
      omega
    cases w with
    | nil => exact length_le_of_mem_root 0 φ hC
    | cons b u => exact absurd hsparse hw.1
  · have hcard : C.toFinset.card ≤ k := by
      refine CountingBranchingRule.IsNodeWord.card_le_of_mem_walk
        (R := rule hM hK) (one_le_countingThreshold hM) hk (fun D' hD' => ?_) hw C.toFinset
        (mem_toClauseSet.mpr ⟨C, hC, rfl⟩)
      obtain ⟨D, hD, rfl⟩ := mem_toClauseSet.mp hD'
      exact (List.toFinset_card_le D).trans (length_le_of_mem_root k φ hD)
    rwa [List.toFinset_card_of_nodup (ψ.2.nodup C hC)] at hcard

end Tree

/-! ### The run of the search -/

/-- The fixed-parameter quantitative depth and leaf-count hypotheses for the
counting-sparsification tree (a library adaptation of Appendix A.2–A.3, Lemmas A.2–A.3, pp. 46–47
[OpenAI2026ETH], open for `K ≥ 2`): from any `CountingNormalized K` root formula `ψ` whose
occurring variables lie in a finite set `declared` of size `N = declared.card`, every leaf word of
`rule hM hK` has length at most `L_coeff * N`, and any finset of leaf words has cardinality at
most `2 ^ (N / B + 1)`. -/
def CountingTreeBound (M K B L_coeff : ℕ) (hM : 1 ≤ M) (hK : 1 ≤ K) : Prop :=
  ∀ (ψ : {ψ : CNF ℕ // CountingNormalized K ψ}) (declared : Finset ℕ),
    (∀ C ∈ ψ.1, ∀ l ∈ C, l.1 ∈ declared) →
    (∀ w, (rule hM hK).IsLeafWord ψ w → w.length ≤ L_coeff * declared.card) ∧
    ∀ W : Finset (List Bool), (∀ w ∈ W, (rule hM hK).IsLeafWord ψ w) →
      W.card ≤ 2 ^ (declared.card / B + 1)

open Classical in
/-- **The run of the counting-sparsification search.** Under `CountingTreeBound`, after
`rounds B φ` rounds the stack is empty and the accumulator records the capped sum of `leafWeight`
over the leaf words of `rootState hkK φ`. At every round `i`, the stack holds at most
`L_coeff * φ.numVars + 1` nodes of depth at most `L_coeff * φ.numVars`, and the accumulator is at
most `2 ^ φ.numVars`. -/
private theorem iterate_step (hM2 : 2 ≤ M) {k B L_coeff : ℕ} (hkK : k ≤ K)
    (hTB : CountingTreeBound M K B L_coeff hM hK) (g : CNF ℕ → ℕ) (φ : CNF ℕ) :
    (∃ W : Finset (List Bool),
      (∀ w, w ∈ W ↔ (rule hM hK).IsLeafWord (rootState hkK φ) w) ∧
      (step M K g)^[rounds B φ] (init k φ) =
        (φ.distinctVars.length, ([], min (2 ^ φ.distinctVars.length)
          (∑ w ∈ W, leafWeight φ.distinctVars.length
            ((rule hM hK).walk (rootState hkK φ) w).1
            (g ((rule hM hK).walk (rootState hkK φ) w).1))))) ∧
    ∀ i, ∃ (stk : List {ψ : CNF ℕ // CountingNormalized K ψ}) (acc : ℕ),
      (step M K g)^[i] (init k φ) = (φ.distinctVars.length, (stk.map Subtype.val, acc)) ∧
      stk.length ≤ L_coeff * φ.numVars + 1 ∧
      acc ≤ 2 ^ φ.numVars ∧
      ∀ t ∈ stk, ∃ w, (rule hM hK).IsNodeWord (rootState hkK φ) w ∧
        w.length ≤ L_coeff * φ.numVars ∧ (rule hM hK).walk (rootState hkK φ) w = t := by
  set R := rule hM hK
  set s₀ := rootState hkK φ
  set n := φ.distinctVars.length
  have hn_eq : n = φ.numVars := CNF.length_distinctVars φ
  obtain ⟨hlen, hWbound⟩ := hTB s₀ φ.vars.toFinset mem_vars_of_mem_root
  obtain ⟨W, hW, N, hN, h⟩ := CountingBranchingRule.exists_iterate_searchStep (R := R)
    (fun _ => two_le_countingThreshold hM2)
    (2 ^ n) (fun t => leafWeight n t.1 (g t.1)) s₀ hlen
  have hWcard : W.card ≤ 2 ^ (φ.numVars / B + 1) :=
    hWbound W fun w hw => (hW w).mp hw
  have hNr : N ≤ rounds B φ := by
    rw [rounds, CNF.length_distinctVars, pow_succ]
    omega
  have hinit : init k φ = (n, ([s₀].map Subtype.val, 0)) := rfl
  obtain ⟨hfin, hmid⟩ := h [] 0 (Nat.zero_le _)
  have hN' : (step M K g)^[N] (init k φ) =
      (n, ([], min (2 ^ n) (∑ w ∈ W, leafWeight n (R.walk s₀ w).1 (g (R.walk s₀ w).1)))) := by
    rw [hinit, iterate_step_map hM hK, hfin]
    simp
  refine ⟨⟨W, hW, ?_⟩, fun i => ?_⟩
  · rw [show rounds B φ = (rounds B φ - N) + N by omega, Function.iterate_add_apply, hN',
      iterate_step_nil]
  · by_cases hi : i ≤ N
    · obtain ⟨stk, acc', heq, hstk, hacc', hmem⟩ := hmid i hi
      refine ⟨stk, acc', ?_, hstk, hn_eq ▸ hacc', hmem⟩
      rw [hinit, iterate_step_map hM hK, heq]
      simp
    · refine ⟨[], min (2 ^ n) (∑ w ∈ W, leafWeight n (R.walk s₀ w).1 (g (R.walk s₀ w).1)),
        ?_, by simp, hn_eq ▸ Nat.min_le_left _ _, by simp⟩
      rw [show i = (i - N) + N by omega, Function.iterate_add_apply, hN', iterate_step_nil]
      rfl

include hM hK in
/-- **The search computes the model count.** If `g` computes `ψ.modelCount` on sparse formulas `ψ`
of width at most `k`, then `search M K k B g φ` returns `φ.modelCount` on formulas of width at most
`k` and `0` otherwise. -/
theorem search_eq_ite_modelCount (hM2 : 2 ≤ M) {k B L_coeff : ℕ} (hkK : k ≤ K)
    (hTB : CountingTreeBound M K B L_coeff hM hK) {g : CNF ℕ → ℕ}
    (hg : ∀ ψ : CNF ℕ, (∀ c ∈ ψ, c.length ≤ k) →
      isSparse (countingThreshold M) K ψ = true → g ψ = ψ.modelCount)
    (φ : CNF ℕ) :
    search M K k B g φ =
      if (φ.all fun c => decide (c.length ≤ k)) then φ.modelCount else 0 := by
  classical
  set R := rule hM hK
  set s₀ := rootState hkK φ
  obtain ⟨⟨W, hW, hfin⟩, -⟩ := iterate_step hM hK hM2 hkK hTB g φ
  rw [search, hfin]
  dsimp only
  have hleaf (w : List Bool) (hw : R.IsLeafWord s₀ w) :
      leafWeight φ.distinctVars.length (R.walk s₀ w).1 (g (R.walk s₀ w).1) =
        (R.walk s₀ w).1.modelCountOn φ.vars.toFinset := by
    set ψ := R.walk s₀ w
    have hsparse : isSparse (countingThreshold M) K ψ.1 = true :=
      (isSparse_eq_true_iff (one_le_countingThreshold hM) ψ.2.toNormalized).mpr hw.sparse_walk
    have hwidth : ∀ c ∈ ψ.1, c.length ≤ k :=
      fun c hc => length_le_of_mem_walk hM hK hkK hw.isNodeWord hc
    rw [leafWeight, hg ψ.1 hwidth hsparse, CNF.length_distinctVars, CNF.length_distinctVars]
    exact (CNF.modelCountOn_eq_mul_modelCount ψ.1 φ.vars.toFinset
      (vars_walk_subset hM hK hkK w)).symm
  have hsum : ∑ w ∈ W, leafWeight φ.distinctVars.length (R.walk s₀ w).1 (g (R.walk s₀ w).1) =
      (root k φ).modelCountOn φ.vars.toFinset :=
    sum_leafWords_countingRule_modelCountOn (one_le_countingThreshold hM)
      (fun _ => two_le_countingThreshold hM2) hK φ.vars.toFinset
      (f := fun t => leafWeight φ.distinctVars.length t.1 (g t.1)) s₀ hleaf hW
  rw [hsum, CNF.length_distinctVars]
  unfold root
  split_ifs with hφ
  · rw [modelCountOn_countingNormalize, CNF.modelCountOn_vars]
    exact Nat.min_eq_right (modelCount_le_two_pow_numVars φ)
  · rw [CNF.modelCountOn_eq_zero_of_nil_mem (List.mem_singleton_self [])]
    exact Nat.min_eq_right (Nat.zero_le _)

include hM hK in
/-- **The search computes `φ.modelCount` on formulas of width at most `k`.** -/
theorem search_eq_modelCount (hM2 : 2 ≤ M) {k B L_coeff : ℕ} (hkK : k ≤ K)
    (hTB : CountingTreeBound M K B L_coeff hM hK) {g : CNF ℕ → ℕ}
    (hg : ∀ ψ : CNF ℕ, (∀ c ∈ ψ, c.length ≤ k) →
      isSparse (countingThreshold M) K ψ = true → g ψ = ψ.modelCount)
    {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ k) :
    search M K k B g φ = φ.modelCount := by
  rw [search_eq_ite_modelCount hM hK hM2 hkK hTB hg φ,
    ite_eq_left_iff.mpr fun h =>
      absurd (List.all_eq_true.mpr fun c hc => decide_eq_true (hφ c hc)) h]

/-! ### Polynomial-time parts -/

section PolyTime

open ComputableTidilyInPolyTime

private theorem computableTidilyInPolyTime_isSparse_head (M K : ℕ) :
    ComputableTidilyInPolyTime
      (fun s : State => isSparse (countingThreshold M) K (s.2.1.headD []))
      encState encBool := by
  have h := (computableInPolyTime_isSparse encNat
    (computableInPolyTime_countingThreshold_le M) K).tidy
  have hH : ComputableTidilyInPolyTime (fun s : State => s.2.1.headD []) encState encCNF := by
    unfold encState
    fun_prop
  exact h.comp hH

private theorem computableTidilyInPolyTime_inner (M K : ℕ) :
    ComputableTidilyInPolyTime (fun s : State =>
      (s.1, (countingNext (countingThreshold M) K (s.2.1.headD []) false ::
        countingNext (countingThreshold M) K (s.2.1.headD []) true :: s.2.1.tail, s.2.2)))
      encState encState := by
  have h := (computableInPolyTime_countingNext encNat
    (computableInPolyTime_countingThreshold_le M) K).tidy
  unfold encState encCNF
  fun_prop

private theorem computableTidilyInPolyTime_leafUpdate :
    ComputableTidilyInPolyTime (fun p : State × ℕ => leafUpdate p.1 p.2)
      (encPair encState encNat) encState := by
  have hvars := SAT.computableInPolyTime_distinctVars.tidy
  have heq : (fun p : State × ℕ => leafUpdate p.1 p.2) = fun p =>
      (p.1.1, (p.1.2.1.tail,
        if decide (2 ^ p.1.1 ≤ p.1.2.2 +
            2 ^ (p.1.1 - (p.1.2.1.headD []).distinctVars.length) * p.2) then
          2 ^ p.1.1
        else
          p.1.2.2 + 2 ^ (p.1.1 - (p.1.2.1.headD []).distinctVars.length) * p.2)) := by
    funext p
    simp [leafUpdate, leafWeight, min_def]
  rw [heq]
  unfold encState encCNF
  fun_prop

private theorem computableTidilyInPolyTime_init (k : ℕ) :
    ComputableTidilyInPolyTime (init k) encCNF encState := by
  have hvars := SAT.computableInPolyTime_distinctVars.tidy
  have hnorm := (computableInPolyTime_countingNormalize encNat).tidy
  unfold init root encState encCNF
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
private theorem computableTidilyInPolyTime_rounds (B : ℕ) :
    ComputableTidilyInPolyTime (rounds B) encCNF encNat := by
  have hvars := SAT.computableInPolyTime_distinctVars.tidy
  have h := unary_div_const B
  unfold rounds
  fun_prop

/-- **The time of a counting-sparsification step**: a polynomial in the length of the encoded state,
plus the time of the leaf counter `g` and a polynomial in the state and counter output lengths when
`g` runs on a sparse head formula. -/
private theorem exists_computableTidilyInO_step (M K : ℕ) {g : CNF ℕ → ℕ} {t : CNF ℕ → ℕ}
    (hg : ComputableTidilyInO g encCNF encNat t t) :
    ∃ d, ComputableTidilyInO (step M K g) encState encState
      (fun s => ((encState s).length + 1) ^ d +
        if s.2.1.isEmpty = false ∧
            isSparse (countingThreshold M) K (s.2.1.headD []) = true then
          t (s.2.1.headD []) +
            ((encState s).length + (encNat (g (s.2.1.headD []))).length + 1) ^ d
        else 0)
      (fun s => ((encState s).length + 1) ^ d +
        if s.2.1.isEmpty = false ∧
            isSparse (countingThreshold M) K (s.2.1.headD []) = true then
          t (s.2.1.headD []) +
            ((encState s).length + (encNat (g (s.2.1.headD []))).length + 1) ^ d
        else 0) := by
  obtain ⟨dE, eE, hE⟩ := (show ComputableTidilyInPolyTime (fun s : State => s.2.1.isEmpty) encState
    encBool by unfold encState; fun_prop).exists_degree
  obtain ⟨dI, eI, hI⟩ := (id' (encIn := encState)).exists_degree
  obtain ⟨dS, eS, hS⟩ := (computableTidilyInPolyTime_isSparse_head M K).exists_degree
  obtain ⟨dH, eH, hH⟩ := (show ComputableTidilyInPolyTime (fun s : State => s.2.1.headD []) encState
    encCNF by unfold encState; fun_prop).exists_degree
  obtain ⟨dN, eN, hN⟩ := (computableTidilyInPolyTime_inner M K).exists_degree
  obtain ⟨dU, eU, hU⟩ := computableTidilyInPolyTime_leafUpdate.exists_degree
  set D := dE + dI + dS + dH + dN + dU + 1
  have hE' := (hE.mono (d' := D) (e' := eE) (by omega) le_rfl).inO
  have hI' := (hI.mono (d' := D) (e' := eI) (by omega) le_rfl).inO
  have hS' := (hS.mono (d' := D) (e' := eS) (by omega) le_rfl).inO
  have hH' := (hH.mono (d' := D) (e' := eH) (by omega) le_rfl).inO
  have hN' := (hN.mono (d' := D) (e' := eN) (by omega) le_rfl).inO
  have hU' := (hU.mono (d' := D) (e' := eU) (by omega) le_rfl).inO
  have hleaf := hU'.comp (hI'.prod (hg.comp hH'))
  have h := hE'.ite hI' (hS'.ite hleaf hN')
  have hpair_le (s : State) (c : ℕ) :
      ((encPair encState encNat (s, c)).length + 1) ^ D ≤
        4 ^ D * ((encState s).length + (encNat c).length + 1) ^ D := by
    rw [ ← mul_pow]
    refine Nat.pow_le_pow_left ?_ D
    simp only [length_encPair]
    omega
  refine ⟨D, h.mono (4 ^ D + 5) (fun s => ?_) (fun s => ?_)⟩ <;>
  · simp only [Function.comp_apply]
    have hp := hpair_le s (g (s.2.1.headD []))
    have h4D : 1 ≤ 4 ^ D := Nat.one_le_pow _ _ (by norm_num)
    generalize 4 ^ D = F at hp h4D ⊢
    generalize ((encState s).length + 1) ^ D = P
    generalize t (s.2.1.headD []) = T
    generalize ((encState s).length + (encNat (g (s.2.1.headD []))).length + 1) ^ D = Q at hp ⊢
    generalize ((encPair encState encNat (s, g (s.2.1.headD []))).length + 1) ^ D = R at hp ⊢
    cases s.2.1.isEmpty <;>
      cases isSparse (countingThreshold M) K (s.2.1.headD []) <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, and_true, and_false,
        Bool.true_eq_false] <;> nlinarith

end PolyTime

/-! ### Encoded state sizes -/

/-- A bound on the length of the encoded formulas in the counting-sparsification tree. -/
private def nodeBound (K L_coeff : ℕ) (φ : CNF ℕ) : ℕ :=
  (φ.length + 1 + K * (L_coeff * φ.numVars)) * (2 * (K * (2 * (encCNF φ).length + 1)) + 1)

/-- A bound on the length of the encoded states of the counting-sparsification search. -/
private def stateBound (K L_coeff : ℕ) (φ : CNF ℕ) : ℕ :=
  4 * φ.numVars + 4 * ((L_coeff * φ.numVars + 1) * (2 * nodeBound K L_coeff φ + 1)) + 10

private theorem length_encLiteral_le_of_mem_vars {φ : CNF ℕ} {l : Literal ℕ}
    (hl : l.1 ∈ φ.vars.toFinset) : (encPair encNat encBool l).length ≤ (encCNF φ).length := by
  obtain ⟨l', hl'F, hl'eq⟩ := List.mem_map.mp (List.mem_toFinset.mp hl)
  obtain ⟨D, hD, hl'D⟩ := List.mem_flatten.mp hl'F
  have hlen_eq : (encPair encNat encBool l).length = (encPair encNat encBool l').length := by
    simp only [length_encPair, encBool_apply, List.length_singleton, hl'eq]
  rw [hlen_eq]
  exact (length_le_encList_of_mem _ hl'D).trans (length_le_encList_of_mem _ hD)

section Sizes

variable {k L_coeff : ℕ} (hkK : k ≤ K) {φ : CNF ℕ}
include hM hK hkK

private theorem length_encCNF_walk_le {w : List Bool}
    (hw : (rule hM hK).IsNodeWord (rootState hkK φ) w) (hwlen : w.length ≤ L_coeff * φ.numVars) :
    (encCNF ((rule hM hK).walk (rootState hkK φ) w).1).length ≤ nodeBound K L_coeff φ := by
  set ψ := (rule hM hK).walk (rootState hkK φ) w
  refine (length_encList_le _ ψ.1 (b := K * (2 * (encCNF φ).length + 1)) fun C hC => ?_).trans
    (Nat.mul_le_mul_right _ (length_walk_le hM hK hkK hw hwlen))
  refine (length_encList_le _ C (b := (encCNF φ).length) fun l hl => ?_).trans
    (Nat.mul_le_mul_right _ (ψ.2.length_le C hC))
  exact length_encLiteral_le_of_mem_vars (mem_vars_of_mem_walk hM hK hkK w C hC l hl)

private theorem length_encState_le {stk : List {ψ : CNF ℕ // CountingNormalized K ψ}} {acc : ℕ}
    (hstk : stk.length ≤ L_coeff * φ.numVars + 1) (hacc : acc ≤ 2 ^ φ.numVars)
    (hmem : ∀ t ∈ stk, ∃ w, (rule hM hK).IsNodeWord (rootState hkK φ) w ∧
      w.length ≤ L_coeff * φ.numVars ∧ (rule hM hK).walk (rootState hkK φ) w = t) :
    (encState (φ.distinctVars.length, (stk.map Subtype.val, acc))).length ≤
      stateBound K L_coeff φ := by
  have hlist := length_encList_le encCNF (stk.map Subtype.val)
    (b := nodeBound K L_coeff φ) fun ψ hψ => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hψ
      obtain ⟨w, hw, hwlen, rfl⟩ := hmem t ht
      exact length_encCNF_walk_le hM hK hkK hw hwlen
  rw [List.length_map] at hlist
  have hlist' := hlist.trans (Nat.mul_le_mul_right _ hstk)
  have hacc' := length_encNat_le_of_le_two_pow hacc
  have hn := CNF.length_distinctVars φ
  simp only [encState, length_encPair, encUnary_apply, List.length_replicate, hn, stateBound]
  omega

end Sizes

/-! ### The time of the counting-sparsification search -/

/-- The time bound of the leaf counter on the sparse leaves of the tree. -/
private noncomputable def leafTime (K M L_coeff : ℕ) (δ : ℝ) (c e : ℕ) (φ : CNF ℕ) : ℕ :=
  ⌈(c : ℝ) * (2 ^ (δ * ((occBound K M * φ.numVars + 1 : ℕ) : ℝ)) *
    ((nodeBound K L_coeff φ : ℝ) + 1) ^ e) + c⌉₊

include hM hK in
/-- **The time and space of the rounds.** Under `CountingTreeBound`, given a total leaf routine `g`
with `hg : ComputableTidilyInO g encCNF encNat t t` and global bound `ht` holding for every
`ψ : CNF ℕ`, `search M K k B g` runs within time equal to initialization plus `rounds B φ + 1`
times the per-round bound (a polynomial in `stateBound`, plus `leafTime`, plus the binary
round-counter step cost), and within space equal to initialization/round-count space plus the
per-round bound (including `leafTime`, since `hg` bounds both time and space of `g` by `t`). -/
private theorem exists_computableTidilyInO_search (hM2 : 2 ≤ M) {k B L_coeff : ℕ} (hkK : k ≤ K)
    (hTB : CountingTreeBound M K B L_coeff hM hK)
    {g : CNF ℕ → ℕ} {t : CNF ℕ → ℕ} (hg : ComputableTidilyInO g encCNF encNat t t)
    (hg_le : ∀ ψ : CNF ℕ, (∀ c ∈ ψ, c.length ≤ k) →
      isSparse (countingThreshold M) K ψ = true → g ψ ≤ 2 ^ ψ.numVars)
    {δ : ℝ} (hδ : 0 ≤ δ) {c e : ℕ}
    (ht : ∀ ψ : CNF ℕ, (t ψ : ℝ) ≤ c * (2 ^ (δ * ψ.length) * ((encCNF ψ).length + 1) ^ e) + c) :
    ∃ d dn di, ComputableTidilyInO (search M K k B g) encCNF encNat
      (fun φ => ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
        (rounds B φ + 1) * (2 * (2 * stateBound K L_coeff φ + 1) ^ d +
          leafTime K M L_coeff δ c e φ +
          stateBound K L_coeff φ + ((encNat (rounds B φ)).length + 1) ^ 2))
      (fun φ => ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
        (2 * (2 * stateBound K L_coeff φ + 1) ^ d + leafTime K M L_coeff δ c e φ) +
        stateBound K L_coeff φ + (encNat (rounds B φ)).length) := by
  obtain ⟨d, hstep⟩ := exists_computableTidilyInO_step M K hg
  obtain ⟨dn, en, hn⟩ := (computableTidilyInPolyTime_rounds B).exists_degree
  obtain ⟨di, ei, hi⟩ := (computableTidilyInPolyTime_init k).exists_degree
  have hround : ∀ φ, ∀ i ≤ rounds B φ,
      (fun s : State => ((encState s).length + 1) ^ d +
        if s.2.1.isEmpty = false ∧
            isSparse (countingThreshold M) K (s.2.1.headD []) = true then
          t (s.2.1.headD []) +
            ((encState s).length + (encNat (g (s.2.1.headD []))).length + 1) ^ d
        else 0) ((step M K g)^[i] (init k φ)) ≤
        2 * (2 * stateBound K L_coeff φ + 1) ^ d + leafTime K M L_coeff δ c e φ := by
    intro φ i _
    obtain ⟨stk, acc, heq, hstk, hacc, hmem⟩ := (iterate_step hM hK hM2 hkK hTB g φ).2 i
    rw [heq]
    dsimp only
    have hS := length_encState_le hM hK hkK hstk hacc hmem
    have hpow1 : ((encState (φ.distinctVars.length, (stk.map Subtype.val, acc))).length + 1) ^ d ≤
        (2 * stateBound K L_coeff φ + 1) ^ d :=
      Nat.pow_le_pow_left (by omega) d
    split_ifs with hc
    · cases stk with
      | nil => simp at hc
      | cons s rest =>
        obtain ⟨w, hw, hwlen, rfl⟩ := hmem s List.mem_cons_self
        simp only [List.map_cons, List.headD_cons] at hc hS hpow1 ⊢
        set ψ := ((rule hM hK).walk (rootState hkK φ) w).1
        have hlen := length_walk_le_of_isSparse hM hK hkK hc.2
        have henc := length_encCNF_walk_le hM hK hkK hw hwlen
        have hwidth : ∀ c ∈ ψ, c.length ≤ k :=
          fun c hC => length_le_of_mem_walk hM hK hkK hw hC
        have hg_bound : g ψ ≤ 2 ^ φ.numVars :=
          (hg_le ψ hwidth hc.2).trans (Nat.pow_le_pow_right (by omega)
            (numVars_walk_le hM hK hkK w))
        have hglen : (encNat (g ψ)).length ≤ φ.numVars + 1 :=
          length_encNat_le_of_le_two_pow hg_bound
        have hN_le_sb : φ.numVars + 1 ≤ stateBound K L_coeff φ := by
          unfold stateBound
          omega
        have hpow2 :
            ((encState (φ.distinctVars.length, (ψ :: rest.map Subtype.val, acc))).length +
              (encNat (g ψ)).length + 1) ^ d ≤ (2 * stateBound K L_coeff φ + 1) ^ d :=
          Nat.pow_le_pow_left (by omega) d
        have h₁ : (2 : ℝ) ^ (δ * ψ.length) ≤
            2 ^ (δ * ((occBound K M * φ.numVars + 1 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (mul_le_mul_of_nonneg_left (by exact_mod_cast hlen) hδ)
        have h₂ : (((encCNF ψ).length : ℝ) + 1) ^ e ≤ ((nodeBound K L_coeff φ : ℝ) + 1) ^ e :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right henc 1) e
        have h₃ := mul_le_mul h₁ h₂ (by positivity) (by positivity)
        have h₄ := mul_le_mul_of_nonneg_left h₃ (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
        have h₅ := (ht ψ).trans (add_le_add h₄ le_rfl)
        have ht_le : t ψ ≤ leafTime K M L_coeff δ c e φ :=
          Nat.cast_le.mp (h₅.trans (Nat.le_ceil _))
        omega
    · omega
  have hstate : ∀ φ, ∀ i ≤ rounds B φ,
      (encState ((step M K g)^[i] (init k φ))).length ≤ stateBound K L_coeff φ := by
    intro φ i _
    obtain ⟨stk, acc, heq, hstk, hacc, hmem⟩ := (iterate_step hM hK hM2 hkK hTB g φ).2 i
    rw [heq]
    exact length_encState_le hM hK hkK hstk hacc hmem
  exact ⟨d, dn, di,
    (ComputableTidilyInO.iterate hn.inO hi.inO hstep hround hround hstate).snd'.snd'⟩

include hM hK in
/-- **The time and space of the counting-sparsification search.** Given a total leaf routine `g`
with `hg : ComputableInO g encCNF encNat t t` whose time and space `t ψ` satisfy the global bound
`ht` (`O(2 ^ (δ * ψ.length) * (|encCNF ψ| + 1) ^ e)`) for every `ψ : CNF ℕ`, and whose output is at
most `2 ^ ψ.numVars` on sparse width-`≤ k` formulas, `search M K k B g` has a combined
time-and-space certificate `ComputableInO (search M K k B g) encCNF encNat T T` with the
fixed-parameter transfer bound
`T φ ≤ C₀ * (2 ^ ((1 / B + occBound K M * δ) * φ.numVars) * (|encCNF φ| + 1) ^ E) + C₀` (a library
adaptation of the leaf-to-root runtime assembly, without an independent polynomial-space
certificate). -/
theorem exists_computableInO_search (hM2 : 2 ≤ M) {k B L_coeff : ℕ} (hkK : k ≤ K)
    (hTB : CountingTreeBound M K B L_coeff hM hK)
    {g : CNF ℕ → ℕ} {t : CNF ℕ → ℕ} (hg : ComputableInO g encCNF encNat t t)
    (hg_le : ∀ ψ : CNF ℕ, (∀ c ∈ ψ, c.length ≤ k) →
      isSparse (countingThreshold M) K ψ = true → g ψ ≤ 2 ^ ψ.numVars)
    {δ : ℝ} (hδ : 0 ≤ δ) {c e : ℕ}
    (ht : ∀ ψ : CNF ℕ, (t ψ : ℝ) ≤ c * (2 ^ (δ * ψ.length) * ((encCNF ψ).length + 1) ^ e) + c) :
    ∃ T : CNF ℕ → ℕ, ∃ C₀ E : ℕ,
      ComputableInO (search M K k B g) encCNF encNat T T ∧
      ∀ φ : CNF ℕ, (T φ : ℝ) ≤
        C₀ * ((2 : ℝ) ^ ((1 / B + occBound K M * δ) * φ.numVars) *
          (((encCNF φ).length : ℝ) + 1) ^ E) + C₀ := by
  obtain ⟨d, dn, di, h⟩ :=
    exists_computableTidilyInO_search hM hK hM2 hkK hTB hg.tidy hg_le hδ ht
  set Kx := K * L_coeff
  set c₁ := (2 + Kx) * (6 * K + 1)
  set c₂ := 4 + 4 * (L_coeff + 1) * (2 * c₁ + 1) + 10
  set C₁ := 2 * (2 * c₂ + 1) ^ d + c₂ + 16
  set E := dn + di + 3 * d + 2 * e + 3
  set C₂ : ℝ := c * 2 ^ δ * ((c₁ : ℝ) + 1) ^ e + c + 1
  set C₀ : ℝ := 2 + 5 * (C₁ + C₂)
  set T : CNF ℕ → ℕ := fun φ =>
    ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
      (rounds B φ + 1) * (2 * (2 * stateBound K L_coeff φ + 1) ^ d +
        leafTime K M L_coeff δ c e φ +
        stateBound K L_coeff φ + ((encNat (rounds B φ)).length + 1) ^ 2)
  have h_mono : ComputableTidilyInO (search M K k B g) encCNF encNat T T :=
    h.mono_le (fun _ => le_rfl) fun φ => by
      dsimp only [T]
      have h1 : 2 * (2 * stateBound K L_coeff φ + 1) ^ d + leafTime K M L_coeff δ c e φ +
          stateBound K L_coeff φ + (encNat (rounds B φ)).length ≤
          2 * (2 * stateBound K L_coeff φ + 1) ^ d + leafTime K M L_coeff δ c e φ +
            stateBound K L_coeff φ + ((encNat (rounds B φ)).length + 1) ^ 2 := by
        have : (encNat (rounds B φ)).length ≤ ((encNat (rounds B φ)).length + 1) ^ 2 :=
          (Nat.le_succ _).trans (Nat.le_self_pow two_ne_zero _)
        omega
      have h2 := Nat.le_mul_of_pos_left
        (2 * (2 * stateBound K L_coeff φ + 1) ^ d + leafTime K M L_coeff δ c e φ +
          stateBound K L_coeff φ + ((encNat (rounds B φ)).length + 1) ^ 2)
        (Nat.succ_pos (rounds B φ))
      simp only [Nat.succ_eq_add_one] at h2
      omega
  refine ⟨T, ⌈C₀⌉₊, E, .of_tidy h_mono, fun φ => ?_⟩
  set L := (encCNF φ).length
  set N := φ.numVars
  set P := (L + 1) ^ E
  have hNL : N ≤ L := φ.numVars_le_length_vars.trans (SAT.length_vars_le φ)
  have hmL : φ.length ≤ L := length_le_length_encList _ φ
  have hP (a : ℕ) (ha : a ≤ E) : (L + 1) ^ a ≤ P := Nat.pow_le_pow_right (Nat.succ_pos L) ha
  have hnb : nodeBound K L_coeff φ ≤ c₁ * (L + 1) ^ 2 := by
    have h₁ : φ.length + 1 + K * (L_coeff * N) ≤ (2 + Kx) * (L + 1) := by
      have : K * (L_coeff * N) = Kx * N := by ring
      nlinarith
    have h₂ : 2 * (K * (2 * L + 1)) + 1 ≤ (6 * K + 1) * (L + 1) := by nlinarith
    calc nodeBound K L_coeff φ ≤ ((2 + Kx) * (L + 1)) * ((6 * K + 1) * (L + 1)) :=
          Nat.mul_le_mul h₁ h₂
      _ = c₁ * (L + 1) ^ 2 := by ring
  have hsb : stateBound K L_coeff φ ≤ c₂ * (L + 1) ^ 3 := by
    have h₁ : L_coeff * N + 1 ≤ (L_coeff + 1) * (L + 1) := by nlinarith
    have h₂ : 2 * nodeBound K L_coeff φ + 1 ≤ (2 * c₁ + 1) * (L + 1) ^ 2 := by
      have : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos L)
      nlinarith
    have h₃ : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_pos L)
    have h₃' : L + 1 ≤ (L + 1) ^ 3 := by
      calc L + 1 = (L + 1) ^ 1 := (pow_one _).symm
        _ ≤ (L + 1) ^ 3 := Nat.pow_le_pow_right (Nat.succ_pos L) (by omega)
    have h₄ := Nat.mul_le_mul h₁ h₂
    have hdef : stateBound K L_coeff φ =
        4 * N + 4 * ((L_coeff * N + 1) * (2 * nodeBound K L_coeff φ + 1)) + 10 := rfl
    have e₁ : 4 * (L + 1) ^ 3 +
        4 * (((L_coeff + 1) * (L + 1)) * ((2 * c₁ + 1) * (L + 1) ^ 2)) + 10 * (L + 1) ^ 3 =
        c₂ * (L + 1) ^ 3 := by simp only [c₂]; ring
    omega
  have henc : (encNat (rounds B φ)).length = N / B + 3 := by
    rw [rounds, CNF.length_distinctVars, encNat_two_pow, List.length_append,
      List.length_replicate, List.length_singleton]
  have hr : rounds B φ + 1 ≤ 5 * 2 ^ (N / B) := by
    have : rounds B φ = 4 * 2 ^ (N / B) := by
      rw [rounds, CNF.length_distinctVars, pow_add]
      ring
    have : 1 ≤ 2 ^ (N / B) := Nat.one_le_two_pow
    omega
  have hpoly : (L + 1) ^ dn + (L + 1) ^ di ≤ 2 * P := by
    have := hP dn (by omega)
    have := hP di (by omega)
    omega
  have hrnd : 2 * (2 * stateBound K L_coeff φ + 1) ^ d + stateBound K L_coeff φ +
      ((encNat (rounds B φ)).length + 1) ^ 2 ≤ C₁ * P := by
    have h₁ : (2 * stateBound K L_coeff φ + 1) ^ d ≤ (2 * c₂ + 1) ^ d * (L + 1) ^ (3 * d) := by
      rw [pow_mul, ← mul_pow]
      refine Nat.pow_le_pow_left ?_ d
      have : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_pos L)
      have e₁ : (2 * c₂ + 1) * (L + 1) ^ 3 = 2 * (c₂ * (L + 1) ^ 3) + (L + 1) ^ 3 := by ring
      omega
    have h₂ : ((encNat (rounds B φ)).length + 1) ^ 2 ≤ 16 * (L + 1) ^ 2 := by
      rw [henc]
      have : N / B + 3 + 1 ≤ 4 * (L + 1) := by
        have := (Nat.div_le_self N B).trans hNL
        omega
      calc (N / B + 3 + 1) ^ 2 ≤ (4 * (L + 1)) ^ 2 := Nat.pow_le_pow_left this 2
        _ = 16 * (L + 1) ^ 2 := by ring
    have h₃ := hP (3 * d) (by omega)
    have h₄ := hP 3 (by omega)
    have h₅ := hP 2 (by omega)
    have h₆ := Nat.mul_le_mul_left ((2 * c₂ + 1) ^ d) h₃
    calc 2 * (2 * stateBound K L_coeff φ + 1) ^ d + stateBound K L_coeff φ +
          ((encNat (rounds B φ)).length + 1) ^ 2
        ≤ 2 * ((2 * c₂ + 1) ^ d * P) + c₂ * P + 16 * P := by
          have := hsb.trans (Nat.mul_le_mul_left c₂ h₄)
          have := h₂.trans (Nat.mul_le_mul_left 16 h₅)
          omega
      _ = C₁ * P := by ring
  set Y : ℝ := 2 ^ ((occBound K M * δ) * N)
  have hY : 1 ≤ Y := Real.one_le_rpow (by norm_num) (by positivity)
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast Nat.one_le_pow _ _ (Nat.succ_pos L)
  have hleaf : (leafTime K M L_coeff δ c e φ : ℝ) ≤ C₂ * Y * P := by
    have h₁ : (2 : ℝ) ^ (δ * ((occBound K M * N + 1 : ℕ) : ℝ)) = 2 ^ δ * Y := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    have h₂ : ((nodeBound K L_coeff φ : ℝ) + 1) ^ e ≤ ((c₁ : ℝ) + 1) ^ e * P := by
      have : ((nodeBound K L_coeff φ : ℝ) + 1) ≤ ((c₁ : ℝ) + 1) * ((L : ℝ) + 1) ^ 2 := by
        have hnb' : (nodeBound K L_coeff φ : ℝ) ≤ c₁ * ((L : ℝ) + 1) ^ 2 := by exact_mod_cast hnb
        have hL2 : (1 : ℝ) ≤ ((L : ℝ) + 1) ^ 2 :=
          one_le_pow₀ (by linarith [(L.cast_nonneg : (0 : ℝ) ≤ L)])
        have e₁ : ((c₁ : ℝ) + 1) * ((L : ℝ) + 1) ^ 2 = c₁ * ((L : ℝ) + 1) ^ 2 +
          ((L : ℝ) + 1) ^ 2 := by ring
        linarith only [hnb', hL2, e₁]
      calc ((nodeBound K L_coeff φ : ℝ) + 1) ^ e ≤ (((c₁ : ℝ) + 1) * ((L : ℝ) + 1) ^ 2) ^ e :=
            pow_le_pow_left₀ (by positivity) this e
        _ = ((c₁ : ℝ) + 1) ^ e * ((L : ℝ) + 1) ^ (2 * e) := by rw [mul_pow, ← pow_mul]
        _ ≤ ((c₁ : ℝ) + 1) ^ e * P := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact_mod_cast hP (2 * e) (by omega)
    have h₃ := Nat.ceil_lt_add_one (show (0 : ℝ) ≤
      (c : ℝ) * (2 ^ (δ * ((occBound K M * N + 1 : ℕ) : ℝ)) *
        ((nodeBound K L_coeff φ : ℝ) + 1) ^ e) + c by positivity)
    unfold leafTime
    rw [h₁] at h₃ ⊢
    have h₄ : (c : ℝ) * (2 ^ δ * Y * ((nodeBound K L_coeff φ : ℝ) + 1) ^ e) ≤
        c * 2 ^ δ * ((c₁ : ℝ) + 1) ^ e * Y * P := by
      have := mul_le_mul_of_nonneg_left h₂ (by positivity : (0 : ℝ) ≤ c * 2 ^ δ * Y)
      linarith only [this]
    have h₅ : (c : ℝ) + 1 ≤ ((c : ℝ) + 1) * Y * P := by
      rw [mul_assoc]
      exact le_mul_of_one_le_right (by positivity)
        (one_le_mul_of_one_le_of_one_le hY hP1)
    calc (⌈(c : ℝ) * (2 ^ δ * Y * ((nodeBound K L_coeff φ : ℝ) + 1) ^ e) + c⌉₊ : ℝ)
        ≤ (c : ℝ) * (2 ^ δ * Y * ((nodeBound K L_coeff φ : ℝ) + 1) ^ e) + c + 1 := h₃.le
      _ ≤ C₂ * Y * P := by simp only [C₂]; linarith only [h₄, h₅]
  set X : ℝ := 2 ^ ((1 / B : ℝ) * N)
  have hX : ((2 ^ (N / B) : ℕ) : ℝ) ≤ X := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [one_div_mul_eq_div]
    exact Nat.cast_div_le
  have hX1 : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
  have hXY : X * Y = 2 ^ ((1 / B + occBound K M * δ) * N) := by
    rw [← Real.rpow_add (by norm_num)]
    ring_nf
  have hT : (T φ : ℝ) ≤ 2 * P + 5 * X * (C₁ * P + C₂ * Y * P) := by
    dsimp only [T]
    have h₁ : ((L + 1) ^ dn + (L + 1) ^ di : ℝ) ≤ 2 * P := by exact_mod_cast hpoly
    have h₂ : ((rounds B φ + 1 : ℕ) : ℝ) ≤ 5 * X := by
      have : ((rounds B φ + 1 : ℕ) : ℝ) ≤ ((5 * 2 ^ (N / B) : ℕ) : ℝ) := by exact_mod_cast hr
      rw [Nat.cast_mul] at this
      push_cast at this hX ⊢
      linarith only [this, hX]
    have h₃ : (((2 * (2 * stateBound K L_coeff φ + 1) ^ d + stateBound K L_coeff φ +
        ((encNat (rounds B φ)).length + 1) ^ 2 : ℕ)) : ℝ) ≤ C₁ * P := by exact_mod_cast hrnd
    have h₄ : (((2 * (2 * stateBound K L_coeff φ + 1) ^ d + leafTime K M L_coeff δ c e φ +
        stateBound K L_coeff φ + ((encNat (rounds B φ)).length + 1) ^ 2 : ℕ)) : ℝ) ≤
        C₁ * P + C₂ * Y * P := by
      push_cast at h₃ ⊢
      linarith only [h₃, hleaf]
    have h₅ := mul_le_mul h₂ h₄ (by positivity) (by positivity)
    push_cast at h₁ h₅ ⊢
    linarith only [h₁, h₅]
  have h_prod : (T φ : ℝ) ≤
      ⌈C₀⌉₊ * (2 ^ ((1 / B + occBound K M * δ) * N) * ((L : ℝ) + 1) ^ E) := by
    calc (T φ : ℝ) ≤ 2 * P + 5 * X * (C₁ * P + C₂ * Y * P) := hT
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
      _ ≤ ⌈C₀⌉₊ * (2 ^ ((1 / B + occBound K M * δ) * N) * ((L : ℝ) + 1) ^ E) := by
          rw [← hXY]
          push_cast [P]
          exact mul_le_mul_of_nonneg_right (Nat.le_ceil C₀) (by positivity)
  linarith [h_prod, (Nat.cast_nonneg ⌈C₀⌉₊ : (0 : ℝ) ≤ ⌈C₀⌉₊)]

/-! ### Captured runtime context -/

section ContextWrapper

variable {P : Type*}

/-- One step of the depth-first search of the counting-sparsification tree carrying an unchanged
runtime context `p : P`, using threshold family `θ p` and context-aware leaf counter `g`
(returning the occurring-variable count `ψ.modelCount` on sparse leaves). -/
def stepWith (θ : P → ℕ → ℕ) (K : ℕ) (g : P × CNF ℕ → ℕ) (ps : P × State) : P × State :=
  (ps.1,
    if ps.2.2.1.isEmpty then ps.2
    else if isSparse (θ ps.1) K (ps.2.2.1.headD []) then
      leafUpdate ps.2 (g (ps.1, ps.2.2.1.headD []))
    else
      (ps.2.1, (countingNext (θ ps.1) K (ps.2.2.1.headD []) false ::
        countingNext (θ ps.1) K (ps.2.2.1.headD []) true :: ps.2.2.1.tail, ps.2.2.2)))

@[simp]
theorem stepWith_fst (θ : P → ℕ → ℕ) (K : ℕ) (g : P × CNF ℕ → ℕ) (ps : P × State) :
    (stepWith θ K g ps).1 = ps.1 := rfl

@[simp]
theorem iterate_stepWith_fst (θ : P → ℕ → ℕ) (K : ℕ) (g : P × CNF ℕ → ℕ) (r : ℕ)
    (ps : P × State) : ((stepWith θ K g)^[r] ps).1 = ps.1 := by
  induction r generalizing ps with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, ih, stepWith_fst]

@[simp]
theorem stepWith_countingThreshold (MOf : P → ℕ) (K : ℕ) (g : P × CNF ℕ → ℕ)
    (p : P) (s : State) :
    stepWith (fun q => countingThreshold (MOf q)) K g (p, s) =
      (p, step (MOf p) K (fun ψ => g (p, ψ)) s) := rfl

@[simp]
theorem iterate_stepWith_countingThreshold (MOf : P → ℕ) (K : ℕ) (g : P × CNF ℕ → ℕ)
    (r : ℕ) (p : P) (s : State) :
    (stepWith (fun q => countingThreshold (MOf q)) K g)^[r] (p, s) =
      (p, (step (MOf p) K (fun ψ => g (p, ψ)))^[r] s) := by
  induction r generalizing s with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, stepWith_countingThreshold, ih,
      Function.iterate_succ_apply]

end ContextWrapper

end CountingSparsify

end Cslib.Complexity
