/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ExactOneCounting
public import CslibFrontier.Foundations.LinearAlgebra.Elimination

/-!
# Executable elimination and nonadaptive exact-one counting queries

`preprocess` performs rational elimination on the original signed rows, detects
inconsistency, checks the actual unique candidate, or emits the two ordinary CNFs
from `sideQuery`. Only the branch with at most one declared bit enumerates Boolean
assignments. No enumeration of row subsets or dependence oracle is used.

This is the functional assembly in [ChenJiangZhu2027], Theorems 1.2 and 5.2,
PDF pp. 5 and 15–17, also applicable to the signed equations in Theorem 6.3.
`preprocess_correct` proves exact counting and `preprocess_budget` the two-query
width, clause and declared-variable bounds. They do not establish the paper's
polynomial bit-time preprocessing claim: rational coefficient growth and encoded
execution costs are not certified here.

## Main definitions

* `preprocess`: all-cases signed-system counting plan construction.
* `CountPlan.execute`: direct answer or two nonadaptive ordinary counts.

## Main results

* `preprocess_correct`: exact counting on all declared bits.
* `preprocess_budget`: width, clause and declared-variable bounds for emitted queries.

-/

public section

namespace Cslib.Logic.PL.ExactOne

open Matrix Cslib.LinearSystem

variable {V I : Type*} [Fintype V] [LinearOrder V] [Fintype I] [LinearOrder I]

/-- A direct answer or two ordinary CNFs on the same declared variables.
Both queries are materialized independently of the oracle answers. -/
inductive CountPlan (V : Type*) where
  /-- Direct cases require no counting query. -/
  | direct (answer : ℕ)
  /-- Two unweighted queries with exactly `k` additional declared bits. -/
  | queries (k : ℕ) (zero one : CNF (V ⊕ Fin k))

/-- Execute a prepared plan with any supplied ordinary declared-variable counter. -/
@[expose] def CountPlan.execute (count : (k : ℕ) → CNF (V ⊕ Fin k) → ℕ) : CountPlan V → ℕ
  | .direct n => n
  | .queries k zero one => count k zero - count k one

/-- Specification of an ordinary count; this cardinality is not an algorithm. -/
@[expose] noncomputable def declaredCount {W : Type*} [Fintype W] [DecidableEq W] (B : CNF W) : ℕ :=
  Fintype.card {x : W → Bool // B.eval x = true}

/-- Semantic evaluation of a prepared plan. -/
@[expose] noncomputable def CountPlan.value (plan : CountPlan V) : ℕ :=
  plan.execute (fun _ => declaredCount)

/-- Source semantics on every declared bit, including unused variables. -/
@[expose] noncomputable def sourceCount (B : CNF V) (S : I → Finset V) (p : I → V → Bool) : ℕ :=
  Fintype.card {x : V → Bool // B.eval x = true ∧ ∀ i, Holds (S i) (p i) x}

/-- Check the actual candidate on all source constraints. It costs a finite scan,
not a count over the Boolean cube. -/
@[expose] def checkCandidate (B : CNF V) (S : I → Finset V) (p : I → V → Bool)
    (z : V → ℚ) : ℕ :=
  if B.eval (candidateBits z) = true ∧ ∀ i, Holds (S i) (p i) (candidateBits z)
    then 1 else 0

/-- Enumeration is confined by `preprocess` to at most one declared bit. -/
@[expose] def smallCount (B : CNF V) (S : I → Finset V) (p : I → V → Bool) : ℕ :=
  (Finset.univ.filter fun x : V → Bool =>
    B.eval x = true ∧ ∀ i, Holds (S i) (p i) x).card

/-- Compile retained original indices. With no rows, use the binary side CNF and
an unsatisfiable second query; otherwise use the existing two-boundary compiler. -/
@[expose] def selectedPlan (B : CNF V) (S : I → Finset V) (p : I → V → Bool) :
    List I → CountPlan V
  | [] => .queries 0 (CNF.relabel Sum.inl B.dedup) [[]]
  | j :: js => .queries js.length
      (sideQuery B (fun t => S ((j :: js).get t)) (fun t => p ((j :: js).get t)) false)
      (sideQuery B (fun t => S ((j :: js).get t)) (fun t => p ((j :: js).get t)) true)

/-- Eliminate in declared-column order using the finite original row enumeration. -/
@[expose] def originalElimination (S : I → Finset V) (p : I → V → Bool) : Elimination I V :=
  eliminateCached (Finset.univ.sort (· ≤ ·)) (Finset.univ.sort (· ≤ ·))
    (fun i => coefficients (S i) (p i)) (fun i => rhs (S i) (p i))

/-- Executable all-cases assembly. The only exhaustive assignment loop is guarded
by `|V| ≤ 1`. All larger instances use row scans, rational arithmetic and syntax
compilation. The right-hand side undergoes the same operations as coefficients. -/
@[expose] def preprocess (B : CNF V) (S : I → Finset V) (p : I → V → Bool) : CountPlan V :=
  if Fintype.card V ≤ 1 then .direct (smallCount B S p) else
    let result := originalElimination S p
    if result.consistent then
      if result.indices.length = Fintype.card V then
        .direct (checkCandidate B S p result.point)
      else selectedPlan B S p result.indices
    else .direct 0

private theorem full_support (A : I → V → ℚ) :
    ∀ i ∈ ((Finset.univ : Finset I).sort (· ≤ ·)), ∀ v,
      v ∉ (Finset.univ : Finset V).sort (· ≤ ·) → A i v = 0 := by
  simp

/-- The program never retains more rows than declared variables. -/
theorem originalElimination_length (S : I → Finset V) (p : I → V → Bool) :
    (originalElimination S p).indices.length ≤ Fintype.card V := by
  simpa [originalElimination, eliminateCached_eq] using eliminate_length_le
    ((Finset.univ : Finset I).sort (· ≤ ·)) (Finset.univ.sort (· ≤ ·))
    (fun i => coefficients (S i) (p i)) (fun i => rhs (S i) (p i))

/-- Its consistency flag is equivalent to actual rational consistency. -/
theorem originalElimination_consistent (S : I → Finset V) (p : I → V → Bool) :
    (originalElimination S p).consistent = true ↔
      ∃ z : V → ℚ, ∀ i, coefficients (S i) (p i) ⬝ᵥ z = rhs (S i) (p i) := by
  simpa [originalElimination, eliminateCached_eq] using eliminate_consistent_iff
    ((Finset.univ : Finset I).sort (· ≤ ·)) (Finset.univ.sort (· ≤ ·))
    (fun i => coefficients (S i) (p i)) (fun i => rhs (S i) (p i)) (full_support _)

/-- Original-index selection preserves the Boolean constraints pointwise. -/
theorem originalElimination_selected (S : I → Finset V) (p : I → V → Bool)
    (hc : (originalElimination S p).consistent = true) (x : V → Bool) :
    (∀ i ∈ (originalElimination S p).indices, Holds (S i) (p i) x) ↔
      ∀ i, Holds (S i) (p i) x := by
  have h := eliminate_selected_iff ((Finset.univ : Finset I).sort (· ≤ ·))
    (Finset.univ.sort (· ≤ ·)) (fun i => coefficients (S i) (p i))
    (fun i => rhs (S i) (p i)) (full_support _)
    (by simpa only [originalElimination, eliminateCached_eq] using hc)
    (rationalPoint x)
  simpa only [originalElimination, eliminateCached_eq, equation_iff, Finset.mem_sort,
    Finset.mem_univ,
    forall_const] using h

private theorem candidate_of_solution (S : I → Finset V) (p : I → V → Bool)
    (hc : (originalElimination S p).consistent = true)
    (hl : (originalElimination S p).indices.length = Fintype.card V)
    (x : V → Bool) (hx : ∀ i, Holds (S i) (p i) x) :
    candidateBits (originalElimination S p).point = x := by
  have hz := eliminate_point ((Finset.univ : Finset I).sort (· ≤ ·))
    (Finset.univ.sort (· ≤ ·)) (fun i => coefficients (S i) (p i))
    (fun i => rhs (S i) (p i)) (full_support _)
    (by simpa only [originalElimination, eliminateCached_eq] using hc)
  have he : rationalPoint x = (originalElimination S p).point := by
    apply eliminate_unique ((Finset.univ : Finset I).sort (· ≤ ·))
      (Finset.univ.sort (· ≤ ·)) (fun i => coefficients (S i) (p i))
      (fun i => rhs (S i) (p i))
      (by simpa only [originalElimination, eliminateCached_eq, Finset.length_sort,
        Finset.card_univ] using hl)
    · intro i _; exact (equation_iff _ _ _).mpr (hx i)
    · simpa only [originalElimination, eliminateCached_eq] using hz
    · simp
  rw [← he]
  funext v
  cases hv : x v <;> simp [candidateBits, rationalPoint, hv]

private theorem checkCandidate_correct (B : CNF V) (S : I → Finset V) (p : I → V → Bool)
    (hc : (originalElimination S p).consistent = true)
    (hl : (originalElimination S p).indices.length = Fintype.card V) :
    checkCandidate B S p (originalElimination S p).point = sourceCount B S p := by
  classical
  let P := fun x : V → Bool => B.eval x = true ∧ ∀ i, Holds (S i) (p i) x
  have he : ∀ x, P x → x = candidateBits (originalElimination S p).point :=
    fun x hx => (candidate_of_solution S p hc hl x hx.2).symm
  let : Subsingleton {x // P x} := ⟨fun x y => Subtype.ext ((he x x.property).trans
    (he y y.property).symm)⟩
  have hle : sourceCount B S p ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  unfold checkCandidate
  split_ifs with hb
  · have hpos : 0 < sourceCount B S p := Fintype.card_pos_iff.mpr ⟨⟨_, hb⟩⟩
    omega
  · symm
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun x => hb ((he x x.property) ▸ x.property)⟩

private theorem declaredCount_false : declaredCount ([[]] : CNF (V ⊕ Fin 0)) = 0 := by
  unfold declaredCount
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun x => by simpa using x.property⟩

private theorem declaredCount_relabel (B : CNF V) :
    declaredCount (B.relabel (Sum.inl : V → V ⊕ Fin 0)) = declaredCount B := by
  unfold declaredCount
  let e : (V ⊕ Fin 0 → Bool) ≃ (V → Bool) :=
    { toFun := fun x => x ∘ Sum.inl
      invFun := fun x => Sum.elim x Fin.elim0
      left_inv := fun x => by funext v; cases v with
        | inl v => rfl
        | inr v => exact Fin.elim0 v
      right_inv := fun _ => rfl }
  exact Fintype.card_congr (e.subtypeEquiv fun x => by
    change (B.relabel Sum.inl).eval x = true ↔ B.eval (x ∘ Sum.inl) = true
    rw [CNF.eval_relabel])

omit [LinearOrder I] in
/-- Compilation from an actual list of retained original rows preserves the count. -/
theorem selectedPlan_correct (B : CNF V) (S : I → Finset V) (p : I → V → Bool)
    (is : List I) (hs : ∀ x : V → Bool,
      (∀ i ∈ is, Holds (S i) (p i) x) ↔ ∀ i, Holds (S i) (p i) x) :
    (selectedPlan B S p is).value = sourceCount B S p := by
  classical
  cases is with
  | nil =>
    have hh (x : V → Bool) : ∀ i, Holds (S i) (p i) x := (hs x).mp (by simp)
    simp only [selectedPlan, CountPlan.value, CountPlan.execute,
      declaredCount_false, Nat.sub_zero, declaredCount_relabel]
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    simp only [hh x, implies_true, and_true, CNF.eval_eq_true_iff, List.mem_dedup]
  | cons j js =>
    change declaredCount (sideQuery B _ _ false) - declaredCount (sideQuery B _ _ true) = _
    unfold declaredCount
    rw [← side_counting_identity]
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    apply and_congr_right
    intro _
    rw [← hs x]
    constructor
    · intro h i hi
      obtain ⟨t, ht⟩ := List.get_of_mem hi
      simpa only [ht] using h t
    · intro h t
      exact h _ (List.get_mem _ _)

/-- Exact all-cases correctness, without solution witnesses, a rank oracle or an
assumed preprocessing contract. `value` supplies mathematical oracle semantics;
`preprocess` itself constructs syntax and direct answers by execution. -/
theorem preprocess_correct (B : CNF V) (S : I → Finset V) (p : I → V → Bool) :
    (preprocess B S p).value = sourceCount B S p := by
  unfold preprocess
  split_ifs with hsmall
  · simp [CountPlan.value, CountPlan.execute, smallCount, sourceCount, Fintype.card_subtype]
  · dsimp only
    split_ifs with hc hl
    · exact checkCandidate_correct B S p hc hl
    · exact selectedPlan_correct B S p _ (originalElimination_selected S p hc)
    · change 0 = sourceCount B S p
      symm
      apply count_eq_zero_of_inconsistent
      exact fun h => hc ((originalElimination_consistent S p).mpr h)

/-- Query budgets; direct answers make no query. -/
@[expose] def CountPlan.Budget (n : ℕ) : CountPlan V → Prop
  | .direct _ => True
  | .queries k zero one =>
      Fintype.card (V ⊕ Fin k) ≤ 2 * n - 2 ∧
      (∀ (β : Bool) c, c ∈ (if β then one else zero) → c.length ≤ 3) ∧
      (∀ β : Bool, (if β then one else zero).length ≤ 13 * n ^ 2)

omit [Fintype I] [LinearOrder I] in
/-- The two-query compiler's budget depends only on the number of retained
original equations, independently of the elimination backend. -/
theorem selectedPlan_budget (B : CNF V) (hb : ∀ c ∈ B, c.length ≤ 2)
    (S : I → Finset V) (p : I → V → Bool) (is : List I)
    (hsmall : ¬ Fintype.card V ≤ 1) (hi : is.length < Fintype.card V) :
    (selectedPlan B S p is).Budget (Fintype.card V) := by
  cases is with
  | nil =>
    refine ⟨by simp only [Fintype.card_sum, Fintype.card_fin]; omega, ?_, ?_⟩
    · intro β c hc
      cases β
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
        have hm : d ∈ B := List.mem_dedup.mp hd
        have hdlen : d.length ≤ 3 := (hb d hm).trans (by decide : 2 ≤ 3)
        simpa only [Clause.relabel, List.length_map] using hdlen
      · have hh : c = [] := List.mem_singleton.mp hc
        simp [hh]
    · intro β
      cases β
      · change (CNF.relabel Sum.inl B.dedup).length ≤ _
        simp only [CNF.relabel, List.length_map]
        have hd := dedup_binary_length B hb
        have hr : 2 ≤ Fintype.card V := by omega
        nlinarith
      · change 1 ≤ _
        have hr : 2 ≤ Fintype.card V := by omega
        nlinarith
  | cons j js =>
    have hk : js.length + 1 < Fintype.card V := by
      simpa only [List.length_cons] using hi
    refine ⟨(query_variables hk).2, ?_, ?_⟩
    · intro β c hc
      cases β <;> exact sideQuery_width B hb _ _ _ c hc
    · intro β
      cases β <;> exact sideQuery_length B hb _ _ hk _

/-- Every emitted query has width three, at most `13r²` clauses and at most
`2r-2` declared variables. Small instances are handled without oracle calls. -/
theorem preprocess_budget (B : CNF V) (hb : ∀ c ∈ B, c.length ≤ 2)
    (S : I → Finset V) (p : I → V → Bool) :
    (preprocess B S p).Budget (Fintype.card V) := by
  unfold preprocess
  split_ifs with hsmall
  · trivial
  · dsimp only
    split_ifs with hc hl
    · trivial
    · have hlt : (originalElimination S p).indices.length < Fintype.card V :=
        lt_of_le_of_ne (originalElimination_length S p) hl
      exact selectedPlan_budget B hb S p _ hsmall hlt
    · trivial

end Cslib.Logic.PL.ExactOne
