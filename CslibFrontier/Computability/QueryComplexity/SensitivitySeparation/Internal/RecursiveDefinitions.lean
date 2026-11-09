/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveProfiles
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Tournament
public import Mathlib.Data.Fintype.Prod

/-!
# Superquadratic sensitivity separation: recursive definitions

This file defines one level of the recursive construction. Next-level inputs are indexed by
`(Fin k × Fin r) × I`: a row `i : Fin k`, a column `c : Fin r` and a child coordinate. Given a
tournament `T`, an edge labeling `label` and a family `F` of `h + 1` child predicates whose last
member is the target predicate, the clause of row `i` at index `q : Fin h` asks that every child of
row `i` satisfies the target predicate and that, for each out-neighbour `j` of `i`, the child
`(j, label i j)` is rejected by the gate predicate `F (gateIndex q)`. The next-level predicate at
`q` is the disjunction of these clauses.

## Main definitions

* `recursiveChild`: the child input at row `j` and column `c` of a next-level input.
* `gateIndex`: the order-reversing embedding `Fin h → Fin (h + 1)` selecting gate predicates.
* `rowClause`: the clause of row `i` at index `q`.
* `recursiveFamily`: the next-level family, the disjunction of all row clauses.

## Main results

* `recursiveFamily_eq_true_iff`: a next-level predicate accepts iff some row clause holds.
* `recursiveFamily_nested`: the construction preserves nested families.
* `recursiveFamily_zero`: if `0 < r` and every child predicate rejects the all-false input, so does
  every next-level predicate.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/RecursiveDefinitions.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- Restrict a recursive input to one row and column of child coordinates. -/
def recursiveChild {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) : I → Bool :=
  fun a => x ((j, c), a)

/-- The reversed gate index among all indices except the final target index. -/
def gateIndex {h : ℕ} (q : Fin h) : Fin (h + 1) := (Fin.rev q).castSucc

/-- Every gate index lies strictly below the target index `Fin.last h`. -/
theorem gateIndex_lt_last {h : ℕ} (q : Fin h) : gateIndex q < Fin.last h :=
  Fin.castSucc_lt_last _

/-- `gateIndex` is antitone: `q ≤ q'` implies `gateIndex q' ≤ gateIndex q`. -/
private theorem gateIndex_antitone {h : ℕ} {q q' : Fin h} (hqq : q ≤ q') :
    gateIndex q' ≤ gateIndex q := by
  exact Fin.rev_le_rev.mpr hqq

/-- `gateIndex` is strictly antitone: `q < q'` implies `gateIndex q' < gateIndex q`. -/
theorem gateIndex_strictAnti {h : ℕ} {q q' : Fin h} (hqq : q < q') :
    gateIndex q' < gateIndex q := by
  exact Fin.rev_lt_rev.mpr hqq

open scoped Classical in
/-- A clause uses every target in its own row and one labeled gate per outgoing edge. -/
def rowClause {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Bool :=
  decide ((∀ c, F (Fin.last h) (recursiveChild x i c) = true) ∧
    ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false)

/-- The next-level predicate is the disjunction of the literal row clauses. -/
def recursiveFamily {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) : Bool :=
  decide (∃ i, rowClause T label F q x i = true)

open scoped Classical in
/-- The clause of row `i` at index `q` holds iff `F (Fin.last h)` accepts every child `(i, c)` and
`F (gateIndex q)` rejects the child `(j, label i j)` for every out-neighbour `j` of `i`. -/
theorem rowClause_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    rowClause T label F q x i = true ↔
      (∀ c, F (Fin.last h) (recursiveChild x i c) = true) ∧
      ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false := by
  simp only [rowClause, decide_eq_true_eq]

/-- The next-level predicate at index `q` accepts `x` iff some row clause holds at `x`. -/
theorem recursiveFamily_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = true ↔ ∃ i, rowClause T label F q x i = true := by
  simp only [recursiveFamily, decide_eq_true_eq]

/-- The next-level predicate at index `q` rejects `x` iff every row clause fails at `x`. -/
theorem recursiveFamily_eq_false_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = false ↔ ∀ i, rowClause T label F q x i = false := by
  simp [recursiveFamily]

/-- For a nested family `F` and `q ≤ q'`, the clause of row `i` at index `q'` implies the clause of
row `i` at index `q`. -/
theorem rowClause_nested {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) {q q' : Fin h} (hqq : q ≤ q')
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : rowClause T label F q' x i = true) : rowClause T label F q x i = true := by
  rw [rowClause_eq_true_iff] at hi ⊢
  refine ⟨hi.1, fun j hij => ?_⟩
  exact hF.rejects_of_le (gateIndex_antitone hqq) (hi.2 j hij)

/-- If `F` is a nested family, then so is `recursiveFamily T label F`. -/
theorem recursiveFamily_nested {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) : NestedFamily (recursiveFamily T label F) := by
  constructor
  intro q q' x hqq hx
  obtain ⟨i, hi⟩ := (recursiveFamily_eq_true_iff T label F q' x).mp hx
  exact (recursiveFamily_eq_true_iff T label F q x).mpr
    ⟨i, rowClause_nested T label F hF hqq x i hi⟩

/-- If `0 < r` and every member of `F` rejects the all-false input, then every next-level predicate
rejects the all-false input. -/
theorem recursiveFamily_zero {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hr : 0 < r) (hzero : ∀ q, F q (fun _ => false) = false) (q : Fin h) :
    recursiveFamily T label F q (fun _ => false) = false := by
  rw [recursiveFamily_eq_false_iff]
  intro i
  cases hi : rowClause T label F q (fun _ => false) i
  · rfl
  · have ht := ((rowClause_eq_true_iff T label F q (fun _ => false) i).mp hi).1
      (⟨0, hr⟩ : Fin r)
    have hz := hzero (Fin.last h)
    change F (Fin.last h) (fun _ => false) = true at ht
    simp [hz] at ht

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
