/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Basic
public import Cslib.Computability.QueryComplexity.Measures

/-!
# Decision-tree lower bounds from query-complexity measures

CSLib supplies sensitivity, block sensitivity and certificate complexity, including
`s(f) ≤ bs(f) ≤ C(f)`. The variables a tree queries at an input form a certificate, so
`C(f) ≤ D(f)` [Nisan1991], [Jukna, Section 14.3][Jukna2012].

The numerical measures use CSLib's `BooleanFunction n`. The coordinate-witness lower bound
`card_le_complexity_of_forall_update_ne` also applies to arbitrary finite coordinate types and
arbitrary outputs, without introducing a second family of measures.

## Main results

* `Cslib.DecisionTree.subset_queries_of_forall_update_ne`: a tree must query every coordinate
  whose flip changes its output.
* `Cslib.DecisionTree.card_le_complexity_of_forall_update_ne`: sensitive coordinates give a
  lower bound for arbitrary output types.
* `Cslib.DecisionTree.certificateComplexity_le_complexity`: `C(f) ≤ D(f)`.
* `Cslib.DecisionTree.sensitivityAt_le_complexity`: sensitivity at any input bounds `D(f)` below.

## References

* [N. Nisan, *CREW PRAMs and decision trees*][Nisan1991]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.DecisionTree

open Finset BitString QueryComplexity

variable {ι β : Type*} [DecidableEq ι]

/-- A tree must query every coordinate whose flip changes the function's value at `x`.
The coordinates and outputs need not be finite. -/
theorem subset_queries_of_forall_update_ne {f : (ι → Bool) → β} {t : DecisionTree ι β}
    (ht : t.Computes f) {x : ι → Bool} {S : Finset ι}
    (hS : ∀ i ∈ S, f (Function.update x i (!x i)) ≠ f x) : S ⊆ t.queries x := by
  intro i hi
  by_contra hnot
  apply hS i hi
  have heval := t.eval_eq_of_forall_mem_queries (x := x) (y := Function.update x i (!x i))
    (fun j hj => Function.update_of_ne (ne_of_mem_of_not_mem hj hnot) _ _)
  exact (ht _).symm.trans (heval.trans (ht x))

/-- Exhibiting sensitive coordinates bounds decision tree complexity below, for any output type. -/
theorem card_le_complexity_of_forall_update_ne [Finite ι] {f : (ι → Bool) → β}
    {x : ι → Bool} {S : Finset ι}
    (hS : ∀ i ∈ S, f (Function.update x i (!x i)) ≠ f x) : #S ≤ complexity f := by
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  exact (card_le_card (subset_queries_of_forall_update_ne ht hS)).trans
    ((t.card_queries_le_depth x).trans hd.le)

/-- Sensitivity to every coordinate forces a tree to query all of them in the worst case. -/
theorem complexity_eq_card_of_forall_update_ne [Fintype ι] {f : (ι → Bool) → β}
    {x : ι → Bool} (h : ∀ i, f (Function.update x i (!x i)) ≠ f x) :
    complexity f = Fintype.card ι := by
  refine le_antisymm (complexity_le_card f) ?_
  simpa only [card_univ] using
    card_le_complexity_of_forall_update_ne (S := univ) (fun i _ => h i)

variable {n : ℕ}

/-- The coordinates queried at an input certify the output of the tree. -/
private theorem isCertificate_queries {f : BooleanFunction n} {t : DecisionTree (Fin n) Bool}
    (ht : t.Computes f) (x : BitString n) : IsCertificate f x (t.queries x) :=
  fun y hy => (ht y).symm.trans ((t.eval_eq_of_forall_mem_queries hy).trans (ht x))

/-- Certificate complexity at an input is at most the depth of any tree computing the function. -/
theorem certificateComplexityAt_le_depth {f : BooleanFunction n}
    {t : DecisionTree (Fin n) Bool} (ht : t.Computes f) (x : BitString n) :
    certificateComplexityAt f x ≤ t.depth :=
  (certificateComplexityAt_le (isCertificate_queries ht x)).trans (t.card_queries_le_depth x)

/-- Certificate complexity is at most decision tree complexity. -/
theorem certificateComplexity_le_complexity (f : BooleanFunction n) :
    certificateComplexity f ≤ complexity f := by
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  exact Finset.sup_le fun x _ => (certificateComplexityAt_le_depth ht x).trans hd.le

/-- A lower bound on sensitivity at one input is a lower bound on decision tree complexity. -/
theorem sensitivityAt_le_complexity (f : BooleanFunction n) (x : BitString n) :
    sensitivityAt f x ≤ complexity f :=
  (sensitivityAt_le_blockSensitivityAt f x).trans <|
    (blockSensitivityAt_le_certificateComplexityAt f x).trans <|
      (certificateComplexityAt_le_certificateComplexity f x).trans
        (certificateComplexity_le_complexity f)

/-- A function sensitive to every variable at some input needs to query all of them. -/
theorem complexity_eq_card_of_sensitivityAt_eq_card {f : BooleanFunction n} {x : BitString n}
    (h : sensitivityAt f x = n) : complexity f = n :=
  le_antisymm ((complexity_le_card f).trans_eq (Fintype.card_fin n))
    (h.symm.trans_le (sensitivityAt_le_complexity f x))

end Cslib.DecisionTree
