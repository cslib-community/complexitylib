/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.VCOneTables
public import Complexity.Logics.Propositional.CNF.ExactOneElimination

/-!
# Executable counting plans from overlapping VC-one tables

`tablePlan` constructs local separators using the existing closure listing, assigns
finite row indices, executes materialized rational elimination in shared global
columns and emits a direct answer or two ordinary 3-CNFs. Scopes may overlap
arbitrarily. There is no enumeration of all local tuples or global assignments,
except for the explicitly guarded branch with at most one global variable.

`tablePlan_correct` and `tablePlan_budget` supply functional correctness and syntax
budgets for [ChenJiangZhu2027], Theorem 6.3, PDF pp. 20–21. Polynomial coefficient
growth and encoded bit-time execution remain unproved; this is not the complete
algorithmic resource theorem.

## Main definitions

* `equationList`: finite numbering of the actually listed missing closure tuples.
* `tablePlan`: executable global table-to-counting-plan compilation.

## Main results

* `tablePlan_correct`: original table solutions have exactly the plan's value.
* `tablePlan_budget`: every emitted query meets the global syntax budgets.

-/

public section

namespace Cslib.Logic.PL.VCOne

variable {V : Type*} [Fintype V] [LinearOrder V] {m : ℕ}
    (w : Fin m → ℕ) (scope : (i : Fin m) → Fin (w i) ↪ V)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool))

/-- List the actually generated equation indices, preserving table indices.
The finite instance for each difference uses `listedClosure`, not the cube. -/
@[expose] def equationList : List (EquationIndex w R) :=
  (List.finRange m).flatMap fun i =>
    letI : Fintype ↥(closure (R i) \ R i) := listedDifferenceFintype (R i)
    let order : LinearOrder ↥(closure (R i) \ R i) :=
      LinearOrder.lift' (fun y => List.ofFn y.val)
        (fun _ _ h => Subtype.ext (List.ofFn_injective h))
    ((Finset.univ : Finset ↥(closure (R i) \ R i)).sort
      (@LE.le _ order.toLE)).map fun y => ⟨i, y⟩

/-- Every semantic equation occurs in the executable list. -/
theorem mem_equationList (j : EquationIndex w R) : j ∈ equationList w R := by
  rcases j with ⟨i, y⟩
  unfold equationList
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, ?_⟩
  exact List.mem_map.mpr ⟨y, by simp, rfl⟩

/-- Binary restrictions enumerated directly from the finite input table list. -/
@[expose] def listedSide : CNF V :=
  (List.finRange m).flatMap fun i => (binary (R i)).relabel (scope i)

omit [Fintype V] [LinearOrder V] in
private theorem listedSide_eval (x : V → Bool) :
    (listedSide w scope R).eval x = (tableSide w scope R).eval x := by
  apply Bool.eq_iff_iff.mpr
  simp [listedSide, tableSide, CNF.eval_flatMap_eq_true_iff]

/-- All locally derived equations are numbered by their position in an explicit
list. Equal tables remain separate; no choice of an abstract finite equivalence
is needed to make original rows available to elimination. -/
@[expose] def listedScopes (t : Fin (equationList w R).length) : Finset V :=
  tableScope w scope R ((equationList w R).get t)

/-- Finite scope lookup preserves each equation's local signs in global columns. -/
@[expose] def listedPolarity (t : Fin (equationList w R).length) : V → Bool :=
  tablePolarity w scope R ((equationList w R).get t)

/-- Compile the actual input tables and execute every preprocessing branch. -/
@[expose] def tablePlan : ExactOne.CountPlan V :=
  let equations := equationList w R
  let scopes := Cslib.Function.tabulate fun t : Fin equations.length =>
    tableScope w scope R (equations.get t)
  let signs := Cslib.Function.tabulate fun t : Fin equations.length =>
    Cslib.Function.tabulate (tablePolarity w scope R (equations.get t))
  ExactOne.preprocess (listedSide w scope R) scopes signs

omit [Fintype V] in
private theorem listed_iff (hR : ∀ i, DimensionOne (R i)) (x : V → Bool) :
    (listedSide w scope R).eval x = true ∧
      (∀ t, ExactOne.Holds (listedScopes w scope R t) (listedPolarity w scope R t) x) ↔
    Satisfies w scope R x := by
  rw [listedSide_eval, tables_iff w scope R hR]
  apply and_congr_right
  intro _
  constructor
  · intro h j
    obtain ⟨t, ht⟩ := List.get_of_mem (mem_equationList w R j)
    simpa only [listedScopes, listedPolarity, ht] using h t
  · intro h t
    exact h ((equationList w R).get t)

open scoped Classical in
/-- Exact global counting, derived from the tables with no supplied rank,
selected rows, candidates or queries. Unused declared bits retain multiplicity. -/
theorem tablePlan_correct (hR : ∀ i, DimensionOne (R i)) :
    (tablePlan w scope R).value = Fintype.card {x : V → Bool // Satisfies w scope R x} := by
  classical
  simp only [tablePlan, Cslib.Function.tabulate_eq, ExactOne.preprocess_correct]
  unfold ExactOne.sourceCount
  simp only [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight (listed_iff w scope R hR))

/-- Every actual emitted query has at most `2r-2` declared variables, width three
and at most `13r²` clauses, irrespective of overlap or the number of tables. -/
theorem tablePlan_budget : (tablePlan w scope R).Budget (Fintype.card V) := by
  apply ExactOne.preprocess_budget
  intro c hc
  obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simpa only [Clause.relabel, List.length_map] using binary_width (R i) d hd

end Cslib.Logic.PL.VCOne
