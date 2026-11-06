/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.VCOneTables
public import Complexity.Logics.Propositional.CNF.ExactOneBinary
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum

/-!
# Executable counting plans from overlapping VC-one tables

`tablePlan` constructs local separators using the existing closure listing, assigns
finite row indices, executes materialized rational elimination in shared global
columns and emits a direct answer or two ordinary 3-CNFs. Scopes may overlap
arbitrarily. There is no enumeration of all local tuples or global assignments,
except for the explicitly guarded branch with at most one global variable.

`tablePlan_correct` and `tablePlan_budget` supply functional correctness and syntax
budgets for [ChenJiangZhu2027], Theorem 6.3, PDF pp. 20–21. Polynomial coefficient
growth and encoded bit-time execution of this rational path remain unproved.
`binaryTablePlan` supplies an alternative using the binary-certified rectangular
backend, with exact count and syntax budgets but no whole-pipeline bit-time
certificate. Neither path is the complete
algorithmic resource theorem.

## Main definitions

* `equationList`: finite numbering of the actually listed missing closure tuples.
* `tablePlan`: executable global table-to-counting-plan compilation.
* `tablePayload`, `equationPayload`: explicit table and signed-equation data.
* `encTablePayload`, `encPlanPayload`: framed bit encodings with unary declarations.
* `binaryTableBits`: serialize the actual binary-backend plan.

## Main results

* `tablePlan_correct`: original table solutions have exactly the plan's value.
* `tablePlan_budget`: every emitted query meets the global syntax budgets.
* `frontier_coordinates_le`, `prefix_comparison_coordinates_le`: promise-restricted
  coordinate volume bounds, without a whole-machine execution claim.

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

/-- Table-to-query assembly using integer rectangular row selection in the
shared declared columns. All closure equations are still constructed locally. -/
@[expose] def binaryTablePlan {r : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) : ExactOne.CountPlan (Fin r) :=
  ExactOne.binaryPreprocess (listedScopes w scope R) (listedPolarity w scope R)
    (listedSide w scope R)

open scoped Classical in
/-- Exact global counting after binary original-row selection, including unused
bits and arbitrarily overlapping scopes. -/
theorem binaryTablePlan_correct {r : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) (hR : ∀ i, DimensionOne (R i)) :
    (binaryTablePlan w scope R).value =
      Fintype.card {x : Fin r → Bool // Satisfies w scope R x} := by
  rw [binaryTablePlan, ExactOne.binaryPreprocess_correct]
  unfold ExactOne.sourceCount
  simp only [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight (listed_iff w scope R hR))

/-- The binary table compiler emits at most two 3-CNFs within the global budget. -/
theorem binaryTablePlan_budget {r : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) :
    (binaryTablePlan w scope R).Budget r := by
  apply ExactOne.binaryPreprocess_budget
  intro c hc
  obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simpa only [Clause.relabel, List.length_map] using binary_width (R i) d hd

/-- Explicit table payload: width, listed Boolean rows, and global column numbers.
Rows are sorted lexicographically; no Boolean cube is enumerated. Width is retained
also for an empty table, and the global declaration count is stored separately. -/
@[expose] def tablePayload {r : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) :
    ℕ × List (ℕ × List (List Bool) × List ℕ) :=
  (r, (List.finRange m).map fun i =>
    (w i, ((R i).image List.ofFn).sort (· ≤ ·),
      (List.finRange (w i)).map fun j => (scope i j).val))

/-- Signed equation payload constructed from the actual equation list. Each pair
stores the original global column and its literal polarity. Equation order and
table multiplicity are preserved. -/
@[expose] def equationPayload {r : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) : List (List (ℕ × Bool)) :=
  (equationList w R).map fun j =>
    ((tableScope w scope R j).sort (· ≤ ·)).map fun v =>
      (v.val, tablePolarity w scope R j v)

/-- Erase bounded column types in an actual counting plan. The tag distinguishes
an immediate answer from two queries. Query declarations include unused bits;
auxiliary column `j` is numbered `r + j`. -/
@[expose] def planPayload {r : ℕ} : ExactOne.CountPlan (Fin r) →
    ℕ ⊕ (ℕ × CNF ℕ × CNF ℕ)
  | .direct n => .inl n
  | .queries k zero one => .inr (r + k,
      zero.relabel (Sum.elim Fin.val (fun j => r + j.val)),
      one.relabel (Sum.elim Fin.val (fun j => r + j.val)))

/-- Actual table compiler followed by explicit output materialization. This is a
functional constructor, not yet a binary-machine resource certificate. -/
@[expose] def binaryTablePayload {r : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) :=
  planPayload (binaryTablePlan w scope R)

open Turing.MultiTapeTM

/-- Framed input encoding. Declarations and widths are unary to charge storage
for declared but unused coordinates; column numbers are binary and Boolean rows
are literal bit strings. Nested lists and products use the library framing. -/
@[expose] def encTablePayload :
    (ℕ × List (ℕ × List (List Bool) × List ℕ)) ↪ List Bool :=
  encPair encUnary (encList (encPair encUnary
    (encPair (encList encBits) (encList encNat))))

/-- Binary signed literals, framed clauses and framed CNFs. -/
@[expose] def encSignedCNF : CNF ℕ ↪ List Bool :=
  encList (encList (encPair encNat encBool))

/-- Tagged direct/two-query output encoding. A direct answer is binary; query
variable declarations are unary and every literal column is binary. -/
@[expose] def encPlanPayload : (ℕ ⊕ (ℕ × CNF ℕ × CNF ℕ)) ↪ List Bool :=
  encSum encNat (encPair encUnary (encPair encSignedCNF encSignedCNF))

/-- Concrete bit output of the actual table compiler. Encoding is injective on
payloads by construction, but a polynomial machine realizing this composition
is a separate obligation. -/
@[expose] def binaryTableBits {r : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) : List Bool :=
  encPlanPayload (binaryTablePayload w scope R)

/-- Every serialized literal is exactly an entry of the constructed signed
system; no advice or independently supplied equation is accepted. -/
theorem mem_equationPayload_iff {r : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) (e : List (ℕ × Bool)) :
    e ∈ equationPayload w scope R ↔ ∃ j : EquationIndex w R,
      e = ((tableScope w scope R j).sort (· ≤ ·)).map
        (fun v => (v.val, tablePolarity w scope R j v)) := by
  simp only [equationPayload, List.mem_map]
  constructor
  · rintro ⟨j, _, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, mem_equationList w R j, rfl⟩

/-- Stored Boolean coordinates in a frontier, using full width rows. This is a
storage volume bound, not a bound on a particular machine configuration. -/
theorem frontier_coordinates_le {a : ℕ} (R : Finset (Fin a → Bool))
    (hR : DimensionOne R) (todo : List (Fin a)) (hn : todo.Nodup) :
    (prefixes R todo).card * a ≤ (a + 1) * a := by
  have h := prefixes_card R hR todo hn
  simp only [Fintype.card_fin] at h
  exact Nat.mul_le_mul_right a h

/-- Even a linear scan of the entire previous frontier for every attempted
extension compares only polynomially many coordinates on promised inputs.
The factor `a` charges full-width equality; the factor `a+1` charges a frontier
scan. Projection checks, separator deletion and machine overhead are separate. -/
theorem prefix_comparison_coordinates_le {a : ℕ} (R : Finset (Fin a → Bool))
    (hR : DimensionOne R) :
    prefixCandidates R (List.finRange a) * (a + 1) * a ≤
      2 * a * (a + 1) * (a + 1) * a := by
  have h := prefixCandidates_le R hR (List.finRange a) (List.nodup_finRange a)
  simp only [List.length_finRange, Fintype.card_fin] at h
  exact Nat.mul_le_mul_right a (Nat.mul_le_mul_right (a + 1) h)

end Cslib.Logic.PL.VCOne
