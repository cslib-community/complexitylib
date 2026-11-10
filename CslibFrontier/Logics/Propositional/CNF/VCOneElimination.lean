/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.VCOneTables
public import CslibFrontier.Logics.Propositional.CNF.ExactOneBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum

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
* `payloadRows`, `payloadRhs`, `payloadConsistent`: binary equation execution.

## Main results

* `tablePlan_correct`: original table solutions have exactly the plan's value.
* `tablePlan_budget`: every emitted query meets the global syntax budgets.
* `payloadConsistent_polytime`: signed materialization composed with binary recovery.
* `payloadConsistent_equationPayload`: correspondence with actual table equations.
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

/-- Materialize the common global columns from literal payloads. Both signs
are tested explicitly; canonical equation rows contain each column at most once. -/
@[expose] def payloadRows (r : ℕ) (es : List (List (ℕ × Bool))) : List (List ℤ) :=
  es.map fun e => (List.range r).map fun c =>
    if e.any (fun l => l.1 == c && l.2) then (1 : ℤ)
    else if e.any (fun l => l.1 == c && !l.2) then -1 else 0

/-- Move the constant of every negative literal to the right-hand side. -/
@[expose] def payloadRhs (es : List (List (ℕ × Bool))) : List ℤ :=
  es.map fun e => 1 - (e.map fun l => if l.2 then (0 : ℤ) else 1).sum

/-- Actual binary execution of signed matrix materialization, including all
zero columns. Width is unary and literal column numbers are binary. -/
@[fun_prop] theorem payloadRows_polytime :
    ComputableInPolyTime (fun p : ℕ × List (List (ℕ × Bool)) => payloadRows p.1 p.2)
      (encPair encUnary encSignedCNF) (encList (encList encIntBin)) := by
  unfold payloadRows encSignedCNF
  apply ComputableInPolyTime.mapWithInput (by fun_prop)
  apply ComputableInPolyTime.mapWithInput (by fun_prop)
  fun_prop

/-- Binary right-hand-side materialization includes scanning negative literals. -/
@[fun_prop] theorem payloadRhs_polytime :
    ComputableInPolyTime payloadRhs encSignedCNF (encList encIntBin) := by
  unfold payloadRhs encSignedCNF
  fun_prop

/-- Canonical scoped rows have exactly the coefficients used by the existing
signed-system backend. This includes negative signs and absent global columns. -/
theorem payloadRows_scoped {r : ℕ} (S : Finset (Fin r)) (p : Fin r → Bool) :
    payloadRows r [((S.sort (· ≤ ·)).map fun v => (v.val, p v))] =
      [List.ofFn fun v : Fin r =>
        if v ∈ S then if p v then (1 : ℤ) else -1 else 0] := by
  simp only [payloadRows, List.map_singleton]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map, List.length_range] at hi
    have hm (b : Bool) :
        (((S.sort (· ≤ ·)).map fun v => (v.val, p v)).any
          (fun l => l.1 == i && (l.2 == b))) = true ↔
        (⟨i, hi⟩ : Fin r) ∈ S ∧ p ⟨i, hi⟩ = b := by
      simp only [List.any_eq_true, List.mem_map, Finset.mem_sort, Bool.and_eq_true,
        beq_iff_eq]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, he, hp⟩
        have : v = ⟨i, hi⟩ := Fin.ext he
        subst v
        exact ⟨hv, hp⟩
      · rintro ⟨hv, hp⟩
        exact ⟨(i, p ⟨i, hi⟩), ⟨⟨i, hi⟩, hv, rfl⟩, rfl, hp⟩
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have ht := hm true
    have hf := hm false
    simp only [Bool.beq_comm, Bool.true_beq, Bool.false_beq] at ht hf
    by_cases hs : (⟨i, hi⟩ : Fin r) ∈ S <;> cases hp : p ⟨i, hi⟩ <;>
      simp_all <;> grind

/-- Negative literal constants agree with the signed backend's exact RHS. -/
theorem payloadRhs_scoped {r : ℕ} (S : Finset (Fin r)) (p : Fin r → Bool) :
    payloadRhs [((S.sort (· ≤ ·)).map fun v => (v.val, p v))] =
      [1 - ((S.filter fun v => p v = false).card : ℤ)] := by
  simp only [payloadRhs, List.map_singleton, List.map_map]
  change [1 - ((S.sort (· ≤ ·)).map (fun v => if p v then (0 : ℤ) else 1)).sum] = _
  change [1 - (Multiset.map (fun v => if p v then (0 : ℤ) else 1)
    (↑(S.sort (· ≤ ·)) : Multiset (Fin r))).sum] = _
  rw [Finset.sort_eq]
  change [1 - ∑ v ∈ S, (if p v then (0 : ℤ) else 1)] = _
  congr 2
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro v _
  cases p v <;> rfl

/-- Materialization of canonical scoped equations is exactly the existing
integer backend, rather than an independently supplied matrix. -/
theorem payload_materialization {r q : ℕ} (S : Fin q → Finset (Fin r))
    (p : Fin q → Fin r → Bool) :
    let es := List.ofFn fun i => ((S i).sort (· ≤ ·)).map fun v => (v.val, p i v)
    payloadRows r es = ExactOne.integerRows S p ∧
      payloadRhs es = ExactOne.integerRhs S p := by
  constructor
  · simp only [payloadRows, List.map_ofFn, ExactOne.integerRows]
    congr 1
    funext i
    have h := payloadRows_scoped (S i) (p i)
    simpa only [payloadRows, List.map_singleton, List.singleton_inj, Function.comp_apply] using h
  · simp only [payloadRhs, List.map_ofFn, ExactOne.integerRhs]
    congr 1
    funext i
    have h := payloadRhs_scoped (S i) (p i)
    simpa only [payloadRhs, List.map_singleton, List.singleton_inj, Function.comp_apply] using h

/-- Execute matrix construction and rectangular consistency on framed equations.
This stage accepts no basis, candidate or resource advice. -/
@[expose] def payloadConsistent (r : ℕ) (es : List (List (ℕ × Bool))) : Bool :=
  Cslib.LinearSystem.rectangularConsistent r (payloadRows r es) (payloadRhs es)

/-- Uniform polynomial binary time for the composed equation-to-solver stage.
The table-to-equation and solver-to-query stages remain separate obligations. -/
theorem payloadConsistent_polytime :
    ComputableInPolyTime (fun p : ℕ × List (List (ℕ × Bool)) =>
      payloadConsistent p.1 p.2) (encPair encUnary encSignedCNF) encBool := by
  unfold payloadConsistent
  have hn : ComputableInPolyTime (fun p : ℕ × List (List (ℕ × Bool)) => p.1)
      (encPair encUnary encSignedCNF) encUnary := by fun_prop
  exact Cslib.LinearSystem.rectangularConsistent_polytime.comp
    ((hn.prod payloadRows_polytime).prod
      (payloadRhs_polytime.comp (by fun_prop)))

/-- The framed equation compiler tests the original signed equations exactly,
for arbitrary overlapping scopes and without a consistency premise. -/
theorem payloadConsistent_scoped {r q : ℕ} (S : Fin q → Finset (Fin r))
    (p : Fin q → Fin r → Bool) :
    payloadConsistent r (List.ofFn fun i =>
      ((S i).sort (· ≤ ·)).map fun v => (v.val, p i v)) = true ↔
      ∃ z : Fin r → ℚ, ∀ i,
        dotProduct (ExactOne.coefficients (S i) (p i)) z = ExactOne.rhs (S i) (p i) := by
  obtain ⟨hA, hb⟩ := payload_materialization S p
  unfold payloadConsistent
  rw [hA, hb]
  exact ExactOne.binaryConsistent_iff S p

/-- The actual table equation payload agrees with the framed scoped input of
the binary compiler, preserving each equation position. -/
theorem equationPayload_scoped {r : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) :
    equationPayload w scope R = List.ofFn fun t =>
      ((listedScopes w scope R t).sort (· ≤ ·)).map fun v =>
        (v.val, listedPolarity w scope R t v) := by
  simp only [equationPayload, listedScopes, listedPolarity]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Execute binary consistency on the actual table equations. Only the
construction of those equations, not this composed stage, lacks a time proof. -/
theorem payloadConsistent_equationPayload {r : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) :
    payloadConsistent r (equationPayload w scope R) = true ↔
      ∃ z : Fin r → ℚ, ∀ t,
        dotProduct (ExactOne.coefficients (listedScopes w scope R t)
          (listedPolarity w scope R t)) z =
        ExactOne.rhs (listedScopes w scope R t) (listedPolarity w scope R t) := by
  rw [equationPayload_scoped]
  exact payloadConsistent_scoped _ _

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
