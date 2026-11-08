/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Table.DeltaMatroid
public import Complexity.Logics.Propositional.CSP.Table.ParityChain
public import Complexity.Logics.Propositional.CSP.Occurrence
public import Complexity.Foundations.Data.BitString.CyclicDifference
public import Complexity.Foundations.Data.BitString.Enumeration

/-!
# Fixed-language cyclic-difference tables

Tables enumerate the accepted tuples at the declared arity and take ordered neighboring
exclusive ors, including last-to-first. This is the `dR` operation of [DvorakKupec2015],
Section 3, printed p. 439, and [KazdaKolmogorovRolinek2018], Definition 14 (v6, printed p. 0:6).
Empty and nullary relations retain their exact meaning. Enumeration costs may be exponential
in the arity; native compilation uses this only as a fixed finite language lookup. No uniform
language-preprocessing claim is made.

The fixed rejection instance has two singleton unary tables on one variable. Each relation
is a nonempty even delta-matroid, although their conjunction is unsatisfiable.

## Main definitions

* `Cslib.Logic.PL.CSP.Table.differenceTable`: explicit ordered difference table.
* `Cslib.Logic.PL.CSP.Table.rejectEdge`: fixed unsatisfiable edge instance.
-/

public section

namespace Cslib.Logic.PL.CSP.Table

open Cslib.BitString

variable {Rel : Type}

/-- Explicit accepted cyclic differences in the original scope order. Enumeration is static
for each symbol of a fixed finite language, independently of raw instance scope lengths. -/
@[expose] def differenceTable (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (r : Rel) : Table :=
  ⟨arity r, ((enum (arity r)).filter fun x => sem r (List.ofFn x)).map
    fun x => List.ofFn (cyclicDifference x)⟩

@[simp] theorem arity_differenceTable (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) (r : Rel) :
    (differenceTable arity sem r).arity = arity r := rfl

/-- Stored rows have the exact original declared width. -/
theorem wellFormed_differenceTable (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) (r : Rel) :
    (differenceTable arity sem r).wellFormed = true := by
  apply wellFormed_eq_true.mpr
  intro row hrow
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hrow
  exact List.length_ofFn

/-- The actual guarded table denotes precisely the existing ordered difference relation. -/
theorem booleanRelation_differenceTable (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) (r : Rel) :
    booleanRelation Table.arity Table.sem (differenceTable arity sem r) =
      cyclicDifferenceRelation (booleanRelation arity sem r) := by
  ext x
  change (differenceTable arity sem r).sem (List.ofFn x) = true ↔ _
  rw [sem_eq_true]
  simp only [wellFormed_differenceTable, true_and]
  change List.ofFn x ∈ ((enum (arity r)).filter _).map _ ↔ _
  simp only [List.mem_map,
    List.mem_filter, mem_enum, true_and]
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, List.ofFn_injective he⟩
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, congrArg List.ofFn he⟩

/-- Accepted rows are exactly the ordered differences of accepted source tuples. -/
theorem sem_differenceTable (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (r : Rel) (row : List Bool) :
    (differenceTable arity sem r).sem row = true ↔
      ∃ x : Fin (arity r) → Bool, sem r (List.ofFn x) = true ∧
        List.ofFn (cyclicDifference x) = row := by
  rw [sem_eq_true]
  simp only [wellFormed_differenceTable, true_and]
  change row ∈ ((enum (arity r)).filter _).map _ ↔ _
  simp only [List.mem_map, List.mem_filter, mem_enum, true_and]

/-- Every accepted difference row has even parity, including the nullary row. -/
theorem parity_differenceTable (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (r : Rel) (row : List Bool) (hrow : (differenceTable arity sem r).sem row = true) :
    wordParity row = false := by
  obtain ⟨x, _, rfl⟩ := (sem_differenceTable arity sem r row).mp hrow
  rw [wordParity_ofFn]
  exact parityOn_cyclicDifference x

/-- Self-complementary recovery through the actual explicit table, at any matching arity. -/
theorem sem_differenceTable_cyclicDifference (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) (r : Rel)
    (hself : IsSelfComplementary (booleanRelation arity sem r))
    {n : ℕ} (hwidth : n = arity r) (x : Fin n → Bool) :
    (differenceTable arity sem r).sem (List.ofFn (cyclicDifference x)) = true ↔
      sem r (List.ofFn x) = true := by
  subst n
  change cyclicDifference x ∈ booleanRelation Table.arity Table.sem
    (differenceTable arity sem r) ↔ x ∈ booleanRelation arity sem r
  rw [booleanRelation_differenceTable]
  exact mem_cyclicDifferenceRelation_iff hself x

/-- Static language evenness transfers to the actual explicit table. Empty relations are
excluded by this hypothesis, rather than silently treated as nonempty delta-matroids. -/
theorem isEvenDeltaMatroid_differenceTable (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) (r : Rel)
    (h : IsEvenDeltaMatroid (cyclicDifferenceRelation (booleanRelation arity sem r))) :
    IsEvenDeltaMatroid (booleanRelation Table.arity Table.sem (differenceTable arity sem r)) := by
  rwa [booleanRelation_differenceTable]

/-- At most one row per Boolean source tuple; duplicates need not be removed. -/
theorem length_rows_differenceTable_le (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) (r : Rel) :
    (differenceTable arity sem r).rows.length ≤ 2 ^ arity r := by
  simpa only [differenceTable, List.length_map, length_enum] using
    List.length_filter_le (fun x => sem r (List.ofFn x)) (enum (arity r))

/-- Unary singleton table, allowing either common parity. -/
@[expose] def pinTable (b : Bool) : Table := ⟨1, [[b]]⟩

/-- The unary singleton table pins its sole coordinate. -/
theorem booleanRelation_pinTable (b : Bool) :
    booleanRelation arity sem (pinTable b) = {fun _ : Fin 1 => b} := by
  ext x
  change Fin 1 → Bool at x
  change (pinTable b).sem (List.ofFn x) = true ↔ x = (fun _ : Fin 1 => b)
  have hw : (pinTable b).wellFormed = true := by simp [pinTable]
  rw [sem_eq_true, hw]
  change (true = true ∧ List.ofFn x ∈ [[b]]) ↔ _
  simp only [true_and, List.mem_singleton]
  rw [← show List.ofFn (fun _ : Fin 1 => b) = [b] by simp]
  exact List.ofFn_inj

/-- Singleton unary relations are even delta-matroids, including the odd pin. -/
theorem isEvenDeltaMatroid_pinTable (b : Bool) :
    IsEvenDeltaMatroid (booleanRelation arity sem (pinTable b)) := by
  rw [booleanRelation_pinTable]
  exact isEvenDeltaMatroid_singleton _

/-- Fixed unsatisfiable edge instance with two nonempty singleton unary relations. -/
@[expose] def rejectEdge : CSP Table ℕ := [(pinTable false, [0]), (pinTable true, [0])]

/-- Rejection remains an edge instance: one variable in two distinct unary constraints. -/
theorem edgeInstance_rejectEdge : EdgeInstance rejectEdge := by
  unfold EdgeInstance
  decide

/-- Both rejecting tables have the exact declared width. -/
theorem wellFormed_rejectEdge : WellFormed arity rejectEdge := by decide

/-- Rejection is semantic, not a malformed or empty-relation shortcut. -/
theorem not_satisfiable_rejectEdge : ¬ rejectEdge.Satisfiable sem := by
  rintro ⟨σ, hσ⟩
  cases h : σ 0 <;> simp [rejectEdge, CSP.eval, Constraint.eval, pinTable, sem,
    wellFormed, h] at hσ

/-- Every rejecting constraint uses a nonempty even delta-matroid. -/
theorem rejectEdge_tables (c : Constraint Table ℕ) (hc : c ∈ rejectEdge) :
    IsEvenDeltaMatroid (booleanRelation arity sem c.1) := by
  simp only [rejectEdge, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> exact isEvenDeltaMatroid_pinTable _

end Cslib.Logic.PL.CSP.Table
