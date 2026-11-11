/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP
import Mathlib.Data.List.Count
import Mathlib.Data.List.Nodup

/-!
# Explicit Boolean relation tables

`CSP.Table` is a relation alphabet for the existing `CSP`, not a second instance format.
Rows are lists, including duplicates; the arity and width guard distinguish the empty nullary
relation from the nullary relation containing the empty row. Malformed tables reject all rows.

The local update `Table.contract` implements [KazdaKolmogorovRolinek2018], arXiv v6,
Section 5.3, printed pp. 12–13: positions are the distinct internal variables in a constraint,
`reference` is its current feasible local row, and the last output bit is the fresh connector.
Outside coordinates retain their original order. Zero internal deviations give connector `false`,
one gives `true`, and more than one discard the row. This module does not prove delta-matroid
preservation, blossom validity, or the correctness of the edge solver. The elementary list
implementation and its proofs are original formalization details.

`Table.exactlyOne` constructs the new connector relation from the length of a supplied scope.
It stores one row per connector, rather than treating all possible active relations as a fixed
finite alphabet. Its semantics agrees with Example 17 and the new constraint in Section 5.3
of the cited paper. In particular, its zero-connector relation is empty.

## Main definitions

* `Cslib.Logic.PL.CSP.Table`: arity and explicit rows.
* `Cslib.Logic.PL.CSP.Table.contract`: guarded local contraction table update.
* `Cslib.Logic.PL.CSP.Table.exactlyOne`: explicit exactly-one connector table.
-/

public section

namespace Cslib.Logic.PL.CSP

/-- An explicit Boolean relation, with an arity even when its row list is empty.
Duplicate rows are permitted. Use this as `Rel` in the existing `CSP Rel V`. -/
structure Table where
  /-- The number of coordinates. -/
  arity : ℕ
  /-- Accepted rows; the guard checks their widths. -/
  rows : List (List Bool)
  deriving DecidableEq, Repr

namespace Table

/-- Every stored row has the declared width. Empty tables are well formed at every arity. -/
@[expose] def wellFormed (table : Table) : Bool :=
  table.rows.all fun row => decide (row.length = table.arity)

/-- Membership semantics for the existing CSP evaluator. Malformed tables reject everything. -/
@[expose] def sem (table : Table) (row : List Bool) : Bool :=
  table.wellFormed && decide (row.length = table.arity) && table.rows.contains row

/-- The width guard characterizes well-formedness. -/
@[simp] theorem wellFormed_eq_true {table : Table} :
    table.wellFormed = true ↔ ∀ row ∈ table.rows, row.length = table.arity := by
  simp [wellFormed]

/-- The executable semantics is precisely guarded row membership. -/
@[simp] theorem sem_eq_true {table : Table} {row : List Bool} :
    table.sem row = true ↔ table.wellFormed = true ∧ row ∈ table.rows := by
  simp only [sem, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem]
  constructor
  · rintro ⟨⟨hw, _⟩, hr⟩
    exact ⟨hw, hr⟩
  · rintro ⟨hw, hr⟩
    exact ⟨⟨hw, wellFormed_eq_true.mp hw row hr⟩, hr⟩

/-- Guard for distinct, in-range coordinate positions. Counting does not deduplicate the input. -/
@[expose] def validPositions (width : ℕ) (positions : List ℕ) : Bool :=
  positions.all fun i => decide (i < width) && decide (positions.count i = 1)

/-- The position guard requires both distinctness and range, including for an empty selection. -/
theorem validPositions_eq_true {width : ℕ} {positions : List ℕ} :
    validPositions width positions = true ↔
      positions.Nodup ∧ ∀ i ∈ positions, i < width := by
  simp only [validPositions, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨List.nodup_iff_count_eq_one.mpr (fun i hi => (h i hi).2),
      fun i hi => (h i hi).1⟩
  · rintro ⟨hd, hr⟩ i hi
    exact ⟨hr i hi, List.count_eq_one_of_mem hd hi⟩

/-- Outside coordinates in increasing original order. -/
@[expose] def outsidePositions (width : ℕ) (positions : List ℕ) : List ℕ :=
  (List.range width).filter fun i => !positions.contains i

/-- Outside positions are a sublist of the original coordinate order. -/
theorem outsidePositions_sublist (width : ℕ) (positions : List ℕ) :
    List.Sublist (outsidePositions width positions) (List.range width) := List.filter_sublist

/-- Selecting outside positions never increases width, even for malformed selections. -/
theorem length_outsidePositions_le (width : ℕ) (positions : List ℕ) :
    (outsidePositions width positions).length ≤ width := by
  simpa only [List.length_range] using (outsidePositions_sublist width positions).length_le

/-- Distinct in-range positions and the outside positions partition the original width. -/
theorem length_outsidePositions_add {width : ℕ} {positions : List ℕ}
    (h : validPositions width positions = true) :
    (outsidePositions width positions).length + positions.length = width := by
  obtain ⟨hd, hr⟩ := validPositions_eq_true.mp h
  have hs : positions.toFinset ⊆ Finset.range width := by
    intro i hi
    exact Finset.mem_range.mpr (hr i (List.mem_toFinset.mp hi))
  have heq : (outsidePositions width positions).toFinset =
      Finset.range width \ positions.toFinset := by
    ext i
    simp [outsidePositions]
  have hc := Finset.card_sdiff_add_card_eq_card hs
  have ho : (outsidePositions width positions).Nodup := List.nodup_range.filter _
  rw [← heq, List.toFinset_card_of_nodup ho, List.toFinset_card_of_nodup hd,
    Finset.card_range] at hc
  exact hc

/-- Read coordinates, with a total fallback for malformed indices. -/
@[expose] def project (row : List Bool) (positions : List ℕ) : List Bool :=
  positions.map fun i => row.getD i false

/-- Number of selected coordinates differing from the current local row.
Positions must be distinct and in range when interpreted as internal variables. -/
@[expose] def deviations (reference row : List Bool) (positions : List ℕ) : ℕ :=
  positions.countP fun i => row.getD i false != reference.getD i false

/-- Preconditions for a local contraction: a feasible reference row and valid internal positions. -/
@[expose] def canContract (table : Table) (reference : List Bool) (positions : List ℕ) : Bool :=
  table.sem reference && validPositions reference.length positions

/-- The contraction contract includes feasible-row membership, well-formedness and distinct
in-range internal coordinates; no delta-matroid or blossom property is assumed here. -/
theorem canContract_eq_true {table : Table} {reference : List Bool} {positions : List ℕ} :
    table.canContract reference positions = true ↔
      table.wellFormed = true ∧ reference ∈ table.rows ∧ positions.Nodup ∧
        ∀ i ∈ positions, i < table.arity := by
  simp only [canContract, Bool.and_eq_true, sem_eq_true, validPositions_eq_true]
  constructor
  · rintro ⟨⟨hw, hf⟩, hd, hp⟩
    exact ⟨hw, hf, hd, by rwa [wellFormed_eq_true.mp hw reference hf] at hp⟩
  · rintro ⟨hw, hf, hd, hp⟩
    exact ⟨⟨hw, hf⟩, hd, by rwa [wellFormed_eq_true.mp hw reference hf]⟩

/-- Local contraction. Malformed data gives the empty nullary table. The implementation only
ranges over the explicit reference row, never over an unchecked binary arity. -/
@[expose] def contract (table : Table) (reference : List Bool) (positions : List ℕ) : Table :=
  if canContract table reference positions then
    { arity := (outsidePositions reference.length positions).length + 1
      rows := (table.rows.filter fun row => decide (deviations reference row positions ≤ 1)).map
        fun row => project row (outsidePositions reference.length positions) ++
          [decide (deviations reference row positions = 1)] }
  else { arity := 0, rows := [] }

/-- Invalid tables, references or position lists have a total rejecting output. -/
theorem contract_of_not_canContract {table : Table} {reference : List Bool} {positions : List ℕ}
    (h : table.canContract reference positions = false) :
    contract table reference positions = ⟨0, []⟩ := by
  simp [contract, h]

/-- Contraction preserves row multiplicity and cannot increase the number of rows. -/
theorem length_rows_contract_le (table : Table) (reference : List Bool) (positions : List ℕ) :
    (contract table reference positions).rows.length ≤ table.rows.length := by
  unfold contract
  split
  · simpa only [List.length_map] using List.length_filter_le
      (fun row => decide (deviations reference row positions ≤ 1)) table.rows
  · simp

/-- A guarded contraction has exactly the outside width plus one connector coordinate. -/
theorem arity_contract {table : Table} {reference : List Bool} {positions : List ℕ}
    (h : canContract table reference positions = true) :
    (contract table reference positions).arity =
      (outsidePositions reference.length positions).length + 1 := by
  simp [contract, h]

/-- The actual blossom hypothesis of at least two internal coordinates strictly decreases
local width. Feasibility alone is insufficient for this conclusion. -/
theorem arity_contract_lt {table : Table} {reference : List Bool} {positions : List ℕ}
    (h : canContract table reference positions = true) (htwo : 2 ≤ positions.length) :
    (contract table reference positions).arity < table.arity := by
  have hg : table.sem reference = true ∧ validPositions reference.length positions = true := by
    simpa only [canContract, Bool.and_eq_true] using h
  have hf := sem_eq_true.mp hg.1
  have hw := wellFormed_eq_true.mp hf.1 reference hf.2
  have hp := length_outsidePositions_add hg.2
  rw [arity_contract h]
  omega

/-- Every output row has the new declared width, including on malformed inputs. -/
@[simp] theorem wellFormed_contract (table : Table) (reference : List Bool) (positions : List ℕ) :
    (contract table reference positions).wellFormed = true := by
  unfold contract
  split
  · simp [wellFormed, project]
  · simp [wellFormed]

/-- Exact contraction membership, with the output connector computed from zero or one internal
changes. The original row is retained as a witness for later lifting. -/
theorem sem_contract_eq_true {table : Table} {reference row : List Bool} {positions : List ℕ}
    (h : canContract table reference positions = true) :
    (contract table reference positions).sem row = true ↔
      ∃ old ∈ table.rows, deviations reference old positions ≤ 1 ∧
        project old (outsidePositions reference.length positions) ++
          [decide (deviations reference old positions = 1)] = row := by
  rw [sem_eq_true]
  simp only [wellFormed_contract, true_and]
  simp [contract, h, and_assoc]

/-- The paper's two cases, stated without a numeric-to-Boolean connector conversion. -/
theorem sem_contract_cases {table : Table} {reference row : List Bool} {positions : List ℕ}
    (h : canContract table reference positions = true) :
    (contract table reference positions).sem row = true ↔
      ∃ old ∈ table.rows,
        (deviations reference old positions = 0 ∧
          project old (outsidePositions reference.length positions) ++ [false] = row) ∨
        (deviations reference old positions = 1 ∧
          project old (outsidePositions reference.length positions) ++ [true] = row) := by
  rw [sem_contract_eq_true h]
  constructor
  · rintro ⟨old, ho, hd, hr⟩
    have hc : deviations reference old positions = 0 ∨ deviations reference old positions = 1 := by
      omega
    rcases hc with hc | hc
    · exact ⟨old, ho, Or.inl ⟨hc, by simpa [hc] using hr⟩⟩
    · exact ⟨old, ho, Or.inr ⟨hc, by simpa only [hc, decide_true] using hr⟩⟩
  · rintro ⟨old, ho, ⟨hd, hr⟩ | ⟨hd, hr⟩⟩
    · exact ⟨old, ho, by omega, by simpa [hd] using hr⟩
    · exact ⟨old, ho, by omega, by simpa only [hd, decide_true] using hr⟩

/-- The feasible reference has no internal deviations. -/
@[simp] theorem deviations_self (reference : List Bool) (positions : List ℕ) :
    deviations reference reference positions = 0 := by
  simp [deviations]

/-- A guarded contraction retains the current feasible row, with its connector set to zero. -/
theorem sem_contract_reference {table : Table} {reference : List Bool} {positions : List ℕ}
    (h : canContract table reference positions = true) :
    (contract table reference positions).sem
      (project reference (outsidePositions reference.length positions) ++ [false]) = true := by
  apply (sem_contract_eq_true h).mpr
  have hg : table.sem reference = true ∧ validPositions reference.length positions = true := by
    simpa only [canContract, Bool.and_eq_true] using h
  exact ⟨reference, (sem_eq_true.mp hg.1).2, by simp, by simp⟩

/-- One-hot rows, indexed by a position strictly below the width. -/
@[expose] def oneHot (width index : ℕ) : List Bool :=
  (List.range width).map fun j => decide (index = j)

/-- A one-hot row at position zero starts with `true`. -/
theorem oneHot_succ_zero (width : ℕ) :
    oneHot (width + 1) 0 = true :: List.replicate width false := by
  simp [oneHot, List.range_succ_eq_map, List.map_map, Function.comp_def]

/-- Shifting the selected position prepends a zero. -/
theorem oneHot_succ_succ (width index : ℕ) :
    oneHot (width + 1) (index + 1) = false :: oneHot width index := by
  simp [oneHot, List.range_succ_eq_map, List.map_map, Function.comp_def]

/-- A valid one-hot row has precisely one true coordinate. -/
theorem count_true_oneHot {width index : ℕ} (h : index < width) :
    (oneHot width index).count true = 1 := by
  induction width generalizing index with
  | zero => omega
  | succ width ih =>
    cases index with
    | zero => simp [oneHot_succ_zero, List.count_replicate]
    | succ index => simpa [oneHot_succ_succ] using ih (by omega)

/-- Every row with exactly one true coordinate is a one-hot row. -/
theorem exists_oneHot_of_count_true {row : List Bool} (h : row.count true = 1) :
    ∃ index < row.length, oneHot row.length index = row := by
  induction row with
  | nil => simp at h
  | cons bit row ih =>
    cases bit with
    | false =>
      have ht : row.count true = 1 := by simpa using h
      obtain ⟨index, hi, hr⟩ := ih ht
      exact ⟨index + 1, by simpa using Nat.succ_lt_succ hi,
        by simpa only [List.length_cons, oneHot_succ_succ] using congrArg (false :: ·) hr⟩
    | true =>
      have ht : true ∉ row := List.count_eq_zero.mp (by simpa using h)
      have hr : row = List.replicate row.length false := List.eq_replicate_of_mem
        (fun bit hb => by cases bit <;> simp_all)
      exact ⟨0, by simp, by simp only [List.length_cons, oneHot_succ_zero, ← hr]⟩

/-- Explicit exactly-one table. The scope's length supplies the output-size resource;
its entries need not be distinct, since this constructs only a relation, not a CSP scope guard. -/
@[expose] def exactlyOne {V : Type*} (scope : List V) : Table :=
  { arity := scope.length
    rows := (List.range scope.length).map (oneHot scope.length) }

/-- Exactly-one stores one row per connector. -/
@[simp] theorem length_rows_exactlyOne {V : Type*} (scope : List V) :
    (exactlyOne scope).rows.length = scope.length := by
  simp [exactlyOne]

/-- Exactly-one tables have the declared width. -/
@[simp] theorem wellFormed_exactlyOne {V : Type*} (scope : List V) :
    (exactlyOne scope).wellFormed = true := by
  simp [wellFormed, exactlyOne, oneHot]

/-- Exactly-one semantics, independently of row ordering and the names in the supplied scope. -/
theorem sem_exactlyOne_eq_true {V : Type*} (scope : List V) (row : List Bool) :
    (exactlyOne scope).sem row = true ↔ row.length = scope.length ∧ row.count true = 1 := by
  rw [sem_eq_true]
  simp only [wellFormed_exactlyOne, true_and]
  constructor
  · intro h
    obtain ⟨index, hi, rfl⟩ := List.mem_map.mp h
    exact ⟨by simp [oneHot], count_true_oneHot (List.mem_range.mp hi)⟩
  · rintro ⟨hw, hc⟩
    obtain ⟨index, hi, hr⟩ := exists_oneHot_of_count_true hc
    exact List.mem_map.mpr ⟨index, List.mem_range.mpr (hw ▸ hi), hw ▸ hr⟩

/-- The connector relation is nonempty precisely when there is a connector. -/
theorem rows_exactlyOne_ne_nil {V : Type*} (scope : List V) :
    (exactlyOne scope).rows ≠ [] ↔ 0 < scope.length := by
  rw [← List.length_pos_iff, length_rows_exactlyOne]

/-- Exactly-one admits a satisfying row precisely when the scope supplies a connector. -/
theorem exists_sem_exactlyOne {V : Type*} (scope : List V) :
    (∃ row, (exactlyOne scope).sem row = true) ↔ 0 < scope.length := by
  constructor
  · rintro ⟨row, hr⟩
    apply (rows_exactlyOne_ne_nil scope).mp
    exact List.ne_nil_of_mem (sem_eq_true.mp hr).2
  · intro h
    refine ⟨oneHot scope.length 0, sem_eq_true.mpr ⟨wellFormed_exactlyOne scope, ?_⟩⟩
    exact List.mem_map.mpr ⟨0, List.mem_range.mpr h, rfl⟩

end Table
end Cslib.Logic.PL.CSP
