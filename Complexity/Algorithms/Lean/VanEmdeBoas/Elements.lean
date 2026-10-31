/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.VanEmdeBoas.Erase
public import Complexity.Algorithms.Lean.VanEmdeBoas.Insert
public import Complexity.Algorithms.Lean.VanEmdeBoas.Predecessor
public import Complexity.Algorithms.Lean.VanEmdeBoas.Successor
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Range

/-!
# Finite-set abstraction of recursive van Emde Boas trees

The finite set below is a mathematical observation of the recursive representation. The
operations do not enumerate this finite set. No execution-time bound is attached to constructing
the observation.

## Main definitions

* `Tree.elements`: the bounded keys represented by a tree.

## Main results

* `Tree.mem_elements_iff`: the finite set agrees with the recursive mathematical interpretation.
* `Tree.elements_insert`, `Tree.elements_erase`: insertion and deletion commute with the
  finite-set observation.
* `Tree.successor_elements_some_iff`, `Tree.successor_elements_none_iff`: strict successor and
  its absence are characterized by the finite set.
* `Tree.predecessor_elements_some_iff`, `Tree.predecessor_elements_none_iff`: strict predecessor
  and its absence are characterized by the finite set.

## References

The representation and its source credit are described in
`Complexity.Algorithms.Lean.VanEmdeBoas.Basic`.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.VanEmdeBoas.Tree

variable {d : ℕ}

/-- Mathematical finite-set abstraction; this enumeration is not used by the operations. -/
def elements (t : Tree d) : Finset ℕ :=
  (Finset.range (universeSize d)).filter fun x => t.member x

/-- The finite observation includes exactly the recursively represented keys. -/
theorem mem_elements_iff {t : Tree d} (ht : t.Valid) (x : ℕ) :
    x ∈ t.elements ↔ t.Contains x := by
  simp only [elements, Finset.mem_filter, Finset.mem_range, member_iff_contains ht]
  exact ⟨And.right, fun hx => ⟨ht.contains_lt hx, hx⟩⟩

/-- The empty van Emde Boas tree represents the empty finite set of keys. -/
@[simp] theorem elements_empty (d : ℕ) : (empty d).elements = ∅ := by
  ext x
  simp only [mem_elements_iff (valid_empty d), contains_empty, Finset.notMem_empty]

/-- The finite-set observation commutes with bounded insertion. -/
theorem elements_insert {t : Tree d} (ht : t.Valid) {x : ℕ} (hx : x < universeSize d) :
    (t.insert x).elements = Insert.insert x t.elements := by
  ext y
  rw [mem_elements_iff (valid_insert ht hx), Finset.mem_insert, mem_elements_iff ht]
  exact contains_insert ht hx y

/-- A successful successor is the least finite-set element strictly above the query. -/
theorem successor_elements_some_iff {t : Tree d} (ht : t.Valid) (x y : ℕ) :
    t.successor x = some y ↔ y ∈ t.elements ∧ x < y ∧
      ∀ z, z ∈ t.elements → x < z → y ≤ z := by
  simp only [mem_elements_iff ht]
  exact successor_eq_some_iff ht x y

/-- An absent successor means that every finite-set element is at most the query. -/
theorem successor_elements_none_iff {t : Tree d} (ht : t.Valid) (x : ℕ) :
    t.successor x = none ↔ ∀ z, z ∈ t.elements → z ≤ x := by
  simp only [mem_elements_iff ht]
  exact successor_eq_none_iff ht x

/-- The finite-set observation commutes with deletion of any key `x : ℕ`. -/
theorem elements_erase {t : Tree d} (ht : t.Valid) (x : ℕ) :
    (t.erase x).elements = t.elements.erase x := by
  ext y
  rw [mem_elements_iff (valid_erase ht x), Finset.mem_erase, mem_elements_iff ht]
  exact contains_erase ht x y

/-- A successful predecessor is the greatest finite-set element strictly below the query. -/
theorem predecessor_elements_some_iff {t : Tree d} (ht : t.Valid) (x y : ℕ) :
    t.predecessor x = some y ↔ y ∈ t.elements ∧ y < x ∧
      ∀ z, z ∈ t.elements → z < x → z ≤ y := by
  simp only [mem_elements_iff ht]
  exact predecessor_eq_some_iff ht x y

/-- An absent predecessor means that every finite-set element is at least the query. -/
theorem predecessor_elements_none_iff {t : Tree d} (ht : t.Valid) (x : ℕ) :
    t.predecessor x = none ↔ ∀ z, z ∈ t.elements → x ≤ z := by
  simp only [mem_elements_iff ht]
  exact predecessor_eq_none_iff ht x

end Cslib.Algorithms.Lean.VanEmdeBoas.Tree
