/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.AList

/-!
# Sparse memory with an explicit default

A sparse memory is Mathlib's association list with a constant value type. Its keys are unique;
writing a cell replaces its old binding. Storing the default value still records a binding, so
cardinality measures stored addresses rather than the support of the denoted function.

## Main definitions

* `SparseMemory`: an association list of distinct addresses and values.
* `SparseMemory.read`: total memory semantics, with an explicit default value.
* `SparseMemory.entries`: the ordinary pair representation used for binary encoding.

## Main results

* `SparseMemory.read_insert`: a write denotes functional update.
* `SparseMemory.length_insert_le`: a write adds at most one stored address.
* `SparseMemory.length_insert_of_mem`: overwriting an address does not grow the store.

## References

The representation and lookup/update correctness reuse Mathlib's `AList` implementation.
-/

@[expose] public section

namespace Cslib.GenericRAM

/-- Finite memory with distinct stored addresses. The default value is supplied to `read`. -/
abbrev SparseMemory (Address Value : Type*) := AList (fun _ : Address => Value)

namespace SparseMemory

variable {Address Value : Type*} [DecidableEq Address]

/-- The finite bindings, viewed as ordinary pairs for encoding. -/
def entries (s : SparseMemory Address Value) : List (Address × Value) :=
  (AList.entries s).map fun e => (e.1, e.2)

/-- Read a stored address, or return the supplied default. -/
def read (default : Value) (a : Address) (s : SparseMemory Address Value) : Value :=
  (s.lookup a).getD default

omit [DecidableEq Address] in
/-- The ordinary entries determine the association list. -/
theorem entries_injective : Function.Injective (entries (Address := Address) (Value := Value)) := by
  intro s t h
  apply AList.ext
  have hi : Function.Injective (fun e : Sigma (fun _ : Address => Value) => (e.1, e.2)) := by
    intro x y h
    cases x
    cases y
    cases h
    rfl
  exact List.map_injective_iff.mpr hi h

omit [DecidableEq Address] in
@[simp] theorem entries_empty : entries (∅ : SparseMemory Address Value) = [] := rfl

/-- Default-valued memory requires no stored cells. -/
@[simp] theorem read_empty (default : Value) (a : Address) :
    read default a (∅ : SparseMemory Address Value) = default := rfl

omit [DecidableEq Address] in
/-- The pair representation has the same number of bindings. -/
@[simp] theorem length_entries (s : SparseMemory Address Value) :
    (entries s).length = (AList.entries s).length := List.length_map _

/-- Writing denotes functional update, including when the value equals the default. -/
theorem read_insert (default : Value) (a : Address) (v : Value)
    (s : SparseMemory Address Value) :
    (fun b => read default b (s.insert a v)) = Function.update (fun b => read default b s) a v := by
  funext b
  by_cases h : b = a
  · subst b
    simp [read]
  · simp [read, AList.lookup_insert_ne h, Function.update_of_ne h]

/-- A write adds at most one distinct stored address. -/
theorem length_insert_le (a : Address) (v : Value) (s : SparseMemory Address Value) :
    (entries (s.insert a v)).length ≤ (entries s).length + 1 := by
  simp only [length_entries, AList.entries_insert, List.length_cons]
  exact Nat.add_le_add_right (List.kerase_sublist a (AList.entries s)).length_le 1

/-- Replacing an existing address preserves the number of stored addresses. -/
theorem length_insert_of_mem (a : Address) (v : Value) (s : SparseMemory Address Value)
    (ha : a ∈ s) : (entries (s.insert a v)).length = (entries s).length := by
  obtain ⟨b, l₁, l₂, _, h, he⟩ := List.exists_of_kerase ha
  simp only [length_entries, AList.entries_insert, List.length_cons, he]
  simp [h, Nat.add_assoc]

/-- Erasure is filtering on distinct-key lists; this identifies the certified scan algorithm. -/
private theorem kerase_eq_filter (a : Address) (l : List (Sigma (fun _ : Address => Value)))
    (h : l.NodupKeys) : l.kerase a = l.filter (fun e => decide (a ≠ e.1)) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨hne, hn⟩ := List.nodupKeys_cons.mp h
    by_cases ha : a = e.1
    · subst a
      rw [List.kerase_cons_eq rfl]
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        not_false_eq_true, List.filter_cons_of_neg]
      symm
      apply List.filter_eq_self.mpr
      intro x hx
      have hx' : x.1 ∈ l.keys := List.mem_map.mpr ⟨x, hx, rfl⟩
      simpa using fun he : e.1 = x.1 => hne (he ▸ hx')
    · simp [List.kerase_cons_ne ha, ha, ih hn]

/-- A write is a filter followed by one cons, on the encoded pair representation. -/
theorem entries_insert (a : Address) (v : Value) (s : SparseMemory Address Value) :
    entries (s.insert a v) = (a, v) :: (entries s).filter (fun e => decide (a ≠ e.1)) := by
  simp only [entries, AList.entries_insert, List.map_cons,
    kerase_eq_filter a (AList.entries s) s.nodupKeys]
  congr 1
  exact (List.filter_map (p := fun e : Address × Value => decide (a ≠ e.1))).symm

/-- Lookup is a first-match scan of the encoded pair representation. -/
theorem read_eq_find (default : Value) (a : Address) (s : SparseMemory Address Value) :
    read default a s =
      (((entries s).find? (fun e => decide (a = e.1))).map Prod.snd).getD default := by
  unfold read AList.lookup entries
  induction (AList.entries s) with
  | nil => rfl
  | cons e l ih =>
    by_cases h : a = e.1
    · cases e
      subst a
      simp [List.dlookup]
    · simp only [List.dlookup, List.map_cons, List.find?_cons, h, Ne.symm h,
        decide_false]
      exact ih

/-- Each binding after a write is either the new binding or a surviving old binding. -/
theorem mem_entries_insert {a : Address} {v : Value} {s : SparseMemory Address Value}
    {e : Address × Value} : e ∈ entries (s.insert a v) ↔ e = (a, v) ∨ e ∈ entries s ∧ a ≠ e.1 := by
  simp [entries_insert]

end SparseMemory
end Cslib.GenericRAM
