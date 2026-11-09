/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.SparseMemory.Basic
public import Mathlib.Data.Finset.Card
import all CslibFrontier.Computability.GenericRAM.SparseMemory.Basic

/-!
# Removing default-valued sparse bindings

`compact` actually filters the stored list, retaining its order and unique keys.
Total reads are unchanged, including explicit default cells. Compaction commutes
with updates after normalization. Its stored-entry count is bounded by any cover
of the denoted nondefault support, rather than historical allocation.

This is a representation operation, not an efficient dictionary lookup theorem.
The companion bit-machine certificate charges the complete filtering scan.
-/

public section
namespace Cslib.GenericRAM.SparseMemory

variable {Address Value : Type} [DecidableEq Address] [DecidableEq Value]

omit [DecidableEq Address] in
/-- Delete every binding equal to the supplied default, preserving surviving order. -/
def compact (default : Value) (s : SparseMemory Address Value) : SparseMemory Address Value :=
  ⟨(AList.entries s).filter (fun e => decide (e.2 ≠ default)),
    List.NodupKeys.sublist List.filter_sublist s.nodupKeys⟩

omit [DecidableEq Address] in
/-- Compaction is a real filter on the encoded pair representation. -/
theorem entries_compact (default : Value) (s : SparseMemory Address Value) :
    entries (compact default s) = (entries s).filter (fun e => decide (e.2 ≠ default)) := by
  simp only [entries, compact]
  exact (List.filter_map (p := fun e : Address × Value => decide (e.2 ≠ default))).symm

/-- Lookup discards precisely the optional default binding. -/
theorem lookup_compact (default : Value) (s : SparseMemory Address Value) (a : Address) :
    (compact default s).lookup a = (s.lookup a).filter (fun v => decide (v ≠ default)) := by
  apply Option.ext
  intro v
  rw [← Option.mem_def, AList.mem_lookup_iff]
  simp only [compact, List.mem_filter, decide_eq_true_eq]
  cases h : s.lookup a with
  | none => simp [Option.filter, ← AList.mem_lookup_iff, h]
  | some u => simp [Option.filter, ← AList.mem_lookup_iff, h, and_comm]; grind

/-- Deleting explicit default bindings preserves total memory, at every address. -/
theorem read_compact (default : Value) (s : SparseMemory Address Value) (a : Address) :
    read default a (compact default s) = read default a s := by
  rw [read, lookup_compact]
  cases h : s.lookup a with
  | none => simp [read, h, Option.filter]
  | some v => by_cases hv : v = default <;> simp [read, h, hv, Option.filter]

omit [DecidableEq Address] in
/-- No surviving entry equals the supplied default. -/
theorem mem_entries_compact {default : Value} {s : SparseMemory Address Value}
    {e : Address × Value} : e ∈ entries (compact default s) ↔ e ∈ entries s ∧ e.2 ≠ default := by
  simp [entries_compact]

omit [DecidableEq Address] in
/-- Normalizing an already compact list changes no binding or order. -/
theorem compact_idem (default : Value) (s : SparseMemory Address Value) :
    compact default (compact default s) = compact default s := by
  apply entries_injective
  simp [entries_compact, List.filter_filter]

/-- Removing defaults before an actual write gives exactly the same normalized store. -/
theorem compact_insert_compact (default : Value) (s : SparseMemory Address Value)
    (a : Address) (v : Value) :
    compact default ((compact default s).insert a v) = compact default (s.insert a v) := by
  apply entries_injective
  simp only [entries_compact, entries_insert, List.filter_cons, List.filter_filter]
  simp [Bool.and_left_comm, Bool.and_comm]

omit [DecidableEq Value] in
/-- Every explicitly stored binding reads back its value. -/
theorem read_of_mem_entries {default : Value} {s : SparseMemory Address Value}
    {a : Address} {v : Value} (h : (a, v) ∈ entries s) : read default a s = v := by
  have hs : (⟨a, v⟩ : Sigma (fun _ : Address => Value)) ∈ (AList.entries s) := by
    obtain ⟨⟨a', v'⟩, he, eq⟩ := List.mem_map.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    exact he
  have hv := AList.mem_lookup_iff.mpr hs
  rw [Option.mem_def] at hv
  simp [read, hv]

/-- The number of retained bindings is bounded by a finite cover of actual nondefault memory.
The cover need not include default-valued cells that were explicitly written. -/
theorem length_compact_le (default : Value) (s : SparseMemory Address Value)
    (S : Finset Address) (hS : ∀ a, read default a s ≠ default → a ∈ S) :
    (entries (compact default s)).length ≤ S.card := by
  let keys := (entries (compact default s)).map Prod.fst
  have hn : keys.Nodup := by
    simpa only [keys, entries, List.map_map, Function.comp_def, List.NodupKeys, List.keys] using
      (compact default s).nodupKeys
  have sub : keys.toFinset ⊆ S := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have mem := mem_entries_compact.mp he
    exact hS e.1 (by simpa only [read_of_mem_entries mem.1] using mem.2)
  have hc := Finset.card_le_card sub
  simpa only [List.toFinset_card_of_nodup hn, keys, List.length_map] using hc

end Cslib.GenericRAM.SparseMemory
