/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ScanSet

/-!
# Memory invariant of a timestamped query list

## Main definitions

* `PrunedQuery.ScanMemory`: a distinct finite list and its timestamp membership directory.

## Main results

* `PrunedQuery.ScanMemory.insert_new`: the two actual stores preserve the invariant on insertion.

The invariant describes memory contents only. Execution and instruction charges are proved
separately for the native scan; no execution certificate is included here.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- The occupied output prefix enumerates `S` once, and the timestamp table identifies exactly
its members. Older timestamps may remain elsewhere in the directory. -/
structure ScanMemory (mem : ℕ → ℕ) (out stamps epoch capacity : ℕ) (S : Finset ℕ) : Prop where
  /-- Each listed value is a valid directory index. -/
  bounded : ∀ q ∈ S, q < capacity
  /-- Every timestamp is at most the current epoch. -/
  stamp_le : ∀ q < capacity, mem (stamps + q) ≤ epoch
  /-- The current epoch is exactly the membership marker. -/
  marked : ∀ q < capacity, mem (stamps + q) = epoch ↔ q ∈ S
  /-- The actual occupied prefix is an injective enumeration of the set. -/
  listed : ∃ v : Fin S.card → ℕ, Function.Injective v ∧
    Set.range v = (S : Set ℕ) ∧ (Block.mk out S.card).Realizes mem v

/-- A realized distinct list cannot exceed its concrete directory capacity. -/
theorem ScanMemory.card_le {mem : ℕ → ℕ} {out stamps epoch capacity : ℕ} {S : Finset ℕ}
    (h : ScanMemory mem out stamps epoch capacity S) : S.card ≤ capacity := by
  have hs : S ⊆ Finset.range capacity := fun q hq => Finset.mem_range.mpr (h.bounded q hq)
  simpa using Finset.card_le_card hs

/-- Agreement on the occupied list and timestamp directory preserves the scan invariant.
Unoccupied list cells have no specified meaning and need not agree. -/
theorem ScanMemory.congr {mem mem' : ℕ → ℕ} {out stamps epoch capacity : ℕ} {S : Finset ℕ}
    (h : ScanMemory mem out stamps epoch capacity S)
    (hlist : ∀ i < S.card, mem' (out + i) = mem (out + i))
    (hstamp : ∀ q < capacity, mem' (stamps + q) = mem (stamps + q)) :
    ScanMemory mem' out stamps epoch capacity S := by
  refine ⟨h.bounded, ?_, ?_, ?_⟩
  · intro q hq
    rw [hstamp q hq]
    exact h.stamp_le q hq
  · intro q hq
    rw [hstamp q hq]
    exact h.marked q hq
  · obtain ⟨v, hv, hrange, hreal⟩ := h.listed
    exact ⟨v, hv, hrange, fun i => (hlist i i.isLt).trans (hreal i)⟩

/-- Reading the occupied native list gives exactly its represented finite set. -/
theorem ScanMemory.image_read {mem : ℕ → ℕ} {out stamps epoch capacity : ℕ} {S : Finset ℕ}
    (h : ScanMemory mem out stamps epoch capacity S) :
    (Finset.range S.card).image (fun i => mem (out + i)) = S := by
  obtain ⟨v, _, hrange, hreal⟩ := h.listed
  ext q
  constructor
  · rintro hq
    obtain ⟨i, hi, hq⟩ := Finset.mem_image.mp hq
    have hi' : i < S.card := Finset.mem_range.mp hi
    have hread : mem (out + i) = v ⟨i, hi'⟩ := hreal ⟨i, hi'⟩
    have hv : v ⟨i, hi'⟩ ∈ S := by
      rw [← Finset.mem_coe, ← hrange]
      exact ⟨⟨i, hi'⟩, rfl⟩
    exact (hread.symm.trans hq) ▸ hv
  · intro hq
    have hv : q ∈ Set.range v := by rw [hrange]; exact hq
    obtain ⟨i, rfl⟩ := hv
    exact Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, hreal i⟩

/-- Occupied native list positions store different codes. -/
theorem ScanMemory.injOn_read {mem : ℕ → ℕ} {out stamps epoch capacity : ℕ} {S : Finset ℕ}
    (h : ScanMemory mem out stamps epoch capacity S) :
    Set.InjOn (fun i => mem (out + i)) {i | i < S.card} := by
  obtain ⟨v, hv, _, hreal⟩ := h.listed
  intro i hi j hj he
  have hreadi : mem (out + i) = v ⟨i, hi⟩ := hreal ⟨i, hi⟩
  have hreadj : mem (out + j) = v ⟨j, hj⟩ := hreal ⟨j, hj⟩
  exact congrArg Fin.val (hv (hreadi.symm.trans (he.trans hreadj)))

/-- An unseen valid code leaves a free output cell for its insertion. -/
theorem ScanMemory.card_lt_of_notMem {mem : ℕ → ℕ} {out stamps epoch capacity : ℕ}
    {S : Finset ℕ} (h : ScanMemory mem out stamps epoch capacity S) {q : ℕ}
    (hq : q < capacity) (hnew : q ∉ S) : S.card < capacity := by
  have hs : insert q S ⊆ Finset.range capacity := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_range.mpr hq
    · exact Finset.mem_range.mpr (h.bounded a ha)
  have hc := Finset.card_le_card hs
  simp only [Finset.card_insert_of_notMem hnew, Finset.card_range] at hc
  omega

/-- A fresh epoch establishes the empty directory without clearing its cells. -/
theorem ScanMemory.empty {mem : ℕ → ℕ} {out stamps epoch capacity : ℕ}
    (h : ∀ q < capacity, mem (stamps + q) < epoch) :
    ScanMemory mem out stamps epoch capacity ∅ := by
  refine ⟨by simp, fun q hq => (h q hq).le, ?_, ?_⟩
  · intro q hq
    simp only [Finset.notMem_empty, iff_false]
    exact Nat.ne_of_lt (h q hq)
  · refine ⟨Fin.elim0, (fun i => i.elim0), ?_, (fun i => i.elim0)⟩
    ext q
    simp

/-- Append one previously unseen code, then mark its directory entry. Disjointness of the
two concrete blocks ensures that neither store corrupts the other representation. -/
theorem ScanMemory.insert_new {mem : ℕ → ℕ} {out stamps epoch capacity : ℕ} {S : Finset ℕ}
    (h : ScanMemory mem out stamps epoch capacity S) {q : ℕ} (hq : q < capacity)
    (hnew : q ∉ S) (hsep : out + capacity ≤ stamps ∨ stamps + capacity ≤ out) :
    ScanMemory
      (Function.update (Function.update mem (out + S.card) q) (stamps + q) epoch)
      out stamps epoch capacity (insert q S) := by
  have hcard := h.card_lt_of_notMem hq hnew
  have haway (a : ℕ) (ha : a < capacity) : stamps + a ≠ out + S.card := by
    rcases hsep with hs | hs <;> omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hq
    · exact h.bounded a ha
  · intro a ha
    by_cases he : a = q
    · subst a
      simp
    · simpa only [Function.update_of_ne (by omega : stamps + a ≠ stamps + q),
        Function.update_of_ne (haway a ha)] using h.stamp_le a ha
  · intro a ha
    by_cases he : a = q
    · subst a
      simp
    · simpa only [Function.update_of_ne (by omega : stamps + a ≠ stamps + q),
        Function.update_of_ne (haway a ha), Finset.mem_insert, he, false_or] using h.marked a ha
  · obtain ⟨v, hv, hrange, hreal⟩ := h.listed
    have hnot : q ∉ Set.range v := by simpa only [hrange, Finset.mem_coe] using hnew
    have hlist := hreal.snoc q
    have hown : ¬(Block.mk out (S.card + 1)).Owns (stamps + q) := by
      change ¬(out ≤ stamps + q ∧ stamps + q < out + (S.card + 1))
      rcases hsep with hs | hs <;> omega
    have hlist' := hlist.update_of_not_owns hown epoch
    rw [Finset.card_insert_of_notMem hnew]
    refine ⟨Fin.snoc v q, Fin.snoc_injective_iff.mpr ⟨hv, hnot⟩, ?_, hlist'⟩
    rw [Fin.range_snoc, hrange]
    simp

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
