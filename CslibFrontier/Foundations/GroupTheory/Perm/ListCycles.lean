/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate (Mathlib GroupTheory/Perm/List)

public import CslibFrontier.Init
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Data.Fin.Basic
import CslibFrontier.Foundations.GroupTheory.Perm.Doubled
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# Successors in a partition into listed directed cycles

The executed successor scans the supplied words and wraps within the first containing word.
When their flattening is duplicate-free, this is exactly the product of Mathlib's
`List.formPerm` permutations. Empty words contribute no points, singleton words retain their
fixed points, and points outside the words are fixed. No bound on the ambient type is needed.
-/

public section

namespace List

variable {α : Type*} [DecidableEq α]

/-- Follow the first listed cycle containing a point; fix points absent from every word.
The scan is bounded by the actual lists, independently of the representation of a point. -/
@[expose] def nextInCycles (cycles : List (List α)) (a : α) : α :=
  let word := (cycles.find? (fun word => decide (a ∈ word))).getD []
  let next := word.idxOf a + 1
  word[if next < word.length then next else 0]?.getD a

/-- The directed permutation represented by a list of cycle words. Overlapping words
are composed in list order; the successor scan agrees when the flattening is Nodup. -/
@[expose] def cyclePermutation (cycles : List (List α)) : Equiv.Perm α :=
  (cycles.map List.formPerm).prod

@[simp] theorem nextInCycles_nil (a : α) : nextInCycles [] a = a := by
  simp [nextInCycles]

/-- A head word not containing the point is skipped by the literal scan. -/
theorem nextInCycles_cons_of_not_mem (word : List α) (cycles : List (List α)) (a : α)
    (ha : a ∉ word) : nextInCycles (word :: cycles) a = nextInCycles cycles a := by
  simp [nextInCycles, ha]

private theorem nextInCycles_cons_of_mem (word : List α) (cycles : List (List α)) (a : α)
    (hw : word.Nodup) (ha : a ∈ word) :
    nextInCycles (word :: cycles) a = word.formPerm a := by
  have hi : word.idxOf a < word.length := List.idxOf_lt_length_of_mem ha
  have hpos : 0 < word.length := Nat.zero_le _ |>.trans_lt hi
  have hmod : (word.idxOf a + 1) % word.length =
      if word.idxOf a + 1 < word.length then word.idxOf a + 1 else 0 := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · have he : word.idxOf a + 1 = word.length := by omega
      rw [he, Nat.mod_self]
  rw [← List.getElem_idxOf hi, List.formPerm_apply_getElem word hw _ hi]
  simp only [List.getElem_idxOf hi, nextInCycles, ha, decide_true, List.find?_cons_of_pos,
    Option.getD_some, hmod]
  rw [List.getD_getElem?, dite_eq_left (by split_ifs <;> omega)]

/-- Points absent from every word are fixed by the product permutation. -/
theorem cyclePermutation_apply_of_not_mem (cycles : List (List α)) (a : α)
    (ha : a ∉ cycles.flatten) : cyclePermutation cycles a = a := by
  induction cycles with
  | nil => rfl
  | cons word cycles ih =>
    have hn : a ∉ word ∧ a ∉ cycles.flatten := by simpa only [flatten_cons,
      mem_append, not_or] using ha
    change word.formPerm (cyclePermutation cycles a) = a
    rw [ih hn.2, List.formPerm_apply_of_notMem hn.1]

/-- The product preserves membership in the union of its words, even if they overlap. -/
theorem cyclePermutation_mem_flatten_iff (cycles : List (List α)) (a : α) :
    cyclePermutation cycles a ∈ cycles.flatten ↔ a ∈ cycles.flatten := by
  constructor
  · intro hm
    by_contra ha
    exact ha (by rwa [cyclePermutation_apply_of_not_mem cycles a ha] at hm)
  · intro ha
    by_contra hm
    have hfix := cyclePermutation_apply_of_not_mem cycles (cyclePermutation cycles a) hm
    have he : cyclePermutation cycles a = a := (cyclePermutation cycles).injective hfix
    exact hm (he.symm ▸ ha)

/-- A partition into directed words executes precisely the product of its cycle permutations.
In particular the total lookup routine is a permutation on every covered finite carrier. -/
theorem nextInCycles_eq_cyclePermutation (cycles : List (List α))
    (hc : cycles.flatten.Nodup) (a : α) :
    nextInCycles cycles a = cyclePermutation cycles a := by
  induction cycles with
  | nil => rfl
  | cons word cycles ih =>
    have hnd := List.nodup_append'.mp (show (word ++ cycles.flatten).Nodup from hc)
    by_cases ha : a ∈ word
    · rw [nextInCycles_cons_of_mem word cycles a hnd.1 ha]
      change word.formPerm a = word.formPerm (cyclePermutation cycles a)
      rw [cyclePermutation_apply_of_not_mem cycles a
        (fun hm => List.disjoint_left.mp hnd.2.2 ha hm)]
    · rw [nextInCycles_cons_of_not_mem word cycles a ha, ih hnd.2.1]
      change cyclePermutation cycles a = word.formPerm (cyclePermutation cycles a)
      symm
      apply List.formPerm_apply_of_notMem
      intro hm
      have hfix := cyclePermutation_apply_of_not_mem cycles
        (cyclePermutation cycles a) (fun hn => List.disjoint_left.mp hnd.2.2 hm hn)
      have he : a = cyclePermutation cycles a :=
        (cyclePermutation cycles).injective (by rw [hfix])
      exact ha (he.symm ▸ hm)

/-- The product follows each constituent word's own directed successor. -/
theorem cyclePermutation_apply_of_mem (cycles : List (List α))
    (hc : cycles.flatten.Nodup) (word : List α) (hw : word ∈ cycles) (a : α)
    (ha : a ∈ word) : cyclePermutation cycles a = word.formPerm a := by
  induction cycles with
  | nil => simp at hw
  | cons head cycles ih =>
    have hnd := List.nodup_append'.mp (show (head ++ cycles.flatten).Nodup from hc)
    rcases List.mem_cons.mp hw with rfl | hw
    · change word.formPerm (cyclePermutation cycles a) = word.formPerm a
      rw [cyclePermutation_apply_of_not_mem cycles a
        (fun hm => List.disjoint_left.mp hnd.2.2 ha hm)]
    · change head.formPerm (cyclePermutation cycles a) = word.formPerm a
      rw [ih hnd.2.1 hw]
      apply List.formPerm_apply_of_notMem
      intro hm
      exact List.disjoint_left.mp hnd.2.2 hm
        (List.mem_flatten.mpr ⟨word, hw, List.formPerm_apply_mem_of_mem ha⟩)

/-- Each nonempty listed word is a complete orbit of the product. Singleton words give
fixed-point orbits; empty words make the assertion vacuous. -/
theorem isCycleOn_cyclePermutation (cycles : List (List α))
    (hc : cycles.flatten.Nodup) (word : List α) (hw : word ∈ cycles) :
    (cyclePermutation cycles).IsCycleOn {a | a ∈ word} := by
  have hword : word.Nodup := (List.nodup_flatten.mp hc).1 word hw
  have hmaps : Set.MapsTo (cyclePermutation cycles) {a | a ∈ word} {a | a ∈ word} := by
    intro a ha
    change cyclePermutation cycles a ∈ word
    rw [cyclePermutation_apply_of_mem cycles hc word hw a ha]
    exact List.formPerm_apply_mem_of_mem ha
  have hfinite : Set.Finite {a | a ∈ word} := word.finite_toSet
  refine ⟨(hfinite.injOn_iff_bijOn_of_mapsTo hmaps).mp
    (cyclePermutation cycles).injective.injOn, ?_⟩
  intro a ha b hb
  obtain ⟨n, hn⟩ := hword.isCycleOn_formPerm.exists_pow_eq' hfinite ha hb
  have hp (k : ℕ) : (cyclePermutation cycles ^ k) a = (word.formPerm ^ k) a := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih,
        cyclePermutation_apply_of_mem cycles hc word hw _
          (hword.isCycleOn_formPerm.1.mapsTo.perm_pow k ha),
        ← Equiv.Perm.mul_apply, ← pow_succ']
  exact ⟨(n : ℤ), by rw [zpow_natCast, hp, hn]⟩

/-- A point in a stored word has exactly that word as its complete orbit, with no
ambient finiteness assumption and without discarding singleton cycles. -/
theorem sameCycle_cyclePermutation_iff_of_mem (cycles : List (List α))
    (hc : cycles.flatten.Nodup) (word : List α) (hw : word ∈ cycles) (a b : α)
    (ha : a ∈ word) : (cyclePermutation cycles).SameCycle a b ↔ b ∈ word := by
  have hcycle := isCycleOn_cyclePermutation cycles hc word hw
  constructor
  · rintro ⟨k, rfl⟩
    exact (hcycle.1.perm_zpow k).mapsTo ha
  · intro hb
    exact hcycle.2 ha hb

/-- Restrict the listed cycle product to a completely covered finite interval. This is a
proof-side permutation of actual positions; the executed successor remains `nextInCycles`. -/
@[expose] def finiteCyclePermutation (cycles : List (List ℕ)) {n : ℕ}
    (hcover : ∀ i, i ∈ cycles.flatten ↔ i < n) : Equiv.Perm (Fin n) :=
  (Fin.equivSubtype (n := n)).symm.permCongr
    ((cyclePermutation cycles).subtypePerm (p := fun i : ℕ => i < n) fun i =>
      (hcover _).symm.trans ((cyclePermutation_mem_flatten_iff cycles i).trans (hcover i)))

/-- Restriction retains the literal natural-number successor. -/
theorem val_finiteCyclePermutation (cycles : List (List ℕ)) {n : ℕ}
    (hcover : ∀ i, i ∈ cycles.flatten ↔ i < n) (i : Fin n) :
    (finiteCyclePermutation cycles hcover i).val = cyclePermutation cycles i.val := rfl

/-- For a partition, the finite successor is the exact bounded lookup routine. -/
theorem val_finiteCyclePermutation_eq_nextInCycles (cycles : List (List ℕ)) {n : ℕ}
    (hcover : ∀ i, i ∈ cycles.flatten ↔ i < n) (hn : cycles.flatten.Nodup) (i : Fin n) :
    (finiteCyclePermutation cycles hcover i).val = nextInCycles cycles i.val :=
  (nextInCycles_eq_cyclePermutation cycles hn i.val).symm

/-- Restriction to the covered interval retains every complete orbit, including fixed points. -/
theorem sameCycle_finiteCyclePermutation_iff (cycles : List (List ℕ)) {n : ℕ}
    (hcover : ∀ i, i ∈ cycles.flatten ↔ i < n) (i j : Fin n) :
    (finiteCyclePermutation cycles hcover).SameCycle i j ↔
      (cyclePermutation cycles).SameCycle i.val j.val := by
  let f := (cyclePermutation cycles).subtypePerm (p := fun i : ℕ => i < n) fun i =>
    (hcover _).symm.trans ((cyclePermutation_mem_flatten_iff cycles i).trans (hcover i))
  have he := Equiv.Perm.sameCycle_equiv_iff (Fin.equivSubtype (n := n)).symm f
    ((Fin.equivSubtype (n := n)).symm.permCongr f) (fun z => by simp)
    (Fin.equivSubtype i) (Fin.equivSubtype j)
  unfold finiteCyclePermutation
  simpa only [Equiv.symm_apply_apply, f, Equiv.Perm.sameCycle_subtypePerm,
    Fin.equivSubtype_apply, Fin.equivSubtype_symm_apply, Fin.eta] using he

end List
