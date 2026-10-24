/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.VanEmdeBoas.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Tauto

/-!
# Correctness of van Emde Boas insertion

The recursive minimum-excluded insertion algorithm follows [Demaine2015VanEmdeBoas], pp. 4–5.
The results here concern the functional Lean implementation and its represented set, with no
machine running-time claim.

## Main definitions

The algorithm and recursive invariant are `Tree.insert` and `Tree.Valid`, imported from `Basic`.

## Main results

* `Tree.valid_insert`: insertion of a bounded key preserves the recursive invariant.
* `Tree.contains_insert`: insertion represents exactly the union with the inserted key.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.VanEmdeBoas.Tree

variable {d : ℕ}

/-- A leaf with bounds `some (m, M)` contains `y` iff `y = m` or `y = M`. -/
@[simp] theorem contains_leaf_some (m M y : ℕ) :
    (leaf (some (m, M))).Contains y ↔ y = m ∨ y = M := by
  simp [Contains]

/-- An internal node with bounds `some (m, M)` contains `y` iff `y = m` or `y` is in some
cluster. -/
@[simp] theorem contains_node_some (m M : ℕ) (s : Tree d)
    (c : Fin (universeSize d) → Tree d) (y : ℕ) :
    (node (some (m, M)) s c).Contains y ↔
      y = m ∨ ∃ i a, (c i).Contains a ∧ y = i.val * universeSize d + a := by
  simp [Contains]

private theorem extrema_insert_of_contains {t t' : Tree d} (ht : t.Valid)
    {m M x : ℕ} (hb : t.bounds = some (m, M))
    (hb' : t'.bounds = some (min m x, max M x)) (hx : x < universeSize d)
    (hs : ∀ y, t'.Contains y ↔ y = x ∨ t.Contains y) : t'.Extrema := by
  have he := ht.extrema
  simp only [Extrema, hb] at he
  simp only [Extrema, hb']
  refine ⟨Nat.le_trans (min_le_right m x) (le_max_right M x), max_lt he.2.1 hx, ?_, ?_, ?_⟩
  · apply (hs _).mpr
    rcases le_total m x with h | h
    · exact Or.inr (by simpa only [min_eq_left h] using he.2.2.1)
    · exact Or.inl (min_eq_right h)
  · apply (hs _).mpr
    rcases le_total M x with h | h
    · exact Or.inl (max_eq_right h)
    · exact Or.inr (by simpa only [max_eq_left h] using he.2.2.2.1)
  · intro y hy
    rcases (hs y).mp hy with rfl | hy
    · exact ⟨min_le_right _ _, le_max_right _ _⟩
    · exact ⟨Nat.le_trans (min_le_left _ _) (he.2.2.2.2 y hy).1,
        Nat.le_trans (he.2.2.2.2 y hy).2 (le_max_left _ _)⟩

/-- Installing the first key changes only an empty node's local header. -/
private theorem singleton_of_bounds_none {t : Tree d} (ht : t.Valid) (hb : t.bounds = none)
    {x : ℕ} (hx : x < universeSize d) :
    (t.withBounds (some (x, x))).Valid ∧
      ∀ y, (t.withBounds (some (x, x))).Contains y ↔ y = x := by
  cases t with
  | leaf b =>
    simp only [bounds] at hb
    subst b
    simp only [withBounds, Valid, Extrema, bounds, contains_leaf_some]
    simp only [universeSize_zero] at hx
    simpa using hx
  | @node d b s c =>
    simp only [bounds] at hb
    subst b
    obtain ⟨he, hs, hc, ho, hsb, hcb⟩ := ht
    have hnone : ∀ i y, ¬(c i).Contains y := fun i y =>
      not_contains_of_bounds_none (hcb i) y
    have hset : ∀ y, (node (some (x, x)) s c).Contains y ↔ y = x := by
      intro y
      simp only [contains_node_some]
      constructor
      · rintro (rfl | ⟨i, a, ha, _⟩)
        · rfl
        · exact False.elim (hnone i a ha)
      · exact Or.inl
    refine ⟨⟨?_, hs, hc, ho, ?_⟩, hset⟩
    · simp only [Extrema, bounds]
      exact ⟨le_rfl, hx, (hset x).mpr rfl, (hset x).mpr rfl,
        fun y hy => by have := (hset y).mp hy; omega⟩
    · exact fun i y hy => False.elim (hnone i y hy)

private theorem contains_node_update {s s' : Tree d}
    {c c' : Fin (universeSize d) → Tree d} {m M x : ℕ}
    {i : Fin (universeSize d)} {a : ℕ} (hz : max m x = i.val * universeSize d + a)
    (hc : ∀ j y, (c' j).Contains y ↔ (j = i ∧ y = a) ∨ (c j).Contains y) :
    ∀ y, (node (some (min m x, max M x)) s' c').Contains y ↔
      y = x ∨ (node (some (m, M)) s c).Contains y := by
  intro y
  simp only [contains_node_some, hc]
  have hminmax : y = min m x ∨ y = max m x ↔ y = x ∨ y = m := by
    rcases le_total m x with h | h
    · simp only [min_eq_left h, max_eq_right h]
      tauto
    · simp only [min_eq_right h, max_eq_left h]
  constructor
  · rintro (hy | ⟨j, b, (⟨rfl, rfl⟩ | hb), he⟩)
    · rcases hminmax.mp (Or.inl hy) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases hminmax.mp (Or.inr (he.trans hz.symm)) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨j, b, hb, he⟩)
  · rintro (hy | hy | ⟨j, b, hb, he⟩)
    · rcases hminmax.mpr (Or.inl hy) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨i, a, Or.inl ⟨rfl, rfl⟩, h.trans hz⟩
    · rcases hminmax.mpr (Or.inr hy) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨i, a, Or.inl ⟨rfl, rfl⟩, h.trans hz⟩
    · exact Or.inr ⟨j, b, Or.inr hb, he⟩

/-- A valid node is occupied exactly when it represents at least one key. -/
theorem Valid.bounds_isSome_iff {t : Tree d} (ht : t.Valid) :
    t.bounds.isSome = true ↔ ∃ y, t.Contains y := by
  cases hb : t.bounds with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists]
    exact not_contains_of_bounds_none hb
  | some b =>
    obtain ⟨m, M⟩ := b
    simp only [Option.isSome_some, true_iff]
    exact ⟨m, ht.contains_minimum hb⟩

private theorem valid_node_update {s s' : Tree d}
    {c c' : Fin (universeSize d) → Tree d} {m M x : ℕ}
    (ht : (node (some (m, M)) s c).Valid) (hx : x < universeSize (d + 1))
    (hm : x ≠ m) {i : Fin (universeSize d)} {a : ℕ}
    (hz : max m x = i.val * universeSize d + a)
    (hs' : s'.Valid) (hc' : ∀ j, (c' j).Valid)
    (hss : ∀ j, s'.Contains j ↔ j = i.val ∨ s.Contains j)
    (hcc : ∀ j y, (c' j).Contains y ↔ (j = i ∧ y = a) ∨ (c j).Contains y) :
    (node (some (min m x, max M x)) s' c').Valid ∧
      ∀ y, (node (some (min m x, max M x)) s' c').Contains y ↔
        y = x ∨ (node (some (m, M)) s c).Contains y := by
  have hset := contains_node_update (s := s) (s' := s') (M := M) hz hcc
  refine ⟨⟨extrema_insert_of_contains ht rfl rfl hx hset, hs', hc', ?_, ?_⟩, hset⟩
  · intro j
    rw [hss, (hc' j).bounds_isSome_iff]
    constructor
    · rintro (hji | hj)
      · have hji' : j = i := Fin.ext hji
        exact ⟨a, (hcc j a).mpr (Or.inl ⟨hji', rfl⟩)⟩
      · obtain ⟨y, hy⟩ := (ht.2.2.1 j).bounds_isSome_iff.mp ((ht.2.2.2.1 j).mp hj)
        exact ⟨y, (hcc j y).mpr (Or.inr hy)⟩
    · rintro ⟨y, hy⟩
      rcases (hcc j y).mp hy with ⟨rfl, rfl⟩ | hy
      · exact Or.inl rfl
      · exact Or.inr ((ht.2.2.2.1 j).mpr
          ((ht.2.2.1 j).bounds_isSome_iff.mpr ⟨y, hy⟩))
  · intro j y hy
    rcases (hcc j y).mp hy with ⟨rfl, rfl⟩ | hy
    · rw [← hz]
      rcases le_total m x with h | h
      · rw [min_eq_left h, max_eq_right h]
        omega
      · rw [min_eq_right h, max_eq_left h]
        omega
    · exact Nat.lt_of_le_of_lt (min_le_left m x) (ht.2.2.2.2 j y hy)

private theorem update_cluster_spec {c : Fin (universeSize d) → Tree d}
    (hc : ∀ j, (c j).Valid) {i : Fin (universeSize d)} {a : ℕ} {t : Tree d}
    (ht : t.Valid) (hs : ∀ y, t.Contains y ↔ y = a ∨ (c i).Contains y) :
    (∀ j, (Function.update c i t j).Valid) ∧
      ∀ j y, (Function.update c i t j).Contains y ↔
        (j = i ∧ y = a) ∨ (c j).Contains y := by
  constructor
  · intro j
    by_cases h : j = i
    · subst j
      simpa only [Function.update_self] using ht
    · simpa only [Function.update_of_ne h] using hc j
  · intro j y
    by_cases h : j = i
    · subst j
      simpa only [Function.update_self, true_and] using hs y
    · simp [h]

private theorem insert_spec {t : Tree d} (ht : t.Valid) {x : ℕ}
    (hx : x < universeSize d) :
    (t.insert x).Valid ∧ ∀ y, (t.insert x).Contains y ↔ y = x ∨ t.Contains y := by
  induction d generalizing x with
  | zero =>
    cases t with
    | leaf b =>
      cases b with
      | none =>
        obtain ⟨hv, hs⟩ := singleton_of_bounds_none ht rfl hx
        refine ⟨hv, fun y => ?_⟩
        simpa only [insert, withBounds, Contains, reduceCtorEq, false_and, exists_false,
          or_false] using hs y
      | some b =>
        obtain ⟨m, M⟩ := b
        have he := ht.extrema
        simp only [Extrema, bounds] at he
        have hset : ∀ y, ((leaf (some (m, M))).insert x).Contains y ↔
            y = x ∨ (leaf (some (m, M))).Contains y := by
          intro y
          simp only [insert, contains_leaf_some]
          simp only [universeSize_zero] at hx he
          omega
        exact ⟨extrema_insert_of_contains ht rfl rfl hx hset, hset⟩
  | succ d ih =>
    cases t with
    | node b s c =>
      cases b with
      | none =>
        obtain ⟨hv, hs⟩ := singleton_of_bounds_none ht rfl hx
        refine ⟨hv, fun y => ?_⟩
        simpa only [insert, withBounds, Contains, reduceCtorEq, false_and, exists_false,
          or_false] using hs y
      | some b =>
        obtain ⟨m, M⟩ := b
        by_cases hm : x = m
        · simp only [insert, ite_eq_left hm]
          refine ⟨ht, fun y => ?_⟩
          constructor
          · exact Or.inr
          · rintro (rfl | hy)
            · simpa only [hm] using ht.contains_minimum rfl
            · exact hy
        · have hm_lt := ht.contains_lt (ht.contains_minimum rfl)
          have hzlt : max m x < universeSize (d + 1) := max_lt hm_lt hx
          have hi : max m x / universeSize d < universeSize d :=
            (Nat.div_lt_iff_lt_mul (universeSize_pos d)).mpr hzlt
          let i : Fin (universeSize d) := ⟨max m x / universeSize d, hi⟩
          let a := max m x % universeSize d
          have ha : a < universeSize d := Nat.mod_lt _ (universeSize_pos d)
          have hz : max m x = i.val * universeSize d + a := by
            simpa only [i, a, Nat.mul_comm] using (Nat.div_add_mod (max m x) (universeSize d)).symm
          cases hb : (c i).bounds with
          | none =>
            obtain ⟨hv, hs⟩ := singleton_of_bounds_none (ht.2.2.1 i) hb ha
            have hset : ∀ y, ((c i).withBounds (some (a, a))).Contains y ↔
                y = a ∨ (c i).Contains y := by
              intro y
              simpa only [not_contains_of_bounds_none hb y, or_false] using hs y
            obtain ⟨hcv, hcs⟩ := update_cluster_spec ht.2.2.1 hv hset
            obtain ⟨hsv, hss⟩ := ih ht.2.1 i.isLt
            have hresult := valid_node_update ht hx hm hz hsv hcv hss hcs
            dsimp only [i] at hb
            simpa only [insert, ite_eq_right hm, dite_eq_left hi, i, a, hb] using hresult
          | some b =>
            obtain ⟨hv, hs⟩ := ih (ht.2.2.1 i) ha
            obtain ⟨hcv, hcs⟩ := update_cluster_spec ht.2.2.1 hv hs
            have hi_mem : s.Contains i.val :=
              (ht.2.2.2.1 i).mpr (by simp [hb])
            have hss : ∀ j, s.Contains j ↔ j = i.val ∨ s.Contains j := by
              intro j
              constructor
              · exact Or.inr
              · rintro (rfl | hj)
                · exact hi_mem
                · exact hj
            have hresult := valid_node_update ht hx hm hz ht.2.1 hcv hss hcs
            dsimp only [i] at hb
            simpa only [insert, ite_eq_right hm, dite_eq_left hi, i, a, hb] using hresult

/-- Bounded insertion preserves the recursive representation invariant. -/
theorem valid_insert {t : Tree d} (ht : t.Valid) {x : ℕ} (hx : x < universeSize d) :
    (t.insert x).Valid :=
  (insert_spec ht hx).1

/-- The represented set after bounded insertion is exactly the old set plus the inserted key. -/
theorem contains_insert {t : Tree d} (ht : t.Valid) {x : ℕ} (hx : x < universeSize d)
    (y : ℕ) : (t.insert x).Contains y ↔ y = x ∨ t.Contains y :=
  (insert_spec ht hx).2 y

end Cslib.Algorithms.Lean.VanEmdeBoas.Tree
