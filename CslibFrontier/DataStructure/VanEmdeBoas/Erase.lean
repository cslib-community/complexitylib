/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.VanEmdeBoas.Insert
import Mathlib.Tactic.Linarith

/-!
# Single-recursion van Emde Boas deletion

This module defines and verifies key deletion on recursive minimum-excluded van Emde Boas trees
([Demaine2015VanEmdeBoas], p. 5; [CLRS2009], Section 20.3, p. 554).

At each internal depth `d + 1`:
* If the tree is empty or the query lies outside `[m, M]`, deletion returns immediately with no
  recursive call.
* If `m = M` (and hence `x = m`), the valid minimum-exclusion invariant guarantees that all
  clusters and the summary are already empty, so clearing the local header clears the node in
  `O(1)`.
* Otherwise (`m < M` and `m ≤ x ≤ M`), if `x = m`, the smallest key stored in the clusters is
  located via `summary.minimum` and `(cluster i).minimum` in `O(1)` header reads, promoted to
  become `newMin`, and targeted for deletion from `cluster i`; if `x ≠ m`, `newMin = m` is kept
  and `x % universeSize d` is targeted for deletion from `cluster (x / universeSize d)`.
* Inspecting `(cluster i).bounds` then chooses **at most one** recursive deletion:
  when `cluster i` is a singleton `{low}`, `cluster i` is cleared in `O(1)` via `withBounds none`
  and `erase` recurses only on `summary`; when `cluster i` has distinct extrema (`cm ≠ cM`), at
  least one key remains after deleting `low`, so `summary` stays unchanged and `erase` recurses
  only on `cluster i`.
* Finally, `clusterMax` reconstructs the updated maximum in `O(1)` from `newMin`, `s'.maximum`,
  and the maximal occupied cluster's cached `maximum`.

These are mathematical correctness statements about the functional Lean representation, without a
machine running-time claim.

## Main definitions

* `Tree.EraseTarget`, `Tree.eraseTarget`: non-recursive `O(1)` header selection of
  `(newMin, i, low)`.
* `Tree.clusterMax`: non-recursive `O(1)` reconstruction of a node's maximum from its summary and
  clusters.
* `Tree.erase`: single-recursion key deletion on `Tree d`.

## Main results

* `Tree.erase_empty`: deleting from `empty d` returns `empty d`.
* `Tree.valid_erase`: deletion of any key `x : ℕ` preserves `Tree.Valid`.
* `Tree.contains_erase`: `(t.erase x).Contains y ↔ y ≠ x ∧ t.Contains y`.
* `Tree.erase_eq_of_not_contains`: deleting an absent key from a valid tree returns `t` unchanged.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 20.3][CLRS2009]
-/

public section

namespace Cslib.DataStructure.VanEmdeBoas.Tree

variable {d : ℕ}

/-- Header-selected cluster target for an internal-node deletion step (`m < M` and `m ≤ x ≤ M`). -/
structure EraseTarget (d : ℕ) where
  /-- Updated local minimum of the parent node. -/
  newMin : ℕ
  /-- Index of the cluster from which `low` is to be removed. -/
  clusterIdx : Fin (universeSize d)
  /-- Low-order coordinate to remove from `cluster clusterIdx`. -/
  low : ℕ

/-- Non-recursive `O(1)` header helper selecting `(newMin, clusterIdx, low)` when `m < M` and
`m ≤ x ≤ M` ([Demaine2015VanEmdeBoas], p. 5; [CLRS2009], Section 20.3, p. 554). -/
@[expose] def eraseTarget {d : ℕ} (m x : ℕ) (s : Tree d)
    (c : Fin (universeSize d) → Tree d) : Option (EraseTarget d) :=
  if x = m then
    match s.minimum with
    | none => none
    | some j =>
      if hj : j < universeSize d then
        let i : Fin (universeSize d) := ⟨j, hj⟩
        (c i).minimum.map fun low => ⟨j * universeSize d + low, i, low⟩
      else none
  else if hx : x / universeSize d < universeSize d then
    some ⟨m, ⟨x / universeSize d, hx⟩, x % universeSize d⟩
  else none

/-- Reconstruct a node's maximum in `O(1)` header reads from `newMin`, `s.maximum`, and the
maximal occupied cluster's cached `maximum` ([Demaine2015VanEmdeBoas], p. 5; [CLRS2009],
Section 20.3, p. 554). -/
@[expose] def clusterMax {d : ℕ} (newMin : ℕ) (s : Tree d)
    (c : Fin (universeSize d) → Tree d) : ℕ :=
  match s.maximum with
  | none => newMin
  | some j =>
    if hj : j < universeSize d then
      match (c ⟨j, hj⟩).maximum with
      | none => newMin
      | some y => j * universeSize d + y
    else newMin

/-- Delete a key from a van Emde Boas tree, performing at most one recursive call per depth level
([Demaine2015VanEmdeBoas], p. 5; [CLRS2009], Section 20.3, p. 554). -/
@[expose] def erase : {d : ℕ} → Tree d → ℕ → Tree d
  | 0, .leaf b, x => match b with
    | none => .leaf none
    | some (m, M) =>
      if x = m ∧ x = M then .leaf none
      else if x = m then .leaf (some (M, M))
      else if x = M then .leaf (some (m, m))
      else .leaf (some (m, M))
  | _ + 1, .node b s c, x => match b with
    | none => .node none s c
    | some (m, M) =>
      if x < m ∨ M < x then .node (some (m, M)) s c
      else if m = M then .node none s c
      else
        match eraseTarget m x s c with
        | none => .node (some (m, M)) s c
        | some ⟨newMin, i, low⟩ =>
          match (c i).bounds with
          | none => .node (some (m, M)) s c
          | some (cm, cM) =>
            if cm = cM then
              if low = cm then
                let c' := Function.update c i ((c i).withBounds none)
                let s' := erase s i.val
                .node (some (newMin, clusterMax newMin s' c')) s' c'
              else .node (some (m, M)) s c
            else
              let c' := Function.update c i (erase (c i) low)
              .node (some (newMin, clusterMax newMin s c')) s c'

/-- Deleting any key from the empty tree at depth `d` returns `empty d`. -/
@[simp] theorem erase_empty (d x : ℕ) : (empty d).erase x = empty d := by
  cases d <;> rfl

private theorem singleton_contains_of_bounds_eq {t : Tree d} (ht : t.Valid) {m : ℕ}
    (hb : t.bounds = some (m, m)) (y : ℕ) : t.Contains y ↔ y = m := by
  have he := ht.extrema_of_bounds hb
  constructor
  · intro hy
    have := he.2.2.2.2 y hy
    omega
  · rintro rfl
    exact he.2.2.1

/-- Clearing the local header of a valid singleton node yields a valid empty node in `O(1)` because
minimum exclusion already forces its summary and clusters to be empty. -/
private theorem empty_of_bounds_eq {t : Tree d} (ht : t.Valid) {m : ℕ}
    (hb : t.bounds = some (m, m)) :
    (t.withBounds none).Valid ∧ (t.withBounds none).bounds = none ∧
      ∀ y, ¬(t.withBounds none).Contains y := by
  cases t with
  | leaf b =>
    obtain rfl : b = some (m, m) := hb
    refine ⟨?_, rfl, not_contains_of_bounds_none rfl⟩
    simp [withBounds, Valid, Extrema, bounds, Contains]
  | @node d b s c =>
    have he := ht.extrema_of_bounds hb
    obtain rfl : b = some (m, m) := hb
    obtain ⟨-, hs, hc, ho, hmin⟩ := ht
    have hcb : ∀ i, (c i).bounds = none := fun i => by
      cases hbi : (c i).bounds with
      | none => rfl
      | some cb =>
        have hcm := (hc i).contains_minimum hbi
        have := hmin i cb.1 hcm
        have := (he.2.2.2.2 _ ⟨m, m, rfl, Or.inr ⟨i, cb.1, hcm, rfl⟩⟩).2
        omega
    have hsb : s.bounds = none := by
      cases hbs : s.bounds with
      | none => rfl
      | some sb =>
        have hsm := hs.contains_minimum hbs
        have := (ho ⟨sb.1, hs.contains_lt hsm⟩).mp hsm
        simp [hcb] at this
    exact ⟨⟨not_contains_of_bounds_none rfl, hs, hc, ho, hsb, hcb⟩, rfl,
      not_contains_of_bounds_none rfl⟩

/-- Any valid summary/cluster pair whose keys strictly exceed `newMin < universeSize (d + 1)` forms
a valid node when paired with `clusterMax newMin s' c'`. -/
private theorem valid_node_of_clusterMax {newMin : ℕ} {s' : Tree d}
    {c' : Fin (universeSize d) → Tree d}
    (hmin_lt : newMin < universeSize (d + 1))
    (hs' : s'.Valid) (hc' : ∀ k, (c' k).Valid)
    (ho' : ∀ k, s'.Contains k.val ↔ (c' k).bounds.isSome = true)
    (hexcl : ∀ k y, (c' k).Contains y → newMin < k.val * universeSize d + y) :
    (node (some (newMin, clusterMax newMin s' c')) s' c').Valid := by
  refine ⟨?_, hs', hc', ho', hexcl⟩
  cases hbs : s'.bounds with
  | none =>
    have hmax : clusterMax newMin s' c' = newMin := by simp [clusterMax, maximum, hbs]
    rw [hmax]
    simp only [Extrema, bounds, contains_node_some]
    refine ⟨le_rfl, hmin_lt, Or.inl trivial, Or.inl trivial, ?_⟩
    rintro z (rfl | ⟨k, y, hy, _⟩)
    · exact ⟨le_rfl, le_rfl⟩
    · exact absurd ((ho' k).mpr ((hc' k).bounds_isSome_iff.mpr ⟨y, hy⟩))
        (not_contains_of_bounds_none hbs k.val)
  | some sb =>
    obtain ⟨sm, sM⟩ := sb
    have hse := hs'.extrema_of_bounds hbs
    let j : Fin (universeSize d) := ⟨sM, hse.2.1⟩
    obtain ⟨⟨cm, cM⟩, hbj⟩ := Option.isSome_iff_exists.mp ((ho' j).mp hse.2.2.2.1)
    have hce := (hc' j).extrema_of_bounds hbj
    have hmax : clusterMax newMin s' c' = sM * universeSize d + cM := by
      simp [clusterMax, maximum, hbs, hse.2.1, j, hbj]
    rw [hmax]
    have hgt : newMin < sM * universeSize d + cM := hexcl j cM hce.2.2.2.1
    have hM_lt : sM * universeSize d + cM < universeSize (d + 1) := by
      simpa only [universeSize_succ, Nat.add_zero] using
        index_lt_index hce.2.1 hse.2.1 (b := 0)
    refine ⟨hgt.le, hM_lt, ⟨newMin, _, rfl, Or.inl rfl⟩,
      ⟨newMin, _, rfl, Or.inr ⟨j, cM, hce.2.2.2.1, rfl⟩⟩, fun z hz => ?_⟩
    simp only [contains_node_some] at hz
    rcases hz with rfl | ⟨k, y, hy, rfl⟩
    · exact ⟨le_rfl, hgt.le⟩
    · refine ⟨(hexcl k y hy).le, ?_⟩
      have hk_le : k.val ≤ sM :=
        (hse.2.2.2.2 k.val ((ho' k).mpr ((hc' k).bounds_isSome_iff.mpr ⟨y, hy⟩))).2
      rcases Nat.lt_or_eq_of_le hk_le with hlt | hEq
      · exact (index_lt_index ((hc' k).contains_lt hy) hlt).le
      · obtain rfl : k = j := Fin.ext hEq
        exact Nat.add_le_add_left (hce.2.2.2.2 y hy).2 _

private theorem update_cluster_erase_spec {c : Fin (universeSize d) → Tree d}
    (hc : ∀ k, (c k).Valid) {i : Fin (universeSize d)} {low : ℕ} {t : Tree d}
    (ht : t.Valid) (hs : ∀ y, t.Contains y ↔ y ≠ low ∧ (c i).Contains y) :
    (∀ k, (Function.update c i t k).Valid) ∧
      ∀ k y, (Function.update c i t k).Contains y ↔
        ¬(k = i ∧ y = low) ∧ (c k).Contains y := by
  constructor
  · intro k
    by_cases h : k = i
    · subst k; simpa only [Function.update_self] using ht
    · simpa only [Function.update_of_ne h] using hc k
  · intro k y
    by_cases h : k = i
    · subst k; simpa only [Function.update_self, true_and] using hs y
    · simp [h]

private theorem cluster_key_eq_iff {d : ℕ} {c : Fin (universeSize d) → Tree d}
    (hc : ∀ k, (c k).Valid) {k : Fin (universeSize d)} {a x : ℕ}
    (ha : (c k).Contains a) :
    k.val * universeSize d + a = x ↔
      k.val = x / universeSize d ∧ a = x % universeSize d := by
  have hcoord := cluster_coordinates (i := k.val) (universeSize_pos d) ((hc k).contains_lt ha)
  constructor
  · rintro rfl; exact ⟨hcoord.1.symm, hcoord.2.symm⟩
  · rintro ⟨hk, ha'⟩
    rw [hk, ha', Nat.mul_comm]
    exact Nat.div_add_mod x (universeSize d)

private theorem contains_node_erase {d m M newMin x low : ℕ}
    {i : Fin (universeSize d)} {s s' : Tree d}
    {c c' : Fin (universeSize d) → Tree d} {M' : ℕ}
    (hc : ∀ k, (c k).Valid)
    (hmin : ∀ k y, (c k).Contains y → m < k.val * universeSize d + y)
    (hcase : (x = m ∧ (c i).Contains low ∧ newMin = i.val * universeSize d + low) ∨
      (x ≠ m ∧ newMin = m ∧ i.val = x / universeSize d ∧ low = x % universeSize d))
    (hcs : ∀ k y, (c' k).Contains y ↔ ¬(k = i ∧ y = low) ∧ (c k).Contains y)
    (y : ℕ) :
    (node (some (newMin, M')) s' c').Contains y ↔
      y ≠ x ∧ (node (some (m, M)) s c).Contains y := by
  simp only [contains_node_some, hcs]
  rcases hcase with ⟨rfl, hclow, rfl⟩ | ⟨hxm, rfl, hi, hlow⟩
  · constructor
    · rintro (rfl | ⟨k, a, ⟨_, ha⟩, rfl⟩)
      · exact ⟨Nat.ne_of_gt (hmin i low hclow), Or.inr ⟨i, low, hclow, rfl⟩⟩
      · exact ⟨Nat.ne_of_gt (hmin k a ha), Or.inr ⟨k, a, ha, rfl⟩⟩
    · rintro ⟨hyx, rfl | ⟨k, a, ha, rfl⟩⟩
      · exact absurd rfl hyx
      · by_cases hka : k = i ∧ a = low
        · rcases hka with ⟨rfl, rfl⟩; exact Or.inl rfl
        · exact Or.inr ⟨k, a, ⟨hka, ha⟩, rfl⟩
  · constructor
    · rintro (rfl | ⟨k, a, ⟨hne, ha⟩, rfl⟩)
      · exact ⟨Ne.symm hxm, Or.inl rfl⟩
      · refine ⟨fun hyx => hne ?_, Or.inr ⟨k, a, ha, rfl⟩⟩
        obtain ⟨hk, ha'⟩ := (cluster_key_eq_iff hc ha).mp hyx
        exact ⟨Fin.ext (hk.trans hi.symm), ha'.trans hlow.symm⟩
    · rintro ⟨hyx, rfl | ⟨k, a, ha, rfl⟩⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨k, a, ⟨?_, ha⟩, rfl⟩
        rintro ⟨rfl, rfl⟩
        rw [hi, hlow, Nat.mul_comm, Nat.div_add_mod] at hyx
        exact hyx rfl

private theorem erase_cluster_branch {s : Tree d} {c : Fin (universeSize d) → Tree d}
    {m M x newMin low cm cM : ℕ} {i : Fin (universeSize d)}
    (hs : s.Valid) (hc : ∀ k, (c k).Valid)
    (ho : ∀ k, s.Contains k.val ↔ (c k).bounds.isSome = true)
    (ih : ∀ {t : Tree d}, t.Valid → ∀ z,
      (t.erase z).Valid ∧ ∀ y, (t.erase z).Contains y ↔ y ≠ z ∧ t.Contains y)
    (hmin_lt : newMin < universeSize (d + 1))
    (hbi : (c i).bounds = some (cm, cM))
    (hlow_eq : cm = cM → low = cm)
    (hmin : ∀ k y, (c k).Contains y → m < k.val * universeSize d + y)
    (hcase : (x = m ∧ (c i).Contains low ∧ newMin = i.val * universeSize d + low) ∨
      (x ≠ m ∧ newMin = m ∧ i.val = x / universeSize d ∧ low = x % universeSize d))
    (hexcl' : ∀ k y, ¬(k = i ∧ y = low) → (c k).Contains y →
      newMin < k.val * universeSize d + y) :
    (let t' :=
      if cm = cM then
        if low = cm then
          let c' := Function.update c i ((c i).withBounds none)
          let s' := erase s i.val
          node (some (newMin, clusterMax newMin s' c')) s' c'
        else node (some (m, M)) s c
      else
        let c' := Function.update c i (erase (c i) low)
        node (some (newMin, clusterMax newMin s c')) s c'
    t'.Valid ∧ ∀ y, t'.Contains y ↔ y ≠ x ∧ (node (some (m, M)) s c).Contains y) := by
  dsimp only
  have finish : ∀ (s' ti : Tree d), s'.Valid → ti.Valid →
      (∀ y, ti.Contains y ↔ y ≠ low ∧ (c i).Contains y) →
      (∀ k, s'.Contains k.val ↔ (Function.update c i ti k).bounds.isSome = true) →
      (node (some (newMin, clusterMax newMin s' (Function.update c i ti))) s'
        (Function.update c i ti)).Valid ∧
      ∀ y, (node (some (newMin, clusterMax newMin s' (Function.update c i ti))) s'
        (Function.update c i ti)).Contains y ↔
        y ≠ x ∧ (node (some (m, M)) s c).Contains y := by
    intro s' ti hsv hti_val hti_set ho'
    obtain ⟨hcv, hcs⟩ := update_cluster_erase_spec hc hti_val hti_set
    exact ⟨valid_node_of_clusterMax hmin_lt hsv hcv ho' fun k y hy =>
        let ⟨hne, hyc⟩ := (hcs k y).mp hy; hexcl' k y hne hyc,
      contains_node_erase hc hmin hcase hcs⟩
  by_cases hcm : cm = cM
  · have hlow : low = cm := hlow_eq hcm
    rw [ite_eq_left hcm, ite_eq_left hlow]
    have hbi' : (c i).bounds = some (cm, cm) := hcm ▸ hbi
    obtain ⟨hci_val, hci_b, hci_none⟩ := empty_of_bounds_eq (hc i) hbi'
    obtain ⟨hsv, hss⟩ := ih hs i.val
    refine finish _ _ hsv hci_val (fun y => ?_) (fun k => ?_)
    · rw [singleton_contains_of_bounds_eq (hc i) hbi', hlow]
      exact ⟨fun hy => False.elim (hci_none y hy), fun h => False.elim (h.1 h.2)⟩
    · rw [hss]
      by_cases hki : k = i
      · subst k; simp [hci_b]
      · have hval : k.val ≠ i.val := fun h => hki (Fin.ext h)
        simp [hki, hval, ho k]
  · rw [ite_eq_right hcm]
    obtain ⟨hci_val, hci_set⟩ := ih (hc i) low
    refine finish _ _ hs hci_val hci_set fun k => ?_
    by_cases hki : k = i
    · subst k
      simp only [Function.update_self, hci_val.bounds_isSome_iff]
      have his : s.Contains i.val := (ho i).mpr (by simp [hbi])
      refine ⟨fun _ => ?_, fun _ => his⟩
      by_cases hlow : low = cm
      · exact ⟨cM, (hci_set cM).mpr ⟨fun h => hcm (hlow.symm.trans h.symm),
          (hc i).contains_maximum hbi⟩⟩
      · exact ⟨cm, (hci_set cm).mpr ⟨fun h => hlow h.symm, (hc i).contains_minimum hbi⟩⟩
    · simpa only [Function.update_of_ne hki] using ho k

private theorem spec_of_not_contains {t : Tree d} (ht : t.Valid) {x : ℕ}
    (hx : ¬t.Contains x) : t.Valid ∧ ∀ y, t.Contains y ↔ y ≠ x ∧ t.Contains y :=
  ⟨ht, fun _ => ⟨fun hy => ⟨fun hyx => hx (hyx ▸ hy), hy⟩, And.right⟩⟩

private theorem eraseTarget_of_ne {d m x : ℕ} {s : Tree d}
    {c : Fin (universeSize d) → Tree d} (hxm : x ≠ m) (hx_lt : x < universeSize (d + 1)) :
    ∃ h : x / universeSize d < universeSize d,
      eraseTarget m x s c = some ⟨m, ⟨x / universeSize d, h⟩, x % universeSize d⟩ :=
  have hdiv : x / universeSize d < universeSize d :=
    (Nat.div_lt_iff_lt_mul (universeSize_pos d)).mpr hx_lt
  ⟨hdiv, by simp [eraseTarget, hxm, hdiv]⟩

private theorem erase_spec {t : Tree d} (ht : t.Valid) (x : ℕ) :
    (t.erase x).Valid ∧ ∀ y, (t.erase x).Contains y ↔ y ≠ x ∧ t.Contains y := by
  induction d generalizing x with
  | zero =>
    cases t with
    | leaf b =>
      rcases b with _ | ⟨m, M⟩
      · exact spec_of_not_contains ht (not_contains_of_bounds_none rfl x)
      · have he := ht.extrema_of_bounds rfl
        have hMlt : M < 2 := by simpa only [universeSize_zero] using he.2.1
        have hmM : m ≤ M := he.1
        have leaf_valid : ∀ a < 2, (leaf (some (a, a))).Valid := fun a ha => by
          simp only [Valid, Extrema, bounds, contains_leaf_some, universeSize_zero]
          exact ⟨le_rfl, ha, Or.inl trivial, Or.inl trivial, fun z hz => by omega⟩
        simp only [erase]
        split_ifs with hboth hxm hxM
        · refine ⟨valid_empty 0, fun y => ?_⟩
          simp only [not_contains_of_bounds_none (t := leaf none) rfl y,
            contains_leaf_some, false_iff, not_and]
          omega
        · refine ⟨leaf_valid M hMlt, fun y => ?_⟩
          simp only [contains_leaf_some]
          omega
        · refine ⟨leaf_valid m (by omega), fun y => ?_⟩
          simp only [contains_leaf_some]
          omega
        · refine ⟨ht, fun y => ?_⟩
          simp only [contains_leaf_some]
          omega
  | succ d ih =>
    cases t with
    | node b s c =>
      rcases b with _ | ⟨m, M⟩
      · exact spec_of_not_contains ht (not_contains_of_bounds_none rfl x)
      · have he := ht.extrema_of_bounds rfl
        by_cases hout : x < m ∨ M < x
        · rw [erase, ite_eq_left hout]
          exact spec_of_not_contains ht fun hx => by have := (he.2.2.2.2 x hx); omega
        · by_cases heq : m = M
          · rw [erase, ite_eq_right hout, ite_eq_left heq]
            have hxm : x = m := by omega
            subst M
            obtain ⟨hv, _, hnone⟩ := empty_of_bounds_eq ht (m := m) rfl
            refine ⟨hv, fun y => ?_⟩
            rw [singleton_contains_of_bounds_eq ht (m := m) rfl y, hxm]
            exact ⟨fun hy => False.elim (hnone y hy), fun h => False.elim (h.1 h.2)⟩
          · have ⟨_, hs, hc, ho, hmin⟩ := ht
            by_cases hxm : x = m
            · -- Deleting the excluded minimum `m`: promote the least cluster key to `newMin`.
              obtain ⟨⟨sm, sM⟩, hbs⟩ : ∃ sb, s.bounds = some sb := by
                rcases (contains_node_some m M s c M).mp he.2.2.2.1 with hMm | ⟨k, y, hy, _⟩
                · exact absurd hMm.symm heq
                · exact Option.isSome_iff_exists.mp
                    (bounds_isSome_of_contains ((ho k).mpr (bounds_isSome_of_contains hy)))
              have hse := hs.extrema_of_bounds hbs
              have hsm_lt : sm < universeSize d := hs.contains_lt hse.2.2.1
              let i : Fin (universeSize d) := ⟨sm, hsm_lt⟩
              obtain ⟨⟨cm, cM⟩, hbi⟩ := Option.isSome_iff_exists.mp ((ho i).mp hse.2.2.1)
              have hce := (hc i).extrema_of_bounds hbi
              let newMin := sm * universeSize d + cm
              have hnewMin_lt : newMin < universeSize (d + 1) :=
                ht.contains_lt ⟨m, M, rfl, Or.inr ⟨i, cm, hce.2.2.1, rfl⟩⟩
              have htarget : eraseTarget m x s c = some ⟨newMin, i, cm⟩ := by
                simp [eraseTarget, hxm, minimum, hbs, hsm_lt, i, hbi, newMin]
              have hexcl' : ∀ k y, ¬(k = i ∧ y = cm) → (c k).Contains y →
                  newMin < k.val * universeSize d + y := by
                intro k y hne hy
                have hik : sm ≤ k.val :=
                  (hse.2.2.2.2 k.val ((ho k).mpr ((hc k).bounds_isSome_iff.mpr ⟨y, hy⟩))).1
                rcases Nat.lt_or_eq_of_le hik with hlt | hEq
                · exact index_lt_index (Nat.lt_of_le_of_lt hce.1 hce.2.1) hlt
                · obtain rfl : k = i := Fin.ext hEq.symm
                  have := (hce.2.2.2.2 y hy).1
                  have : y ≠ cm := fun h => hne ⟨rfl, h⟩
                  dsimp only [newMin, i]
                  omega
              have hres := erase_cluster_branch (m := m) (M := M) (x := x)
                hs hc ho ih hnewMin_lt hbi (fun _ => rfl) hmin (Or.inl ⟨hxm, hce.2.2.1, rfl⟩)
                hexcl'
              rw [erase, ite_eq_right hout, ite_eq_right heq, htarget]
              dsimp only at hres ⊢
              rw [hbi]
              exact hres
            · -- Deleting `x ≠ m` (`m < x ≤ M`): keep `m` and delete `x % u` from `c (x / u)`.
              obtain ⟨hx_div, htarget⟩ := eraseTarget_of_ne (s := s) (c := c) hxm
                (Nat.lt_of_le_of_lt (show x ≤ M by omega) he.2.1)
              let i : Fin (universeSize d) := ⟨x / universeSize d, hx_div⟩
              let low := x % universeSize d
              have hnot_mem_of_not_low : ¬(c i).Contains low →
                  ¬(node (some (m, M)) s c).Contains x := by
                rintro hnot hx_mem
                simp only [contains_node_some] at hx_mem
                rcases hx_mem with rfl | ⟨k, a, ha, hxa⟩
                · exact hxm rfl
                · obtain ⟨hki, halow⟩ := (cluster_key_eq_iff hc ha).mp hxa.symm
                  exact hnot (Fin.ext (show i.val = k.val from hki.symm) ▸
                    (show a = low from halow) ▸ ha)
              rw [erase, ite_eq_right hout, ite_eq_right heq, htarget]
              dsimp only
              cases hbi : (c i).bounds with
              | none =>
                exact spec_of_not_contains ht
                  (hnot_mem_of_not_low (not_contains_of_bounds_none hbi low))
              | some cb =>
                obtain ⟨cm, cM⟩ := cb
                dsimp only
                by_cases hsingleton_miss : cm = cM ∧ low ≠ cm
                · rcases hsingleton_miss with ⟨rfl, hne⟩
                  rw [ite_eq_left rfl, ite_eq_right hne]
                  exact spec_of_not_contains ht (hnot_mem_of_not_low (by
                    rw [singleton_contains_of_bounds_eq (hc i) hbi]; exact hne))
                · have hlow_eq : cm = cM → low = cm := fun hcm =>
                    by_contra fun hl => hsingleton_miss ⟨hcm, hl⟩
                  exact erase_cluster_branch (m := m) (M := M) (x := x)
                    hs hc ho ih (ht.contains_lt he.2.2.1) hbi hlow_eq hmin
                    (Or.inr ⟨hxm, rfl, rfl, rfl⟩) (fun k y _ hy => hmin k y hy)

/-- Deletion of any key preserves the recursive van Emde Boas representation invariant. -/
theorem valid_erase {t : Tree d} (ht : t.Valid) (x : ℕ) : (t.erase x).Valid :=
  (erase_spec ht x).1

/-- Deletion removes `x` and preserves membership of every other key. -/
theorem contains_erase {t : Tree d} (ht : t.Valid) (x y : ℕ) :
    (t.erase x).Contains y ↔ y ≠ x ∧ t.Contains y :=
  (erase_spec ht x).2 y

private theorem clusterMax_eq_of_valid {m M : ℕ} {s : Tree d}
    {c : Fin (universeSize d) → Tree d} (ht : (node (some (m, M)) s c).Valid) :
    clusterMax m s c = M := by
  have he := ht.extrema_of_bounds rfl
  have ⟨_, hs, hc, ho, hmin⟩ := ht
  have hv' := valid_node_of_clusterMax (ht.contains_lt he.2.2.1) hs hc ho hmin
  have he' := hv'.extrema_of_bounds rfl
  have hsame : ∀ z, (node (some (m, clusterMax m s c)) s c).Contains z ↔
      (node (some (m, M)) s c).Contains z := fun z => by simp [contains_node_some]
  have h1 : clusterMax m s c ≤ M := (he.2.2.2.2 _ ((hsame _).mp he'.2.2.2.1)).2
  have h2 : M ≤ clusterMax m s c := (he'.2.2.2.2 _ ((hsame _).mpr he.2.2.2.1)).2
  omega

/-- Deleting a key not represented by a valid tree returns the exact tree `t`. -/
theorem erase_eq_of_not_contains {t : Tree d} (ht : t.Valid) {x : ℕ}
    (hx : ¬t.Contains x) : t.erase x = t := by
  induction d generalizing x with
  | zero =>
    cases t with
    | leaf b =>
      cases b with
      | none => rfl
      | some b =>
        obtain ⟨m, M⟩ := b
        simp only [contains_leaf_some, not_or] at hx
        simp [erase, hx.1, hx.2]
  | succ d ih =>
    cases t with
    | node b s c =>
      rcases b with _ | ⟨m, M⟩
      · rfl
      · have he := ht.extrema_of_bounds rfl
        by_cases hout : x < m ∨ M < x
        · rw [erase, ite_eq_left hout]
        · have hxm : x ≠ m := fun h => hx (h ▸ he.2.2.1)
          have heq : m ≠ M := fun h => hx (by rw [show x = m by omega]; exact he.2.2.1)
          obtain ⟨hx_div, htarget⟩ := eraseTarget_of_ne (s := s) (c := c) hxm
            (Nat.lt_of_le_of_lt (show x ≤ M by omega) he.2.1)
          let i : Fin (universeSize d) := ⟨x / universeSize d, hx_div⟩
          have hnot_low : ¬(c i).Contains (x % universeSize d) := fun hlow =>
            hx ⟨m, M, rfl, Or.inr ⟨i, x % universeSize d, hlow, by
              simpa only [i, Nat.mul_comm] using (Nat.div_add_mod x (universeSize d)).symm⟩⟩
          rw [erase, ite_eq_right hout, ite_eq_right heq, htarget]
          dsimp only
          cases hbi : (c i).bounds with
          | none => rfl
          | some cb =>
            obtain ⟨cm, cM⟩ := cb
            dsimp only
            by_cases hcm : cm = cM
            · subst cM
              have hne : x % universeSize d ≠ cm := fun h =>
                hnot_low (h ▸ (ht.2.2.1 i).contains_minimum hbi)
              rw [ite_eq_left rfl, ite_eq_right hne]
            · rw [ite_eq_right hcm]
              have hc_eq : Function.update c i (erase (c i) (x % universeSize d)) = c := by
                rw [ih (ht.2.2.1 i) hnot_low]
                funext k
                by_cases hk : k = i <;> simp [hk]
              rw [hc_eq, clusterMax_eq_of_valid ht]

end Cslib.DataStructure.VanEmdeBoas.Tree
