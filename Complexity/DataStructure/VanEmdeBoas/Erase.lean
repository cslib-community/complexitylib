/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.VanEmdeBoas.Insert
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
  have he := ht.extrema
  simp only [Extrema, hb] at he
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
    simp only [bounds] at hb
    subst b
    refine ⟨?_, rfl, not_contains_of_bounds_none rfl⟩
    simp [withBounds, Valid, Extrema, bounds, Contains]
  | @node d b s c =>
    simp only [bounds] at hb
    subst b
    obtain ⟨he, hs, hc, ho, hmin⟩ := ht
    simp only [Extrema, bounds] at he
    have hcb : ∀ i, (c i).bounds = none := by
      intro i
      cases hbi : (c i).bounds with
      | none => rfl
      | some b' =>
        obtain ⟨cm, cM⟩ := b'
        have hcm := (hc i).contains_minimum hbi
        have hlt := hmin i cm hcm
        have hle := (he.2.2.2.2 (i.val * universeSize d + cm)
          ⟨m, m, rfl, Or.inr ⟨i, cm, hcm, rfl⟩⟩).2
        omega
    have hsb : s.bounds = none := by
      cases hbs : s.bounds with
      | none => rfl
      | some b' =>
        obtain ⟨sm, sM⟩ := b'
        have hsm := hs.contains_minimum hbs
        have hsmlt := hs.contains_lt hsm
        have his := (ho ⟨sm, hsmlt⟩).mp hsm
        simp [hcb ⟨sm, hsmlt⟩] at his
    have hbnone : (node none s c).bounds = none := rfl
    refine ⟨⟨?_, hs, hc, ho, hsb, hcb⟩, rfl, not_contains_of_bounds_none hbnone⟩
    simp only [Extrema, hbnone]
    exact not_contains_of_bounds_none hbnone

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
    have hcnone : ∀ k y, ¬(c' k).Contains y := by
      intro k y hy
      have hsk : s'.Contains k.val := (ho' k).mpr ((hc' k).bounds_isSome_iff.mpr ⟨y, hy⟩)
      exact not_contains_of_bounds_none hbs k.val hsk
    have hmax : clusterMax newMin s' c' = newMin := by
      simp [clusterMax, maximum, hbs]
    rw [hmax]
    simp only [Extrema, bounds, contains_node_some]
    refine ⟨le_rfl, hmin_lt, Or.inl trivial, Or.inl trivial, ?_⟩
    rintro z (rfl | ⟨k, y, hy, _⟩)
    · exact ⟨le_rfl, le_rfl⟩
    · exact False.elim (hcnone k y hy)
  | some sb =>
    obtain ⟨sm, sM⟩ := sb
    have hse := hs'.extrema
    simp only [Extrema, hbs] at hse
    let j : Fin (universeSize d) := ⟨sM, hse.2.1⟩
    have hbj_some : (c' j).bounds.isSome = true := (ho' j).mp hse.2.2.2.1
    cases hbj : (c' j).bounds with
    | none => simp [hbj] at hbj_some
    | some cb =>
      obtain ⟨cm, cM⟩ := cb
      have hce := (hc' j).extrema
      simp only [Extrema, hbj] at hce
      have hmax : clusterMax newMin s' c' = sM * universeSize d + cM := by
        simp [clusterMax, maximum, hbs, hse.2.1, j, hbj]
      rw [hmax]
      simp only [Extrema, bounds]
      have hgt : newMin < sM * universeSize d + cM := hexcl j cM hce.2.2.2.1
      have hM_lt : sM * universeSize d + cM < universeSize (d + 1) := by
        have := cluster_key_lt_of_lt (b := 0) hce.2.1 hse.2.1
        rwa [Nat.add_zero] at this
      refine ⟨hgt.le, hM_lt, ⟨newMin, _, rfl, Or.inl rfl⟩,
        ⟨newMin, _, rfl, Or.inr ⟨j, cM, hce.2.2.2.1, rfl⟩⟩, ?_⟩
      intro z hz
      simp only [contains_node_some] at hz
      rcases hz with rfl | ⟨k, y, hy, rfl⟩
      · exact ⟨le_rfl, hgt.le⟩
      · refine ⟨(hexcl k y hy).le, ?_⟩
        have hsk : s'.Contains k.val := (ho' k).mpr ((hc' k).bounds_isSome_iff.mpr ⟨y, hy⟩)
        have hk_le : k.val ≤ sM := (hse.2.2.2.2 k.val hsk).2
        by_cases hkj : k = j
        · subst k
          exact Nat.add_le_add_left (hce.2.2.2.2 y hy).2 (j.val * universeSize d)
        · have hk_lt : k.val < sM := by
            have : k.val ≠ sM := fun h => hkj (Fin.ext h)
            omega
          exact (cluster_key_lt_of_lt ((hc' k).contains_lt hy) hk_lt).le

private theorem update_cluster_erase_spec {c : Fin (universeSize d) → Tree d}
    (hc : ∀ k, (c k).Valid) {i : Fin (universeSize d)} {low : ℕ} {t : Tree d}
    (ht : t.Valid) (hs : ∀ y, t.Contains y ↔ y ≠ low ∧ (c i).Contains y) :
    (∀ k, (Function.update c i t k).Valid) ∧
      ∀ k y, (Function.update c i t k).Contains y ↔
        ¬(k = i ∧ y = low) ∧ (c k).Contains y := by
  constructor
  · intro k
    by_cases h : k = i
    · subst k
      simpa only [Function.update_self] using ht
    · simpa only [Function.update_of_ne h] using hc k
  · intro k y
    by_cases h : k = i
    · subst k
      simpa only [Function.update_self, true_and] using hs y
    · simp [h]

/-- One recursive deletion step at a valid occupied node. Removing `low` from cluster `i` and
installing `newMin` as the local minimum yields a valid node representing the old set without
`x`, provided `hkeys` describes that set as `newMin` plus the remaining cluster keys. -/
private theorem erase_cluster_branch {s : Tree d} {c : Fin (universeSize d) → Tree d}
    {m M x newMin low cm cM : ℕ} {i : Fin (universeSize d)}
    (ht : (node (some (m, M)) s c).Valid)
    (ih : ∀ {t : Tree d}, t.Valid → ∀ z,
      (t.erase z).Valid ∧ ∀ y, (t.erase z).Contains y ↔ y ≠ z ∧ t.Contains y)
    (hmin_lt : newMin < universeSize (d + 1))
    (hbi : (c i).bounds = some (cm, cM))
    (hlow_eq : cm = cM → low = cm)
    (hexcl' : ∀ k y, ¬(k = i ∧ y = low) → (c k).Contains y →
      newMin < k.val * universeSize d + y)
    (hkeys : ∀ y, (y = newMin ∨ ∃ k a, (¬(k = i ∧ a = low) ∧ (c k).Contains a) ∧
        y = k.val * universeSize d + a) ↔
      y ≠ x ∧ (node (some (m, M)) s c).Contains y) :
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
  have hs := ht.summary
  have hc := ht.cluster
  have ho := ht.summary_contains_iff
  -- Every update of cluster `i` that removes exactly `low` has the represented set `hkeys`.
  have hset_eq : ∀ (s' : Tree d) (c' : Fin (universeSize d) → Tree d) (M' : ℕ),
      (∀ k y, (c' k).Contains y ↔ ¬(k = i ∧ y = low) ∧ (c k).Contains y) →
        ∀ y, (node (some (newMin, M')) s' c').Contains y ↔
          y ≠ x ∧ (node (some (m, M)) s c).Contains y := by
    intro s' c' M' hcs y
    rw [← hkeys y]
    simp only [contains_node_some, hcs]
  dsimp only
  by_cases hcm : cm = cM
  · have hlow : low = cm := hlow_eq hcm
    rw [ite_eq_left hcm, ite_eq_left hlow]
    have hbi' : (c i).bounds = some (cm, cm) := hcm ▸ hbi
    obtain ⟨hci_val, hci_b, hci_none⟩ := empty_of_bounds_eq (hc i) hbi'
    have hci_set : ∀ y, ((c i).withBounds none).Contains y ↔ y ≠ low ∧ (c i).Contains y := by
      intro y
      rw [singleton_contains_of_bounds_eq (hc i) hbi', hlow]
      exact ⟨fun hy => False.elim (hci_none y hy), fun h => False.elim (h.1 h.2)⟩
    obtain ⟨hcv, hcs⟩ := update_cluster_erase_spec hc hci_val hci_set
    obtain ⟨hsv, hss⟩ := ih hs i.val
    let c' := Function.update c i ((c i).withBounds none)
    let s' := erase s i.val
    have ho' : ∀ k, s'.Contains k.val ↔ (c' k).bounds.isSome = true := by
      intro k
      rw [hss]
      by_cases hki : k = i
      · subst k
        simp [c', hci_b]
      · have hval : k.val ≠ i.val := fun h => hki (Fin.ext h)
        simp [c', hki, hval, ho k]
    have hexcl : ∀ k y, (c' k).Contains y → newMin < k.val * universeSize d + y := by
      intro k y hy
      obtain ⟨hne, hyc⟩ := (hcs k y).mp hy
      exact hexcl' k y hne hyc
    exact ⟨valid_node_of_clusterMax hmin_lt hsv hcv ho' hexcl, hset_eq s' c' _ hcs⟩
  · rw [ite_eq_right hcm]
    obtain ⟨hci_val, hci_set⟩ := ih (hc i) low
    obtain ⟨hcv, hcs⟩ := update_cluster_erase_spec hc hci_val hci_set
    let c' := Function.update c i (erase (c i) low)
    have hci_nonempty : ∃ y, ((c i).erase low).Contains y := by
      by_cases hlow : low = cm
      · refine ⟨cM, (hci_set cM).mpr ⟨fun h => hcm (hlow.symm.trans h.symm), ?_⟩⟩
        exact (hc i).contains_maximum hbi
      · refine ⟨cm, (hci_set cm).mpr ⟨fun h => hlow h.symm, ?_⟩⟩
        exact (hc i).contains_minimum hbi
    have ho' : ∀ k, s.Contains k.val ↔ (c' k).bounds.isSome = true := by
      intro k
      by_cases hki : k = i
      · subst k
        simp only [c', Function.update_self, hci_val.bounds_isSome_iff]
        have his : s.Contains i.val := (ho i).mpr (by simp only [hbi, Option.isSome_some])
        exact ⟨fun _ => hci_nonempty, fun _ => his⟩
      · simpa only [c', Function.update_of_ne hki] using ho k
    have hexcl : ∀ k y, (c' k).Contains y → newMin < k.val * universeSize d + y := by
      intro k y hy
      obtain ⟨hne, hyc⟩ := (hcs k y).mp hy
      exact hexcl' k y hne hyc
    exact ⟨valid_node_of_clusterMax hmin_lt hs hcv ho' hexcl, hset_eq s c' _ hcs⟩

private theorem clusterMax_eq_of_valid {m M : ℕ} {s : Tree d}
    {c : Fin (universeSize d) → Tree d} (ht : (node (some (m, M)) s c).Valid) :
    clusterMax m s c = M := by
  have hv' := valid_node_of_clusterMax (ht.contains_lt (ht.contains_minimum rfl)) ht.summary
    ht.cluster ht.summary_contains_iff fun _ _ => ht.min_lt_cluster
  -- Both nodes represent the same keys, so their cached maxima bound each other.
  have hsame : ∀ z, (node (some (m, clusterMax m s c)) s c).Contains z ↔
      (node (some (m, M)) s c).Contains z := by
    intro z
    simp
  have h1 := ht.le_max_of_contains rfl ((hsame _).mp (hv'.contains_maximum rfl))
  have h2 := hv'.le_max_of_contains rfl ((hsame _).mpr (ht.contains_maximum rfl))
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
      cases b with
      | none => rfl
      | some b =>
        obtain ⟨m, M⟩ := b
        by_cases hout : x < m ∨ M < x
        · rw [erase, ite_eq_left hout]
        -- Otherwise `m < x ≤ M`, so `x` is routed to cluster `x / u` at low part `x % u`.
        have hxm : x ≠ m := fun h => hx (h ▸ ht.contains_minimum rfl)
        have heq : m ≠ M := by omega
        have hx_div : x / universeSize d < universeSize d :=
          (Nat.div_lt_iff_lt_mul (universeSize_pos d)).mpr
            ((show x ≤ M by omega).trans_lt (ht.contains_lt (ht.contains_maximum rfl)))
        let i : Fin (universeSize d) := ⟨x / universeSize d, hx_div⟩
        let low := x % universeSize d
        have hnot_low : ¬(c i).Contains low := fun hlow => hx ((contains_node_some ..).mpr
          (Or.inr ⟨i, low, hlow, (Nat.div_add_mod' x (universeSize d)).symm⟩))
        have htarget : eraseTarget m x s c = some ⟨m, i, low⟩ := by
          simp [eraseTarget, hxm, hx_div, i, low]
        rw [erase, ite_eq_right hout, ite_eq_right heq, htarget]
        dsimp only
        cases hbi : (c i).bounds with
        | none => rfl
        | some cb =>
          obtain ⟨cm, cM⟩ := cb
          dsimp only
          by_cases hcm : cm = cM
          · -- A singleton cluster that does not contain `low` is left alone.
            subst cM
            have hne : low ≠ cm := fun h =>
              hnot_low (h ▸ (ht.cluster i).contains_minimum hbi)
            rw [ite_eq_left rfl, ite_eq_right hne]
          · -- The recursive deletion is the identity, and so is the rebuilt header.
            rw [ite_eq_right hcm, ih (ht.cluster i) hnot_low, Function.update_eq_self,
              clusterMax_eq_of_valid ht]

/-- Deleting an absent key leaves both the invariant and the represented set unchanged. -/
private theorem erase_spec_of_not_contains {t : Tree d} (ht : t.Valid) {x : ℕ}
    (hx : ¬t.Contains x) :
    (t.erase x).Valid ∧ ∀ y, (t.erase x).Contains y ↔ y ≠ x ∧ t.Contains y := by
  rw [erase_eq_of_not_contains ht hx]
  exact ⟨ht, fun y => ⟨fun hy => ⟨fun hyx => hx (hyx ▸ hy), hy⟩, And.right⟩⟩

/-- Deleting the excluded minimum `m` of a valid node with `m < M` promotes the least cluster key
`newMin` to the local minimum and deletes it from its cluster. -/
private theorem erase_spec_min {s : Tree d} {c : Fin (universeSize d) → Tree d} {m M : ℕ}
    (ht : (node (some (m, M)) s c).Valid) (heq : m ≠ M)
    (ih : ∀ {t : Tree d}, t.Valid → ∀ z,
      (t.erase z).Valid ∧ ∀ y, (t.erase z).Contains y ↔ y ≠ z ∧ t.Contains y) :
    let t' := (node (some (m, M)) s c).erase m
    t'.Valid ∧ ∀ y, t'.Contains y ↔ y ≠ m ∧ (node (some (m, M)) s c).Contains y := by
  have hmM := ht.min_le_of_contains rfl (ht.contains_maximum rfl)
  have hout : ¬(m < m ∨ M < m) := by omega
  -- Since `m < M`, the maximum lies in some cluster, so the summary is occupied.
  obtain ⟨kM, yM, hyM, -⟩ :=
    ((contains_node_some ..).mp (ht.contains_maximum rfl)).resolve_left (Ne.symm heq)
  obtain ⟨⟨sm, sM⟩, hbs⟩ :=
    Option.isSome_iff_exists.mp (bounds_isSome_of_contains (ht.summary_contains hyM))
  -- The least cluster key lies in the cluster `i` named by the summary minimum.
  have hsm := ht.summary.contains_minimum hbs
  have hsm_lt := ht.summary.contains_lt hsm
  let i : Fin (universeSize d) := ⟨sm, hsm_lt⟩
  obtain ⟨⟨cm, cM⟩, hbi⟩ := Option.isSome_iff_exists.mp ((ht.summary_contains_iff i).mp hsm)
  have hcm := (ht.cluster i).contains_minimum hbi
  let newMin := sm * universeSize d + cm
  have hnew : newMin = i.val * universeSize d + cm := rfl
  have hm_new : m < newMin := ht.min_lt_cluster hcm
  have hnewMin_lt : newMin < universeSize (d + 1) :=
    ht.contains_lt ((contains_node_some ..).mpr (Or.inr ⟨i, cm, hcm, rfl⟩))
  have htarget : eraseTarget m m s c = some ⟨newMin, i, cm⟩ := by
    simp [eraseTarget, minimum, hbs, hsm_lt, i, hbi, newMin]
  -- Every other cluster key lies above `newMin`, the least cluster key.
  have hexcl' : ∀ k y, ¬(k = i ∧ y = cm) → (c k).Contains y →
      newMin < k.val * universeSize d + y := by
    intro k y hne hy
    have hik : sm ≤ k.val := ht.summary.min_le_of_contains hbs (ht.summary_contains hy)
    rcases Nat.lt_or_eq_of_le hik with hlt | hik
    · exact cluster_key_lt_of_lt ((ht.cluster i).contains_lt hcm) hlt
    · obtain rfl : i = k := Fin.ext hik
      have hcmy := (ht.cluster i).min_le_of_contains hbi hy
      have hyne : y ≠ cm := fun h => hne ⟨rfl, h⟩
      omega
  have hkeys : ∀ y, (y = newMin ∨ ∃ k a, (¬(k = i ∧ a = cm) ∧ (c k).Contains a) ∧
      y = k.val * universeSize d + a) ↔
      y ≠ m ∧ (node (some (m, M)) s c).Contains y := by
    intro y
    simp only [contains_node_some]
    constructor
    · rintro (rfl | ⟨k, a, ⟨-, ha⟩, rfl⟩)
      · exact ⟨by omega, Or.inr ⟨i, cm, hcm, rfl⟩⟩
      · exact ⟨by have := ht.min_lt_cluster ha; omega, Or.inr ⟨k, a, ha, rfl⟩⟩
    · rintro ⟨hym, rfl | ⟨k, a, ha, rfl⟩⟩
      · exact absurd rfl hym
      by_cases hka : k = i ∧ a = cm
      · obtain ⟨rfl, rfl⟩ := hka
        exact Or.inl rfl
      · exact Or.inr ⟨k, a, ⟨hka, ha⟩, rfl⟩
  have hres := erase_cluster_branch (x := m) ht ih hnewMin_lt hbi (fun _ => rfl) hexcl' hkeys
  dsimp only
  rw [erase, ite_eq_right hout, ite_eq_right heq, htarget]
  dsimp only at hres ⊢
  rw [hbi]
  exact hres

/-- Deleting a cluster key `x = j * u + a` of a valid node keeps the local minimum `m` and
deletes `a` from cluster `j`. -/
private theorem erase_spec_cluster {s : Tree d} {c : Fin (universeSize d) → Tree d}
    {m M a : ℕ} {j : Fin (universeSize d)}
    (ht : (node (some (m, M)) s c).Valid)
    (ih : ∀ {t : Tree d}, t.Valid → ∀ z,
      (t.erase z).Valid ∧ ∀ y, (t.erase z).Contains y ↔ y ≠ z ∧ t.Contains y)
    (ha : (c j).Contains a) :
    let x := j.val * universeSize d + a
    let t' := (node (some (m, M)) s c).erase x
    t'.Valid ∧ ∀ y, t'.Contains y ↔ y ≠ x ∧ (node (some (m, M)) s c).Contains y := by
  intro x
  have hx : (node (some (m, M)) s c).Contains x :=
    (contains_node_some ..).mpr (Or.inr ⟨j, a, ha, rfl⟩)
  have ha_lt := (ht.cluster j).contains_lt ha
  have hxm : m < x := ht.min_lt_cluster ha
  have hxM := ht.le_max_of_contains rfl hx
  have hout : ¬(x < m ∨ M < x) := by omega
  have heq : m ≠ M := by omega
  have hcoord := cluster_coordinates (i := j.val) (universeSize_pos d) ha_lt
  have htarget : eraseTarget m x s c = some ⟨m, j, a⟩ := by
    simp [eraseTarget, x, hxm.ne', hcoord.1, hcoord.2]
  obtain ⟨⟨cm, cM⟩, hbi⟩ := Option.isSome_iff_exists.mp (bounds_isSome_of_contains ha)
  -- In a singleton cluster, the represented key `a` must be its only key.
  have hlow_eq : cm = cM → a = cm := by
    rintro rfl
    exact (singleton_contains_of_bounds_eq (ht.cluster j) hbi a).mp ha
  have hkeys : ∀ y, (y = m ∨ ∃ k b, (¬(k = j ∧ b = a) ∧ (c k).Contains b) ∧
      y = k.val * universeSize d + b) ↔
      y ≠ x ∧ (node (some (m, M)) s c).Contains y := by
    intro y
    simp only [contains_node_some]
    constructor
    · rintro (rfl | ⟨k, b, ⟨hne, hb⟩, rfl⟩)
      · exact ⟨hxm.ne, Or.inl rfl⟩
      · refine ⟨fun hyx => hne ?_, Or.inr ⟨k, b, hb, rfl⟩⟩
        have := (cluster_key_eq_iff ((ht.cluster k).contains_lt hb) ha_lt).mp hyx
        exact ⟨Fin.ext this.1, this.2⟩
    · rintro ⟨hyx, rfl | ⟨k, b, hb, rfl⟩⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨k, b, ⟨?_, hb⟩, rfl⟩
        rintro ⟨rfl, rfl⟩
        exact hyx rfl
  dsimp only
  rw [erase, ite_eq_right hout, ite_eq_right heq, htarget]
  dsimp only
  rw [hbi]
  exact erase_cluster_branch ht ih (ht.contains_lt (ht.contains_minimum rfl)) hbi hlow_eq
    (fun _ _ _ hy => ht.min_lt_cluster hy) hkeys

private theorem erase_spec {t : Tree d} (ht : t.Valid) (x : ℕ) :
    (t.erase x).Valid ∧ ∀ y, (t.erase x).Contains y ↔ y ≠ x ∧ t.Contains y := by
  by_cases hx : t.Contains x
  swap
  · exact erase_spec_of_not_contains ht hx
  induction d generalizing x with
  | zero =>
    cases t with
    | leaf b =>
      cases b with
      | none => exact absurd hx (not_contains_of_bounds_none rfl x)
      | some b =>
        obtain ⟨m, M⟩ := b
        -- A depth-zero leaf stores at most the two keys `m ≤ M < 2`.
        have hmM := ht.min_le_of_contains rfl (ht.contains_maximum rfl)
        have hM := ht.contains_lt (ht.contains_maximum rfl)
        simp only [contains_leaf_some, universeSize_zero] at hx hM
        simp only [erase]
        split_ifs
        · exact ⟨valid_empty 0, fun y => by simp [Contains]; omega⟩
        all_goals
          refine ⟨?_, fun y => ?_⟩
          · simp only [Valid, Extrema, bounds, contains_leaf_some, universeSize_zero, or_self,
              forall_eq, true_and]
            omega
          · simp only [contains_leaf_some]
            omega
  | succ d ih =>
    have ih' : ∀ {t : Tree d}, t.Valid → ∀ z,
        (t.erase z).Valid ∧ ∀ y, (t.erase z).Contains y ↔ y ≠ z ∧ t.Contains y := by
      intro t ht z
      by_cases hz : t.Contains z
      · exact ih ht z hz
      · exact erase_spec_of_not_contains ht hz
    cases t with
    | node b s c =>
      cases b with
      | none => exact absurd hx (not_contains_of_bounds_none rfl x)
      | some b =>
        obtain ⟨m, M⟩ := b
        by_cases heq : m = M
        · -- A singleton node: clearing the local header clears the whole node.
          subst M
          have hxm : x = m := (singleton_contains_of_bounds_eq ht rfl x).mp hx
          subst x
          have hout : ¬(m < m ∨ m < m) := by omega
          rw [erase, ite_eq_right hout, ite_eq_left rfl]
          obtain ⟨hv, _, hnone⟩ := empty_of_bounds_eq ht (m := m) rfl
          refine ⟨hv, fun y => ?_⟩
          rw [singleton_contains_of_bounds_eq ht (m := m) rfl y]
          exact ⟨fun hy => False.elim (hnone y hy), fun h => False.elim (h.1 h.2)⟩
        rcases (contains_node_some ..).mp hx with rfl | ⟨j, a, ha, rfl⟩
        · exact erase_spec_min ht heq ih'
        · exact erase_spec_cluster ht ih' ha

/-- Deletion of any key preserves the recursive van Emde Boas representation invariant. -/
theorem valid_erase {t : Tree d} (ht : t.Valid) (x : ℕ) : (t.erase x).Valid :=
  (erase_spec ht x).1

/-- Deletion removes `x` and preserves membership of every other key. -/
theorem contains_erase {t : Tree d} (ht : t.Valid) (x y : ℕ) :
    (t.erase x).Contains y ↔ y ≠ x ∧ t.Contains y :=
  (erase_spec ht x).2 y

end Cslib.DataStructure.VanEmdeBoas.Tree
