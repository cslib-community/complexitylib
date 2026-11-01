/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Prefixes
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.PrefixPartition
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Values
import Complexity.Foundations.Data.Nat.Radix

/-!
# Completed native query tasks

A full prefix is the same leaf decoded from its actual native decimal code. Its
used-count is the existing signed order, and its initial-P0 count selects the existing
`starBelow` box. These finite readbacks connect native leaf arithmetic to the original
box-query value without supplying an intermediate layout or value certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Finset Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The real leaf of a completed prefix, retaining each original term in its original level. -/
@[expose] def completeLeaf {L : ℕ} (xs : List Term) (h : xs.length = L) : Leaf L :=
  fun i => xs.get ⟨i.val, by omega⟩

/-- Reading every completed prefix term recovers that prefix exactly. -/
theorem ofFn_completeLeaf {L : ℕ} (xs : List Term) (h : xs.length = L) :
    List.ofFn (completeLeaf xs h) = xs := by
  subst L
  exact List.ofFn_get xs

/-- The native prefix code uses precisely the existing leaf-array indexing. -/
theorem prefixCode_ofFn {L : ℕ} (τ : Leaf L) :
    prefixCode (List.ofFn τ) = (Encoding.leafIndex τ).val := by
  rw [prefixCode, List.map_ofFn, Nat.ofDigits_ofFn_eq_sum]
  rfl

/-- The full prefix and actual decoded leaf have the same original numeric array position. -/
theorem prefixCode_completeLeaf {L : ℕ} (xs : List Term) (h : xs.length = L) :
    prefixCode xs = (Encoding.leafIndex (completeLeaf xs h)).val := by
  calc
    prefixCode xs = prefixCode (List.ofFn (completeLeaf xs h)) :=
      congrArg prefixCode (ofFn_completeLeaf xs h).symm
    _ = _ := prefixCode_ofFn _

/-- Native decimal decoding of the completed prefix recovers the actual leaf. -/
theorem leafAt_prefixCode {L : ℕ} (xs : List Term) (h : xs.length = L) :
    BoxTable.leafAt ⟨prefixCode xs, by simpa only [← h] using prefixCode_lt xs⟩ =
      completeLeaf xs h := by
  have hi : (⟨prefixCode xs, by simpa only [← h] using prefixCode_lt xs⟩ : Fin (10 ^ L)) =
      Encoding.leafIndex (completeLeaf xs h) := Fin.ext (prefixCode_completeLeaf xs h)
  rw [hi]
  exact BoxTable.leafAt_leafIndex _

private theorem compatible_iff_get {L : ℕ} (η : OutStr L) (k : ℕ) (xs : List Term) :
    Compatible η k xs ↔ ∀ i : Fin xs.length, (xs.get i).Contributes (outAt η (k + i.val)) := by
  induction xs generalizing k with
  | nil => simp [Compatible]
  | cons lam xs ih =>
    simp only [Compatible, List.length_cons, Fin.forall_fin_succ, List.get_eq_getElem,
      List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_zero, Nat.add_zero,
      Fin.val_succ, ih]
    simp only [Nat.add_left_comm, Nat.add_comm]

/-- Compatibility of a complete tuple is exactly the existing contribution relation. -/
theorem compatible_ofFn_iff {L : ℕ} (η : OutStr L) (τ : Leaf L) :
    Compatible η 0 (List.ofFn τ) ↔ Leaf.Contributes τ η := by
  constructor
  · intro hc i
    have hh := (compatible_iff_get η 0 (List.ofFn τ)).mp hc
      ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩
    simpa [outAt, i.isLt] using hh
  · intro hc
    apply (compatible_iff_get η 0 (List.ofFn τ)).mpr
    intro i
    have hi : i.val < L := by simpa only [List.length_ofFn] using i.isLt
    simpa [outAt, hi] using hc ⟨i.val, hi⟩

private theorem usedFrom_eq_sum_get {L : ℕ} (η : OutStr L) (k : ℕ) (xs : List Term) :
    usedFrom η k xs = ∑ i : Fin xs.length,
      if (outAt η (k + i.val)).IsInner ∧ xs.get i ≠ .P0 then 1 else 0 := by
  induction xs generalizing k with
  | nil => simp [usedFrom]
  | cons lam xs ih =>
    simp only [usedFrom, List.length_cons]
    rw [Fin.sum_univ_succ, ih]
    simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ,
      Fin.val_zero, Fin.val_succ, Nat.add_zero, Nat.add_left_comm, Nat.add_comm]
    rfl

/-- The full used-count is the number of inner positions selecting a non-P0 term. -/
theorem usedFrom_ofFn {L : ℕ} (η : OutStr L) (τ : Leaf L) :
    usedFrom η 0 (List.ofFn τ) = ((innerSetO η).filter fun i => τ i ≠ .P0).card := by
  have hh := usedFrom_eq_sum_get η 0 (List.ofFn τ)
  rw [hh]
  calc
    _ = ∑ i : Fin L, if (η i).IsInner ∧ τ i ≠ .P0 then 1 else 0 := by
      apply Fintype.sum_equiv (finCongr (show (List.ofFn τ).length = L from List.length_ofFn)) _ _
      intro i
      have hi : i.val < L := by simpa only [List.length_ofFn] using i.isLt
      simp [outAt, hi, finCongr, Fin.cast]
      rfl
    _ = _ := by
      have hset : (univ.filter fun i : Fin L => (η i).IsInner ∧ τ i ≠ .P0) =
          (innerSetO η).filter (fun i => τ i ≠ .P0) := by
        ext i
        simp [innerSetO]
      simpa only [sum_boole, Nat.cast_id] using congrArg Finset.card hset

/-- With actual contribution, native used-count is exactly the original signed order. -/
theorem usedFrom_ofFn_eq_order {L m : ℕ} (η : OutStr L) (τ : Leaf L)
    (hη : (innerSetO η).card = m) (hτ : Leaf.Contributes τ η) :
    (usedFrom η 0 (List.ofFn τ) : ℤ) = order m τ := by
  have hp := P0Levels_subset hτ
  have hset : (innerSetO η).filter (fun i => τ i ≠ .P0) = innerSetO η \ P0Levels τ := by
    ext i
    simp
  rw [usedFrom_ofFn, hset, card_sdiff_of_subset hp, hη, order]
  have hc := card_le_card hp
  omega

/-- A complete good task is exactly a contributing leaf within the original order budget. -/
theorem Good_ofFn_iff {L m t : ℕ} (η : OutStr L) (hη : (innerSetO η).card = m)
    (τ : Leaf L) :
    Good η t (List.ofFn τ) ↔ Leaf.Contributes τ η ∧ order m τ ≤ (t : ℤ) := by
  simp only [Good, List.length_ofFn, le_refl, true_and, compatible_ofFn_iff]
  constructor
  · rintro ⟨hc, hu⟩
    exact ⟨hc, by rw [← usedFrom_ofFn_eq_order η τ hη hc]; exact_mod_cast hu⟩
  · rintro ⟨hc, ho⟩
    exact ⟨hc, by rw [← usedFrom_ofFn_eq_order η τ hη hc] at ho; exact_mod_cast ho⟩

/-- Complete compatible prefixes give actual contributing leaves. -/
theorem completeLeaf_contributes {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (h : xs.length = L) : Leaf.Contributes (completeLeaf xs h) η := by
  rw [← compatible_ofFn_iff, ofFn_completeLeaf]
  exact hx.2.1

private theorem starsFrom_eq_sum_get {L : ℕ} (η : OutStr L) (k : ℕ) (xs : List Term) :
    starsFrom η k xs = ∑ i : Fin xs.length,
      if (outAt η (k + i.val)).IsInner ∧
        (∀ j : Fin xs.length, j ≤ i → (outAt η (k + j.val)).IsInner → xs.get j = .P0)
      then 1 else 0 := by
  induction xs generalizing k with
  | nil => simp [starsFrom]
  | cons lam xs ih =>
    simp only [starsFrom, List.length_cons, Fin.sum_univ_succ, Fin.forall_fin_succ,
      Fin.val_zero, Fin.val_succ, List.get_eq_getElem, List.getElem_cons_zero,
      List.getElem_cons_succ, Nat.add_zero, Fin.le_zero_iff, Fin.zero_le,
      Fin.succ_le_succ_iff, Fin.succ_ne_zero]
    by_cases hi : (outAt η k).IsInner <;> by_cases hp : lam = .P0
    all_goals simp [hi, hp, ih, Nat.add_left_comm, Nat.add_comm]

private theorem starsFrom_ofFn_eq_sum {L : ℕ} (η : OutStr L) (τ : Leaf L) :
    starsFrom η 0 (List.ofFn τ) = ∑ i : Fin L,
      if (η i).IsInner ∧ (∀ j : Fin L, j ≤ i → (η j).IsInner → τ j = .P0)
      then 1 else 0 := by
  rw [starsFrom_eq_sum_get]
  let e : Fin (List.ofFn τ).length ≃ Fin L :=
    finCongr (show (List.ofFn τ).length = L from List.length_ofFn)
  apply Fintype.sum_equiv e _ _
  intro i
  have hi : i.val < L := by simpa only [List.length_ofFn] using i.isLt
  have hpred :
      (∀ j : Fin (List.ofFn τ).length, j ≤ i →
        (outAt η (0 + j.val)).IsInner → (List.ofFn τ).get j = .P0) ↔
      (∀ j : Fin L, j ≤ e i → (η j).IsInner → τ j = .P0) := by
    constructor
    · intro h j hji hj
      have hs := h (e.symm j) (by exact hji)
      have hjL : (e.symm j).val < L := j.isLt
      simpa [outAt, hjL, e, finCongr, Fin.cast] using hs (by
        simpa [outAt, hjL, e, finCongr, Fin.cast] using hj)
    · intro h j hji hj
      have hjL : j.val < L := by simpa only [List.length_ofFn] using j.isLt
      have hs := h (e j) (by exact hji) (by
        simpa [outAt, hjL, e, finCongr, Fin.cast] using hj)
      simpa [e, finCongr, Fin.cast] using hs
  simp only [hpred]
  have he : e i = ⟨i.val, hi⟩ := rfl
  simp only [Nat.zero_add, outAt, dite_eq_left hi, he]

/-- The native initial-P0 count is exactly the existing canonical output box's star count. -/
theorem starsFrom_ofFn {L : ℕ} (η : OutStr L) (τ : Leaf L) :
    starsFrom η 0 (List.ofFn τ) = (starBelow η τ).starLevels.card := by
  rw [starsFrom_ofFn_eq_sum, starBelow, Cube.starLevels_starAt]
  have hpred (i : Fin L) :
      ((η i).IsInner ∧ ∀ j : Fin L, j ≤ i → (η j).IsInner → τ j = .P0) ↔
      i ∈ initialLevels (innerSetO η) (P0LevelsWithin (innerSetO η) τ) := by
    simp only [initialLevels, mem_filter, mem_innerSetO]
    constructor
    · rintro ⟨hi, h⟩
      refine ⟨hi, fun j hj => ?_⟩
      have hjQ := (mem_sdiff.mp hj).1
      have hjnot := (mem_sdiff.mp hj).2
      by_contra hn
      exact hjnot (mem_filter.mpr ⟨hjQ, h j (le_of_not_gt hn) (mem_innerSetO.mp hjQ)⟩)
    · rintro ⟨hi, h⟩
      refine ⟨hi, fun j hji hj => ?_⟩
      by_contra hn
      exact not_lt_of_ge hji (h j (mem_sdiff.mpr
        ⟨mem_innerSetO.mpr hj, by simp [P0LevelsWithin, hn]⟩))
  simp_rw [hpred]
  simp

/-- The actual full-prefix used scalar equals the original leaf's signed order. -/
theorem completeLeaf_used {L m t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (h : xs.length = L) (hη : (innerSetO η).card = m) :
    (usedFrom η 0 xs : ℤ) = order m (completeLeaf xs h) := by
  simpa only [ofFn_completeLeaf] using usedFrom_ofFn_eq_order η (completeLeaf xs h)
    hη (completeLeaf_contributes hx h)

/-- The actual full-prefix initial-P0 scalar is the selected canonical box's star count. -/
theorem completeLeaf_stars {L : ℕ} (η : OutStr L) (xs : List Term) (h : xs.length = L) :
    starsFrom η 0 xs = (starBelow η (completeLeaf xs h)).starLevels.card := by
  simpa only [ofFn_completeLeaf] using starsFrom_ofFn η (completeLeaf xs h)

/-- Native multiplication/addition computes the exact existing key of the threshold box. -/
theorem completeLeaf_key {L : ℕ} (η : OutStr L) (xs : List Term) (h : xs.length = L) :
    starsFrom η 0 xs * 10 ^ L + prefixCode xs =
      BoxTable.cubeSlot (starBelow η (completeLeaf xs h)) := by
  rw [BoxTable.cubeSlot, starsToP0_starBelow, ← completeLeaf_stars η xs h,
    ← prefixCode_completeLeaf xs h]

/-- A reached threshold leaf selects a genuine global box at the original parameters. -/
theorem completeLeaf_threshold_isBox {L m t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (h : xs.length = L) (hη : (innerSetO η).card = m)
    (hu : usedFrom η 0 xs = t) : IsBox m t (starBelow η (completeLeaf xs h)) := by
  have hord : order m (completeLeaf xs h) = (t : ℤ) := by
    rw [← completeLeaf_used hx h hη, hu]
  obtain ⟨V, hV, hπ⟩ := mem_biUnion.mp (starBelow_mem (completeLeaf_contributes hx h) hord)
  exact boxesAt_isBox hV hπ

/-- Consequently the actual native lookup addresses an emitted eligible directory entry. -/
theorem completeLeaf_threshold_eligible {L m t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (h : xs.length = L) (hη : (innerSetO η).card = m)
    (hu : usedFrom η 0 xs = t) :
    BoxTable.Eligible L (m - t) (starsFrom η 0 xs * 10 ^ L + prefixCode xs) := by
  rw [completeLeaf_key η xs h]
  exact BoxTable.eligible_cubeSlot (completeLeaf_threshold_isBox hx h hη hu)

/-- That key is inside the real shared directory allocated by the constructor. -/
theorem completeLeaf_threshold_key_lt {L m t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (h : xs.length = L) (hη : (innerSetO η).card = m)
    (hu : usedFrom η 0 xs = t) :
    starsFrom η 0 xs * 10 ^ L + prefixCode xs < (m - t + 1) * 10 ^ L := by
  rw [completeLeaf_key η xs h]
  exact BoxTable.cubeSlot_lt (completeLeaf_threshold_isBox hx h hη hu)

/-- The native low/threshold branch and numeric key select precisely the finite query value. -/
theorem completeLeaf_value {L m t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (h : xs.length = L) (hη : (innerSetO η).card = m)
    (a b : Leaf L → ℤ) :
    leafQueryValue m t η a b (completeLeaf xs h) =
      if usedFrom η 0 xs < t then a (completeLeaf xs h) * b (completeLeaf xs h) else
        BoxTable.slotValue a b (starsFrom η 0 xs * 10 ^ L + prefixCode xs) := by
  unfold leafQueryValue
  have hord := completeLeaf_used hx h hη
  have hlt : order m (completeLeaf xs h) < (t : ℤ) ↔ usedFrom η 0 xs < t := by
    rw [← hord]
    exact_mod_cast Iff.rfl
  simp only [hlt, completeLeaf_key η xs h]

/-- The initial worklist's possible leaves are exactly the finite threshold-pruned query set. -/
theorem possibleLeaves_root_eq_queryLeaves {L m t : ℕ} (η : OutStr L)
    (hη : (innerSetO η).card = m) : possibleLeaves η t [] = queryLeaves m t η := by
  ext τ
  simp [Good_ofFn_iff η hη]

/-- The initial finite work potential uses the actual query cardinality. -/
theorem potential_root_eq {L m t : ℕ} (η : OutStr L) (hη : (innerSetO η).card = m) :
    potential η t [] = (L + 1) * (queryLeaves m t η).card := by
  simp [potential, possibleLeaves_root_eq_queryLeaves η hη]

/-- Its alpha-count bound therefore charges exactly the sparse query family, not all leaves. -/
theorem potential_root_eq_alpha {L m t : ℕ} (η : OutStr L)
    (hη : (innerSetO η).card = m) :
    potential η t [] = (L + 1) * ∑ d ∈ range (t + 1), alpha m d := by
  rw [potential_root_eq η hη, card_queryLeaves t η hη]

/-- Original depth and encoding span also bound every possible initial task contribution. -/
theorem potential_root_le_span {L m t : ℕ} (η : OutStr L)
    (hη : (innerSetO η).card = m) : potential η t [] ≤ (L + 1) * 10 ^ L := by
  rw [potential_root_eq η hη]
  exact Nat.mul_le_mul_left _ (card_queryLeaves_le_span t η hη)

/-- At the original depth only the actual decoded leaf remains, without repetition. -/
theorem possibleLeaves_complete {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (h : xs.length = L) :
    possibleLeaves η t xs = {completeLeaf xs h} := by
  have hg : Good η t (List.ofFn (completeLeaf xs h)) := by
    rw [ofFn_completeLeaf]
    exact hx
  simpa only [ofFn_completeLeaf] using possibleLeaves_ofFn (completeLeaf xs h) hg

/-- A completed task's finite semantic sum is its actual full leaf's value. -/
theorem sum_possibleLeaves_complete {G : Type*} [AddCommMonoid G] {L t : ℕ}
    {η : OutStr L} {xs : List Term} (hx : Good η t xs) (h : xs.length = L)
    (f : Leaf L → G) : ∑ τ ∈ possibleLeaves η t xs, f τ = f (completeLeaf xs h) := by
  rw [possibleLeaves_complete hx h, sum_singleton]

/-- Popping one completed task consumes exactly one unit of the work potential. -/
theorem potential_complete {L t : ℕ} {η : OutStr L} {xs : List Term}
    (hx : Good η t xs) (h : xs.length = L) : potential η t xs = 1 := by
  simp [potential, h, possibleLeaves_complete hx h]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
