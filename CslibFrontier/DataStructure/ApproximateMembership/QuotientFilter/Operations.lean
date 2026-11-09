/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.ApproximateMembership.QuotientFilter.Basic

/-!
# Pure Cluster-Level Insert and Delete Operations for the Quotient Filter

This file defines the computable cluster-level state updates `insertCluster` and `deleteCluster` on
`FilterState b f`, together with `FilterInv.insertState` and `FilterInv.deleteState`, and proves
that they preserve the canonical quotient-filter invariant `FilterInv`.

## Main definitions

* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.FilterState.setFull`,
  `setOcc`, `setRunStart`, `setRem`: primitive slot updates on `FilterState b f`.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.shiftRight`,
  `Cslib.DataStructure.ApproximateMembership.QuotientFilter.shiftLeft`: tail-recursive slot-shift
  loops on `(isRunStart, remAt)`.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.calcRunStart`,
  `calcTargetSlot`, `calcDeleteStop`: computable run-boundary and target-slot indices inside a
  cluster `[o .. o + ℓ)`.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.insertCluster`,
  `Cslib.DataStructure.ApproximateMembership.QuotientFilter.deleteCluster`: computable cluster
  updates for `insert` and `delete`.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.FilterInv.insertState`,
  `Cslib.DataStructure.ApproximateMembership.QuotientFilter.FilterInv.deleteState`: pure
  quotient-filter state transitions.

## Main results

* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.FilterInv.insertState_filterInv`:
  inserting `u ∉ S` (when `#(insert u S) ≤ n` and `#(insert u S) < 2 ^ b`) preserves `FilterInv`.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.FilterInv.deleteState_filterInv`:
  deleting `u ∈ S` preserves `FilterInv`.
-/

public section

namespace Cslib.DataStructure.ApproximateMembership.QuotientFilter

open Finset
open Cslib.DataStructure.Dictionary.WordRAM.LinearProbing

/-- Distinct offsets below `2 ^ b` from the same origin probe distinct slots. -/
private theorem probeSlot_ne {b : ℕ} (o : Fin (2 ^ b)) {i j : ℕ} (hi : i < 2 ^ b) (hj : j < 2 ^ b)
    (hij : i ≠ j) : probeSlot b o i ≠ probeSlot b o j := fun h =>
  hij (probeSlot_injOn_range o (len := 2 ^ b) le_rfl
    (Finset.mem_coe.mpr (Finset.mem_range.mpr hi)) (Finset.mem_coe.mpr (Finset.mem_range.mpr hj)) h)

/-! ## Section 1: Primitive slot updates and shift loops on `FilterState` -/

/-- Update `isFull` at slot `q`. -/
@[expose] def FilterState.setFull {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b)) (v : Bool) :
    FilterState b f :=
  { st with isFull := Function.update st.isFull q v }

/-- Update `isOcc` at bucket `q`. -/
@[expose] def FilterState.setOcc {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b)) (v : Bool) :
    FilterState b f :=
  { st with isOcc := Function.update st.isOcc q v }

/-- Update `isRunStart` at slot `q`. -/
@[expose] def FilterState.setRunStart {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b))
    (v : Bool) : FilterState b f :=
  { st with isRunStart := Function.update st.isRunStart q v }

/-- Update `remAt` at slot `q`. -/
@[expose] def FilterState.setRem {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b))
    (v : Fin (2 ^ f)) : FilterState b f :=
  { st with remAt := Function.update st.remAt q v }

@[simp] theorem FilterState.isFull_setFull {b f : ℕ} (st : FilterState b f) (q p : Fin (2 ^ b))
    (v : Bool) : (st.setFull q v).isFull p = if p = q then v else st.isFull p := by
  simp [FilterState.setFull, Function.update_apply]

@[simp] theorem FilterState.isOcc_setFull {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b))
    (v : Bool) : (st.setFull q v).isOcc = st.isOcc := rfl

@[simp] theorem FilterState.isRunStart_setFull {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b))
    (v : Bool) : (st.setFull q v).isRunStart = st.isRunStart := rfl

@[simp] theorem FilterState.remAt_setFull {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b))
    (v : Bool) : (st.setFull q v).remAt = st.remAt := rfl

@[simp] theorem FilterState.isFull_setOcc {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b))
    (v : Bool) : (st.setOcc q v).isFull = st.isFull := rfl

@[simp] theorem FilterState.isOcc_setOcc {b f : ℕ} (st : FilterState b f) (q p : Fin (2 ^ b))
    (v : Bool) : (st.setOcc q v).isOcc p = if p = q then v else st.isOcc p := by
  simp [FilterState.setOcc, Function.update_apply]

@[simp] theorem FilterState.isRunStart_setOcc {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b))
    (v : Bool) : (st.setOcc q v).isRunStart = st.isRunStart := rfl

@[simp] theorem FilterState.remAt_setOcc {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b))
    (v : Bool) : (st.setOcc q v).remAt = st.remAt := rfl

@[simp] theorem FilterState.isFull_setRunStart {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b))
    (v : Bool) : (st.setRunStart q v).isFull = st.isFull := rfl

@[simp] theorem FilterState.isOcc_setRunStart {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b))
    (v : Bool) : (st.setRunStart q v).isOcc = st.isOcc := rfl

@[simp] theorem FilterState.isRunStart_setRunStart {b f : ℕ} (st : FilterState b f)
    (q p : Fin (2 ^ b)) (v : Bool) :
    (st.setRunStart q v).isRunStart p = if p = q then v else st.isRunStart p := by
  simp [FilterState.setRunStart, Function.update_apply]

@[simp] theorem FilterState.remAt_setRunStart {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b))
    (v : Bool) : (st.setRunStart q v).remAt = st.remAt := rfl

@[simp] theorem FilterState.isFull_setRem {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b))
    (v : Fin (2 ^ f)) : (st.setRem q v).isFull = st.isFull := rfl

@[simp] theorem FilterState.isOcc_setRem {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b))
    (v : Fin (2 ^ f)) : (st.setRem q v).isOcc = st.isOcc := rfl

@[simp] theorem FilterState.isRunStart_setRem {b f : ℕ} (st : FilterState b f) (q : Fin (2 ^ b))
    (v : Fin (2 ^ f)) : (st.setRem q v).isRunStart = st.isRunStart := rfl

@[simp] theorem FilterState.remAt_setRem {b f : ℕ} (st : FilterState b f) (q p : Fin (2 ^ b))
    (v : Fin (2 ^ f)) : (st.setRem q v).remAt p = if p = q then v else st.remAt p := by
  simp [FilterState.setRem, Function.update_apply]

/-- Tail-recursive right-shift of `(isRunStart, remAt)` on `[s .. s + k)` into
`[s + 1 .. s + k + 1)` relative to `o`. -/
@[expose] def shiftRight {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (s : ℕ) :
    ℕ → FilterState b f
  | 0 => st
  | k + 1 =>
    let src := probeSlot b o (s + k)
    let dst := probeSlot b o (s + k + 1)
    let st' := (st.setRunStart dst (st.isRunStart src)).setRem dst (st.remAt src)
    shiftRight st' o s k

@[simp] theorem isFull_shiftRight {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (s k : ℕ) :
    (shiftRight st o s k).isFull = st.isFull := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih => exact ih _

@[simp] theorem isOcc_shiftRight {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (s k : ℕ) :
    (shiftRight st o s k).isOcc = st.isOcc := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih => exact ih _

theorem shiftRight_outside {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (s k : ℕ)
    (p : Fin (2 ^ b)) (hp : ∀ d < k, p ≠ probeSlot b o (s + d + 1)) :
    (shiftRight st o s k).isRunStart p = st.isRunStart p ∧
      (shiftRight st o s k).remAt p = st.remAt p := by
  induction k generalizing st with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have hne : p ≠ probeSlot b o (s + k + 1) := hp k (Nat.lt_succ_self k)
    have ih' := ih ((st.setRunStart (probeSlot b o (s + k + 1))
      (st.isRunStart (probeSlot b o (s + k)))).setRem (probeSlot b o (s + k + 1))
      (st.remAt (probeSlot b o (s + k)))) (fun d hd => hp d (Nat.lt_succ_of_lt hd))
    simpa [shiftRight, hne] using ih'

theorem shiftRight_probeSlot {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) {s k : ℕ}
    (hsk : s + k < 2 ^ b) {i : ℕ} (hi : i ≤ s + k) :
    (shiftRight st o s k).isRunStart (probeSlot b o i) =
      (if s < i then st.isRunStart (probeSlot b o (i - 1)) else st.isRunStart (probeSlot b o i)) ∧
    (shiftRight st o s k).remAt (probeSlot b o i) =
      (if s < i then st.remAt (probeSlot b o (i - 1)) else st.remAt (probeSlot b o i)) := by
  induction k generalizing st with
  | zero =>
    have hnot : ¬(s < i) := by omega
    simp [shiftRight, hnot]
  | succ k ih =>
    rcases eq_or_lt_of_le hi with rfl | hlt
    · have hout := shiftRight_outside
        ((st.setRunStart (probeSlot b o (s + k + 1))
          (st.isRunStart (probeSlot b o (s + k)))).setRem (probeSlot b o (s + k + 1))
          (st.remAt (probeSlot b o (s + k)))) o s k (probeSlot b o (s + (k + 1)))
          fun d hd => probeSlot_ne o hsk (by omega) (by omega)
      have hgt : s < s + (k + 1) := by omega
      have hsub : s + (k + 1) - 1 = s + k := by omega
      have hadd : s + (k + 1) = s + k + 1 := by omega
      rw [ite_eq_left hgt, ite_eq_left hgt, hsub]
      simpa [shiftRight, hadd] using hout
    · have ih' := ih ((st.setRunStart (probeSlot b o (s + k + 1))
          (st.isRunStart (probeSlot b o (s + k)))).setRem (probeSlot b o (s + k + 1))
          (st.remAt (probeSlot b o (s + k)))) (by omega) (by omega : i ≤ s + k)
      have hne_i : probeSlot b o i ≠ probeSlot b o (s + k + 1) :=
        probeSlot_ne o (by omega) hsk (by omega)
      have hne_pred : probeSlot b o (i - 1) ≠ probeSlot b o (s + k + 1) :=
        probeSlot_ne o (by omega) hsk (by omega)
      simp only [shiftRight]
      rw [ih'.1, ih'.2]
      split_ifs <;> simp [hne_i, hne_pred]

/-- Tail-recursive left-shift of `(isRunStart, remAt)` on `[s + 1 .. s + k + 1)` into `[s .. s + k)`
relative to `o`. -/
@[expose] def shiftLeft {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (s : ℕ) :
    ℕ → FilterState b f
  | 0 => st
  | k + 1 =>
    let src := probeSlot b o (s + 1)
    let dst := probeSlot b o s
    let st' := (st.setRunStart dst (st.isRunStart src)).setRem dst (st.remAt src)
    shiftLeft st' o (s + 1) k

@[simp] theorem isFull_shiftLeft {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (s k : ℕ) :
    (shiftLeft st o s k).isFull = st.isFull := by
  induction k generalizing st s with
  | zero => rfl
  | succ k ih => exact ih _ _

@[simp] theorem isOcc_shiftLeft {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (s k : ℕ) :
    (shiftLeft st o s k).isOcc = st.isOcc := by
  induction k generalizing st s with
  | zero => rfl
  | succ k ih => exact ih _ _

theorem shiftLeft_outside {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (s k : ℕ)
    (p : Fin (2 ^ b)) (hp : ∀ d < k, p ≠ probeSlot b o (s + d)) :
    (shiftLeft st o s k).isRunStart p = st.isRunStart p ∧
      (shiftLeft st o s k).remAt p = st.remAt p := by
  induction k generalizing st s with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have hne : p ≠ probeSlot b o s := by simpa using hp 0 (Nat.zero_lt_succ k)
    have ih' := ih ((st.setRunStart (probeSlot b o s)
      (st.isRunStart (probeSlot b o (s + 1)))).setRem (probeSlot b o s)
      (st.remAt (probeSlot b o (s + 1)))) (s + 1) (fun d hd => by
        simpa [Nat.add_right_comm, Nat.add_assoc] using hp (d + 1) (Nat.succ_lt_succ hd))
    simpa [shiftLeft, hne] using ih'

theorem shiftLeft_probeSlot {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) {s k : ℕ}
    (hsk : s + k < 2 ^ b) {i : ℕ} (hi : i < s + k) :
    (shiftLeft st o s k).isRunStart (probeSlot b o i) =
      (if s ≤ i then st.isRunStart (probeSlot b o (i + 1)) else st.isRunStart (probeSlot b o i)) ∧
    (shiftLeft st o s k).remAt (probeSlot b o i) =
      (if s ≤ i then st.remAt (probeSlot b o (i + 1)) else st.remAt (probeSlot b o i)) := by
  induction k generalizing st s with
  | zero =>
    have hnot : ¬(s ≤ i) := by omega
    simp [shiftLeft, hnot]
  | succ k ih =>
    rcases lt_trichotomy i s with hlt | rfl | hgt
    · have hnot1 : ¬(s + 1 ≤ i) := by omega
      have hnot0 : ¬(s ≤ i) := by omega
      have ih' := ih ((st.setRunStart (probeSlot b o s)
          (st.isRunStart (probeSlot b o (s + 1)))).setRem (probeSlot b o s)
          (st.remAt (probeSlot b o (s + 1)))) (s := s + 1) (by omega) (by omega)
      have hne : probeSlot b o i ≠ probeSlot b o s :=
        probeSlot_ne o (by omega) (by omega) (by omega)
      simp only [shiftLeft]
      rw [ih'.1, ih'.2]
      simp [hnot1, hnot0, hne]
    · have hout := shiftLeft_outside
        ((st.setRunStart (probeSlot b o i)
          (st.isRunStart (probeSlot b o (i + 1)))).setRem (probeSlot b o i)
          (st.remAt (probeSlot b o (i + 1)))) o (i + 1) k (probeSlot b o i)
          fun d hd => probeSlot_ne o (by omega) (by omega) (by omega)
      simp only [shiftLeft, le_rfl, ↓reduceIte] at hout ⊢
      simpa using hout
    · have hs1 : s + 1 ≤ i := by omega
      have hs0 : s ≤ i := by omega
      have ih' := ih ((st.setRunStart (probeSlot b o s)
          (st.isRunStart (probeSlot b o (s + 1)))).setRem (probeSlot b o s)
          (st.remAt (probeSlot b o (s + 1)))) (s := s + 1) (by omega) (by omega : i < (s + 1) + k)
      have hne_succ : probeSlot b o (i + 1) ≠ probeSlot b o s :=
        probeSlot_ne o (by omega) (by omega) (by omega)
      simp only [shiftLeft]
      rw [ih'.1, ih'.2]
      simp [hs1, hs0, hne_succ]

/-! ## Section 2: Sorted-list insertion/deletion splitting and range filter helpers -/

theorem orderedInsert_eq_take_append_drop_of_pairwise {α : Type*} [LinearOrder α]
    {r : α} {xs : List α} (hpw : xs.Pairwise (· ≤ ·)) :
    let k := xs.countP (· < r)
    List.orderedInsert (· ≤ ·) r xs = xs.take k ++ r :: xs.drop k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx_le, hpw_xs⟩ := List.pairwise_cons.mp hpw
    by_cases hle : r ≤ x
    · have hlt : decide (x < r) = false := decide_eq_false (not_lt.mpr hle)
      have hzero : xs.countP (· < r) = 0 := by grind
      simp [hle, hlt, hzero]
    · have hlt : decide (x < r) = true := decide_eq_true (lt_of_not_ge hle)
      simp [hle, hlt, ih hpw_xs]

theorem erase_eq_take_append_drop_of_pairwise {α : Type*} [LinearOrder α] {r : α} {xs : List α}
    (hpw : xs.Pairwise (· ≤ ·)) (hmem : r ∈ xs) :
    let k := xs.countP (· < r)
    xs.erase r = xs.take k ++ xs.drop (k + 1) := by
  induction xs with
  | nil => cases hmem
  | cons x xs ih =>
    obtain ⟨hx_le, hpw_xs⟩ := List.pairwise_cons.mp hpw
    by_cases hxr : x = r
    · subst hxr
      have hzero : xs.countP (· < x) = 0 := by
        rw [List.countP_eq_zero]
        intro y hy
        simp [not_lt.mpr (hx_le y hy)]
      simp [hzero]
    · have hr_mem : r ∈ xs := by
        rcases List.mem_cons.mp hmem with rfl | h
        · exact False.elim (hxr rfl)
        · exact h
      have hlt_xr : x < r := lt_of_le_of_ne (hx_le r hr_mem) hxr
      have hlt : decide (x < r) = true := decide_eq_true hlt_xr
      have hbeq : (x == r) = false := beq_false_of_ne hxr
      simp [hlt, hbeq, ih hpw_xs hr_mem]

theorem getElem_lt_iff_lt_countP_of_pairwise {α : Type*} [LinearOrder α] {r : α} {xs : List α}
    (hpw : xs.Pairwise (· ≤ ·)) {d : ℕ} (hd : d < xs.length) :
    xs[d] < r ↔ d < xs.countP (· < r) := by
  induction xs generalizing d with
  | nil => simp at hd
  | cons x xs ih =>
    obtain ⟨hx_le, hpw_xs⟩ := List.pairwise_cons.mp hpw
    by_cases hlt : x < r
    · have hd_true : decide (x < r) = true := decide_eq_true hlt
      cases d with
      | zero => simp [hlt]
      | succ d =>
        have hd' : d < xs.length := Nat.lt_of_succ_lt_succ hd
        simp [hd_true, ih hpw_xs hd']
    · have hd_false : decide (x < r) = false := decide_eq_false hlt
      have hzero : xs.countP (· < r) = 0 := by
        rw [List.countP_eq_zero]
        intro y hy
        simp [not_lt.mpr (le_trans (not_lt.mp hlt) (hx_le y hy))]
      have hge : r ≤ (x :: xs)[d] := by
        have hmem : (x :: xs)[d] ∈ x :: xs := List.getElem_mem hd
        rcases List.mem_cons.mp hmem with h | h
        · rw [h]
          exact not_lt.mp hlt
        · exact le_trans (not_lt.mp hlt) (hx_le _ h)
      simp [hd_false, hzero, not_lt.mpr hge]

theorem length_filter_range_eq_of_iff {ℓ s : ℕ} (hs : s ≤ ℓ) (P : ℕ → Bool)
    (hP : ∀ i < ℓ, P i = true ↔ i < s) :
    ((List.range ℓ).filter P).length = s := by
  have hr : List.range ℓ = List.range s ++ (List.range (ℓ - s)).map (s + ·) := by
    rw [← List.range_add, Nat.add_sub_of_le hs]
  have h1 : (List.range s).filter P = List.range s := by grind [List.filter_eq_self]
  have h2 : ((List.range (ℓ - s)).map (s + ·)).filter P = [] := by
    rw [List.filter_eq_nil_iff]
    intro i hi
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hi
    have hd_lt : d < ℓ - s := List.mem_range.mp hd
    rw [hP (s + d) (by omega)]
    omega
  rw [hr, List.filter_append, h1, h2, List.append_nil, List.length_range]

/-! ## Section 3: Computable run boundaries and target slot offsets -/

/-- Computable starting slot offset `S_a` of bucket `a`'s run in cluster `[o .. o + ℓ)`. -/
@[expose] def calcRunStart {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a ℓ : ℕ) : ℕ :=
  ((List.range ℓ).filter fun i =>
    decide (runsBefore st o (i + 1) ≤ occBefore st o a)).length

/-- Computable target slot offset `s` for inserting or deleting remainder `r` in bucket `a` of
cluster `[o .. o + ℓ)`. -/
@[expose] def calcTargetSlot {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a ℓ : ℕ)
    (r : Fin (2 ^ f)) : ℕ :=
  ((List.range ℓ).filter fun i =>
    decide (runsBefore st o (i + 1) ≤ occBefore st o a ∨
      (runsBefore st o (i + 1) ≤ occBefore st o (a + 1) ∧
        st.remAt (probeSlot b o i) < r))).length

/-- Prefix scan over `m < i` for the stopping offset of the left-shift during `delete` in cluster
`[o .. o + ℓ)`: the first `m < i` with `a < m` and `occBefore st o m < runsBefore st o (m + 1)`, or
`ℓ` if none exists in `[0, i)`. -/
@[expose] def calcDeleteStopPrefix {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b))
    (a ℓ i : ℕ) : ℕ :=
  (((List.range i).filter fun m =>
    decide (a < m ∧ occBefore st o m < runsBefore st o (m + 1))).head?).getD ℓ

/-- Computable stopping offset `e ∈ (a, ℓ]` for the left-shift during `delete` in cluster
`[o .. o + ℓ)`: the first `m > a` (`m < ℓ`) where `occBefore st o m < runsBefore st o (m + 1)`, or
`ℓ` if none exists. -/
@[expose] def calcDeleteStop {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a ℓ : ℕ) : ℕ :=
  calcDeleteStopPrefix st o a ℓ ℓ

theorem IntervalValid.calcRunStart_eq {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ)
    (hocc : ∀ q : Fin (2 ^ b), st.isOcc q = !(bucketRun S quot rem q).isEmpty)
    {a : ℕ} (ha : a ≤ ℓ) :
    calcRunStart st o a ℓ = runOffset S quot rem o a := by
  have hle : runOffset S quot rem o a ≤ ℓ := by
    rw [← hinv.runOffset_eq]
    exact runOffset_mono S quot rem o ha
  refine length_filter_range_eq_of_iff hle _ fun i hi => ?_
  rw [decide_eq_true_eq, ← hinv.lt_runOffset_iff hocc ha hi]

theorem IntervalValid.remAt_probeSlot_eq_getElem {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ) {a : ℕ} (ha : a < ℓ)
    {d : ℕ} (hd : d < (bucketRun S quot rem (probeSlot b o a)).length) :
    st.remAt (probeSlot b o (runOffset S quot rem o a + d)) =
      (bucketRun S quot rem (probeSlot b o a))[d] := by
  set S_a := runOffset S quot rem o a
  have hS_a1 : runOffset S quot rem o (a + 1) =
      S_a + (bucketRun S quot rem (probeSlot b o a)).length :=
    runOffset_succ S quot rem o a
  have hS_a1_le : runOffset S quot rem o (a + 1) ≤ ℓ := by
    rw [← hinv.runOffset_eq]
    exact runOffset_mono S quot rem o (by omega)
  have hi_lt : S_a + d < ℓ := by omega
  have hmap_snd :
      (List.range ℓ).map (fun i => st.remAt (probeSlot b o i)) =
        (List.range ℓ).flatMap (fun j => bucketRun S quot rem (probeSlot b o j)) := by
    have := congrArg (List.map Prod.snd) hinv.slots_eq_flatMap
    simpa [List.map_map, List.map_flatMap, map_snd_taggedRun, Function.comp_def] using this
  have hr : List.range ℓ =
      List.range a ++ [a] ++ (List.range (ℓ - (a + 1))).map (a + 1 + ·) := by
    have h1 : List.range ℓ = List.range (a + 1) ++ (List.range (ℓ - (a + 1))).map (a + 1 + ·) := by
      rw [← List.range_add, Nat.add_sub_of_le (by omega)]
    rw [h1, List.range_succ, List.append_assoc, List.singleton_append]
  have hpref_len :
      ((List.range a).flatMap (fun j => bucketRun S quot rem (probeSlot b o j))).length = S_a := by
    have hmap :
        (List.range a).flatMap (fun j => bucketRun S quot rem (probeSlot b o j)) =
          ((List.range a).flatMap
            (fun j => taggedRun (bucketRun S quot rem (probeSlot b o j)))).map Prod.snd := by
      simp [List.map_flatMap, map_snd_taggedRun]
    rw [hmap, List.length_map]
    rfl
  have hget := congrArg (fun xs : List (Fin (2 ^ f)) => xs[S_a + d]?) hmap_snd
  rw [List.getElem?_map, List.getElem?_range hi_lt, Option.map_some] at hget
  rw [hr, List.flatMap_append, List.flatMap_append, List.flatMap_singleton, List.append_assoc,
    List.getElem?_append_right (by omega)] at hget
  have hsub : S_a + d -
      ((List.range a).flatMap (fun j => bucketRun S quot rem (probeSlot b o j))).length = d := by
    omega
  simp only [hsub, List.getElem?_append_left hd, List.getElem?_eq_getElem hd,
    Option.some.injEq] at hget
  exact hget

theorem IntervalValid.calcTargetSlot_eq {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ)
    (hocc : ∀ q : Fin (2 ^ b), st.isOcc q = !(bucketRun S quot rem q).isEmpty)
    {a : ℕ} (ha : a < ℓ) (r : Fin (2 ^ f)) :
    calcTargetSlot st o a ℓ r =
      runOffset S quot rem o a +
        (bucketRun S quot rem (probeSlot b o a)).countP (· < r) := by
  set S_a := runOffset S quot rem o a
  set S_a1 := runOffset S quot rem o (a + 1)
  set xs := bucketRun S quot rem (probeSlot b o a)
  set k := xs.countP (· < r)
  have hS_a1_eq : S_a1 = S_a + xs.length := runOffset_succ S quot rem o a
  have hk_le : k ≤ xs.length := List.countP_le_length
  have hS_a1_le : S_a1 ≤ ℓ := by
    rw [← hinv.runOffset_eq]
    exact runOffset_mono S quot rem o (by omega)
  have hs_le : S_a + k ≤ ℓ := by omega
  have hpw : xs.Pairwise (· ≤ ·) := pairwise_le_bucketRun S quot rem (probeSlot b o a)
  refine length_filter_range_eq_of_iff hs_le _ fun i hi => ?_
  rw [decide_eq_true_eq]
  have hiff_a := hinv.lt_runOffset_iff hocc (by omega : a ≤ ℓ) hi
  have hiff_a1 := hinv.lt_runOffset_iff hocc (by omega : a + 1 ≤ ℓ) hi
  change i < S_a ↔ runsBefore st o (i + 1) ≤ occBefore st o a at hiff_a
  change i < S_a1 ↔ runsBefore st o (i + 1) ≤ occBefore st o (a + 1) at hiff_a1
  rw [← hiff_a, ← hiff_a1]
  by_cases hi_lt : i < S_a
  · simp [hi_lt, show i < S_a + k by omega]
  · simp only [hi_lt, false_or]
    by_cases hi_lt1 : i < S_a1
    · simp only [hi_lt1, true_and]
      have hd_lt : i - S_a < xs.length := by omega
      have hi_eq : S_a + (i - S_a) = i := by omega
      have hrem := hinv.remAt_probeSlot_eq_getElem ha hd_lt
      rw [hi_eq] at hrem
      rw [hrem, getElem_lt_iff_lt_countP_of_pairwise hpw hd_lt]
      omega
    · simp [hi_lt1, show ¬(i < S_a + k) by omega]

theorem IntervalValid.calcDeleteStop_spec {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ)
    (hocc : ∀ q : Fin (2 ^ b), st.isOcc q = !(bucketRun S quot rem q).isEmpty)
    {a : ℕ} (ha : a < ℓ) :
    let e := calcDeleteStop st o a ℓ
    a < e ∧ e ≤ ℓ ∧ runOffset S quot rem o e = e ∧
      ∀ m, a ≤ m → m + 1 < e → m + 2 ≤ runOffset S quot rem o (m + 1) := by
  set L := (List.range ℓ).filter fun m =>
    decide (a < m ∧ occBefore st o m < runsBefore st o (m + 1))
  -- Off the stop list `L`, the run offset strictly exceeds the bucket index.
  have hstep : ∀ m, a ≤ m → m + 1 < ℓ → m + 1 ∉ L → m + 2 ≤ runOffset S quot rem o (m + 1) := by
    intro m hm hm1 hnot
    have hge := hinv.prefix_le_runOffset m (by omega)
    have hne_self : runOffset S quot rem o (m + 1) ≠ m + 1 := by
      intro h_eq
      rcases (hinv.runOffset_eq_self_iff hocc (by omega : m + 1 ≤ ℓ)).mp h_eq with h | h
      · omega
      · exact hnot (List.mem_filter.mpr ⟨List.mem_range.mpr hm1, decide_eq_true ⟨by omega, h⟩⟩)
    omega
  cases hL : L with
  | nil =>
    have he : calcDeleteStop st o a ℓ = ℓ := by
      dsimp only [calcDeleteStop]
      change L.head?.getD ℓ = ℓ
      rw [hL]
      rfl
    rw [he]
    exact ⟨ha, le_rfl, hinv.runOffset_eq, fun m hm hm_lt => hstep m hm hm_lt (by simp [hL])⟩
  | cons e rest =>
    have he_eq : calcDeleteStop st o a ℓ = e := by
      dsimp only [calcDeleteStop]
      change L.head?.getD ℓ = e
      rw [hL]
      rfl
    rw [he_eq]
    have he_mem : e ∈ L := by simp [hL]
    simp only [L, List.mem_filter, List.mem_range, decide_eq_true_eq] at he_mem
    obtain ⟨he_lt, ha_lt_e, he_cond⟩ := he_mem
    have he_run : runOffset S quot rem o e = e :=
      (hinv.runOffset_eq_self_iff hocc he_lt.le).mpr (Or.inr he_cond)
    refine ⟨ha_lt_e, he_lt.le, he_run, fun m hm hm_lt => hstep m hm (by omega) fun hmem => ?_⟩
    -- `L` is strictly increasing, so nothing in it lies below its head `e`.
    have hpw : L.Pairwise (· < ·) := List.pairwise_lt_range.filter _
    rw [hL, List.pairwise_cons] at hpw
    rw [hL] at hmem
    rcases List.mem_cons.mp hmem with h | h
    · omega
    · have := hpw.1 (m + 1) h
      omega

/-! ## Section 4: Slot-stream list lemmas for `shiftRight` and `shiftLeft` -/

/-- Pair `(isRunStart, remAt)` stored at offset `i` from `o`. -/
@[expose] def slotPair {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (i : ℕ) :
    Bool × Fin (2 ^ f) :=
  (st.isRunStart (probeSlot b o i), st.remAt (probeSlot b o i))

theorem map_slotPair_setRunStart_lt {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b))
    {s n : ℕ} (hn : n ≤ 2 ^ b) (hs : s < n) (v : Bool) :
    (List.range n).map (slotPair (st.setRunStart (probeSlot b o s) v) o) =
      ((List.range n).map (slotPair st o)).set s (v, st.remAt (probeSlot b o s)) := by
  refine List.ext_getElem (by simp) fun i hi₁ hi₂ => ?_
  have hi_lt : i < n := by simpa using hi₁
  rw [List.getElem_map, List.getElem_range]
  by_cases his : i = s
  · subst his
    rw [List.getElem_set_self]
    simp [slotPair]
  · rw [List.getElem_set_ne (Ne.symm his), List.getElem_map, List.getElem_range]
    have hne : probeSlot b o i ≠ probeSlot b o s := probeSlot_ne o (by omega) (by omega) his
    simp [slotPair, hne]

theorem map_slotPair_setRunStart_ge {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b))
    {s n : ℕ} (hs_lt : s < 2 ^ b) (hge : n ≤ s) (v : Bool) :
    (List.range n).map (slotPair (st.setRunStart (probeSlot b o s) v) o) =
      (List.range n).map (slotPair st o) := by
  refine List.ext_getElem (by simp) fun i hi₁ hi₂ => ?_
  have hi_lt : i < n := by simpa using hi₁
  rw [List.getElem_map, List.getElem_map, List.getElem_range]
  have hne : probeSlot b o i ≠ probeSlot b o s := probeSlot_ne o (by omega) hs_lt (by omega)
  simp [slotPair, hne]

theorem map_slotPair_shiftRight {b f : ℕ} (st₁ : FilterState b f) (o : Fin (2 ^ b))
    {s ℓ : ℕ} (hs : s ≤ ℓ) (hℓ : ℓ < 2 ^ b) (v : Bool) (r : Fin (2 ^ f)) :
    let st₂ := shiftRight st₁ o s (ℓ - s)
    let st₃ := (st₂.setRunStart (probeSlot b o s) v).setRem (probeSlot b o s) r
    let L₁ := (List.range ℓ).map (slotPair st₁ o)
    (List.range (ℓ + 1)).map (slotPair st₃ o) =
      L₁.take s ++ (v, r) :: L₁.drop s := by
  intro st₂ st₃ L₁
  have hlen_L₁ : L₁.length = ℓ := by simp [L₁]
  refine List.ext_getElem ?_ fun i hi₁ hi₂ => ?_
  · simp [hlen_L₁, Nat.min_eq_left hs]
    omega
  · have hi_le : i ≤ ℓ := by simpa [Nat.lt_succ_iff] using hi₁
    rw [List.getElem_map, List.getElem_range]
    rcases lt_trichotomy i s with hlt | rfl | hgt
    · have hne : probeSlot b o i ≠ probeSlot b o s :=
        probeSlot_ne o (by omega) (by omega) (by omega)
      have hsr := shiftRight_probeSlot st₁ o (s := s) (k := ℓ - s) (by omega) (i := i) (by omega)
      have hnot : ¬(s < i) := by omega
      simp only [hnot, ↓reduceIte] at hsr
      have hpair : slotPair st₃ o i = slotPair st₁ o i := by
        simp [st₃, st₂, slotPair, hne, hsr.1, hsr.2]
      rw [hpair, List.getElem_append_left (by simp [hlen_L₁, hs, hlt]),
        List.getElem_take, List.getElem_map, List.getElem_range]
    · have hpair : slotPair st₃ o i = (v, r) := by simp [st₃, slotPair]
      rw [hpair, List.getElem_append_right (by simp [hlen_L₁, hs])]
      simp [hlen_L₁, Nat.min_eq_left hs]
    · have hne : probeSlot b o i ≠ probeSlot b o s :=
        probeSlot_ne o (by omega) (by omega) (by omega)
      have hsr := shiftRight_probeSlot st₁ o (s := s) (k := ℓ - s) (by omega) (i := i) (by omega)
      simp only [hgt, ↓reduceIte] at hsr
      have hpair : slotPair st₃ o i = slotPair st₁ o (i - 1) := by
        simp [st₃, st₂, slotPair, hne, hsr.1, hsr.2]
      rw [hpair, List.getElem_append_right (by simp [hlen_L₁, hs]; omega)]
      have hlen_take : (L₁.take s).length = s := by simp [hlen_L₁, hs]
      have hsub : i - (L₁.take s).length = (i - s - 1) + 1 := by omega
      simp only [hsub, List.getElem_cons_succ, List.getElem_drop, L₁, List.getElem_map,
        List.getElem_range]
      exact congrArg (slotPair st₁ o) (by omega)

theorem map_slotPair_shiftLeft {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b))
    {s e : ℕ} (hs : s < e) (he : e ≤ 2 ^ b) :
    let st₁ := shiftLeft st o s (e - 1 - s)
    let M := (List.range e).map (slotPair st o)
    (List.range (e - 1)).map (slotPair st₁ o) =
      M.take s ++ M.drop (s + 1) := by
  intro st₁ M
  have hlen_M : M.length = e := by simp [M]
  refine List.ext_getElem ?_ fun i hi₁ hi₂ => ?_
  · simp [hlen_M, show s ≤ e by omega]
    omega
  · have hi_lt : i < e - 1 := by simpa using hi₁
    rw [List.getElem_map, List.getElem_range]
    have hsl := shiftLeft_probeSlot st o (s := s) (k := e - 1 - s) (by omega) (i := i) (by omega)
    by_cases hlt : i < s
    · have hnot : ¬(s ≤ i) := by omega
      simp only [hnot, ↓reduceIte] at hsl
      have hpair : slotPair st₁ o i = slotPair st o i := by
        simp [st₁, slotPair, hsl.1, hsl.2]
      rw [hpair, List.getElem_append_left (by simp [hlen_M, show s ≤ e by omega, hlt]),
        List.getElem_take, List.getElem_map, List.getElem_range]
    · have hge : s ≤ i := by omega
      simp only [hge, ↓reduceIte] at hsl
      have hpair : slotPair st₁ o i = slotPair st o (i + 1) := by
        simp [st₁, slotPair, hsl.1, hsl.2]
      rw [hpair, List.getElem_append_right (by simp [hlen_M, show s ≤ e by omega, hge]),
        List.getElem_drop, List.getElem_map, List.getElem_range]
      have hlen_take : (M.take s).length = s := by simp [hlen_M, show s ≤ e by omega]
      exact congrArg (slotPair st o) (by omega)

theorem taggedRun_insert_split {f : ℕ} (xs : List (Fin (2 ^ f))) (r : Fin (2 ^ f))
    {k : ℕ} (hk : k ≤ xs.length) :
    let M₁ : List (Bool × Fin (2 ^ f)) := if k = 0 then xs.map (false, ·) else taggedRun xs
    M₁.take k ++ (decide (k = 0), r) :: M₁.drop k =
      taggedRun (xs.take k ++ r :: xs.drop k) := by
  cases k with
  | zero => simp [taggedRun]
  | succ k =>
    cases xs with
    | nil => simp at hk
    | cons x₀ xs' =>
      simp [taggedRun, ← List.map_take, ← List.map_drop]

theorem taggedRun_delete_split_succ {f : ℕ} (xs : List (Fin (2 ^ f))) (k : ℕ)
    (hk : k + 1 < xs.length) :
    (taggedRun xs).take (k + 1) ++ (taggedRun xs).drop (k + 2) =
      taggedRun (xs.take (k + 1) ++ xs.drop (k + 2)) := by
  cases xs with
  | nil => simp at hk
  | cons x₀ xs' =>
    simp [taggedRun, ← List.map_take, ← List.map_drop]

/-! ## Section 5: `IntervalValid` combinators -/

theorem runOffset_congr {U b f : ℕ} {S S' : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {o : Fin (2 ^ b)} {m : ℕ}
    (h : ∀ j < m, bucketRun S' quot rem (probeSlot b o j) =
      bucketRun S quot rem (probeSlot b o j)) :
    runOffset S' quot rem o m = runOffset S quot rem o m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [runOffset_succ, runOffset_succ, ih (fun j hj => h j (by omega)), h m (Nat.lt_succ_self m)]

theorem IntervalValid.congr {U b f : ℕ} {S S' : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st st' : FilterState b f} {o : Fin (2 ^ b)} {ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ)
    (hbucket : ∀ j < ℓ, bucketRun S' quot rem (probeSlot b o j) =
      bucketRun S quot rem (probeSlot b o j))
    (hfull : ∀ i < ℓ, st'.isFull (probeSlot b o i) = st.isFull (probeSlot b o i))
    (hpair : ∀ i < ℓ, slotPair st' o i = slotPair st o i) :
    IntervalValid S' quot rem st' o ℓ where
  full_of_lt i hi := by rw [hfull i hi, hinv.full_of_lt i hi]
  prefix_le_runOffset m hm := by
    rw [runOffset_congr (fun j hj => hbucket j (by omega))]
    exact hinv.prefix_le_runOffset m hm
  slots_eq_flatMap := by
    have hmap :
        (List.range ℓ).map (fun i =>
          (st'.isRunStart (probeSlot b o i), st'.remAt (probeSlot b o i))) =
        (List.range ℓ).map (fun i =>
          (st.isRunStart (probeSlot b o i), st.remAt (probeSlot b o i))) := by
      refine List.map_congr_left fun i hi => ?_
      exact hpair i (List.mem_range.mp hi)
    have hflat :
        ((List.range ℓ).flatMap fun j => taggedRun (bucketRun S' quot rem (probeSlot b o j))) =
          (List.range ℓ).flatMap fun j => taggedRun (bucketRun S quot rem (probeSlot b o j)) := by
      refine List.flatMap_congr fun j hj => ?_
      rw [hbucket j (List.mem_range.mp hj)]
    rw [hmap, hinv.slots_eq_flatMap, hflat]

theorem runOffset_add {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f))
    (o : Fin (2 ^ b)) (m₁ m₂ : ℕ) :
    runOffset S quot rem o (m₁ + m₂) =
      runOffset S quot rem o m₁ + runOffset S quot rem (probeSlot b o m₁) m₂ := by
  dsimp only [runOffset]
  rw [List.range_add, List.flatMap_append, List.length_append, List.flatMap_map]
  congr 2
  refine List.flatMap_congr fun j _ => ?_
  rw [probeSlot_add]

theorem IntervalValid.append {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {ℓ₁ ℓ₂ : ℕ}
    (h₁ : IntervalValid S quot rem st o ℓ₁)
    (h₂ : IntervalValid S quot rem st (probeSlot b o ℓ₁) ℓ₂) :
    IntervalValid S quot rem st o (ℓ₁ + ℓ₂) where
  full_of_lt i hi := by
    by_cases hlt : i < ℓ₁
    · exact h₁.full_of_lt i hlt
    · have hi_eq : i = ℓ₁ + (i - ℓ₁) := by omega
      rw [hi_eq, ← probeSlot_add]
      exact h₂.full_of_lt (i - ℓ₁) (by omega)
  prefix_le_runOffset m hm := by
    by_cases hlt : m < ℓ₁
    · exact h₁.prefix_le_runOffset m hlt
    · have hm_eq : m + 1 = ℓ₁ + (m - ℓ₁ + 1) := by omega
      rw [hm_eq, runOffset_add, h₁.runOffset_eq]
      have hge := h₂.prefix_le_runOffset (m - ℓ₁) (by omega)
      omega
  slots_eq_flatMap := by
    rw [List.range_add, List.map_append, List.flatMap_append, h₁.slots_eq_flatMap]
    congr 1
    simpa only [List.map_map, List.flatMap_map, Function.comp_def, probeSlot_add]
      using h₂.slots_eq_flatMap

/-- When bucket `e`'s run starts exactly at slot `e`, the slot-stream identity of a valid interval
splits at offset `e` into the identities for `[0, e)` and `[e, ℓ)`. -/
private theorem IntervalValid.slots_split {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {e ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ) (he : e ≤ ℓ)
    (hrun_e : runOffset S quot rem o e = e) :
    (List.range e).map (slotPair st o) =
        (List.range e).flatMap (fun j => taggedRun (bucketRun S quot rem (probeSlot b o j))) ∧
      ((List.range (ℓ - e)).map (e + ·)).map (slotPair st o) =
        ((List.range (ℓ - e)).map (e + ·)).flatMap
          (fun j => taggedRun (bucketRun S quot rem (probeSlot b o j))) := by
  have hslots := hinv.slots_eq_flatMap
  rw [← Nat.add_sub_of_le he, List.range_add, List.map_append, List.flatMap_append] at hslots
  refine List.append_inj hslots ?_
  rw [List.length_map, List.length_range]
  exact hrun_e.symm

theorem IntervalValid.drop_of_runOffset_eq {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {e ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ) (he : e ≤ ℓ)
    (hrun_e : runOffset S quot rem o e = e) :
    IntervalValid S quot rem st (probeSlot b o e) (ℓ - e) where
  full_of_lt i hi := by
    rw [probeSlot_add]
    exact hinv.full_of_lt (e + i) (by omega)
  prefix_le_runOffset m hm := by
    have hge := hinv.prefix_le_runOffset (e + m) (by omega)
    have hadd : e + m + 1 = e + (m + 1) := by omega
    rw [hadd, runOffset_add, hrun_e] at hge
    omega
  slots_eq_flatMap := by
    have hright := (hinv.slots_split he hrun_e).2
    simpa only [List.map_map, List.flatMap_map, Function.comp_def, slotPair, probeSlot_add]
      using hright

/-! ## Section 6: Cluster-level `insertCluster` and `deleteCluster` -/

theorem IntervalValid.calcTargetSlot_eq_of_empty {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ)
    (hocc : ∀ q : Fin (2 ^ b), st.isOcc q = !(bucketRun S quot rem q).isEmpty)
    {a : ℕ} (ha : a ≤ ℓ) (ha_eq : a = ℓ → bucketRun S quot rem (probeSlot b o a) = [])
    (r : Fin (2 ^ f)) :
    calcTargetSlot st o a ℓ r =
      runOffset S quot rem o a +
        (bucketRun S quot rem (probeSlot b o a)).countP (· < r) := by
  rcases lt_or_eq_of_le ha with hlt | rfl
  · exact hinv.calcTargetSlot_eq hocc hlt r
  · rw [ha_eq rfl, List.countP_nil, add_zero, hinv.runOffset_eq]
    refine length_filter_range_eq_of_iff le_rfl _ fun i hi => ?_
    rw [decide_eq_true_eq]
    have hiff := (hinv.lt_runOffset_iff hocc le_rfl hi).mp (by rw [hinv.runOffset_eq]; exact hi)
    exact ⟨fun _ => hi, fun _ => Or.inl hiff⟩

/-- Pure cluster-level insertion of remainder `r` into bucket `a ≤ ℓ` of cluster `[o .. o + ℓ)`. -/
@[expose] def insertCluster {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a ℓ : ℕ)
    (r : Fin (2 ^ f)) : FilterState b f :=
  let q := probeSlot b o a
  let s₀ := calcRunStart st o a ℓ
  let s := calcTargetSlot st o a ℓ r
  let st₁ := if st.isOcc q && decide (s = s₀) then
    st.setRunStart (probeSlot b o s₀) false
  else
    st
  let st₂ := shiftRight st₁ o s (ℓ - s)
  let st₃ := (st₂.setRunStart (probeSlot b o s) (decide (s = s₀))).setRem (probeSlot b o s) r
  (st₃.setOcc q true).setFull (probeSlot b o ℓ) true

/-- Pure cluster-level deletion of remainder `r` from bucket `a < ℓ` of cluster `[o .. o + ℓ)`. -/
@[expose] def deleteCluster {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a ℓ : ℕ)
    (r : Fin (2 ^ f)) : FilterState b f :=
  let q := probeSlot b o a
  let s₀ := calcRunStart st o a ℓ
  let s := calcTargetSlot st o a ℓ r
  let e := calcDeleteStop st o a ℓ
  let hasMore := decide (s₀ + 1 < e) && !st.isRunStart (probeSlot b o (s₀ + 1))
  let st₁ := shiftLeft st o s (e - 1 - s)
  let st₂ := if !hasMore then
    st₁.setOcc q false
  else if s = s₀ then
    st₁.setRunStart (probeSlot b o s₀) true
  else
    st₁
  let p_end := probeSlot b o (e - 1)
  ((st₂.setFull p_end false).setRunStart p_end false).setRem p_end ⟨0, Nat.two_pow_pos f⟩

theorem flatMap_taggedRun_three_split {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) (o : Fin (2 ^ b))
    {a n : ℕ} (ha : a < n) :
    ((List.range n).flatMap fun j => taggedRun (bucketRun S quot rem (probeSlot b o j))) =
      ((List.range a).flatMap fun j => taggedRun (bucketRun S quot rem (probeSlot b o j))) ++
        taggedRun (bucketRun S quot rem (probeSlot b o a)) ++
        (((List.range (n - (a + 1))).map (a + 1 + ·)).flatMap fun j =>
          taggedRun (bucketRun S quot rem (probeSlot b o j))) := by
  have hr : List.range n =
      List.range a ++ [a] ++ (List.range (n - (a + 1))).map (a + 1 + ·) := by
    have h1 : List.range n = List.range (a + 1) ++ (List.range (n - (a + 1))).map (a + 1 + ·) := by
      rw [← List.range_add, Nat.add_sub_of_le (by omega)]
    rw [h1, List.range_succ, List.append_assoc, List.singleton_append]
  conv_lhs => rw [hr, List.flatMap_append, List.flatMap_append, List.flatMap_singleton]

theorem take_append_drop_middle {α : Type*} (pref mid suff : List α) (x : α)
    {k : ℕ} (hk : k ≤ mid.length) :
    (pref ++ mid ++ suff).take (pref.length + k) ++ x ::
        (pref ++ mid ++ suff).drop (pref.length + k) =
      pref ++ (mid.take k ++ x :: mid.drop k) ++ suff := by
  rw [List.append_assoc pref mid suff, List.take_append, List.drop_append]
  have h1 : ¬(pref.length + k ≤ pref.length) ∨ k = 0 := by omega
  simp only [Nat.add_sub_cancel_left]
  rw [List.take_of_length_le (Nat.le_add_right _ _), List.drop_eq_nil_of_le (Nat.le_add_right _ _),
    List.nil_append, List.take_append_of_le_length hk, List.drop_append_of_le_length hk]
  simp [List.append_assoc]

theorem take_append_drop_succ_middle {α : Type*} (pref mid suff : List α)
    {k : ℕ} (hk : k < mid.length) :
    (pref ++ mid ++ suff).take (pref.length + k) ++
        (pref ++ mid ++ suff).drop (pref.length + k + 1) =
      pref ++ (mid.take k ++ mid.drop (k + 1)) ++ suff := by
  have hadd : pref.length + k + 1 = pref.length + (k + 1) := by omega
  rw [hadd, List.append_assoc pref mid suff, List.take_append, List.drop_append]
  simp only [Nat.add_sub_cancel_left]
  rw [List.take_of_length_le (Nat.le_add_right _ _), List.drop_eq_nil_of_le (Nat.le_add_right _ _),
    List.nil_append, List.take_append_of_le_length (le_of_lt hk),
    List.drop_append_of_le_length (Nat.succ_le_of_lt hk)]
  simp [List.append_assoc]

theorem set_middle_zero {α : Type*} (pref : List α) (x₀ : α) (xs suff : List α) (y : α) :
    (pref ++ (x₀ :: xs) ++ suff).set pref.length y = pref ++ (y :: xs) ++ suff := by
  rw [List.append_assoc, List.set_append_right _ _ le_rfl, Nat.sub_self, List.cons_append,
    List.set_cons_zero]
  simp [List.append_assoc]

/-- Inserting `u` into its bucket `probeSlot b o a` leaves the run of every other bucket of the
probe window unchanged. -/
private theorem bucketRun_insert_probeSlot_of_ne {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) {o : Fin (2 ^ b)} {u : Fin U}
    {a j : ℕ} (hq : quot u = probeSlot b o a) (ha : a < 2 ^ b) (hj : j < 2 ^ b) (hja : j ≠ a) :
    bucketRun (insert u S) quot rem (probeSlot b o j) = bucketRun S quot rem (probeSlot b o j) := by
  refine bucketRun_insert_of_ne S quot rem u ?_
  rw [hq]
  exact probeSlot_ne o ha hj (Ne.symm hja)

/-- Erasing `u` from its bucket `probeSlot b o a` leaves the run of every other bucket of the
probe window unchanged. -/
private theorem bucketRun_erase_probeSlot_of_ne {U b f : ℕ} (S : Finset (Fin U))
    (quot : Fin U → Fin (2 ^ b)) (rem : Fin U → Fin (2 ^ f)) {o : Fin (2 ^ b)} {u : Fin U}
    {a j : ℕ} (hq : quot u = probeSlot b o a) (ha : a < 2 ^ b) (hj : j < 2 ^ b) (hja : j ≠ a) :
    bucketRun (S.erase u) quot rem (probeSlot b o j) = bucketRun S quot rem (probeSlot b o j) := by
  refine bucketRun_erase_of_ne S quot rem u ?_
  rw [hq]
  exact probeSlot_ne o ha hj (Ne.symm hja)

/-- If `S'` agrees with `S` on the buckets of `[o .. o + n)` except bucket `a`, whose run is one
element longer, then every run offset past `a` grows by one. -/
private theorem runOffset_eq_add_of_length_succ {U b f : ℕ} {S S' : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {o : Fin (2 ^ b)} {a n : ℕ}
    (hoff : ∀ j < n, j ≠ a →
      bucketRun S' quot rem (probeSlot b o j) = bucketRun S quot rem (probeSlot b o j))
    (hlen : (bucketRun S' quot rem (probeSlot b o a)).length =
      (bucketRun S quot rem (probeSlot b o a)).length + 1) :
    ∀ m ≤ n, runOffset S' quot rem o m = runOffset S quot rem o m + if a < m then 1 else 0 := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    rw [runOffset_succ, runOffset_succ, ih (by omega)]
    by_cases hma : m = a
    · subst hma
      rw [hlen]
      split_ifs <;> omega
    · rw [hoff m (by omega) hma]
      split_ifs <;> omega

/-- If `S'` agrees with `S` on the buckets of `[o .. o + n)` except bucket `a`, then the tagged
stream of `S'` is that of `S` with bucket `a`'s tagged run replaced. -/
private theorem flatMap_taggedRun_three_split_of_eq {U b f : ℕ} {S S' : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {o : Fin (2 ^ b)} {a n : ℕ}
    (ha : a < n)
    (hoff : ∀ j < n, j ≠ a →
      bucketRun S' quot rem (probeSlot b o j) = bucketRun S quot rem (probeSlot b o j)) :
    ((List.range n).flatMap fun j => taggedRun (bucketRun S' quot rem (probeSlot b o j))) =
      ((List.range a).flatMap fun j => taggedRun (bucketRun S quot rem (probeSlot b o j))) ++
        taggedRun (bucketRun S' quot rem (probeSlot b o a)) ++
        (((List.range (n - (a + 1))).map (a + 1 + ·)).flatMap fun j =>
          taggedRun (bucketRun S quot rem (probeSlot b o j))) := by
  rw [flatMap_taggedRun_three_split S' quot rem o ha]
  congr 1
  · congr 1
    refine List.flatMap_congr fun j hj => ?_
    have hj := List.mem_range.mp hj
    rw [hoff j (by omega) (by omega)]
  · refine List.flatMap_congr fun j hj => ?_
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hj
    have hd := List.mem_range.mp hd
    rw [hoff (a + 1 + d) (by omega) (by omega)]

/-- Reading the slot stream at the first position past a prefix `L₁`. -/
private theorem slotPair_of_map_eq_append {b f : ℕ} {st : FilterState b f} {o : Fin (2 ^ b)}
    {n : ℕ} {L₁ L₂ : List (Bool × Fin (2 ^ f))} {y : Bool × Fin (2 ^ f)}
    (h : (List.range n).map (slotPair st o) = L₁ ++ y :: L₂) :
    L₁.length < n ∧ slotPair st o L₁.length = y := by
  have hlt : L₁.length < n := by
    have hlen := congrArg List.length h
    simp only [List.length_map, List.length_range, List.length_append, List.length_cons] at hlen
    omega
  refine ⟨hlt, ?_⟩
  have hget := congrArg (fun L : List (Bool × Fin (2 ^ f)) => L[L₁.length]?) h
  rw [List.getElem?_map, List.getElem?_range hlt, Option.map_some,
    List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero] at hget
  exact Option.some.inj hget

/-- Overwriting the run-start bit of the slot that holds the first entry of a middle segment of
the slot stream. -/
private theorem map_slotPair_setRunStart_middle {b f : ℕ} {st : FilterState b f}
    {o : Fin (2 ^ b)} {n : ℕ} (hn : n ≤ 2 ^ b) {pref ys suff : List (Bool × Fin (2 ^ f))}
    {c : Bool} {x : Fin (2 ^ f)}
    (h : (List.range n).map (slotPair st o) = pref ++ ((c, x) :: ys) ++ suff) (v : Bool) :
    (List.range n).map (slotPair (st.setRunStart (probeSlot b o pref.length) v) o) =
      pref ++ ((v, x) :: ys) ++ suff := by
  have h' := h
  rw [List.append_assoc, List.cons_append] at h'
  obtain ⟨hlt, hy⟩ := slotPair_of_map_eq_append h'
  have hx : st.remAt (probeSlot b o pref.length) = x := congrArg Prod.snd hy
  rw [map_slotPair_setRunStart_lt st o hn hlt v, h, hx]
  exact set_middle_zero pref (c, x) ys suff (v, x)

theorem IntervalValid.insertCluster_intervalValid {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ)
    (hocc : ∀ q : Fin (2 ^ b), st.isOcc q = !(bucketRun S quot rem q).isEmpty)
    (hℓ : ℓ < 2 ^ b)
    (hempty_ℓ : bucketRun S quot rem (probeSlot b o ℓ) = [])
    {u : Fin U} (hu : u ∉ S) {a : ℕ} (ha : a ≤ ℓ) (hq : quot u = probeSlot b o a) :
    IntervalValid (insert u S) quot rem (insertCluster st o a ℓ (rem u)) o (ℓ + 1) := by
  let r := rem u
  let q := probeSlot b o a
  set xs := bucketRun S quot rem q
  set k := xs.countP (· < r)
  set s₀ := calcRunStart st o a ℓ
  set s := calcTargetSlot st o a ℓ r
  have hs₀_eq : s₀ = runOffset S quot rem o a := hinv.calcRunStart_eq hocc ha
  have hs_eq : s = s₀ + k := by
    rw [hs₀_eq]
    exact hinv.calcTargetSlot_eq_of_empty hocc ha (fun h => h ▸ hempty_ℓ) r
  have hk_le : k ≤ xs.length := List.countP_le_length
  have hs_le_ℓ : s ≤ ℓ := by
    rcases lt_or_eq_of_le ha with hlt | rfl
    · have h1 : runOffset S quot rem o (a + 1) = s₀ + xs.length := by
        rw [hs₀_eq]
        exact runOffset_succ S quot rem o a
      have h2 : runOffset S quot rem o (a + 1) ≤ ℓ := by
        rw [← hinv.runOffset_eq]
        exact runOffset_mono S quot rem o (by omega)
      omega
    · have hk0 : k = 0 := by simp [k, xs, q, hempty_ℓ]
      rw [hs_eq, hs₀_eq, hinv.runOffset_eq, hk0, add_zero]
  set st₁ := if st.isOcc q && decide (s = s₀) then
    st.setRunStart (probeSlot b o s₀) false
  else
    st
  set st₂ := shiftRight st₁ o s (ℓ - s)
  set st₃ := (st₂.setRunStart (probeSlot b o s) (decide (s = s₀))).setRem (probeSlot b o s) r
  set st₄ := (st₃.setOcc q true).setFull (probeSlot b o ℓ) true
  change IntervalValid (insert u S) quot rem st₄ o (ℓ + 1)
  have hoff : ∀ j < ℓ + 1, j ≠ a →
      bucketRun (insert u S) quot rem (probeSlot b o j) = bucketRun S quot rem (probeSlot b o j) :=
    fun j hj hja => bucketRun_insert_probeSlot_of_ne S quot rem hq (by omega) (by omega) hja
  have hins_q : bucketRun (insert u S) quot rem q = xs.orderedInsert (· ≤ ·) r := by
    dsimp only [xs, q, r]
    rw [← hq, bucketRun_insert_self quot rem hu]
  have hrun_insert : ∀ m ≤ ℓ + 1,
      runOffset (insert u S) quot rem o m =
        runOffset S quot rem o m + if a < m then 1 else 0 := by
    refine runOffset_eq_add_of_length_succ hoff ?_
    change (bucketRun (insert u S) quot rem q).length = xs.length + 1
    rw [hins_q, List.orderedInsert_length]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
    · have hne_ℓ : probeSlot b o i ≠ probeSlot b o ℓ := probeSlot_ne o (by omega) hℓ (by omega)
      have hst₁_full : st₁.isFull (probeSlot b o i) = true := by
        dsimp only [st₁]
        split_ifs <;> simp [hinv.full_of_lt i hlt]
      simp [st₄, st₃, st₂, hne_ℓ, hst₁_full]
    · simp [st₄]
  · intro m hm
    rw [hrun_insert (m + 1) (by omega)]
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hlt | rfl
    · have := hinv.prefix_le_runOffset m hlt
      split_ifs <;> omega
    · rw [runOffset_succ, hinv.runOffset_eq, hempty_ℓ]
      simp [ha]
  · -- Split the old slot stream around bucket `a`'s run.
    set pref :=
      (List.range a).flatMap fun j => taggedRun (bucketRun S quot rem (probeSlot b o j))
    set suff :=
      ((List.range (ℓ - a)).map (a + 1 + ·)).flatMap fun j =>
        taggedRun (bucketRun S quot rem (probeSlot b o j))
    have hpref_len : pref.length = s₀ := hs₀_eq.symm
    have hL₀_split :
        (List.range ℓ).map (slotPair st o) = pref ++ taggedRun xs ++ suff := by
      have h1 :
          ((List.range (ℓ + 1)).flatMap fun j =>
            taggedRun (bucketRun S quot rem (probeSlot b o j))) =
          (List.range ℓ).flatMap fun j =>
            taggedRun (bucketRun S quot rem (probeSlot b o j)) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, hempty_ℓ,
          taggedRun_nil, List.append_nil]
      change (List.range ℓ).map (fun i =>
        (st.isRunStart (probeSlot b o i), st.remAt (probeSlot b o i))) = _
      rw [hinv.slots_eq_flatMap, ← h1,
        flatMap_taggedRun_three_split S quot rem o (Nat.lt_succ_of_le ha),
        Nat.succ_sub_succ_eq_sub]
    -- `st₁` clears the old run head when `r` becomes the new head of a nonempty run.
    set M₁ : List (Bool × Fin (2 ^ f)) := if k = 0 then xs.map (false, ·) else taggedRun xs
    have hM₁_len : M₁.length = xs.length := by
      dsimp only [M₁]
      split_ifs <;> simp [length_taggedRun]
    have hL₁_split :
        (List.range ℓ).map (slotPair st₁ o) = pref ++ M₁ ++ suff := by
      by_cases hk0 : k = 0
      · have hs_eq_s₀ : s = s₀ := by omega
        cases hxs : xs with
        | nil =>
          have hocc_q : st.isOcc q = false := by
            rw [hocc q]
            simp [xs, hxs]
          have hst₁ : st₁ = st := by simp [st₁, hocc_q]
          rw [hst₁, hL₀_split]
          simp [M₁, hk0, hxs]
        | cons x₀ xs' =>
          have hocc_q : st.isOcc q = true := by
            rw [hocc q]
            simp [xs, hxs]
          have hst₁ : st₁ = st.setRunStart (probeSlot b o s₀) false := by
            simp [st₁, hocc_q, hs_eq_s₀]
          rw [hxs, taggedRun_cons] at hL₀_split
          rw [hst₁, ← hpref_len, map_slotPair_setRunStart_middle hℓ.le hL₀_split false]
          simp only [M₁, hk0, ↓reduceIte, hxs, List.map_cons]
      · have hs_ne_s₀ : ¬(s = s₀) := by omega
        have hst₁ : st₁ = st := by simp [st₁, hs_ne_s₀]
        rw [hst₁, hL₀_split]
        simp [M₁, hk0]
    -- Shifting right and writing `r` at slot `s` inserts it into bucket `a`'s run.
    have hdec_eq : decide (s = s₀) = decide (k = 0) := by
      rw [hs_eq]
      simp
    have hshift := map_slotPair_shiftRight st₁ o hs_le_ℓ hℓ (decide (s = s₀)) r
    change (List.range (ℓ + 1)).map (slotPair st₃ o) = _ at hshift
    have hst₄_eq :
        (List.range (ℓ + 1)).map (fun i =>
          (st₄.isRunStart (probeSlot b o i), st₄.remAt (probeSlot b o i))) =
        (List.range (ℓ + 1)).map (slotPair st₃ o) := rfl
    rw [hst₄_eq, hshift, hdec_eq, hL₁_split, hs_eq, ← hpref_len,
      take_append_drop_middle pref M₁ suff (decide (k = 0), r) (by omega),
      taggedRun_insert_split xs r hk_le,
      ← orderedInsert_eq_take_append_drop_of_pairwise (r := r) (pairwise_le_bucketRun S quot rem q),
      ← hins_q, flatMap_taggedRun_three_split_of_eq (Nat.lt_succ_of_le ha) hoff,
      Nat.succ_sub_succ_eq_sub]

theorem IntervalValid.take_of_runOffset_eq {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {e ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ) (he : e ≤ ℓ)
    (hrun_e : runOffset S quot rem o e = e) :
    IntervalValid S quot rem st o e where
  full_of_lt i hi := hinv.full_of_lt i (by omega)
  prefix_le_runOffset m hm := hinv.prefix_le_runOffset m (by omega)
  slots_eq_flatMap := (hinv.slots_split he hrun_e).1

theorem IntervalValid.deleteCluster_intervalValid {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState b f} {o : Fin (2 ^ b)} {ℓ : ℕ}
    (hinv : IntervalValid S quot rem st o ℓ)
    (hocc : ∀ q : Fin (2 ^ b), st.isOcc q = !(bucketRun S quot rem q).isEmpty)
    (hℓ : ℓ ≤ 2 ^ b)
    {u : Fin U} (hu : u ∈ S) {a : ℕ} (ha : a < ℓ) (hq : quot u = probeSlot b o a) :
    let e := calcDeleteStop st o a ℓ
    let st' := deleteCluster st o a ℓ (rem u)
    IntervalValid (S.erase u) quot rem st' o (e - 1) ∧
      st'.isOcc (probeSlot b o a) =
        !(bucketRun (S.erase u) quot rem (probeSlot b o a)).isEmpty ∧
      bucketRun (S.erase u) quot rem (probeSlot b o (e - 1)) = [] := by
  let r := rem u
  let q := probeSlot b o a
  set xs := bucketRun S quot rem q
  set k := xs.countP (· < r)
  set s₀ := calcRunStart st o a ℓ
  set s := calcTargetSlot st o a ℓ r
  set e := calcDeleteStop st o a ℓ
  have hspec : a < e ∧ e ≤ ℓ ∧ runOffset S quot rem o e = e ∧
      ∀ m, a ≤ m → m + 1 < e → m + 2 ≤ runOffset S quot rem o (m + 1) :=
    hinv.calcDeleteStop_spec hocc ha
  obtain ⟨ha_lt_e, he_le, he_run, he_min⟩ := hspec
  have hr_mem : r ∈ xs := (mem_bucketRun_iff S quot rem q r).mpr ⟨u, hu, hq, rfl⟩
  have hxs_ne : xs ≠ [] := List.ne_nil_of_mem hr_mem
  have hpw : xs.Pairwise (· ≤ ·) := pairwise_le_bucketRun S quot rem q
  have herase_split : xs.erase r = xs.take k ++ xs.drop (k + 1) :=
    erase_eq_take_append_drop_of_pairwise hpw hr_mem
  have hk_lt : k < xs.length := by grind [List.length_append, List.length_take, List.length_drop]
  have hs₀_eq : s₀ = runOffset S quot rem o a := hinv.calcRunStart_eq hocc ha.le
  have hs_eq : s = s₀ + k := by
    rw [hs₀_eq]
    exact hinv.calcTargetSlot_eq hocc ha r
  have hs₀_len_le_e : s₀ + xs.length ≤ e := by
    have h1 : runOffset S quot rem o (a + 1) = s₀ + xs.length := by
      rw [hs₀_eq]
      exact runOffset_succ S quot rem o a
    have h2 : runOffset S quot rem o (a + 1) ≤ e := by
      rw [← he_run]
      exact runOffset_mono S quot rem o (by omega)
    omega
  have hs_lt_e : s < e := by omega
  have her_q : bucketRun (S.erase u) quot rem q = xs.erase r := by
    dsimp only [xs, q, r]
    rw [← hq, bucketRun_erase_self quot rem hu]
  have hoff : ∀ j < ℓ, j ≠ a →
      bucketRun S quot rem (probeSlot b o j) = bucketRun (S.erase u) quot rem (probeSlot b o j) :=
    fun j hj hja => (bucketRun_erase_probeSlot_of_ne S quot rem hq (by omega) (by omega) hja).symm
  -- Erasing `u` removes one entry from bucket `a`, so later run offsets drop by one.
  have hrun_erase : ∀ m ≤ ℓ,
      runOffset S quot rem o m =
        runOffset (S.erase u) quot rem o m + if a < m then 1 else 0 := by
    refine runOffset_eq_add_of_length_succ hoff ?_
    change xs.length = (bucketRun (S.erase u) quot rem q).length + 1
    rw [her_q, List.length_erase_of_mem hr_mem]
    have := List.length_pos_iff.mpr hxs_ne
    omega
  -- After the deletion, the run of slot `e - 1` (now empty) ends the cluster.
  have hempty_e1 : bucketRun (S.erase u) quot rem (probeSlot b o (e - 1)) = [] := by
    have hre := hrun_erase e he_le
    have hre1 := hrun_erase (e - 1) (by omega)
    have hsucc := runOffset_succ (S.erase u) quot rem o (e - 1)
    rw [show e - 1 + 1 = e by omega] at hsucc
    rw [ite_eq_left ha_lt_e] at hre
    by_cases hlt : a < e - 1
    · have := he_min (e - 2) (by omega) (by omega)
      rw [show e - 2 + 1 = e - 1 by omega] at this
      rw [ite_eq_left hlt] at hre1
      exact List.eq_nil_of_length_eq_zero (by omega)
    · have := hinv.le_runOffset (m := e - 1) (by omega)
      rw [ite_eq_right hlt] at hre1
      exact List.eq_nil_of_length_eq_zero (by omega)
  set hasMore := decide (s₀ + 1 < e) && !st.isRunStart (probeSlot b o (s₀ + 1))
  set st₁ := shiftLeft st o s (e - 1 - s)
  set st₂ := if !hasMore then
    st₁.setOcc q false
  else if s = s₀ then
    st₁.setRunStart (probeSlot b o s₀) true
  else
    st₁
  set p_end := probeSlot b o (e - 1)
  set st₃ := ((st₂.setFull p_end false).setRunStart p_end false).setRem p_end ⟨0, Nat.two_pow_pos f⟩
  change IntervalValid (S.erase u) quot rem st₃ o (e - 1) ∧
    st₃.isOcc q = !(bucketRun (S.erase u) quot rem q).isEmpty ∧
    bucketRun (S.erase u) quot rem p_end = []
  -- Split the slot stream of `[0, e)` around bucket `a`'s run.
  have hinv_e : IntervalValid S quot rem st o e := hinv.take_of_runOffset_eq he_le he_run
  set pref :=
    (List.range a).flatMap fun j => taggedRun (bucketRun S quot rem (probeSlot b o j))
  set suff :=
    ((List.range (e - (a + 1))).map (a + 1 + ·)).flatMap fun j =>
      taggedRun (bucketRun S quot rem (probeSlot b o j))
  have hpref_len : pref.length = s₀ := hs₀_eq.symm
  have hM_split :
      (List.range e).map (slotPair st o) = pref ++ taggedRun xs ++ suff := by
    change (List.range e).map (fun i =>
      (st.isRunStart (probeSlot b o i), st.remAt (probeSlot b o i))) = _
    rw [hinv_e.slots_eq_flatMap]
    exact flatMap_taggedRun_three_split S quot rem o ha_lt_e
  -- Shifting left over slot `s` removes the `k`-th entry of bucket `a`'s run.
  have hshift := map_slotPair_shiftLeft st o hs_lt_e (he_le.trans hℓ)
  change (List.range (e - 1)).map (slotPair st₁ o) = _ at hshift
  rw [hM_split, hs_eq, ← hpref_len,
    take_append_drop_succ_middle pref (taggedRun xs) suff (by simp [hk_lt])] at hshift
  have hst₃_eq :
      (List.range (e - 1)).map (fun i =>
        (st₃.isRunStart (probeSlot b o i), st₃.remAt (probeSlot b o i))) =
      (List.range (e - 1)).map (slotPair st₂ o) := by
    refine List.map_congr_left fun i hi => ?_
    have hi_lt : i < e - 1 := List.mem_range.mp hi
    have hne_end : probeSlot b o i ≠ p_end := probeSlot_ne o (by omega) (by omega) (by omega)
    simp [st₃, slotPair, hne_end]
  -- Bucket `a` keeps a run exactly when `xs` has a second entry, which `hasMore` detects.
  have hst₂_split_and_occ :
      (List.range (e - 1)).map (slotPair st₂ o) = pref ++ taggedRun (xs.erase r) ++ suff ∧
        st₃.isOcc q = !(xs.erase r).isEmpty := by
    rw [herase_split]
    rcases hxs : xs with _ | ⟨x₀, _ | ⟨x₁, xs'⟩⟩
    · exact absurd hxs hxs_ne
    · have hk0 : k = 0 := by
        have : xs.length = 1 := by simp [hxs]
        omega
      -- The slot after the deleted entry, if any, starts the next run.
      have hnot_more : hasMore = false := by
        dsimp only [hasMore]
        by_cases hlt : s₀ + 1 < e
        · have hsuff_ne : suff ≠ [] := by
            intro hnil
            have hlen := congrArg List.length hM_split
            simp [hpref_len, hxs, hnil] at hlen
            omega
          obtain ⟨p, rest, hsuff_cons⟩ := List.exists_cons_of_ne_nil hsuff_ne
          have hp_fst : p.1 = true :=
            fst_head_nonempty_flatMap_taggedRun ((List.range (e - (a + 1))).map (a + 1 + ·))
              (fun j => bucketRun S quot rem (probeSlot b o j)) hsuff_cons
          rw [hxs, hsuff_cons] at hM_split
          have hfst := congrArg Prod.fst (slotPair_of_map_eq_append hM_split).2
          simp only [slotPair, List.length_append, hpref_len, length_taggedRun, List.length_cons,
            List.length_nil, hp_fst] at hfst
          simp [hfst]
        · simp [hlt]
      have hst₂ : st₂ = st₁.setOcc q false := by simp [st₂, hnot_more]
      refine ⟨?_, ?_⟩
      · rw [hst₂]
        change (List.range (e - 1)).map (slotPair st₁ o) = _
        rw [hshift, hxs, hk0]
        simp
      · rw [hk0]
        simp [st₃, hst₂]
    · have hs1_lt : s₀ + 1 < e := by
        have : xs.length = xs'.length + 2 := by simp [hxs]
        omega
      -- The slot after the run head continues the run, so bucket `a` stays occupied.
      have hrun_s1 : st.isRunStart (probeSlot b o (s₀ + 1)) = false := by
        have h' : (List.range e).map (slotPair st o) =
            (pref ++ [(true, x₀)]) ++ (false, x₁) :: (xs'.map (false, ·) ++ suff) := by
          rw [hM_split, hxs]
          simp [taggedRun_cons]
        have hfst := congrArg Prod.fst (slotPair_of_map_eq_append h').2
        simpa only [slotPair, List.length_append, hpref_len, List.length_singleton] using hfst
      have hmore : hasMore = true := by simp [hasMore, hs1_lt, hrun_s1]
      have hocc_q : st.isOcc q = true := by
        rw [hocc q]
        simp [xs, hxs]
      refine ⟨?_, ?_⟩
      · rcases hk : k with _ | k'
        · -- Deleting the run head promotes the next entry to run head.
          have hs_eq_s₀ : s = s₀ := by omega
          have hst₂ : st₂ = st₁.setRunStart (probeSlot b o s₀) true := by
            simp [st₂, hmore, hs_eq_s₀]
          rw [hxs, hk] at hshift
          simp only [taggedRun_cons, List.map_cons, List.take_zero, List.nil_append,
            List.drop_succ_cons, List.drop_zero] at hshift
          rw [hst₂, ← hpref_len, map_slotPair_setRunStart_middle (by omega) hshift true]
          simp [taggedRun_cons]
        · have hs_ne_s₀ : ¬(s = s₀) := by omega
          have hst₂ : st₂ = st₁ := by simp [st₂, hmore, hs_ne_s₀]
          have hk'_lt : k' + 1 < (x₀ :: x₁ :: xs').length := by
            rw [← hxs, ← hk]
            exact hk_lt
          rw [hst₂, hshift, hxs, hk, taggedRun_delete_split_succ (x₀ :: x₁ :: xs') k' hk'_lt]
      · have hst₃_occ : st₃.isOcc q = st.isOcc q := by
          by_cases hs : s = s₀ <;> simp [st₃, st₂, st₁, hmore, hs]
        rw [hst₃_occ, hocc_q]
        cases k <;> simp
  refine ⟨⟨?_, ?_, ?_⟩, ?_, hempty_e1⟩
  · intro i hi
    have hne_end : probeSlot b o i ≠ p_end := probeSlot_ne o (by omega) (by omega) (by omega)
    have hst₂_full : st₂.isFull (probeSlot b o i) = true := by
      dsimp only [st₂]
      split_ifs <;> simp [st₁, hinv.full_of_lt i (by omega)]
    simp [st₃, hne_end, hst₂_full]
  · intro m hm
    have hm1 := hrun_erase (m + 1) (by omega)
    by_cases hlt : a < m + 1
    · have := he_min m (by omega) (by omega)
      rw [ite_eq_left hlt] at hm1
      omega
    · have := hinv.prefix_le_runOffset m (by omega)
      rw [ite_eq_right hlt] at hm1
      omega
  · rw [hst₃_eq, hst₂_split_and_occ.1, ← her_q]
    have h1 :
        ((List.range e).flatMap fun j =>
          taggedRun (bucketRun (S.erase u) quot rem (probeSlot b o j))) =
        (List.range (e - 1)).flatMap fun j =>
          taggedRun (bucketRun (S.erase u) quot rem (probeSlot b o j)) := by
      have hr : List.range e = List.range (e - 1) ++ [e - 1] := by
        rw [← List.range_succ]
        exact congrArg List.range (by omega)
      rw [hr, List.flatMap_append, List.flatMap_singleton, hempty_e1, taggedRun_nil,
        List.append_nil]
    rw [← h1, flatMap_taggedRun_three_split_of_eq ha_lt_e fun j hj hja =>
      (hoff j (by omega) hja).symm]
  · rw [her_q, hst₂_split_and_occ.2]

/-! ## Section 7: Global `FilterInv` preservation under `insert` and `delete` -/

theorem backSlot_probeSlot_self {b : ℕ} (q : Fin (2 ^ b)) (d : ℕ) :
    backSlot b (probeSlot b q d) d = q := by
  apply Fin.ext
  simp only [backSlot, probeSlot, Dictionary.WordRAM.LinearProbing.cyclicSlotMod]
  have h1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hd : d ≤ 2 ^ b * (d + 1) := by
    calc d ≤ 1 * (d + 1) := by omega
      _ ≤ 2 ^ b * (d + 1) := Nat.mul_le_mul_right (d + 1) h1
  have hsub : ((q.val + d) % 2 ^ b + 2 ^ b * (d + 1) - d) % 2 ^ b =
      ((q.val + d) % 2 ^ b + (2 ^ b * (d + 1) - d)) % 2 ^ b := by
    congr 1
    omega
  rw [hsub, Nat.mod_add_mod, show q.val + d + (2 ^ b * (d + 1) - d) =
      q.val + 2 ^ b * (d + 1) by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt q.isLt]

theorem probeSlot_left_cancel {b : ℕ} {q₁ q₂ : Fin (2 ^ b)} {d : ℕ}
    (h : probeSlot b q₁ d = probeSlot b q₂ d) : q₁ = q₂ := by
  have := congrArg (fun p => backSlot b p d) h
  simpa [backSlot_probeSlot_self] using this

/-- The slot before offset `i + 1` from `o` is offset `i`. -/
private theorem backSlot_probeSlot_succ {b : ℕ} (o : Fin (2 ^ b)) (i : ℕ) :
    backSlot b (probeSlot b o (i + 1)) 1 = probeSlot b o i := by
  rw [← probeSlot_add, backSlot_probeSlot_self]

/-- The slot before `o` is not among the next `2 ^ b - 1` offsets from `o`. -/
private theorem backSlot_one_ne_probeSlot {b : ℕ} (o : Fin (2 ^ b)) {i : ℕ}
    (hi : i + 1 < 2 ^ b) : backSlot b o 1 ≠ probeSlot b o i := by
  intro h_eq
  have h1 : probeSlot b (backSlot b o 1) 1 = probeSlot b (probeSlot b o i) 1 := by rw [h_eq]
  rw [probeSlot_backSlot_add o 1 0, probeSlot_add] at h1
  exact probeSlot_ne o (by omega) hi (by omega) h1

theorem maximal_full_eq_or_disjoint {b : ℕ} (isFull : Fin (2 ^ b) → Bool)
    {o₁ o₂ : Fin (2 ^ b)} {ℓ₁ ℓ₂ : ℕ}
    (hback₁ : isFull (backSlot b o₁ 1) = false)
    (hend₁ : isFull (probeSlot b o₁ ℓ₁) = false)
    (hfull₁ : ∀ i < ℓ₁, isFull (probeSlot b o₁ i) = true)
    (hback₂ : isFull (backSlot b o₂ 1) = false)
    (hend₂ : isFull (probeSlot b o₂ ℓ₂) = false)
    (hfull₂ : ∀ j < ℓ₂, isFull (probeSlot b o₂ j) = true) :
    (o₁ = o₂ ∧ ℓ₁ = ℓ₂) ∨ ∀ i ≤ ℓ₁, ∀ j < ℓ₂, probeSlot b o₁ i ≠ probeSlot b o₂ j := by
  by_cases hdisj : ∀ i ≤ ℓ₁, ∀ j < ℓ₂, probeSlot b o₁ i ≠ probeSlot b o₂ j
  · exact Or.inr hdisj
  · left
    push Not at hdisj
    obtain ⟨i, hi_le, j, hj_lt, heq⟩ := hdisj
    have hi_lt : i < ℓ₁ := by grind
    have hij : i = j := by
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · have h1 : probeSlot b (backSlot b o₁ 1) (1 + i) =
            probeSlot b (probeSlot b o₂ (j - 1 - i)) (1 + i) := by
          rw [probeSlot_backSlot_add o₁ 1 i, probeSlot_add,
            show j - 1 - i + (1 + i) = j by omega, heq]
        have h2 := probeSlot_left_cancel h1
        have h3 := hback₁
        rw [h2, hfull₂ (j - 1 - i) (by omega)] at h3
        cases h3
      · rfl
      · have h1 : probeSlot b (probeSlot b o₁ (i - 1 - j)) (1 + j) =
            probeSlot b (backSlot b o₂ 1) (1 + j) := by
          rw [probeSlot_backSlot_add o₂ 1 j, probeSlot_add,
            show i - 1 - j + (1 + j) = i by omega, heq]
        have h2 := probeSlot_left_cancel h1
        have h3 := hback₂
        rw [← h2, hfull₁ (i - 1 - j) (by omega)] at h3
        cases h3
    subst hij
    have ho : o₁ = o₂ := probeSlot_left_cancel heq
    subst ho
    refine ⟨rfl, ?_⟩
    rcases lt_trichotomy ℓ₁ ℓ₂ with hlt | rfl | hgt
    · have h1 := hend₁
      rw [hfull₂ ℓ₁ hlt] at h1
      cases h1
    · rfl
    · have h1 := hend₂
      rw [hfull₁ ℓ₂ hgt] at h1
      cases h1

theorem isFull_insertCluster {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a ℓ : ℕ)
    (r : Fin (2 ^ f)) (p : Fin (2 ^ b)) :
    (insertCluster st o a ℓ r).isFull p =
      if p = probeSlot b o ℓ then true else st.isFull p := by
  dsimp only [insertCluster]
  split_ifs <;> simp [*]

theorem isOcc_insertCluster {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a ℓ : ℕ)
    (r : Fin (2 ^ f)) (p : Fin (2 ^ b)) :
    (insertCluster st o a ℓ r).isOcc p =
      if p = probeSlot b o a then true else st.isOcc p := by
  dsimp only [insertCluster]
  split_ifs <;> simp [*]

theorem insertCluster_outside {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a ℓ : ℕ)
    (r : Fin (2 ^ f)) (p : Fin (2 ^ b)) (hp : ∀ i ≤ ℓ, p ≠ probeSlot b o i) :
    (insertCluster st o a ℓ r).isRunStart p = st.isRunStart p ∧
      (insertCluster st o a ℓ r).remAt p = st.remAt p := by
  set s₀ := calcRunStart st o a ℓ
  set s := calcTargetSlot st o a ℓ r
  have hs₀_le : s₀ ≤ ℓ := by
    dsimp only [s₀, calcRunStart]
    exact (List.length_filter_le _ _).trans (by simp)
  have hs_le : s ≤ ℓ := by
    dsimp only [s, calcTargetSlot]
    exact (List.length_filter_le _ _).trans (by simp)
  have hne_s₀ : p ≠ probeSlot b o s₀ := hp s₀ hs₀_le
  have hne_s : p ≠ probeSlot b o s := hp s hs_le
  set st₁ := if st.isOcc (probeSlot b o a) && decide (s = s₀) then
    st.setRunStart (probeSlot b o s₀) false
  else
    st
  have hst₁ : st₁.isRunStart p = st.isRunStart p ∧ st₁.remAt p = st.remAt p := by
    dsimp only [st₁]
    split_ifs <;> simp [hne_s₀]
  have hshift := shiftRight_outside st₁ o s (ℓ - s) p (fun d hd => hp (s + d + 1) (by omega))
  dsimp only [insertCluster]
  change (((shiftRight st₁ o s (ℓ - s)).setRunStart (probeSlot b o s)
    (decide (s = s₀))).setRem (probeSlot b o s) r).isRunStart p = st.isRunStart p ∧
    (((shiftRight st₁ o s (ℓ - s)).setRunStart (probeSlot b o s)
      (decide (s = s₀))).setRem (probeSlot b o s) r).remAt p = st.remAt p
  simp [hne_s, hshift.1, hshift.2, hst₁.1, hst₁.2]

theorem isFull_deleteCluster {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a ℓ : ℕ)
    (r : Fin (2 ^ f)) (p : Fin (2 ^ b)) :
    (deleteCluster st o a ℓ r).isFull p =
      if p = probeSlot b o (calcDeleteStop st o a ℓ - 1) then false else st.isFull p := by
  dsimp only [deleteCluster]
  split_ifs <;> simp [*]

theorem deleteCluster_outside {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) {a ℓ : ℕ}
    (ha : a < calcDeleteStop st o a ℓ)
    (r : Fin (2 ^ f)) (p : Fin (2 ^ b))
    (hp : ∀ i < calcDeleteStop st o a ℓ, p ≠ probeSlot b o i) :
    (deleteCluster st o a ℓ r).isRunStart p = st.isRunStart p ∧
      (deleteCluster st o a ℓ r).remAt p = st.remAt p := by
  set s₀ := calcRunStart st o a ℓ
  set s := calcTargetSlot st o a ℓ r
  set e := calcDeleteStop st o a ℓ
  set hasMore := decide (s₀ + 1 < e) && !st.isRunStart (probeSlot b o (s₀ + 1))
  let st₁ := shiftLeft st o s (e - 1 - s)
  have hshift : st₁.isRunStart p = st.isRunStart p ∧ st₁.remAt p = st.remAt p :=
    shiftLeft_outside st o s (e - 1 - s) p (fun d hd => hp (s + d) (by omega))
  have hne_end : p ≠ probeSlot b o (e - 1) := hp (e - 1) (by omega)
  let st₂ := if !hasMore then
    st₁.setOcc (probeSlot b o a) false
  else if s = s₀ then
    st₁.setRunStart (probeSlot b o s₀) true
  else
    st₁
  have hst₂ : st₂.isRunStart p = st.isRunStart p ∧ st₂.remAt p = st.remAt p := by
    dsimp only [st₂]
    by_cases h1 : (!hasMore) = true
    · simp [h1, hshift.1, hshift.2]
    · simp only [h1]
      by_cases h2 : s = s₀
      · have hs₀_lt_e : s₀ < e := by grind
        have hne_s₀ : p ≠ probeSlot b o s₀ := hp s₀ hs₀_lt_e
        simp [h2, hne_s₀, hshift.1, hshift.2]
      · simp [h2, hshift.1, hshift.2]
  dsimp only [deleteCluster]
  change (((st₂.setFull (probeSlot b o (e - 1)) false).setRunStart (probeSlot b o (e - 1))
    false).setRem (probeSlot b o (e - 1)) ⟨0, Nat.two_pow_pos f⟩).isRunStart p =
      st.isRunStart p ∧
    (((st₂.setFull (probeSlot b o (e - 1)) false).setRunStart (probeSlot b o (e - 1))
      false).setRem (probeSlot b o (e - 1)) ⟨0, Nat.two_pow_pos f⟩).remAt p = st.remAt p
  simp [hne_end, hst₂.1, hst₂.2]

/-- Pure quotient-filter state update for `insert u`. -/
@[expose] noncomputable def FilterInv.insertState {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (u : Fin U) : FilterState b f :=
  insertCluster st (hinv.clusterStart hS_lt (quot u))
    (hinv.backLen hS_lt (quot u)) (hinv.clusterLen hS_lt (quot u)) (rem u)

/-- Pure quotient-filter state update for `delete u`. -/
@[expose] noncomputable def FilterInv.deleteState {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (u : Fin U) : FilterState b f :=
  deleteCluster st (hinv.clusterStart hS_lt (quot u))
    (hinv.backLen hS_lt (quot u)) (hinv.clusterLen hS_lt (quot u)) (rem u)

/-- The cluster around `quot u`: bucket `quot u` sits at offset `backLen` from `clusterStart`, and
the slots just before and just after the cluster are empty. -/
private theorem FilterInv.cluster_spec {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) (hS_lt : #S < 2 ^ b) (q : Fin (2 ^ b)) :
    q = probeSlot b (hinv.clusterStart hS_lt q) (hinv.backLen hS_lt q) ∧
      st.isFull (backSlot b (hinv.clusterStart hS_lt q) 1) = false ∧
      st.isFull (probeSlot b (hinv.clusterStart hS_lt q) (hinv.clusterLen hS_lt q)) = false := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 := probeSlot_backSlot_add q (hinv.backLen hS_lt q) 0
    rw [add_zero, probeSlot_zero] at h1
    exact h1.symm
  · dsimp only [clusterStart]
    rw [backSlot_backSlot]
    exact hinv.isFull_backSlot_succ_backLen hS_lt q
  · dsimp only [clusterStart, clusterLen]
    rw [probeSlot_backSlot_add]
    exact hinv.isFull_probeSlot_fwdLen hS_lt q

/-- Under `FilterInv`, the bucket of an empty slot has no run. -/
private theorem FilterInv.bucketRun_eq_nil_of_isFull_eq_false {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) {p : Fin (2 ^ b)} (hp : st.isFull p = false) :
    bucketRun S quot rem p = [] := by
  have h1 := hinv.isOcc_eq p
  rw [(hinv.empty_slot p hp).1] at h1
  cases h : bucketRun S quot rem p
  · rfl
  · simp [h] at h1

/-- A valid interval whose slots avoid the slots `[o₀ .. o₀ + ℓ₀]` rewritten by `insertCluster`
stays valid after inserting `u` into bucket `probeSlot b o₀ a` of that cluster. -/
private theorem IntervalValid.insertCluster_of_disjoint {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    {o o₀ : Fin (2 ^ b)} {ℓ a ℓ₀ : ℕ} {u : Fin U}
    (hvalid : IntervalValid S quot rem st o ℓ)
    (hdisj : ∀ j < ℓ, ∀ i ≤ ℓ₀, probeSlot b o j ≠ probeSlot b o₀ i)
    (ha : a ≤ ℓ₀) (hq : quot u = probeSlot b o₀ a) :
    IntervalValid (insert u S) quot rem (insertCluster st o₀ a ℓ₀ (rem u)) o ℓ := by
  refine hvalid.congr (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
  · refine bucketRun_insert_of_ne S quot rem u ?_
    rw [hq]
    exact (hdisj j hj a ha).symm
  · rw [isFull_insertCluster, ite_eq_right (hdisj j hj ℓ₀ le_rfl)]
  · have hout := insertCluster_outside st o₀ a ℓ₀ (rem u) (probeSlot b o j) (hdisj j hj)
    dsimp only [slotPair]
    rw [hout.1, hout.2]

/-- A valid interval whose slots avoid the slots `[o₀ .. o₀ + e)` rewritten by `deleteCluster`
stays valid after erasing `u` from bucket `probeSlot b o₀ a` of that cluster. -/
private theorem IntervalValid.deleteCluster_of_disjoint {U b f : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    {o o₀ : Fin (2 ^ b)} {ℓ a ℓ₀ : ℕ} {u : Fin U}
    (hvalid : IntervalValid S quot rem st o ℓ)
    (ha : a < calcDeleteStop st o₀ a ℓ₀)
    (hdisj : ∀ j < ℓ, ∀ i < calcDeleteStop st o₀ a ℓ₀, probeSlot b o j ≠ probeSlot b o₀ i)
    (hq : quot u = probeSlot b o₀ a) :
    IntervalValid (S.erase u) quot rem (deleteCluster st o₀ a ℓ₀ (rem u)) o ℓ := by
  refine hvalid.congr (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
  · refine bucketRun_erase_of_ne S quot rem u ?_
    rw [hq]
    exact (hdisj j hj a ha).symm
  · rw [isFull_deleteCluster,
      ite_eq_right (hdisj j hj (calcDeleteStop st o₀ a ℓ₀ - 1) (by omega))]
  · have hout := deleteCluster_outside st o₀ ha (rem u) (probeSlot b o j) (hdisj j hj)
    dsimp only [slotPair]
    rw [hout.1, hout.2]

/-- **Global `FilterInv` preservation under `insert`**: inserting `u ∉ S` (when `#(insert u S) ≤ n`
and `#(insert u S) < 2 ^ b`) preserves `FilterInv`. -/
theorem FilterInv.insertState_filterInv {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) {u : Fin U} (hu : u ∉ S)
    (hcap : #(insert u S) ≤ n) (hS'_lt : #(insert u S) < 2 ^ b) :
    FilterInv n (insert u S) quot rem
      (hinv.insertState (by rw [Finset.card_insert_of_notMem hu] at hS'_lt; omega) u) := by
  have hS_lt : #S < 2 ^ b := by rw [Finset.card_insert_of_notMem hu] at hS'_lt; omega
  have hcard_ins : #(insert u S) = #S + 1 := Finset.card_insert_of_notMem hu
  obtain ⟨hq_eq, hback_o₀, hfull_end₀⟩ := hinv.cluster_spec hS_lt (quot u)
  set q := quot u
  set a := hinv.backLen hS_lt q
  set t := hinv.fwdLen hS_lt q
  set o₀ := hinv.clusterStart hS_lt q
  set ℓ₀ := hinv.clusterLen hS_lt q
  set st' := hinv.insertState hS_lt u
  have hst'_def : st' = insertCluster st o₀ a ℓ₀ (rem u) := rfl
  have ha_le : a ≤ ℓ₀ := Nat.le_add_right a t
  have hℓ₀_le_S : ℓ₀ ≤ #S := hinv.clusterLen_le_card hS_lt q
  have hℓ₀_lt : ℓ₀ < 2 ^ b := lt_of_le_of_lt hℓ₀_le_S hS_lt
  have hvalid₀ : IntervalValid S quot rem st o₀ ℓ₀ := hinv.intervalValid_cluster hS_lt q
  have hempty_ℓ₀ : bucketRun S quot rem (probeSlot b o₀ ℓ₀) = [] :=
    hinv.bucketRun_eq_nil_of_isFull_eq_false hfull_end₀
  have hocc' : ∀ p : Fin (2 ^ b), st'.isOcc p = !(bucketRun (insert u S) quot rem p).isEmpty := by
    intro p
    rw [hst'_def, isOcc_insertCluster, ← hq_eq]
    by_cases hp : p = quot u
    · subst hp
      rw [ite_eq_left rfl, bucketRun_insert_self quot rem hu]
      have hpw := pairwise_le_bucketRun S quot rem (quot u)
      rw [orderedInsert_eq_take_append_drop_of_pairwise (r := rem u) hpw]
      cases List.take (List.countP (· < rem u) (bucketRun S quot rem (quot u)))
        (bucketRun S quot rem (quot u)) <;> rfl
    · rw [ite_eq_right hp,
        bucketRun_insert_of_ne S quot rem u (Ne.symm hp), hinv.isOcc_eq p]
  refine ⟨hcap, hocc', ?_, ?_, ?_⟩
  · intro p hp_empty
    rw [hst'_def, isFull_insertCluster] at hp_empty
    have hp_ne_end : p ≠ probeSlot b o₀ ℓ₀ := by
      rintro rfl
      simp at hp_empty
    rw [ite_eq_right hp_ne_end] at hp_empty
    have hp_outside : ∀ i ≤ ℓ₀, p ≠ probeSlot b o₀ i := by
      intro i hi
      rcases lt_or_eq_of_le hi with hlt | rfl
      · rintro rfl
        have := hvalid₀.full_of_lt i hlt
        rw [hp_empty] at this
        cases this
      · exact hp_ne_end
    have hout := insertCluster_outside st o₀ a ℓ₀ (rem u) p hp_outside
    have hp_ne_a : p ≠ probeSlot b o₀ a := hp_outside a ha_le
    have hocc_p : st'.isOcc p = st.isOcc p := by
      rw [hst'_def, isOcc_insertCluster, ite_eq_right hp_ne_a]
    rw [hocc_p, hst'_def, hout.1, hout.2]
    exact hinv.empty_slot p hp_empty
  · have hfilter :
        (Finset.univ.filter fun p : Fin (2 ^ b) => st'.isFull p = true) =
          insert (probeSlot b o₀ ℓ₀)
            (Finset.univ.filter fun p : Fin (2 ^ b) => st.isFull p = true) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        hst'_def, isFull_insertCluster]
      by_cases hp : p = probeSlot b o₀ ℓ₀ <;> simp [hp]
    have hnotMem :
        probeSlot b o₀ ℓ₀ ∉ Finset.univ.filter (fun p : Fin (2 ^ b) => st.isFull p = true) := by
      simp [hfull_end₀]
    rw [hfilter, Finset.card_insert_of_notMem hnotMem, hinv.card_full_eq, hcard_ins]
  · intro o ℓ hℓ_le hback hend hfull
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ_pos
    · exact intervalValid_zero (insert u S) quot rem st' o
    -- The new cluster is the old one, the filled slot `o₀ + ℓ₀`, and the cluster after it.
    · set p₁ := probeSlot b o₀ (ℓ₀ + 1)
      set ℓ₂ := hinv.fwdLen hS_lt p₁
      have hback_p₁ : st.isFull (backSlot b p₁ 1) = false := by
        have h1 : backSlot b p₁ 1 = probeSlot b o₀ ℓ₀ := backSlot_probeSlot_succ o₀ ℓ₀
        rw [h1]
        exact hfull_end₀
      have hend_p₁ : st.isFull (probeSlot b p₁ ℓ₂) = false :=
        hinv.isFull_probeSlot_fwdLen hS_lt p₁
      have hfull_p₁ : ∀ i < ℓ₂, st.isFull (probeSlot b p₁ i) = true :=
        fun i hi => hinv.isFull_probeSlot_of_lt_fwdLen hS_lt p₁ hi
      have hℓ₂_le_S : ℓ₂ ≤ #S :=
        (hinv.fwdLen_le_sub hS_lt p₁).trans (Nat.sub_le _ _)
      have hvalid_p₁ : IntervalValid S quot rem st p₁ ℓ₂ :=
        hinv.maximal_intervalValid p₁ ℓ₂ hℓ₂_le_S hback_p₁ hend_p₁ hfull_p₁
      -- The two old clusters are disjoint sets of full slots, so together they fit in `S`.
      have hsum_le : (ℓ₀ + 1) + ℓ₂ ≤ #(insert u S) := by
        set A₁ := (Finset.range ℓ₀).image (probeSlot b o₀)
        set A₂ := (Finset.range ℓ₂).image (probeSlot b p₁)
        have hdisj_A : Disjoint A₁ A₂ := by
          rw [Finset.disjoint_left]
          intro x hx₁ hx₂
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx₁
          obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hx₂
          have hi_lt : i < ℓ₀ := Finset.mem_range.mp hi
          have hj_lt : j < ℓ₂ := Finset.mem_range.mp hj
          rcases maximal_full_eq_or_disjoint st.isFull hback_o₀ hfull_end₀ hvalid₀.full_of_lt
            hback_p₁ hend_p₁ hfull_p₁ with ⟨ho_eq, _⟩ | hdisj
          · have h1 : probeSlot b o₀ (ℓ₀ + 1) = probeSlot b o₀ 0 := by
              rw [probeSlot_zero]
              exact ho_eq.symm
            exact probeSlot_ne o₀ (by omega) (by omega) (by omega) h1
          · exact hdisj i hi_lt.le j hj_lt heq.symm
        have hcard_union : #(A₁ ∪ A₂) ≤ #S := by
          refine hinv.card_full_slots_le (A₁ ∪ A₂) fun x hx => ?_
          rcases Finset.mem_union.mp hx with hx₁ | hx₂
          · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx₁
            exact hvalid₀.full_of_lt i (Finset.mem_range.mp hi)
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx₂
            exact hfull_p₁ j (Finset.mem_range.mp hj)
        rw [Finset.card_union_of_disjoint hdisj_A,
          Finset.card_image_of_injOn (probeSlot_injOn_range o₀ hℓ₀_lt.le),
          Finset.card_image_of_injOn (probeSlot_injOn_range p₁ (hℓ₂_le_S.trans hS_lt.le)),
          Finset.card_range, Finset.card_range] at hcard_union
        omega
      have hvalid'_p₁ : IntervalValid (insert u S) quot rem st' p₁ ℓ₂ := by
        rw [hst'_def]
        refine hvalid_p₁.insertCluster_of_disjoint (fun j hj i hi => ?_) ha_le hq_eq
        dsimp only [p₁]
        rw [probeSlot_add]
        exact probeSlot_ne o₀ (by omega) (by omega) (by omega)
      have hvalid'_left : IntervalValid (insert u S) quot rem st' o₀ (ℓ₀ + 1) :=
        hvalid₀.insertCluster_intervalValid hinv.isOcc_eq hℓ₀_lt hempty_ℓ₀ hu ha_le hq_eq
      have hvalid'_merged : IntervalValid (insert u S) quot rem st' o₀ ((ℓ₀ + 1) + ℓ₂) :=
        hvalid'_left.append hvalid'_p₁
      have hback'_o₀ : st'.isFull (backSlot b o₀ 1) = false := by
        have hne_b : backSlot b o₀ 1 ≠ probeSlot b o₀ ℓ₀ :=
          backSlot_one_ne_probeSlot o₀ (by omega)
        rw [hst'_def, isFull_insertCluster, ite_eq_right hne_b, hback_o₀]
      have hend'_o₀ : st'.isFull (probeSlot b o₀ ((ℓ₀ + 1) + ℓ₂)) = false := by
        have hne_e : probeSlot b o₀ ((ℓ₀ + 1) + ℓ₂) ≠ probeSlot b o₀ ℓ₀ :=
          probeSlot_ne o₀ (by omega) hℓ₀_lt (by omega)
        rw [hst'_def, isFull_insertCluster, ite_eq_right hne_e,
          ← probeSlot_add o₀ (ℓ₀ + 1) ℓ₂]
        exact hend_p₁
      rcases maximal_full_eq_or_disjoint st'.isFull hback'_o₀ hend'_o₀ hvalid'_merged.full_of_lt
        hback hend hfull with ⟨rfl, rfl⟩ | hdisj
      · exact hvalid'_merged
      -- A maximal interval disjoint from the merged cluster was already maximal before.
      · have hne_back : backSlot b o 1 ≠ probeSlot b o₀ ℓ₀ := by
          intro h_eq
          have h1 : st'.isFull (probeSlot b o₀ ℓ₀) = true :=
            hvalid'_merged.full_of_lt ℓ₀ (by omega)
          rw [← h_eq, hback] at h1
          cases h1
        have hne_end : probeSlot b o ℓ ≠ probeSlot b o₀ ℓ₀ := by
          intro h_eq
          have h1 : st'.isFull (probeSlot b o₀ ℓ₀) = true :=
            hvalid'_merged.full_of_lt ℓ₀ (by omega)
          rw [← h_eq, hend] at h1
          cases h1
        have hback_st : st.isFull (backSlot b o 1) = false := by
          rw [hst'_def, isFull_insertCluster, ite_eq_right hne_back] at hback
          exact hback
        have hend_st : st.isFull (probeSlot b o ℓ) = false := by
          rw [hst'_def, isFull_insertCluster, ite_eq_right hne_end] at hend
          exact hend
        have hfull_st : ∀ j < ℓ, st.isFull (probeSlot b o j) = true := by
          intro j hj
          have hne_j : probeSlot b o j ≠ probeSlot b o₀ ℓ₀ :=
            (hdisj ℓ₀ (by omega) j hj).symm
          have h1 := hfull j hj
          rw [hst'_def, isFull_insertCluster, ite_eq_right hne_j] at h1
          exact h1
        have hℓ_le_S : ℓ ≤ #S := by
          set A := (Finset.range ℓ).image (probeSlot b o)
          have hcard := hinv.card_full_slots_le A fun x hx => by
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
            exact hfull_st j (Finset.mem_range.mp hj)
          rwa [Finset.card_image_of_injOn (probeSlot_injOn_range o (hℓ_le.trans hS'_lt.le)),
            Finset.card_range] at hcard
        have hvalid_o : IntervalValid S quot rem st o ℓ :=
          hinv.maximal_intervalValid o ℓ hℓ_le_S hback_st hend_st hfull_st
        rw [hst'_def]
        exact hvalid_o.insertCluster_of_disjoint
          (fun j hj i hi => (hdisj i (by omega) j hj).symm) ha_le hq_eq

theorem isOcc_deleteCluster_of_ne {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a ℓ : ℕ)
    (r : Fin (2 ^ f)) {p : Fin (2 ^ b)} (hp : p ≠ probeSlot b o a) :
    (deleteCluster st o a ℓ r).isOcc p = st.isOcc p := by
  dsimp only [deleteCluster]
  split_ifs <;> simp [hp]

theorem deleteCluster_at_end {b f : ℕ} (st : FilterState b f) (o : Fin (2 ^ b)) (a ℓ : ℕ)
    (r : Fin (2 ^ f)) :
    let p_end := probeSlot b o (calcDeleteStop st o a ℓ - 1)
    (deleteCluster st o a ℓ r).isRunStart p_end = false ∧
      (deleteCluster st o a ℓ r).remAt p_end = ⟨0, Nat.two_pow_pos f⟩ := by
  dsimp only [deleteCluster]
  simp

/-- **Global `FilterInv` preservation under `delete`**: deleting `u ∈ S` (when `#S < 2 ^ b`)
preserves `FilterInv`. -/
theorem FilterInv.deleteState_filterInv {U b f n : ℕ} {S : Finset (Fin U)}
    {quot : Fin U → Fin (2 ^ b)} {rem : Fin U → Fin (2 ^ f)} {st : FilterState b f}
    (hinv : FilterInv n S quot rem st) {u : Fin U} (hu : u ∈ S) (hS_lt : #S < 2 ^ b) :
    FilterInv n (S.erase u) quot rem (hinv.deleteState hS_lt u) := by
  obtain ⟨hq_eq, hback_o₀, hfull_end₀⟩ := hinv.cluster_spec hS_lt (quot u)
  set q := quot u
  set a := hinv.backLen hS_lt q
  set t := hinv.fwdLen hS_lt q
  set o₀ := hinv.clusterStart hS_lt q
  set ℓ₀ := hinv.clusterLen hS_lt q
  set st' := hinv.deleteState hS_lt u
  have hst'_def : st' = deleteCluster st o₀ a ℓ₀ (rem u) := rfl
  have hℓ₀_le_S : ℓ₀ ≤ #S := hinv.clusterLen_le_card hS_lt q
  have hℓ₀_lt : ℓ₀ < 2 ^ b := lt_of_le_of_lt hℓ₀_le_S hS_lt
  have hvalid₀ : IntervalValid S quot rem st o₀ ℓ₀ := hinv.intervalValid_cluster hS_lt q
  -- Bucket `q` holds `rem u`, so its slot is full and lies strictly inside the cluster.
  have ha_lt : a < ℓ₀ := by
    have hr_mem : rem u ∈ bucketRun S quot rem q :=
      (mem_bucketRun_iff S quot rem q (rem u)).mpr ⟨u, hu, rfl, rfl⟩
    have hfull_q : st.isFull q = true := by
      cases h : st.isFull q
      · rw [hinv.bucketRun_eq_nil_of_isFull_eq_false h] at hr_mem
        cases hr_mem
      · rfl
    refine lt_of_le_of_ne (Nat.le_add_right a t) fun ha_eq => ?_
    rw [← ha_eq, ← hq_eq, hfull_q] at hfull_end₀
    cases hfull_end₀
  let e := calcDeleteStop st o₀ a ℓ₀
  obtain ⟨ha_lt_e, he_le, he_run, _⟩ := hvalid₀.calcDeleteStop_spec hinv.isOcc_eq ha_lt
  obtain ⟨hvalid'_left, hocc'_q, hempty_e1⟩ :=
    hvalid₀.deleteCluster_intervalValid hinv.isOcc_eq hℓ₀_lt.le hu ha_lt hq_eq
  have hocc' : ∀ p : Fin (2 ^ b), st'.isOcc p = !(bucketRun (S.erase u) quot rem p).isEmpty := by
    intro p
    by_cases hp : p = probeSlot b o₀ a
    · subst hp
      exact hocc'_q
    · have hne_q : q ≠ p := by
        rw [hq_eq]
        exact Ne.symm hp
      rw [hst'_def, isOcc_deleteCluster_of_ne st o₀ a ℓ₀ (rem u) hp,
        bucketRun_erase_of_ne S quot rem u hne_q, hinv.isOcc_eq p]
  refine ⟨(Finset.card_erase_le).trans hinv.card_le, hocc', ?_, ?_, ?_⟩
  · intro p hp_empty
    rw [hst'_def, isFull_deleteCluster] at hp_empty
    by_cases hp_end : p = probeSlot b o₀ (e - 1)
    · subst hp_end
      have hocc_end : st'.isOcc (probeSlot b o₀ (e - 1)) = false := by
        rw [hocc' (probeSlot b o₀ (e - 1)), hempty_e1]
        rfl
      have hend_meta := deleteCluster_at_end st o₀ a ℓ₀ (rem u)
      exact ⟨hocc_end, hend_meta.1, hend_meta.2⟩
    · rw [ite_eq_right hp_end] at hp_empty
      have hp_out : ∀ i < e, p ≠ probeSlot b o₀ i := by
        intro i hi
        rintro rfl
        have := hvalid₀.full_of_lt i (by omega)
        rw [hp_empty] at this
        cases this
      have hout := deleteCluster_outside st o₀ ha_lt_e (rem u) p hp_out
      have hp_ne_a : p ≠ probeSlot b o₀ a := hp_out a ha_lt_e
      have hocc_p : st'.isOcc p = st.isOcc p := by
        rw [hst'_def]
        exact isOcc_deleteCluster_of_ne st o₀ a ℓ₀ (rem u) hp_ne_a
      rw [hocc_p, hst'_def, hout.1, hout.2]
      exact hinv.empty_slot p hp_empty
  · have hfilter :
        (Finset.univ.filter fun p : Fin (2 ^ b) => st'.isFull p = true) =
          (Finset.univ.filter fun p : Fin (2 ^ b) => st.isFull p = true).erase
            (probeSlot b o₀ (e - 1)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        hst'_def, isFull_deleteCluster]
      by_cases hp : p = probeSlot b o₀ (e - 1) <;> simp [hp, e]
    have hmem :
        probeSlot b o₀ (e - 1) ∈
          Finset.univ.filter (fun p : Fin (2 ^ b) => st.isFull p = true) := by
      simp [hvalid₀.full_of_lt (e - 1) (by omega)]
    rw [hfilter, Finset.card_erase_of_mem hmem, hinv.card_full_eq, Finset.card_erase_of_mem hu]
  · intro o ℓ hℓ_le hback hend hfull
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ_pos
    · exact intervalValid_zero (S.erase u) quot rem st' o
    -- The old cluster splits into the shortened left part `[o₀, o₀ + e - 1)` and the untouched
    -- right part `[o₀ + e, o₀ + ℓ₀)`.
    · set p_end := probeSlot b o₀ (e - 1)
      set p₂ := probeSlot b o₀ e
      have hvalid_right : IntervalValid S quot rem st p₂ (ℓ₀ - e) :=
        hvalid₀.drop_of_runOffset_eq he_le he_run
      have hvalid'_right : IntervalValid (S.erase u) quot rem st' p₂ (ℓ₀ - e) := by
        rw [hst'_def]
        refine hvalid_right.deleteCluster_of_disjoint ha_lt_e (fun j hj i hi => ?_) hq_eq
        dsimp only [p₂]
        rw [probeSlot_add]
        exact probeSlot_ne o₀ (by omega) (by omega) (by omega)
      have hback'_o₀ : st'.isFull (backSlot b o₀ 1) = false := by
        have hne_b : backSlot b o₀ 1 ≠ probeSlot b o₀ (e - 1) :=
          backSlot_one_ne_probeSlot o₀ (by omega)
        rw [hst'_def, isFull_deleteCluster, ite_eq_right hne_b, hback_o₀]
      have hend'_left : st'.isFull (probeSlot b o₀ (e - 1)) = false := by
        rw [hst'_def, isFull_deleteCluster, ite_eq_left rfl]
      have hback'_p₂ : st'.isFull (backSlot b p₂ 1) = false := by
        have h1 : backSlot b p₂ 1 = probeSlot b o₀ (e - 1) := by
          have h2 := backSlot_probeSlot_succ o₀ (e - 1)
          rwa [Nat.sub_add_cancel (by omega : 1 ≤ e)] at h2
        rw [h1]
        exact hend'_left
      have hend'_p₂ : st'.isFull (probeSlot b p₂ (ℓ₀ - e)) = false := by
        have h1 : probeSlot b p₂ (ℓ₀ - e) = probeSlot b o₀ ℓ₀ := by
          dsimp only [p₂]
          rw [probeSlot_add, Nat.add_sub_of_le he_le]
        have hne_e : probeSlot b o₀ ℓ₀ ≠ probeSlot b o₀ (e - 1) :=
          probeSlot_ne o₀ hℓ₀_lt (by omega) (by omega)
        rw [h1, hst'_def, isFull_deleteCluster, ite_eq_right hne_e, hfull_end₀]
      rcases maximal_full_eq_or_disjoint st'.isFull hback'_o₀ hend'_left hvalid'_left.full_of_lt
        hback hend hfull with ⟨rfl, rfl⟩ | hdisj₁
      · exact hvalid'_left
      · rcases maximal_full_eq_or_disjoint st'.isFull hback'_p₂ hend'_p₂ hvalid'_right.full_of_lt
          hback hend hfull with ⟨rfl, rfl⟩ | hdisj₂
        · exact hvalid'_right
        -- A maximal interval disjoint from both parts avoids the whole old cluster.
        · have hdisj_all : ∀ i ≤ ℓ₀, ∀ j < ℓ, probeSlot b o₀ i ≠ probeSlot b o j := by
            intro i hi j hj
            by_cases hle : i ≤ e - 1
            · exact hdisj₁ i hle j hj
            · have hi_eq : i = e + (i - e) := by omega
              rw [hi_eq, ← probeSlot_add]
              exact hdisj₂ (i - e) (by omega) j hj
          have hne_back : backSlot b o 1 ≠ p_end := by
            intro h_eq
            have h1 : probeSlot b (backSlot b o 1) 1 = probeSlot b p_end 1 :=
              congrArg (fun p => probeSlot b p 1) h_eq
            rw [probeSlot_backSlot_add o 1 0] at h1
            dsimp only [p_end] at h1
            rw [probeSlot_add, show e - 1 + 1 = e by omega] at h1
            exact hdisj_all e he_le 0 hℓ_pos h1.symm
          have hfull_st : ∀ j < ℓ, st.isFull (probeSlot b o j) = true := by
            intro j hj
            have hne_j : probeSlot b o j ≠ p_end := (hdisj_all (e - 1) (by omega) j hj).symm
            have h1 := hfull j hj
            rw [hst'_def, isFull_deleteCluster, ite_eq_right hne_j] at h1
            exact h1
          -- The slot before `p_end` is empty (`e = 1`) or in the left part, while the slot
          -- before `o + ℓ` is full and outside the old cluster.
          have hne_end : probeSlot b o ℓ ≠ p_end := by
            intro h_eq
            have h1 : backSlot b p_end 1 = probeSlot b o (ℓ - 1) := by
              rw [← h_eq, ← backSlot_probeSlot_succ o (ℓ - 1), Nat.sub_add_cancel (by omega)]
            have hfull_prev := hfull_st (ℓ - 1) (by omega)
            rw [← h1] at hfull_prev
            rcases Nat.eq_zero_or_pos (e - 1) with he0 | he_pos
            · dsimp only [p_end] at hfull_prev
              rw [he0, probeSlot_zero, hback_o₀] at hfull_prev
              cases hfull_prev
            · have hp_end_prev : backSlot b p_end 1 = probeSlot b o₀ (e - 2) := by
                dsimp only [p_end]
                rw [show e - 1 = e - 2 + 1 by omega, backSlot_probeSlot_succ]
              rw [hp_end_prev] at h1
              exact hdisj_all (e - 2) (by omega) (ℓ - 1) (by omega) h1
          have hback_st : st.isFull (backSlot b o 1) = false := by
            rw [hst'_def, isFull_deleteCluster, ite_eq_right hne_back] at hback
            exact hback
          have hend_st : st.isFull (probeSlot b o ℓ) = false := by
            rw [hst'_def, isFull_deleteCluster, ite_eq_right hne_end] at hend
            exact hend
          have hℓ_le_S : ℓ ≤ #S := hℓ_le.trans Finset.card_erase_le
          have hvalid_o : IntervalValid S quot rem st o ℓ :=
            hinv.maximal_intervalValid o ℓ hℓ_le_S hback_st hend_st hfull_st
          rw [hst'_def]
          exact hvalid_o.deleteCluster_of_disjoint ha_lt_e
            (fun j hj i hi => (hdisj_all i (by omega) j hj).symm) hq_eq

end Cslib.DataStructure.ApproximateMembership.QuotientFilter
