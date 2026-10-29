/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Place

/-!
# Meaning of the native Chan–He placement writes

## Main results

* `Place.heavyList_nodup`: compact output retains injective enumeration.
* `Place.memory_heavy`: each compact cell contains its original signed integer.

## References

These memory proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Place

open Cslib.WordRAM.Signed

/-- Selecting a subsequence preserves injective input enumeration. -/
theorem heavyList_nodup (values : ℕ → ℤ) (n M : ℕ)
    (hinj : Set.InjOn values (↑(Finset.range n) : Set ℕ)) :
    (heavyList values n M n).Nodup := by
  rw [heavyList_eq_filter]
  apply List.Nodup.map_on
  · intro i hi j hj he
    exact hinj (Finset.mem_range.mpr (List.mem_range.mp (List.mem_filter.mp hi).1))
      (Finset.mem_range.mpr (List.mem_range.mp (List.mem_filter.mp hj).1)) he
  · exact List.nodup_range.filter _

/-- The number returned by the scan is the exact cardinality of the existing heavy subset. -/
theorem length_heavyList (values : ℕ → ℤ) (n : ℕ) {M : ℕ} (hM : 0 < M)
    (hinj : Set.InjOn values (↑(Finset.range n) : Set ℕ)) :
    (heavyList values n M n).length =
      (Cslib.Algorithms.ThreeSum.ChanHe.heavy ((Finset.range n).image values) M).card := by
  rw [← heavyList_toFinset values n hM hinj]
  exact (List.toFinset_card_of_nodup (heavyList_nodup values n M hinj)).symm

/-- Every compact cell is written once, without padding or a tag. Unused capacity retains
its arbitrary old contents. -/
theorem memory_heavy (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M out dst col dist t : ℕ)
    (neg : Bool) (hdisj : out + n ≤ dst) {k : ℕ} (hk : k ≤ n)
    {j : ℕ} (hj : j < (heavyList values n M k).length) :
    memory mem values n M out dst col dist t neg k (out + j) =
      encode ((heavyList values n M k)[j]) := by
  induction k generalizing j with
  | zero => simp only [heavyList, List.length_nil] at hj; omega
  | succ k ih =>
    let L := heavyList values n M k
    have hl : L.length ≤ k := length_heavyList_le values n M k
    have hlen : (heavyList values n M k).length = L.length := rfl
    by_cases hh : 1 < Histogram.count (fun i => residueKey M (values i)) n
        (residueKey M (values k))
    · have hlist : heavyList values n M (k + 1) = L ++ [values k] := by
        simp only [heavyList, hh, ↓reduceIte, L]
      simp only [hlist] at hj ⊢
      simp only [memory, write, hh, ↓reduceIte]
      by_cases hj' : j < L.length
      · rw [Function.update_of_ne (by omega), ih (by omega) hj']
        rw [List.getElem_append_left hj']
      · have he : j = L.length := by
          simp only [List.length_append, List.length_singleton] at hj
          omega
        subst j
        rw [Function.update_self]
        simp
    · have hlist : heavyList values n M (k + 1) = L := by
        simp only [heavyList, hh, ↓reduceIte, List.append_nil, L]
      simp only [hlist] at hj ⊢
      simp only [memory, write, hh, ↓reduceIte]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact ih (by omega) hj

/-- The signed target keys identify exactly the same buckets as the original keys. -/
theorem targetKey_eq_iff {M : ℕ} (hM : 0 < M) (neg : Bool) (a b : ℤ) :
    targetKey M neg a = targetKey M neg b ↔ residueKey M a = residueKey M b := by
  rw [targetKey_eq hM, targetKey_eq hM]
  cases neg
  · rfl
  · exact residueKey_neg_eq_iff hM a b

/-- The two copies cannot alias another bucket's cells. -/
theorem targetKey_eq_of_address_eq {M dst col dist r s : ℕ} (hr : r < M) (hs : s < M)
    (hd : dist = 0 ∨ dist = 4 * M) {a : ℕ}
    (ha : a = dst + 4 * r + col ∨ a = dst + 4 * r + col + dist)
    (hb : a = dst + 4 * s + col ∨ a = dst + 4 * s + col + dist) : r = s := by
  rcases hd with hd | hd <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega

/-- A light entry is written to all of its required cells, and no later input can overwrite it.
The count-one hypothesis itself proves uniqueness of the position. -/
theorem memory_light (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M out dst col dist t : ℕ)
    (neg : Bool) (hM : 0 < M) (hd : dist = 0 ∨ dist = 4 * M) (hdisj : out + n ≤ dst)
    {i k a : ℕ} (hk : k ≤ n) (hi : i < k)
    (hlight : Histogram.count (fun j => residueKey M (values j)) n
      (residueKey M (values i)) = 1)
    (ha : a = dst + 4 * targetKey M neg (values i) + col ∨
      a = dst + 4 * targetKey M neg (values i) + col + dist) :
    memory mem values n M out dst col dist t neg k a =
      encode (signedValue neg (values i) + (t : ℤ)) := by
  have ha' : dst ≤ a := by rcases ha with ha | ha <;> omega
  induction k with
  | zero => omega
  | succ k ih =>
    have hl := length_heavyList_le values n M k
    simp only [memory, write]
    by_cases hh : 1 < Histogram.count (fun j => residueKey M (values j)) n
        (residueKey M (values k))
    · rw [ite_eq_left hh, Function.update_of_ne (by omega)]
      apply ih (by omega) (by
        by_contra h
        have : i = k := by omega
        subst i
        omega)
    · rw [ite_eq_right hh]
      by_cases he : i = k
      · subst i
        rcases ha with rfl | rfl <;> simp [Function.update_apply]
      · have hne (b : ℕ)
            (hb : b = dst + 4 * targetKey M neg (values k) + col ∨
              b = dst + 4 * targetKey M neg (values k) + col + dist) : a ≠ b := by
          intro hab
          have heq := targetKey_eq_of_address_eq
            (by rw [targetKey_eq hM]; exact residueKey_lt hM _)
            (by rw [targetKey_eq hM]; exact residueKey_lt hM _) hd ha (hab ▸ hb)
          have hr := (targetKey_eq_iff hM neg (values i) (values k)).mp heq
          exact he (eq_of_count_one values n M (by omega) (by omega) hlight hr)
        rw [Function.update_of_ne (hne _ (Or.inr rfl)),
          Function.update_of_ne (hne _ (Or.inl rfl))]
        exact ih (by omega) (by omega)

/-- A packed cell to which no light input is assigned retains its initialized padding. -/
theorem memory_unwritten (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M out dst col dist t : ℕ)
    (neg : Bool) (hdisj : out + n ≤ dst) {k a : ℕ} (hk : k ≤ n) (ha : dst ≤ a)
    (hnot : ∀ i < k, Histogram.count (fun j => residueKey M (values j)) n
        (residueKey M (values i)) = 1 →
      a ≠ dst + 4 * targetKey M neg (values i) + col ∧
        a ≠ dst + 4 * targetKey M neg (values i) + col + dist) :
    memory mem values n M out dst col dist t neg k a = mem a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hl := length_heavyList_le values n M k
    simp only [memory, write]
    split_ifs with hh
    · rw [Function.update_of_ne (by omega)]
      exact ih (by omega) (fun i hi => hnot i (by omega))
    · have hc : Histogram.count (fun j => residueKey M (values j)) n
          (residueKey M (values k)) = 1 := by
        have := count_residue_pos values n M (show k < n by omega)
        omega
      obtain ⟨hne₁, hne₂⟩ := hnot k (by omega) hc
      rw [Function.update_of_ne hne₂, Function.update_of_ne hne₁]
      exact ih (by omega) (fun i hi => hnot i (by omega))

/-- The first or second packed column is exactly the existing `arrXY`, including all padding
beyond the modulus. No initial contents of the output block are required except its pattern. -/
theorem memory_arrXY (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M out dst col t U : ℕ)
    (hM : 0 < M) (hdisj : out + n ≤ dst)
    (hinj : Set.InjOn values (↑(Finset.range n) : Set ℕ)) (i : ℕ)
    (hpad : mem (dst + 4 * i + col) =
      encode (Cslib.Algorithms.ThreeSum.ChanHe.pad U + (t : ℤ))) :
    memory mem values n M out dst col 0 t false n (dst + 4 * i + col) =
      encode (Cslib.Algorithms.ThreeSum.ChanHe.arrXY
        ((Finset.range n).image values) M U i + (t : ℤ)) := by
  let S := (Finset.range n).image values
  by_cases hc : (Cslib.Algorithms.ThreeSum.ChanHe.bucket S M i).card = 1
  · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc
    have hmem : z ∈ Cslib.Algorithms.ThreeSum.ChanHe.bucket S M i := by
      rw [hz]
      exact Finset.mem_singleton_self _
    obtain ⟨hS, hres⟩ := Finset.mem_filter.mp hmem
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hS
    have hkey : residueKey M (values j) = i := by
      simp only [residueKey, hres, Int.toNat_natCast]
    have hj' := Finset.mem_range.mp hj
    have hlight : Histogram.count (fun k => residueKey M (values k)) n
        (residueKey M (values j)) = 1 := by
      rw [hkey, count_eq_card_bucket values n hM hinj]
      exact hc
    have he := memory_light mem values n M out dst col 0 t false hM (Or.inl rfl)
      hdisj le_rfl hj' hlight (a := dst + 4 * i + col)
      (Or.inl (by simp only [targetKey, Bool.false_eq_true, ↓reduceIte, hkey]))
    rw [he]
    dsimp only [S] at hc hz
    simp only [Cslib.Algorithms.ThreeSum.ChanHe.arrXY,
      Cslib.Algorithms.ThreeSum.ChanHe.arr, ↓reduceIte, hz, Finset.sum_singleton,
      Finset.card_singleton,
      signedValue, Bool.false_eq_true]
  · have he := memory_unwritten mem values n M out dst col 0 t false hdisj
      (k := n) (a := dst + 4 * i + col) le_rfl (by omega) (by
        intro j hj hlight
        have hne : dst + 4 * i + col ≠ dst + 4 * targetKey M false (values j) + col := by
          intro heq
          have hkey : residueKey M (values j) = i := by
            change dst + 4 * i + col = dst + 4 * residueKey M (values j) + col at heq
            omega
          apply hc
          rw [← count_eq_card_bucket values n hM hinj, ← hkey]
          exact hlight
        exact ⟨hne, by simpa only [Nat.add_zero] using hne⟩)
    rw [he, hpad]
    dsimp only [S] at hc
    simp only [Cslib.Algorithms.ThreeSum.ChanHe.arrXY,
      Cslib.Algorithms.ThreeSum.ChanHe.arr, hc, ↓reduceIte]

/-- Below `2M`, a residue occurs at exactly its first and second copies. -/
theorem mod_eq_iff_copies {M i r : ℕ} (hi : i < 2 * M) (hr : r < M) :
    i % M = r ↔ i = r ∨ i = r + M := by
  by_cases h : i < M
  · rw [Nat.mod_eq_of_lt h]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : M ≤ i), Nat.mod_eq_of_lt (by omega : i - M < M)]
    omega

/-- The duplicated, negated third column is exactly the existing `arrZ`. -/
theorem memory_arrZ (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M out dst col t U : ℕ)
    (hM : 0 < M) (hdisj : out + n ≤ dst)
    (hinj : Set.InjOn values (↑(Finset.range n) : Set ℕ)) (i : ℕ)
    (hpad : mem (dst + 4 * i + col) =
      encode (-Cslib.Algorithms.ThreeSum.ChanHe.pad U + (t : ℤ))) :
    memory mem values n M out dst col (4 * M) t true n (dst + 4 * i + col) =
      encode (Cslib.Algorithms.ThreeSum.ChanHe.arrZ
        ((Finset.range n).image values) M U i + (t : ℤ)) := by
  let vals := fun j => -values j
  let T := (Finset.range n).image vals
  have hT : ((Finset.range n).image values).image (fun z : ℤ => -z) = T := by
    rw [Finset.image_image]
    rfl
  have hinj' : Set.InjOn vals (↑(Finset.range n) : Set ℕ) := by
    intro j hj k hk he
    exact hinj hj hk (neg_injective he)
  have hkey (j : ℕ) : targetKey M true (values j) = residueKey M (vals j) :=
    targetKey_eq hM true _
  have hcount (j : ℕ) :
      Histogram.count (fun k => residueKey M (vals k)) n (residueKey M (vals j)) =
        Histogram.count (fun k => residueKey M (values k)) n (residueKey M (values j)) :=
    count_neg_residue values n hM j
  by_cases hi : i < 2 * M
  · by_cases hc : (Cslib.Algorithms.ThreeSum.ChanHe.bucket T M ((i % M : ℕ) : ℤ)).card = 1
    · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc
      have hmem : z ∈ Cslib.Algorithms.ThreeSum.ChanHe.bucket T M ((i % M : ℕ) : ℤ) := by
        rw [hz]
        exact Finset.mem_singleton_self _
      obtain ⟨hS, hres⟩ := Finset.mem_filter.mp hmem
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hS
      have hr : residueKey M (vals j) = i % M := by
        simp only [residueKey, hres, Int.toNat_natCast]
      have hj' := Finset.mem_range.mp hj
      have hlight : Histogram.count (fun k => residueKey M (values k)) n
          (residueKey M (values j)) = 1 := by
        rw [← hcount, hr, count_eq_card_bucket vals n hM hinj']
        exact hc
      have hcopies := (mod_eq_iff_copies hi (residueKey_lt hM (vals j))).mp hr.symm
      have he := memory_light mem values n M out dst col (4 * M) t true hM (Or.inr rfl)
        hdisj le_rfl hj' hlight (a := dst + 4 * i + col) (by
          rw [hkey]
          rcases hcopies with hc | hc
          · exact Or.inl (by omega)
          · exact Or.inr (by omega))
      rw [he]
      simp only [Cslib.Algorithms.ThreeSum.ChanHe.arrZ, hi, ↓reduceIte, hT,
        Cslib.Algorithms.ThreeSum.ChanHe.arr, hz, Finset.sum_singleton,
        Finset.card_singleton, signedValue]
      rfl
    · have he := memory_unwritten mem values n M out dst col (4 * M) t true hdisj
        (k := n) (a := dst + 4 * i + col) le_rfl (by omega) (by
          intro j hj hlight
          have hn : i % M ≠ targetKey M true (values j) := by
            intro heq
            apply hc
            rw [← count_eq_card_bucket vals n hM hinj', heq, hkey, hcount]
            exact hlight
          have hr := residueKey_lt hM (vals j)
          have hcopies := (mod_eq_iff_copies hi hr).not.mp (by simpa only [hkey] using hn)
          rw [hkey]
          constructor <;> intro heq <;> apply hcopies <;> omega)
      rw [he, hpad]
      simp only [Cslib.Algorithms.ThreeSum.ChanHe.arrZ, hi, ↓reduceIte, hT,
        Cslib.Algorithms.ThreeSum.ChanHe.arr, hc]
  · have he := memory_unwritten mem values n M out dst col (4 * M) t true hdisj
      (k := n) (a := dst + 4 * i + col) le_rfl (by omega) (by
        intro j hj hlight
        have hr : targetKey M true (values j) < M := by rw [hkey]; exact residueKey_lt hM _
        constructor <;> omega)
    rw [he, hpad]
    simp only [Cslib.Algorithms.ThreeSum.ChanHe.arrZ, hi, ↓reduceIte]

/-- Placement changes only its own packed column. -/
theorem memory_other_column (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M out dst col dist t : ℕ)
    (neg : Bool) (hdisj : out + n ≤ dst) (hc : col < 4)
    (hd : dist = 0 ∨ dist = 4 * M) (u : ℕ) (hu : u % 4 ≠ col) :
    memory mem values n M out dst col dist t neg n (dst + u) = mem (dst + u) := by
  apply memory_unwritten _ _ _ _ _ _ _ _ _ _ hdisj le_rfl (by omega)
  intro j hj hlight
  rcases hd with hd | hd <;> constructor <;> intro he <;> apply hu <;> omega

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Place
