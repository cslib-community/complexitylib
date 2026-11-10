/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Sort.Bitonic.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Bool.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# The zero-one argument for bitonic splitting

Thresholding a tuple at any pivot preserves its four-point bitonic invariant. A finite
kernel-checked Boolean lemma therefore proves that pairwise minima and maxima of two halves
remain bitonic over every linear order.

## Main results

* `Cslib.BitonicSort.IsBitonic.min_halves`: pairwise minima preserve the invariant.
* `Cslib.BitonicSort.IsBitonic.max_halves`: pairwise maxima preserve the invariant.

## References

* Adapted from MassProduction/SortingSemantics/Boolean.lean and the threshold argument in
  SortingSemantics/Internal.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.BitonicSort

variable {α : Type*}

/-- Pairwise minima of the two Boolean halves used by the finite cleaning
check. -/
private def boolHalfMin (sequence : Fin 8 → Bool) : Fin 4 → Bool :=
  fun i => min (sequence (Fin.castAdd 4 i)) (sequence (Fin.natAdd 4 i))

-- Any strictly increasing quadruple in `Fin 4` is `(0, 1, 2, 3)`, and six four-point
-- bitonic constraints on `input` suffice to discharge the resulting eight-bit check.
private theorem bool_min_bitonic (input : Fin 8 → Bool) (h : IsBitonic input) :
    IsBitonic (boolHalfMin input) := by
  intro i j k l hij hjk hkl
  obtain ⟨rfl, rfl, rfl, rfl⟩ : i = 0 ∧ j = 1 ∧ k = 2 ∧ l = 3 := by
    refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;> lia
  have h0123 := h 0 1 2 3 (by decide) (by decide) (by decide)
  have h0127 := h 0 1 2 7 (by decide) (by decide) (by decide)
  have h0167 := h 0 1 6 7 (by decide) (by decide) (by decide)
  have h1234 := h 1 2 3 4 (by decide) (by decide) (by decide)
  have h2345 := h 2 3 4 5 (by decide) (by decide) (by decide)
  have h4567 := h 4 5 6 7 (by decide) (by decide) (by decide)
  change (min (min (input 0) (input 4)) (min (input 2) (input 6)) ≤
      max (min (input 1) (input 5)) (min (input 3) (input 7))) ∧
    (min (min (input 1) (input 5)) (min (input 3) (input 7)) ≤
      max (min (input 0) (input 4)) (min (input 2) (input 6)))
  revert h0123 h0127 h0167 h1234 h2345 h4567
  generalize input 0 = b0, input 1 = b1, input 2 = b2, input 3 = b3,
    input 4 = b4, input 5 = b5, input 6 = b6, input 7 = b7
  decide +revert

private def threshold [LinearOrder α] (pivot value : α) : Bool :=
  decide (pivot ≤ value)

private theorem threshold_mono [LinearOrder α] (pivot : α) :
    Monotone (threshold pivot) := by
  intro first second hle
  simp only [threshold, decide_eq_true_eq, Bool.le_iff_imp]
  exact fun hpivot => hpivot.trans hle

@[simp] private theorem threshold_min [LinearOrder α]
    (pivot first second : α) :
    threshold pivot (min first second) =
      min (threshold pivot first) (threshold pivot second) := by
  simp only [threshold, Bool.min_eq_and, Bool.decide_and, le_min_iff]

@[simp] private theorem threshold_max [LinearOrder α]
    (pivot first second : α) :
    threshold pivot (max first second) =
      max (threshold pivot first) (threshold pivot second) := by
  simp only [threshold, Bool.max_eq_or, Bool.decide_or, le_max_iff]

private theorem bitonic_threshold [LinearOrder α] {n : ℕ}
    {sequence : Fin n → α} (hsequence : IsBitonic sequence)
    (pivot : α) :
    IsBitonic (fun i => threshold pivot (sequence i)) := by
  intro i j k l hij hjk hkl
  have h := hsequence i j k l hij hjk hkl
  constructor
  · rw [← threshold_min, ← threshold_max]
    exact threshold_mono pivot h.1
  · rw [← threshold_min, ← threshold_max]
    exact threshold_mono pivot h.2

@[simp] private theorem finAppend_addNat_self {n : ℕ}
    (first second : Fin n → α) (i : Fin n) :
    Fin.append first second (i.addNat n) = second i := by
  simpa only [Fin.natAdd_eq_addNat] using Fin.append_right first second i

private def selectFour {n : ℕ} (i j k l : Fin n) : Fin 4 → Fin n :=
  ![i, j, k, l]

@[simp] private theorem selectFour_zero {n : ℕ} (i j k l : Fin n) :
    selectFour i j k l 0 = i := rfl

@[simp] private theorem selectFour_one {n : ℕ} (i j k l : Fin n) :
    selectFour i j k l 1 = j := rfl

@[simp] private theorem selectFour_two {n : ℕ} (i j k l : Fin n) :
    selectFour i j k l 2 = k := rfl

@[simp] private theorem selectFour_three {n : ℕ} (i j k l : Fin n) :
    selectFour i j k l 3 = l := rfl

private theorem selectFour_strictMono {n : ℕ} (i j k l : Fin n)
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    StrictMono (selectFour i j k l) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro index
  fin_cases index <;> assumption

private def embedEight {n : ℕ} (i j k l : Fin n) : Fin 8 → Fin (n + n) :=
  fun index =>
    if hleft : index.val < 4 then
      Fin.castAdd n (selectFour i j k l ⟨index.val, hleft⟩)
    else
      Fin.natAdd n
        (selectFour i j k l ⟨index.val - 4, by lia⟩)

private theorem embedEight_strictMono {n : ℕ} (i j k l : Fin n)
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    StrictMono (embedEight i j k l) := by
  intro first second hlt
  unfold embedEight
  split_ifs with hfirst hsecond
  · change
      (selectFour i j k l ⟨first.val, hfirst⟩).val <
        (selectFour i j k l ⟨second.val, hsecond⟩).val
    apply selectFour_strictMono i j k l hij hjk hkl
    exact hlt
  · change
      (selectFour i j k l ⟨first.val, hfirst⟩).val <
        n + (selectFour i j k l ⟨second.val - 4, by lia⟩).val
    have hbound := (selectFour i j k l ⟨first.val, hfirst⟩).isLt
    lia
  · exfalso
    lia
  · change
      n + (selectFour i j k l ⟨first.val - 4, by lia⟩).val <
        n + (selectFour i j k l ⟨second.val - 4, by lia⟩).val
    apply Nat.add_lt_add_left
    apply selectFour_strictMono i j k l hij hjk hkl
    simp only [Fin.mk_lt_mk]
    lia

private theorem IsBitonic.comp_strictMono
    [LinearOrder α] {n m : ℕ} {sequence : Fin n → α}
    (hsequence : IsBitonic sequence) {embed : Fin m → Fin n}
    (hembed : StrictMono embed) :
    IsBitonic (fun index => sequence (embed index)) := by
  intro i j k l hij hjk hkl
  exact hsequence _ _ _ _ (hembed hij) (hembed hjk) (hembed hkl)

private theorem localEight_bitonic [LinearOrder α] {n : ℕ}
    (first second : Fin n → α)
    (hsequence : IsBitonic (Fin.append first second))
    (i j k l : Fin n) (hij : i < j) (hjk : j < k) (hkl : k < l) :
    IsBitonic
      ![first i, first j, first k, first l,
        second i, second j, second k, second l] := by
  have hselected := IsBitonic.comp_strictMono hsequence
    (embedEight_strictMono i j k l hij hjk hkl)
  have hequal :
      (fun index => Fin.append first second (embedEight i j k l index)) =
        ![first i, first j, first k, first l,
          second i, second j, second k, second l] := by
    funext index
    fin_cases index <;>
      simp [embedEight, selectFour]
  rw [hequal] at hselected
  exact hselected

/-- The minima of corresponding entries in the two halves of a bitonic tuple are bitonic. -/
theorem IsBitonic.min_halves [LinearOrder α] {n : ℕ}
    (first second : Fin n → α)
    (hsequence : IsBitonic (Fin.append first second)) :
    IsBitonic (min first second) := by
  intro i j k l hij hjk hkl
  let localSequence : Fin 8 → α :=
    ![first i, first j, first k, first l,
      second i, second j, second k, second l]
  have hlocal : IsBitonic localSequence :=
    localEight_bitonic first second hsequence
      i j k l hij hjk hkl
  have hhalf (pivot : α) :
      boolHalfMin (fun index => threshold pivot (localSequence index)) =
        fun index => threshold pivot
          (min first second (selectFour i j k l index)) := by
    funext index
    fin_cases index <;>
      simp [boolHalfMin, localSequence, selectFour]
  have reflect (a b : α) (h : ∀ pivot, threshold pivot a ≤ threshold pivot b) : a ≤ b := by
    have htrue := Bool.le_iff_imp.mp (h a) (by simp [threshold])
    exact of_decide_eq_true htrue
  have hbool (pivot : α) := bool_min_bitonic _ (bitonic_threshold hlocal pivot)
  constructor
  · apply reflect
    intro pivot
    simpa only [hhalf, selectFour_zero, selectFour_one, selectFour_two, selectFour_three,
      threshold_min, threshold_max] using (hbool pivot 0 1 2 3 (by lia) (by lia) (by lia)).1
  · apply reflect
    intro pivot
    simpa only [hhalf, selectFour_zero, selectFour_one, selectFour_two, selectFour_three,
      threshold_min, threshold_max] using (hbool pivot 0 1 2 3 (by lia) (by lia) (by lia)).2

/-- Reversing the value order exchanges the two four-point inequalities. -/
theorem IsBitonic.dual [LinearOrder α] {n : ℕ} {input : Fin n → α}
    (h : IsBitonic input) : IsBitonic (κ := OrderDual α) input := by
  intro i j k l hij hjk hkl
  exact (h i j k l hij hjk hkl).symm

/-- The maxima of corresponding entries in the two halves of a bitonic tuple are bitonic. -/
theorem IsBitonic.max_halves [LinearOrder α] {n : ℕ} (first second : Fin n → α)
    (h : IsBitonic (Fin.append first second)) : IsBitonic (max first second) :=
  (IsBitonic.min_halves (α := OrderDual α) first second h.dual).dual

end Cslib.BitonicSort
