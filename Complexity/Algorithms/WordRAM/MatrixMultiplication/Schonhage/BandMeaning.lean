/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandProgram
public import Complexity.Algorithms.MatrixMultiplication.Schonhage.SplitDigits

/-!
# Meaning of the native band indices

## Main results

* `BandPreparation.leftAt_isInner`, `BandPreparation.rightAt_isInner`: the original
  encoder numberings classify the same inner positions as the native decoder.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Encoding BandDigits

/-- Digits three through six are exactly the inner left variables. -/
theorem leftAt_isInner (d : Fin 7) : (leftAt d).IsInner ↔ ¬d.val < 3 := by decide +revert

/-- The same four digits classify the inner right variables. -/
theorem rightAt_isInner (d : Fin 7) : (rightAt d).IsInner ↔ ¬d.val < 3 := by decide +revert

/-- An outer left digit is its ordinary base-three value. -/
theorem leftAt_outer (d : Fin 7) (h : d.val < 3) :
    (leftAt d).outerIndex.val = d.val := by decide +revert

/-- An outer right digit is its ordinary base-three value. -/
theorem rightAt_outer (d : Fin 7) (h : d.val < 3) :
    (rightAt d).outerIndex.val = d.val := by decide +revert

/-- The four inner left digits use the existing row-major pair numbering. -/
theorem leftAt_inner (d : Fin 7) (h : ¬d.val < 3) :
    (finProdFinEquiv (leftAt d).innerIndex).val = d.val - 3 := by decide +revert

/-- The four inner right digits use the same pair numbering. -/
theorem rightAt_inner (d : Fin 7) (h : ¬d.val < 3) :
    (finProdFinEquiv (rightAt d).innerIndex).val = d.val - 3 := by decide +revert

private theorem filter_outer {L : ℕ} (u : Fin L → Fin 7)
    (Q : Finset (Fin L)) (hQ : ∀ ℓ, ℓ ∈ Q ↔ (u ℓ).val < 3)
    (n : ℕ) (hn : Q.card = n) (f : Fin L → ℕ)
    (hf : ∀ ℓ ∈ Q, f ℓ = (u ℓ).val) :
    (List.ofFn fun ℓ => (u ℓ).val).filter (fun d => d < 3) =
      List.ofFn (fun k => f (Q.orderEmbOfFin hn k)) := by
  rw [Finset.ofFn_orderEmbOfFin, Finset.sort_eq_filter_finRange,
    List.ofFn_eq_map, List.filter_map]
  have hp : (fun ℓ : Fin L => decide ((u ℓ).val < 3)) = (fun ℓ => decide (ℓ ∈ Q)) := by
    funext ℓ
    simp only [hQ]
  simp only [Function.comp_def, hp]
  apply List.map_congr_left
  intro ℓ hℓ
  exact (hf ℓ (by simpa only [List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq] using hℓ)).symm

/-- Base-three compression follows the increasing outer positions used by `outerPartL`. -/
theorem outer_digits_left {L m : ℕ} (u : Fin L → Fin 7)
    (h : (innerSetL (fun ℓ => leftAt (u ℓ))).card = m) :
    (List.ofFn fun ℓ => (u ℓ).val).filter (fun d => d < 3) =
      List.ofFn (fun k => (outerPartL (fun ℓ => leftAt (u ℓ)) h k).val) := by
  have hQ : ∀ ℓ, ℓ ∈ (innerSetL (fun ℓ => leftAt (u ℓ)))ᶜ ↔ (u ℓ).val < 3 := by
    intro ℓ
    simp [innerSetL, leftAt_isInner]
  apply filter_outer u (innerSetL (fun ℓ => leftAt (u ℓ)))ᶜ hQ (L - m)
    (Finset.card_compl_of_card_eq _ h) (fun ℓ => (leftAt (u ℓ)).outerIndex.val)
  intro ℓ hℓ
  exact leftAt_outer _ ((hQ ℓ).mp hℓ)

/-- Base-three compression follows the increasing outer positions used by `outerPartR`. -/
theorem outer_digits_right {L m : ℕ} (u : Fin L → Fin 7)
    (h : (innerSetR (fun ℓ => rightAt (u ℓ))).card = m) :
    (List.ofFn fun ℓ => (u ℓ).val).filter (fun d => d < 3) =
      List.ofFn (fun k => (outerPartR (fun ℓ => rightAt (u ℓ)) h k).val) := by
  have hQ : ∀ ℓ, ℓ ∈ (innerSetR (fun ℓ => rightAt (u ℓ)))ᶜ ↔ (u ℓ).val < 3 := by
    intro ℓ
    simp [innerSetR, rightAt_isInner]
  apply filter_outer u (innerSetR (fun ℓ => rightAt (u ℓ)))ᶜ hQ (L - m)
    (Finset.card_compl_of_card_eq _ h) (fun ℓ => (rightAt (u ℓ)).outerIndex.val)
  intro ℓ hℓ
  exact rightAt_outer _ ((hQ ℓ).mp hℓ)

private theorem filter_inner {L : ℕ} (u : Fin L → Fin 7)
    (Q : Finset (Fin L)) (hQ : ∀ ℓ, ℓ ∈ Q ↔ ¬(u ℓ).val < 3)
    (n : ℕ) (hn : Q.card = n) (f : Fin L → ℕ)
    (hf : ∀ ℓ ∈ Q, f ℓ = (u ℓ).val - 3) :
    (((List.ofFn fun ℓ => (u ℓ).val).filter (fun d => ¬d < 3)).map fun d => d - 3) =
      List.ofFn (fun k => f (Q.orderEmbOfFin hn k)) := by
  rw [Finset.ofFn_orderEmbOfFin, Finset.sort_eq_filter_finRange,
    List.ofFn_eq_map, List.filter_map, List.map_map]
  have hp : (fun ℓ : Fin L => decide (¬(u ℓ).val < 3)) = (fun ℓ => decide (ℓ ∈ Q)) := by
    funext ℓ
    simp only [hQ]
  simp only [Function.comp_def, hp]
  apply List.map_congr_left
  intro ℓ hℓ
  exact (hf ℓ (by simpa only [List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq] using hℓ)).symm

/-- Base-four compression follows the increasing inner positions used by `innerPartL`. -/
theorem inner_digits_left {L m : ℕ} (u : Fin L → Fin 7)
    (h : (innerSetL (fun ℓ => leftAt (u ℓ))).card = m) :
    (((List.ofFn fun ℓ => (u ℓ).val).filter (fun d => ¬d < 3)).map fun d => d - 3) =
      List.ofFn (fun k => (finProdFinEquiv (innerPartL (fun ℓ => leftAt (u ℓ)) h k)).val) := by
  have hQ : ∀ ℓ, ℓ ∈ innerSetL (fun ℓ => leftAt (u ℓ)) ↔ ¬(u ℓ).val < 3 := by
    intro ℓ
    simp [innerSetL, leftAt_isInner]
  apply filter_inner u (innerSetL (fun ℓ => leftAt (u ℓ))) hQ m h
    (fun ℓ => (finProdFinEquiv (leftAt (u ℓ)).innerIndex).val)
  intro ℓ hℓ
  exact leftAt_inner _ ((hQ ℓ).mp hℓ)

/-- The right inner index uses the identical four pair digits. -/
theorem inner_digits_right {L m : ℕ} (u : Fin L → Fin 7)
    (h : (innerSetR (fun ℓ => rightAt (u ℓ))).card = m) :
    (((List.ofFn fun ℓ => (u ℓ).val).filter (fun d => ¬d < 3)).map fun d => d - 3) =
      List.ofFn (fun k => (finProdFinEquiv (innerPartR (fun ℓ => rightAt (u ℓ)) h k)).val) := by
  have hQ : ∀ ℓ, ℓ ∈ innerSetR (fun ℓ => rightAt (u ℓ)) ↔ ¬(u ℓ).val < 3 := by
    intro ℓ
    simp [innerSetR, rightAt_isInner]
  apply filter_inner u (innerSetR (fun ℓ => rightAt (u ℓ))) hQ m h
    (fun ℓ => (finProdFinEquiv (rightAt (u ℓ)).innerIndex).val)
  intro ℓ hℓ
  exact rightAt_inner _ ((hQ ℓ).mp hℓ)

/-- Native mask compression agrees with the exact inner level set of the original array. -/
theorem parts_mask_left {L : ℕ} (a : Fin (7 ^ L)) :
    (parts L a.val).mask =
      (MaskTable.maskCode (innerSetL (fun ℓ => leftAt (finFunctionFinEquiv.symm a ℓ)))).val := by
  rw [(parts_lists L a.val).1, sevenDigits_eq_ofFn]
  change _ = (finFunctionFinEquiv (fun ℓ =>
    if ℓ ∈ innerSetL (fun ℓ => leftAt (finFunctionFinEquiv.symm a ℓ))
      then (1 : Fin 2) else 0)).val
  rw [← Nat.ofDigits_finFunctionFinEquiv, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext ℓ
  change (if (finFunctionFinEquiv.symm a ℓ).val < 3 then 0 else 1) = _
  by_cases h : (finFunctionFinEquiv.symm a ℓ).val < 3 <;>
    simp only [innerSetL, Finset.mem_filter, Finset.mem_univ, true_and,
      leftAt_isInner, h, not_true_eq_false, not_false_eq_true, ↓reduceIte,
      Fin.val_zero, Fin.val_one]

/-- The right mask is classified identically, without changing the encoder numbering. -/
theorem parts_mask_right {L : ℕ} (a : Fin (7 ^ L)) :
    (parts L a.val).mask =
      (MaskTable.maskCode (innerSetR (fun ℓ => rightAt (finFunctionFinEquiv.symm a ℓ)))).val := by
  rw [(parts_lists L a.val).1, sevenDigits_eq_ofFn]
  change _ = (finFunctionFinEquiv (fun ℓ =>
    if ℓ ∈ innerSetR (fun ℓ => rightAt (finFunctionFinEquiv.symm a ℓ))
      then (1 : Fin 2) else 0)).val
  rw [← Nat.ofDigits_finFunctionFinEquiv, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext ℓ
  change (if (finFunctionFinEquiv.symm a ℓ).val < 3 then 0 else 1) = _
  by_cases h : (finFunctionFinEquiv.symm a ℓ).val < 3 <;>
    simp only [innerSetR, Finset.mem_filter, Finset.mem_univ, true_and,
      rightAt_isInner, h, not_true_eq_false, not_false_eq_true, ↓reduceIte,
      Fin.val_zero, Fin.val_one]

/-- Native left outer offset, with the exact public mathematical string interface. -/
theorem parts_outer_left {L m : ℕ} (a : Fin (7 ^ L))
    (h : (innerSetL (fun ℓ => leftAt (finFunctionFinEquiv.symm a ℓ))).card = m) :
    (parts L a.val).outer =
      (finFunctionFinEquiv
        (outerPartL (fun ℓ => leftAt (finFunctionFinEquiv.symm a ℓ)) h)).val := by
  rw [(parts_lists L a.val).2.1, sevenDigits_eq_ofFn]
  change Nat.ofDigits 3 ((List.ofFn fun ℓ => (finFunctionFinEquiv.symm a ℓ).val).filter
    (fun d => d < 3)) = _
  rw [outer_digits_left _ h, Nat.ofDigits_finFunctionFinEquiv]

/-- Native right outer offset in the same least-significant-first convention. -/
theorem parts_outer_right {L m : ℕ} (a : Fin (7 ^ L))
    (h : (innerSetR (fun ℓ => rightAt (finFunctionFinEquiv.symm a ℓ))).card = m) :
    (parts L a.val).outer =
      (finFunctionFinEquiv
        (outerPartR (fun ℓ => rightAt (finFunctionFinEquiv.symm a ℓ)) h)).val := by
  rw [(parts_lists L a.val).2.1, sevenDigits_eq_ofFn]
  change Nat.ofDigits 3 ((List.ofFn fun ℓ => (finFunctionFinEquiv.symm a ℓ).val).filter
    (fun d => d < 3)) = _
  rw [outer_digits_right _ h, Nat.ofDigits_finFunctionFinEquiv]

/-- Native left thin-dimension offset agrees with the row-major pair digits of `Layout`. -/
theorem parts_inner_left {L m : ℕ} (a : Fin (7 ^ L))
    (h : (innerSetL (fun ℓ => leftAt (finFunctionFinEquiv.symm a ℓ))).card = m) :
    (parts L a.val).inner = (finFunctionFinEquiv fun k =>
      finProdFinEquiv (innerPartL (fun ℓ => leftAt (finFunctionFinEquiv.symm a ℓ)) h k)).val := by
  rw [(parts_lists L a.val).2.2, sevenDigits_eq_ofFn]
  change Nat.ofDigits 4 (((List.ofFn fun ℓ => (finFunctionFinEquiv.symm a ℓ).val).filter
    (fun d => ¬d < 3)).map fun d => d - 3) = _
  rw [inner_digits_left _ h, Nat.ofDigits_finFunctionFinEquiv]

/-- Native right thin-dimension offset uses the same `Layout` equivalence. -/
theorem parts_inner_right {L m : ℕ} (a : Fin (7 ^ L))
    (h : (innerSetR (fun ℓ => rightAt (finFunctionFinEquiv.symm a ℓ))).card = m) :
    (parts L a.val).inner = (finFunctionFinEquiv fun k =>
      finProdFinEquiv (innerPartR (fun ℓ => rightAt (finFunctionFinEquiv.symm a ℓ)) h k)).val := by
  rw [(parts_lists L a.val).2.2, sevenDigits_eq_ofFn]
  change Nat.ofDigits 4 (((List.ofFn fun ℓ => (finFunctionFinEquiv.symm a ℓ).val).filter
    (fun d => ¬d < 3)).map fun d => d - 3) = _
  rw [inner_digits_right _ h, Nat.ofDigits_finFunctionFinEquiv]

/-- Numeric specification of one guarded band-array read. `matrix r k` denotes an original
matrix cell (or the transposed indexing of the right matrix); the native implementation
computes its actual row-major address and loads it. -/
def bandValue (L m N β : ℕ) (rightSide : Bool) (matrix : ℕ → ℕ → ℤ) (a : ℕ) : ℤ :=
  let p := parts L a
  let q := MaskTable.lookup L m p.mask
  if q = 0 then 0 else
    let b := if rightSide then (q - 1) % K0 L m else (q - 1) / K0 L m
    let r := (β * K0 L m + b) * N0 L m + p.outer
    if r < N then matrix r p.inner else 0

/-- The numeric left-band specification is the unchanged mathematical `bandArrayL` for
the computed deterministic layout, including all unselected strings and padding. -/
theorem bandValue_left {L m N : ℕ} (hm : m ≤ L)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (matrix : ℕ → ℕ → ℤ)
    (hX : ∀ i k, matrix i.val k.val = X i k) (β : ℕ) (a : Fin (7 ^ L)) :
    bandValue L m N β false matrix a.val =
      bandArrayL (MaskTable.layout hm) X β (fun ℓ => leftAt (finFunctionFinEquiv.symm a ℓ)) := by
  let u : LeftStr L := fun ℓ => leftAt (finFunctionFinEquiv.symm a ℓ)
  let lay := MaskTable.layout hm
  have hmask : (parts L a.val).mask = (MaskTable.maskCode (innerSetL u)).val :=
    parts_mask_left a
  by_cases hz : MaskTable.lookup L m (parts L a.val).mask = 0
  · have hmissing : ∀ gh, lay.table gh ≠ innerSetL u := by
      intro gh heq
      have hc := congrArg (fun Q => (MaskTable.maskCode Q).val) heq
      change (MaskTable.maskCode (MaskTable.maskSet (MaskTable.selectedMask gh))).val = _ at hc
      rw [MaskTable.maskCode_maskSet] at hc
      have ha : (MaskTable.selectedMask gh).val = (parts L a.val).mask := hc.trans hmask.symm
      have hne : MaskTable.lookup L m (MaskTable.selectedMask gh).val ≠ 0 := by
        rw [MaskTable.lookup_selectedMask]
        omega
      exact hne (ha ▸ hz)
    have hf := bandFamilyL_eq_zero lay X β hmissing
    simp only [bandValue, ↓reduceIte, hz]
    change 0 = (arrayL m (bandFamilyL lay X β)) u
    unfold arrayL
    split <;> simp only [hf, Matrix.zero_apply]
  · obtain ⟨gh, hs⟩ := MaskTable.exists_selectedMask_of_lookup hz
    have hcode : MaskTable.selectedMask gh = MaskTable.maskCode (innerSetL u) :=
      Fin.ext (hs.trans hmask)
    have hset : lay.table gh = innerSetL u := by
      change MaskTable.maskSet (MaskTable.selectedMask gh) = _
      rw [hcode, MaskTable.maskSet_maskCode]
    have hcard : (innerSetL u).card = m := hset ▸ lay.table_card gh
    have hf : bandFamilyL lay X β (innerSetL u) = rowBlock lay X (β * K0 L m + gh.1) := by
      rw [← hset]
      exact bandFamilyL_table lay X β gh.1 gh.2
    have ho : (parts L a.val).outer = (lay.rowIdx.symm (outerPartL u hcard)).val :=
      parts_outer_left a hcard
    have hi : (parts L a.val).inner = (lay.innerIdx.symm (innerPartL u hcard)).val := by
      change (parts L a.val).inner =
        (finFunctionFinEquiv fun k => finProdFinEquiv (innerPartL u hcard k)).val
      exact parts_inner_left a hcard
    have hg : (MaskTable.lookup L m (parts L a.val).mask - 1) / K0 L m = gh.1.val := by
      rw [← hs]
      exact (MaskTable.lookup_blockPair gh).1
    change bandValue L m N β false matrix a.val = (arrayL m (bandFamilyL lay X β)) u
    rw [arrayL, dite_eq_left hcard, hf]
    simp only [bandValue, hz, ↓reduceIte, Bool.false_eq_true, hg, ho, hi,
      rowBlock, padRows]
    split_ifs with hr
    · exact hX ⟨_, hr⟩ _
    · rfl

/-- The numeric right-band specification is the unchanged mathematical `bandArrayR`.
Its natural row parameter refers to a column of the original right matrix. -/
theorem bandValue_right {L m N : ℕ} (hm : m ≤ L)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (matrix : ℕ → ℕ → ℤ)
    (hY : ∀ i k, matrix i.val k.val = Y k i) (β : ℕ) (a : Fin (7 ^ L)) :
    bandValue L m N β true matrix a.val =
      bandArrayR (MaskTable.layout hm) Y β (fun ℓ => rightAt (finFunctionFinEquiv.symm a ℓ)) := by
  let u : RightStr L := fun ℓ => rightAt (finFunctionFinEquiv.symm a ℓ)
  let lay := MaskTable.layout hm
  have hmask : (parts L a.val).mask = (MaskTable.maskCode (innerSetR u)).val :=
    parts_mask_right a
  by_cases hz : MaskTable.lookup L m (parts L a.val).mask = 0
  · have hmissing : ∀ gh, lay.table gh ≠ innerSetR u := by
      intro gh heq
      have hc := congrArg (fun Q => (MaskTable.maskCode Q).val) heq
      change (MaskTable.maskCode (MaskTable.maskSet (MaskTable.selectedMask gh))).val = _ at hc
      rw [MaskTable.maskCode_maskSet] at hc
      have ha : (MaskTable.selectedMask gh).val = (parts L a.val).mask := hc.trans hmask.symm
      have hne : MaskTable.lookup L m (MaskTable.selectedMask gh).val ≠ 0 := by
        rw [MaskTable.lookup_selectedMask]
        omega
      exact hne (ha ▸ hz)
    have hf := bandFamilyR_eq_zero lay Y β hmissing
    simp only [bandValue, ↓reduceIte, hz]
    change 0 = (arrayR m (bandFamilyR lay Y β)) u
    unfold arrayR
    split <;> simp only [hf, Matrix.zero_apply]
  · obtain ⟨gh, hs⟩ := MaskTable.exists_selectedMask_of_lookup hz
    have hcode : MaskTable.selectedMask gh = MaskTable.maskCode (innerSetR u) :=
      Fin.ext (hs.trans hmask)
    have hset : lay.table gh = innerSetR u := by
      change MaskTable.maskSet (MaskTable.selectedMask gh) = _
      rw [hcode, MaskTable.maskSet_maskCode]
    have hcard : (innerSetR u).card = m := hset ▸ lay.table_card gh
    have hf : bandFamilyR lay Y β (innerSetR u) = colBlock lay Y (β * K0 L m + gh.2) := by
      rw [← hset]
      exact bandFamilyR_table lay Y β gh.1 gh.2
    have ho : (parts L a.val).outer = (lay.colIdx.symm (outerPartR u hcard)).val :=
      parts_outer_right a hcard
    have hi : (parts L a.val).inner = (lay.innerIdx.symm (innerPartR u hcard)).val := by
      change (parts L a.val).inner =
        (finFunctionFinEquiv fun k => finProdFinEquiv (innerPartR u hcard k)).val
      exact parts_inner_right a hcard
    have hg : (MaskTable.lookup L m (parts L a.val).mask - 1) % K0 L m = gh.2.val := by
      rw [← hs]
      exact (MaskTable.lookup_blockPair gh).2
    change bandValue L m N β true matrix a.val = (arrayR m (bandFamilyR lay Y β)) u
    rw [arrayR, dite_eq_left hcard, hf]
    simp only [bandValue, hz, ↓reduceIte, hg, ho, hi, colBlock, padCols]
    split_ifs with hr
    · exact hY ⟨_, hr⟩ _
    · rfl

/-- A selected native mask ensures that its compressed offsets fit the actual matrix
dimensions, rather than merely the coarser depth-based bounds. -/
theorem selected_parts_bounds {L m : ℕ} (a : Fin (7 ^ L))
    (hz : MaskTable.lookup L m (parts L a.val).mask ≠ 0) :
    (parts L a.val).outer < N0 L m ∧ (parts L a.val).inner < D m := by
  obtain ⟨gh, hs⟩ := MaskTable.exists_selectedMask_of_lookup hz
  let u : LeftStr L := fun ℓ => leftAt (finFunctionFinEquiv.symm a ℓ)
  have hc : MaskTable.selectedMask gh = MaskTable.maskCode (innerSetL u) :=
    Fin.ext (hs.trans (parts_mask_left a))
  have hset : MaskTable.maskSet (MaskTable.selectedMask gh) = innerSetL u := by
    rw [hc, MaskTable.maskSet_maskCode]
  have hcard : (innerSetL u).card = m := hset ▸ MaskTable.card_selectedMask gh
  constructor
  · rw [parts_outer_left a hcard]
    exact (finFunctionFinEquiv (outerPartL u hcard)).isLt
  · rw [parts_inner_left a hcard]
    exact (finFunctionFinEquiv (fun k => finProdFinEquiv (innerPartL u hcard k))).isLt

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
