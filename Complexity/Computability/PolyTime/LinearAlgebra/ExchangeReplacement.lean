/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.PolyTime.Int.Table
public import Complexity.Foundations.Data.Nat.Radix
public import Complexity.Foundations.Data.Polynomial.CoeffList
public import Complexity.Foundations.LinearAlgebra.VariableCopyPlacement
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Foundations.Data.Int.Order
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.Data.List.OfFn
import Complexity.Foundations.Data.Nat.BinarySize
import Mathlib.Data.List.GetD
import Mathlib.Data.Matrix.Basic

/-!
# Polynomial-time construction of auxiliary exchange matrices and replacement rows

Executable pure-integer counterparts, Lemma 4.6 magnitude and bit-length bounds, and plain
`Turing.MultiTapeTM.ComputableInPolyTime` certificates for the auxiliary measurement matrix `C^B`
(`measurementMatrix`), swap-interpolation matrix `(R - 1)! M_0` (`M0ScaledInt`), common denominator
`d_den = (R - 1)! Q!` (`commonDenom`), and cleared replacement rows `d_den · P⃗_u(T)`
(`auxReplacementRowScaledInt`) from §§4.1–4.3 and §4.6 (Lemmas 4.1, 4.3, 4.6, and 4.7,
pp. 27–29, 33–34) of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]. Plain
`ComputableInPolyTime` certificates cover the concrete `Nat`- and `List`-encoded routines
(`decodeAuxDigits`, `encodeAuxDigits`, `commonDenom`, `auxMeasurementRowsBounded`,
`auxReplacementRowCoeffsDigits`, `auxReplacementRowCoeffsIdx`, `auxReplacementTableBounded`), while
`AuxLabel` wrappers and full-`D` aliases (`auxMeasurementRows`, `auxReplacementTable`) provide
unencoded semantic bridges to `Complexity.Foundations.LinearAlgebra.ExchangeReplacement`.

## Main definitions and results

* `Cslib.LinearAlgebra.decodeAuxDigits`, `Cslib.LinearAlgebra.encodeAuxDigits`,
  `Cslib.LinearAlgebra.encodeAuxLabel`, `Cslib.LinearAlgebra.decodeAuxLabel`,
  `Cslib.LinearAlgebra.auxLabelEquivFin`: mixed-radix `AuxLabel Q r` encoding and decoding.
* `Cslib.LinearAlgebra.size_commonDenom_le`, `Cslib.LinearAlgebra.computableInPolyTime_commonDenom`:
  bit-length bounds and polynomial-time certificates for `commonDenom Q R`.
* `Cslib.LinearAlgebra.auxMeasurementRowsBounded`, `Cslib.LinearAlgebra.auxMeasurementRows`,
  `Cslib.LinearAlgebra.isTableShape_auxMeasurementRows`,
  `Cslib.LinearAlgebra.rowEntry_auxMeasurementRows`,
  `Cslib.LinearAlgebra.measurementMatrix_mulVec_eq_zero_iff_auxMeasurementRows`,
  `Cslib.LinearAlgebra.computableInPolyTime_auxMeasurementRowsBounded`: executable `{0, 1, -1}`
  measurement matrix `C^B`, table shape, kernel correspondence, and polynomial-time construction.
* `Cslib.LinearAlgebra.auxReplacementRowCoeffs`, `Cslib.LinearAlgebra.auxReplacementTableBounded`,
  `Cslib.LinearAlgebra.natDegree_mismatchAnnihilatorScaledInt_le`,
  `Cslib.LinearAlgebra.getD_auxReplacementRowCoeffs`,
  `Cslib.LinearAlgebra.sum_row_natAbs_auxReplacementRowCoeffs_le`,
  `Cslib.LinearAlgebra.computableInPolyTime_auxReplacementTableBounded`: executable cleared integer
  replacement rows via 1D swap-orbit DP, exact `auxReplacementRowScaledInt` equality, Lemma 4.6
  bounds, and polynomial-time construction.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §§4.1–4.3 and §4.6
-/

@[expose] public section

namespace Cslib.LinearAlgebra

open Finset Matrix Polynomial Turing.MultiTapeTM

/-! ### 1. Mixed-radix `AuxLabel` encoding and decoding -/

/-- Decode `idx` in base `r` into two length-`Q` digit lists `(u₁, u₂)` via `Cslib.Radix.digit`.
Total for all `r, idx`: extracts the low `2 * Q` digits `idx / r ^ i % r` when `idx ≥ r ^ (2 * Q)`
(`0` digits at `r = 1`; at `r = 0`, slot `0` is `idx` when `0 < Q` and higher slots are `0`). -/
def decodeAuxDigits (Q r idx : ℕ) : List ℕ × List ℕ :=
  ((List.range Q).map (Cslib.Radix.digit r idx),
   (List.range Q).map fun s => Cslib.Radix.digit r idx (Q + s))

/-- Pack a pair of base-`r` digit lists `(u₁, u₂)` into a natural number via `Nat.ofDigits`. -/
def encodeAuxDigits (r : ℕ) (u : List ℕ × List ℕ) : ℕ := Nat.ofDigits r (u.1 ++ u.2)

/-- Convert `u : AuxLabel Q r` to its pair of length-`Q` natural-number digit lists. -/
def auxLabelToDigits {Q r : ℕ} (u : AuxLabel Q r) : List ℕ × List ℕ :=
  (List.ofFn (fun s => (u.1 s).1), List.ofFn (fun s => (u.2 s).1))

/-- Pack `u : AuxLabel Q r` into its mixed-radix index `< r ^ (2 * Q)`. -/
def encodeAuxLabel {Q r : ℕ} (u : AuxLabel Q r) : ℕ := encodeAuxDigits r (auxLabelToDigits u)

private theorem pos_of_pow_two_mul_pos {Q r : ℕ} (hD : 0 < r ^ (2 * Q)) (s : Fin Q) : 0 < r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exfalso; rw [zero_pow (by have := s.2; omega)] at hD; omega
  · exact hr

/-- Decode an index `idx : ℕ` into `AuxLabel Q r` whenever `0 < r ^ (2 * Q)`. -/
def decodeAuxLabel {Q r : ℕ} (hD : 0 < r ^ (2 * Q)) (idx : ℕ) : AuxLabel Q r :=
  (fun s => ⟨Cslib.Radix.digit r idx s.1, by
      rw [Cslib.Radix.digit_eq_div_pow_mod]; exact Nat.mod_lt _ (pos_of_pow_two_mul_pos hD s)⟩,
   fun s => ⟨Cslib.Radix.digit r idx (Q + s.1), by
      rw [Cslib.Radix.digit_eq_div_pow_mod]; exact Nat.mod_lt _ (pos_of_pow_two_mul_pos hD s)⟩)

/-- First coordinate list of `decodeAuxDigits Q r idx` has length `Q`. -/
@[simp] theorem length_fst_decodeAuxDigits (Q r idx : ℕ) : (decodeAuxDigits Q r idx).1.length = Q :=
  by simp only [decodeAuxDigits, List.length_map, List.length_range]

/-- Second coordinate list of `decodeAuxDigits Q r idx` has length `Q`. -/
@[simp] theorem length_snd_decodeAuxDigits (Q r idx : ℕ) : (decodeAuxDigits Q r idx).2.length = Q :=
  by simp only [decodeAuxDigits, List.length_map, List.length_range]

/-- Every digit in `(decodeAuxDigits Q r idx).1` is strictly less than `r` when `1 ≤ r`. -/
theorem mem_fst_decodeAuxDigits_lt {Q r idx a : ℕ} (hr : 1 ≤ r)
    (ha : a ∈ (decodeAuxDigits Q r idx).1) : a < r := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rw [Cslib.Radix.digit_eq_div_pow_mod]
  exact Nat.mod_lt _ hr

/-- Every digit in `(decodeAuxDigits Q r idx).2` is strictly less than `r` when `1 ≤ r`. -/
theorem mem_snd_decodeAuxDigits_lt {Q r idx a : ℕ} (hr : 1 ≤ r)
    (ha : a ∈ (decodeAuxDigits Q r idx).2) : a < r := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rw [Cslib.Radix.digit_eq_div_pow_mod]
  exact Nat.mod_lt _ hr

/-- A pair of length-`Q` digit lists `< r` encodes below `r ^ (2 * Q)` when `Q = 0 ∨ 1 ≤ r`. -/
theorem encodeAuxDigits_lt {Q r : ℕ} {u : List ℕ × List ℕ} (hu₁ : u.1.length = Q)
    (hu₂ : u.2.length = Q) (hb₁ : ∀ a ∈ u.1, a < r) (hb₂ : ∀ a ∈ u.2, a < r)
    (hQr : Q = 0 ∨ 1 ≤ r) : encodeAuxDigits r u < r ^ (2 * Q) := by
  rcases hQr with rfl | hr
  · simp only [encodeAuxDigits, List.eq_nil_of_length_eq_zero hu₁, Nat.mul_zero, pow_zero,
      List.eq_nil_of_length_eq_zero hu₂, List.append_nil, Nat.ofDigits_nil, Nat.zero_lt_one]
  · have hlt := Nat.ofDigits_lt_base_pow_length_of_pos hr (u.1 ++ u.2) fun a ha =>
      (List.mem_append.1 ha).elim (hb₁ a) (hb₂ a)
    rwa [List.length_append, hu₁, hu₂, ← two_mul] at hlt

/-- Decoding `encodeAuxDigits r u` recovers `u` for every pair of length-`Q` digit lists `< r`. -/
theorem decodeAuxDigits_encodeAuxDigits {Q r : ℕ} {u : List ℕ × List ℕ} (hu₁ : u.1.length = Q)
    (hu₂ : u.2.length = Q) (hb₁ : ∀ a ∈ u.1, a < r) (hb₂ : ∀ a ∈ u.2, a < r) :
    decodeAuxDigits Q r (encodeAuxDigits r u) = u := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · rcases u with ⟨u₁, u₂⟩; obtain rfl := List.eq_nil_of_length_eq_zero hu₁
    obtain rfl := List.eq_nil_of_length_eq_zero hu₂
    simp only [decodeAuxDigits, List.range_zero, List.map_nil]
  · have hr : 0 < r := Nat.zero_lt_of_lt (hb₁ u.1[0] (List.getElem_mem (by omega)))
    have hall : ∀ a ∈ u.1 ++ u.2, a < r := fun a ha => (List.mem_append.1 ha).elim (hb₁ a) (hb₂ a)
    ext : 1
    · apply List.ext_getElem (by simp only [length_fst_decodeAuxDigits, hu₁]); intro s _ hs₂
      simp only [decodeAuxDigits, List.getElem_map, List.getElem_range, encodeAuxDigits]
      rw [Cslib.Radix.digit_ofDigits hr _ hall s (by rw [List.length_append, hu₁]; omega),
        List.getElem_append_left hs₂]
    · apply List.ext_getElem (by simp only [length_snd_decodeAuxDigits, hu₂]); intro s _ _
      simp only [decodeAuxDigits, List.getElem_map, List.getElem_range, encodeAuxDigits]
      rw [Cslib.Radix.digit_ofDigits hr _ hall (Q + s)
        (by rw [List.length_append, hu₁, hu₂]; omega), List.getElem_append_right (by omega)]
      congr 1; omega

/-- Encoding `decodeAuxDigits Q r idx` recovers `idx` for every `idx < r ^ (2 * Q)`. -/
theorem encodeAuxDigits_decodeAuxDigits {Q r idx : ℕ} (hidx : idx < r ^ (2 * Q)) :
    encodeAuxDigits r (decodeAuxDigits Q r idx) = idx := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp only [Nat.mul_zero, pow_zero] at hidx; obtain rfl : idx = 0 := by omega
    simp only [decodeAuxDigits, List.range_zero, List.map_nil, encodeAuxDigits, List.append_nil,
      Nat.ofDigits_nil]
  · obtain ⟨x, hx, hof⟩ := Nat.exists_ofDigits_ofFn hidx
    have hr : 0 < r := Nat.zero_lt_of_lt (hx ⟨0, by omega⟩)
    have hall : ∀ a ∈ List.ofFn x, a < r := fun a ha => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact hx i
    have happ : (decodeAuxDigits Q r idx).1 ++ (decodeAuxDigits Q r idx).2 = List.ofFn x := by
      apply List.ext_getElem (by simp only [List.length_append, length_fst_decodeAuxDigits,
        length_snd_decodeAuxDigits, List.length_ofFn]; omega)
      intro i _ hi₂; rw [List.length_ofFn] at hi₂
      have hdig : Cslib.Radix.digit r idx i = (List.ofFn x)[i] :=
        hof ▸ Cslib.Radix.digit_ofDigits hr _ hall i (by rw [List.length_ofFn]; exact hi₂)
      by_cases hlt : i < Q
      · rw [List.getElem_append_left (by simp only [length_fst_decodeAuxDigits]; exact hlt)]
        simp only [decodeAuxDigits, List.getElem_map, List.getElem_range]; exact hdig
      · rw [List.getElem_append_right (by simp only [length_fst_decodeAuxDigits]; omega)]
        simp only [decodeAuxDigits, List.length_map, List.length_range, List.getElem_map,
          List.getElem_range]
        rwa [show Q + (i - Q) = i by omega]
    rw [encodeAuxDigits, happ, hof]

/-- Converting `decodeAuxLabel hD idx` back to digits yields `decodeAuxDigits Q r idx`. -/
@[simp] theorem auxLabelToDigits_decodeAuxLabel {Q r : ℕ} (hD : 0 < r ^ (2 * Q)) (idx : ℕ) :
    auxLabelToDigits (decodeAuxLabel hD idx) = decodeAuxDigits Q r idx := by
  ext : 1 <;>
  · apply List.ext_getElem (by simp only [auxLabelToDigits, decodeAuxDigits, List.length_ofFn,
      List.length_map, List.length_range])
    intro _ _ _; simp only [auxLabelToDigits, decodeAuxLabel, decodeAuxDigits, List.getElem_ofFn,
      List.getElem_map, List.getElem_range]

/-- Every `u : AuxLabel Q r` encodes to an index strictly less than `r ^ (2 * Q)`. -/
theorem encodeAuxLabel_lt {Q r : ℕ} (u : AuxLabel Q r) : encodeAuxLabel u < r ^ (2 * Q) :=
  encodeAuxDigits_lt (by simp only [auxLabelToDigits, List.length_ofFn])
    (by simp only [auxLabelToDigits, List.length_ofFn])
    (fun _ ha => by obtain ⟨s, rfl⟩ := List.mem_ofFn.1 ha; exact (u.1 s).2)
    (fun _ ha => by obtain ⟨s, rfl⟩ := List.mem_ofFn.1 ha; exact (u.2 s).2)
    (Nat.eq_zero_or_pos Q |>.imp id fun hpos => Nat.zero_lt_of_lt (u.1 ⟨0, hpos⟩).2)

/-- Decoding `encodeAuxLabel u` yields `auxLabelToDigits u`. -/
@[simp] theorem decodeAuxDigits_encodeAuxLabel {Q r : ℕ} (u : AuxLabel Q r) :
    decodeAuxDigits Q r (encodeAuxLabel u) = auxLabelToDigits u :=
  decodeAuxDigits_encodeAuxDigits (by simp only [auxLabelToDigits, List.length_ofFn])
    (by simp only [auxLabelToDigits, List.length_ofFn])
    (fun _ ha => by obtain ⟨s, rfl⟩ := List.mem_ofFn.1 ha; exact (u.1 s).2)
    (fun _ ha => by obtain ⟨s, rfl⟩ := List.mem_ofFn.1 ha; exact (u.2 s).2)

/-- Left-inverse identity for `decodeAuxLabel` and `encodeAuxLabel`. -/
@[simp] theorem decodeAuxLabel_encodeAuxLabel {Q r : ℕ} (hD : 0 < r ^ (2 * Q)) (u : AuxLabel Q r) :
    decodeAuxLabel hD (encodeAuxLabel u) = u := by
  have hdig :=
    auxLabelToDigits_decodeAuxLabel hD (encodeAuxLabel u) ▸ decodeAuxDigits_encodeAuxLabel u
  refine Prod.ext (funext fun s => Fin.ext ?_) (funext fun s => Fin.ext ?_)
  · simpa only [auxLabelToDigits, List.getD_ofFn] using congrArg (fun p => p.1.getD s 0) hdig
  · simpa only [auxLabelToDigits, List.getD_ofFn] using congrArg (fun p => p.2.getD s 0) hdig

/-- Right-inverse identity for `encodeAuxLabel` and `decodeAuxLabel` on `idx < r ^ (2 * Q)`. -/
@[simp] theorem encodeAuxLabel_decodeAuxLabel {Q r idx : ℕ} (hD : 0 < r ^ (2 * Q))
    (hidx : idx < r ^ (2 * Q)) : encodeAuxLabel (decodeAuxLabel hD idx) = idx := by
  rw [encodeAuxLabel, auxLabelToDigits_decodeAuxLabel, encodeAuxDigits_decodeAuxDigits hidx]

/-- Computable mixed-radix equivalence between `AuxLabel Q r` and `Fin (r ^ (2 * Q))`. -/
def auxLabelEquivFin (Q r : ℕ) : AuxLabel Q r ≃ Fin (r ^ (2 * Q)) where
  toFun u := ⟨encodeAuxLabel u, encodeAuxLabel_lt u⟩
  invFun i := decodeAuxLabel (Nat.zero_lt_of_lt i.2) i.1
  left_inv u := decodeAuxLabel_encodeAuxLabel (Nat.zero_lt_of_lt (encodeAuxLabel_lt u)) u
  right_inv i := Fin.ext (encodeAuxLabel_decodeAuxLabel (Nat.zero_lt_of_lt i.2) i.2)

/-! ### 2. Common denominator bit-length bounds (`commonDenom`) -/

/-- Binary bit-length bound for `commonDenom Q R = (R - 1)! * Q!` (Lemma 4.6, p. 33). -/
theorem size_commonDenom_le (Q R : ℕ) :
    (commonDenom Q R).size ≤ (R - 1) * (R - 1).size + Q * Q.size + 2 := by
  unfold commonDenom; have := Nat.size_factorial_le (R - 1); have := Nat.size_factorial_le Q
  have := Nat.size_mul_le (R - 1).factorial Q.factorial; omega

/-- Encoded `encIntBin` bit-length bound for `(commonDenom Q R : ℤ)`. -/
theorem length_encIntBin_commonDenom_le (Q R : ℕ) :
    (encIntBin (commonDenom Q R : ℤ)).length ≤ (R - 1) * (R - 1).size + Q * Q.size + 3 := by
  rw [length_encIntBin, Int.natAbs_natCast]; have := size_commonDenom_le Q R; omega

/-! ### 3. Executable `{0, 1, -1}` measurement matrix `C^B` -/

/-- Executable 1-slot `{0, 1, -1}` basis value on natural-number digits `α δ x y : ℕ`. -/
def pairBasisNat (α δ x y : ℕ) : ℤ :=
  if α = δ then (if x = α ∧ y = α then 1 else 0)
  else if α < δ then (if x = α ∧ y = δ then 1 else 0) + (if x = δ ∧ y = α then 1 else 0)
  else (if x = δ ∧ y = α then 1 else 0) - (if x = α ∧ y = δ then 1 else 0)

/-- Executable `{0, 1, -1}` entry `ψ_β(u)` on digit lists `β, u` (missing digits read as `0`). -/
def eigenvecDigits (Q : ℕ) (β u : List ℕ × List ℕ) : ℤ :=
  ((List.range Q).map fun s =>
    pairBasisNat (β.1.getD s 0) (β.2.getD s 0) (u.1.getD s 0) (u.2.getD s 0)).prod

/-- Antisymmetric slot count `#{s < Q | β.2[s] < β.1[s]}` on digits `β` (missing digits `0`). -/
def antisymCountDigits (Q : ℕ) (β : List ℕ × List ℕ) : ℕ :=
  (List.range Q).countP fun s => decide (β.2.getD s 0 < β.1.getD s 0)

/-- Measurement row indices outside `Ico A₀ (A₀ + R)`, truncated to `< min D_cap (r ^ (2 * Q))`. -/
def auxMeasurementIndicesBounded (D_cap Q r A₀ R : ℕ) : List ℕ :=
  (List.range (min D_cap (r ^ (2 * Q)))).filter fun b_idx =>
    let j := antisymCountDigits Q (decodeAuxDigits Q r b_idx)
    !(decide (A₀ ≤ j) && decide (j < A₀ + R))

/-- Full list of measurement row indices `< r ^ (2 * Q)` outside `Finset.Ico A₀ (A₀ + R)`. -/
def auxMeasurementIndices (Q r A₀ R : ℕ) : List ℕ :=
  auxMeasurementIndicesBounded (r ^ (2 * Q)) Q r A₀ R

/-- Executable `{0, 1, -1}` measurement matrix `C^B` truncated below `min D_cap (r ^ (2 * Q))`. -/
def auxMeasurementRowsBounded (D_cap Q r A₀ R : ℕ) : List (List ℤ) :=
  let D_len := min D_cap (r ^ (2 * Q))
  (auxMeasurementIndicesBounded D_cap Q r A₀ R).map fun b_idx =>
    (List.range D_len).map fun u_idx =>
      eigenvecDigits Q (decodeAuxDigits Q r b_idx) (decodeAuxDigits Q r u_idx)

/-- Executable `{0, 1, -1}` measurement matrix `C^B` of Lemma 4.1 (p. 28). -/
def auxMeasurementRows (Q r A₀ R : ℕ) : List (List ℤ) :=
  auxMeasurementRowsBounded (r ^ (2 * Q)) Q r A₀ R

private theorem pairBasisNat_fin {r : ℕ} (α δ x y : Fin r) :
    pairBasisNat α.1 δ.1 x.1 y.1 = pairBasis α δ x y := by
  unfold pairBasisNat pairBasis pairInd; simp only [Fin.ext_iff, Fin.val_fin_lt]

/-- Every value of `pairBasisNat` lies in `{0, 1, -1}`. -/
theorem pairBasisNat_mem (α δ x y : ℕ) :
    pairBasisNat α δ x y = 0 ∨ pairBasisNat α δ x y = 1 ∨ pairBasisNat α δ x y = -1 := by
  unfold pairBasisNat; split_ifs <;> omega

/-- Every entry of `eigenvecDigits` lies in `{0, 1, -1}`. -/
theorem eigenvecDigits_mem (Q : ℕ) (β u : List ℕ × List ℕ) :
    eigenvecDigits Q β u = 0 ∨ eigenvecDigits Q β u = 1 ∨ eigenvecDigits Q β u = -1 := by
  unfold eigenvecDigits; generalize List.range Q = l; induction l with
  | nil => simp only [List.map_nil, List.prod_nil, true_or, or_true]
  | cons s l ih =>
    rw [List.map_cons, List.prod_cons]
    rcases pairBasisNat_mem (β.1.getD s 0) (β.2.getD s 0) (u.1.getD s 0) (u.2.getD s 0) with
      h1 | h1 | h1 <;> rcases ih with h2 | h2 | h2 <;> (rw [h1, h2]; decide)

/-- `eigenvecDigits` on `auxLabelToDigits` agrees identically with `eigenvecInt`. -/
@[simp] theorem eigenvecDigits_auxLabelToDigits {Q r : ℕ} (β u : AuxLabel Q r) :
    eigenvecDigits Q (auxLabelToDigits β) (auxLabelToDigits u) = eigenvecInt β u := by
  unfold eigenvecDigits eigenvecInt; rw [List.map_range_eq_ofFn, List.prod_ofFn]
  exact Finset.prod_congr rfl fun _ _ => by simp only [auxLabelToDigits, List.getD_ofFn,
    pairBasisNat_fin]

/-- `antisymCountDigits` on `auxLabelToDigits` agrees identically with `antisymCount`. -/
@[simp] theorem antisymCountDigits_auxLabelToDigits {Q r : ℕ} (β : AuxLabel Q r) :
    antisymCountDigits Q (auxLabelToDigits β) = antisymCount β := by
  unfold antisymCountDigits antisymCount; rw [List.countP_range_eq_card_filter]; congr 1; ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, auxLabelToDigits, List.getD_ofFn,
    decide_eq_true_eq, Fin.val_fin_lt]

/-- When `r ^ (2 * Q) ≤ D_cap`, `auxMeasurementRowsBounded` equals `auxMeasurementRows`. -/
theorem auxMeasurementRowsBounded_eq_auxMeasurementRows {D_cap Q r A₀ R : ℕ}
    (h : r ^ (2 * Q) ≤ D_cap) :
    auxMeasurementRowsBounded D_cap Q r A₀ R = auxMeasurementRows Q r A₀ R := by
  simp only [auxMeasurementRows, auxMeasurementRowsBounded, auxMeasurementIndicesBounded,
    Nat.min_eq_right h, Nat.min_self]

private theorem mem_auxMeasurementIndices_lt {Q r A₀ R b_idx : ℕ}
    (hb : b_idx ∈ auxMeasurementIndices Q r A₀ R) : b_idx < r ^ (2 * Q) := by
  unfold auxMeasurementIndices auxMeasurementIndicesBounded at hb
  rw [Nat.min_self] at hb; exact List.mem_range.1 (List.mem_of_mem_filter hb)

/-- Characterization of membership in `auxMeasurementIndices Q r A₀ R` via `measurementIndices`. -/
theorem decodeAuxLabel_mem_measurementIndices_iff {Q r A₀ R b_idx : ℕ} (hb : b_idx < r ^ (2 * Q)) :
    decodeAuxLabel (Nat.zero_lt_of_lt hb) b_idx ∈ measurementIndices Q r A₀ R ↔
      b_idx ∈ auxMeasurementIndices Q r A₀ R := by
  have hD : 0 < r ^ (2 * Q) := Nat.zero_lt_of_lt hb
  simp only [measurementIndices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico,
    auxMeasurementIndices, auxMeasurementIndicesBounded, Nat.min_self, List.mem_filter,
    List.mem_range, hb, ← antisymCountDigits_auxLabelToDigits (decodeAuxLabel hD b_idx),
    auxLabelToDigits_decodeAuxLabel, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not]; tauto

/-- `auxMeasurementRows Q r A₀ R` is a `#(measurementIndices Q r A₀ R) × r ^ (2 * Q)` table. -/
theorem isTableShape_auxMeasurementRows (Q r A₀ R : ℕ) :
    Cslib.IsTableShape #(measurementIndices Q r A₀ R) (r ^ (2 * Q))
      (auxMeasurementRows Q r A₀ R) := by
  refine ⟨?_, fun row hrow => ?_⟩
  · simp only [auxMeasurementRows, auxMeasurementRowsBounded, List.length_map]
    rcases Nat.eq_zero_or_pos (r ^ (2 * Q)) with h0 | hD
    · have hempty : IsEmpty (AuxLabel Q r) := Fintype.card_eq_zero_iff.1 (card_auxLabel Q r ▸ h0)
      simp only [auxMeasurementIndicesBounded, h0, Nat.min_self, List.range_zero, List.filter_nil,
        List.length_nil, Finset.eq_empty_of_isEmpty (measurementIndices Q r A₀ R),
        Finset.card_empty]
    · have hnodup : (auxMeasurementIndices Q r A₀ R).Nodup := by
        unfold auxMeasurementIndices auxMeasurementIndicesBounded
        exact List.Nodup.filter _ List.nodup_range
      rw [← auxMeasurementIndices, ← List.toFinset_card_of_nodup hnodup]
      refine Finset.card_bij (fun b_idx _ => decodeAuxLabel hD b_idx)
        (fun _ hb => (decodeAuxLabel_mem_measurementIndices_iff
          (mem_auxMeasurementIndices_lt (List.mem_toFinset.1 hb))).2 (List.mem_toFinset.1 hb))
        (fun _ hb₁ _ hb₂ heq => ?_) fun β hβ => ⟨encodeAuxLabel β, List.mem_toFinset.2 ?_,
          decodeAuxLabel_encodeAuxLabel hD β⟩
      · have henc := congrArg encodeAuxLabel heq
        have h1 := mem_auxMeasurementIndices_lt (List.mem_toFinset.1 hb₁)
        have h2 := mem_auxMeasurementIndices_lt (List.mem_toFinset.1 hb₂)
        rwa [encodeAuxLabel_decodeAuxLabel hD h1, encodeAuxLabel_decodeAuxLabel hD h2] at henc
      · rwa [← decodeAuxLabel_mem_measurementIndices_iff (encodeAuxLabel_lt β),
          decodeAuxLabel_encodeAuxLabel]
  · simp only [auxMeasurementRows, auxMeasurementRowsBounded, Nat.min_self, List.mem_map] at hrow
    rcases hrow with ⟨_, _, rfl⟩; simp only [List.length_map, List.length_range]

/-- Every entry of `auxMeasurementRowsBounded D_cap Q r A₀ R` belongs to `{0, 1, -1}`. -/
theorem mem_auxMeasurementRowsBounded_mem {D_cap Q r A₀ R : ℕ} {row : List ℤ} {c : ℤ}
    (hrow : row ∈ auxMeasurementRowsBounded D_cap Q r A₀ R) (hc : c ∈ row) :
    c = 0 ∨ c = 1 ∨ c = -1 := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 hrow; obtain ⟨_, _, rfl⟩ := List.mem_map.1 hc
  exact eigenvecDigits_mem Q _ _

/-- Every entry of `auxMeasurementRowsBounded D_cap Q r A₀ R` has absolute value at most `1`. -/
theorem abs_mem_auxMeasurementRowsBounded_le_one {D_cap Q r A₀ R : ℕ} {row : List ℤ} {c : ℤ}
    (hrow : row ∈ auxMeasurementRowsBounded D_cap Q r A₀ R) (hc : c ∈ row) : |c| ≤ 1 := by
  rcases mem_auxMeasurementRowsBounded_mem hrow hc with h | h | h <;>
    simp only [h, abs_zero, abs_one, abs_neg, zero_le_one, le_refl]

/-- In-bounds entry correspondence (`i < length`, `u_idx < r ^ (2 * Q)`) between
`auxMeasurementRows` and `eigenvecInt` via `Cslib.rowEntry` (`0` out of bounds). -/
theorem rowEntry_auxMeasurementRows {Q r A₀ R i u_idx : ℕ}
    (hi : i < (auxMeasurementIndices Q r A₀ R).length) (hu : u_idx < r ^ (2 * Q)) :
    Cslib.rowEntry (auxMeasurementRows Q r A₀ R) i u_idx =
      eigenvecInt (decodeAuxLabel (Nat.zero_lt_of_lt hu) ((auxMeasurementIndices Q r A₀ R)[i]'hi))
        (decodeAuxLabel (Nat.zero_lt_of_lt hu) u_idx) := by
  have hD : 0 < r ^ (2 * Q) := Nat.zero_lt_of_lt hu
  have hi' : i < (auxMeasurementRows Q r A₀ R).length := by
    simpa only [auxMeasurementRows, auxMeasurementRowsBounded, auxMeasurementIndices,
      List.length_map] using hi
  rw [Cslib.rowEntry, List.getD_eq_getElem _ _ hi']
  simp only [auxMeasurementRows, auxMeasurementRowsBounded, auxMeasurementIndices, Nat.min_self,
    List.getElem_map]
  rw [List.getD_map_range _ 0 hu, ← auxLabelToDigits_decodeAuxLabel hD,
    ← auxLabelToDigits_decodeAuxLabel hD, eigenvecDigits_auxLabelToDigits]

private theorem sum_row_eigenvecDigits_eq_dotProduct {Q r : ℕ} (K : Type*) [CommRing K]
    (β : AuxLabel Q r) (ξ : AuxLabel Q r → K) :
    (∑ u : AuxLabel Q r, (((List.range (r ^ (2 * Q))).map fun u_idx =>
        eigenvecDigits Q (auxLabelToDigits β) (decodeAuxDigits Q r u_idx)).getD
          (encodeAuxLabel u) 0 : K) * ξ u) = dotProduct (eigenvec K β) ξ :=
  Finset.sum_congr rfl fun u _ => by
    rw [List.getD_map_range _ 0 (encodeAuxLabel_lt u), decodeAuxDigits_encodeAuxLabel,
      eigenvecDigits_auxLabelToDigits]; rfl

/-- **Kernel correspondence**: `ξ` lies in `ker (measurementMatrix Q r A₀ R K)` iff its inner
product with every row in `auxMeasurementRows Q r A₀ R` vanishes. -/
theorem measurementMatrix_mulVec_eq_zero_iff_auxMeasurementRows (Q r A₀ R : ℕ) (K : Type*)
    [CommRing K] (ξ : AuxLabel Q r → K) :
    (measurementMatrix Q r A₀ R K).mulVec ξ = 0 ↔
      ∀ row ∈ auxMeasurementRows Q r A₀ R,
        (∑ u : AuxLabel Q r, (row.getD (encodeAuxLabel u) 0 : K) * ξ u) = 0 := by
  rw [measurementMatrix_mulVec_eq_zero_iff]; constructor
  · intro hker row hrow
    simp only [auxMeasurementRows, auxMeasurementRowsBounded, Nat.min_self, List.mem_map] at hrow
    rcases hrow with ⟨b_idx, hb, rfl⟩; have hlt := mem_auxMeasurementIndices_lt hb
    rw [← auxLabelToDigits_decodeAuxLabel (Nat.zero_lt_of_lt hlt) b_idx,
      sum_row_eigenvecDigits_eq_dotProduct]
    exact hker _ (Finset.mem_filter.1 ((decodeAuxLabel_mem_measurementIndices_iff hlt).2 hb)).2
  · intro hrows β hβ
    have hb : encodeAuxLabel β ∈ auxMeasurementIndices Q r A₀ R := by
      rw [← decodeAuxLabel_mem_measurementIndices_iff (encodeAuxLabel_lt β),
        decodeAuxLabel_encodeAuxLabel]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ β, hβ⟩
    rw [← sum_row_eigenvecDigits_eq_dotProduct K β ξ, ← decodeAuxDigits_encodeAuxLabel β]
    exact hrows _ <| by
      simp only [auxMeasurementRows, auxMeasurementRowsBounded, Nat.min_self, List.mem_map]
      exact ⟨encodeAuxLabel β, hb, rfl⟩

/-! ### 4. Executable cleared integer replacement rows (`auxReplacementRowCoeffs`) -/

/-- Whether `y` lies in the swap orbit of `(u.2, u.1)` across slots `< Q` (missing digits `0`). -/
def isSwapOrbitDigits (Q : ℕ) (u y : List ℕ × List ℕ) : Bool :=
  (List.range Q).all fun s =>
    decide ((y.1.getD s 0 = u.2.getD s 0 ∧ y.2.getD s 0 = u.1.getD s 0) ∨
      (y.1.getD s 0 = u.1.getD s 0 ∧ y.2.getD s 0 = u.2.getD s 0))

/-- Number of off-diagonal slots `s < Q` where `u.2[s] ≠ u.1[s]` (missing digits read as `0`). -/
def offDiagCountDigits (Q : ℕ) (u : List ℕ × List ℕ) : ℕ :=
  (List.range Q).countP fun s => decide (u.2.getD s 0 ≠ u.1.getD s 0)

/-- Number of mismatch slots `s < Q` where `y.1[s] ≠ u.2[s]` (missing digits read as `0`). -/
def mismatchCountDigits (Q : ℕ) (u y : List ℕ × List ℕ) : ℕ :=
  (List.range Q).countP fun s => decide (y.1.getD s 0 ≠ u.2.getD s 0)

/-- One factor `(2 W_0 - c I)` on the `(m + 1)`-state Hamming-weight vector `f` of a swap orbit. -/
def orbitWeightStep (m : ℕ) (c : ℤ) (f : List ℤ) : List ℤ :=
  (List.range (m + 1)).map fun d =>
    ((m : ℤ) - c) * f.getD d 0 - (if 0 < d then (d : ℤ) * f.getD (d - 1) 0 else 0) -
      (if d < m then ((m - d : ℕ) : ℤ) * f.getD (d + 1) 0 else 0)

/-- Weight profile after multiplying `∏_{a < j} (2 W_0 - 2 (A₀ + a) I)` on a swap orbit. -/
def fallingOrbitWeights (m A₀ j : ℕ) : List ℤ :=
  (List.range j).foldl (fun f (a : ℕ) => orbitWeightStep m (2 * ((A₀ : ℤ) + (a : ℤ))) f)
    (1 :: List.replicate m 0)

/-- Executable `(R - 1)! M_0[u, y]` entry summing `j < R` runs of the `(m + 1)`-state 1D
swap-orbit DP `fallingOrbitWeights` (`0` at `R = 0`; missing digits read as `0`). -/
def m0ScaledIntDigits (Q A₀ R : ℕ) (u y : List ℕ × List ℕ) : ℤ :=
  if isSwapOrbitDigits Q u y then
    let m := offDiagCountDigits Q u; let d := mismatchCountDigits Q u y
    ((List.range R).map fun j =>
      ((((R - 1).factorial / j.factorial : ℕ) : ℤ) * (-1 : ℤ) ^ (A₀ + j)) *
        (fallingOrbitWeights m A₀ j).getD d 0).sum
  else 0

/-- Multiply a polynomial coefficient list `p` (constant term first) by `(t - X)`. -/
def mulLinearSub (p : List ℤ) (t : ℤ) : List ℤ :=
  (List.range (p.length + 1)).map fun k =>
    t * p.getD k 0 - (if 0 < k then p.getD (k - 1) 0 else 0)

/-- Executable integer coefficient list of `Q! φ_{u,y}(T) = mismatchAnnihilatorScaledInt u y`
(missing digits at slots `s ≥ length` read as `0`). -/
def mismatchAnnihilatorCoeffsDigits (Q : ℕ) (u y : List ℕ × List ℕ) : List ℤ :=
  (List.range Q).foldl (fun p s =>
    if y.1.getD s 0 = u.2.getD s 0 then p.map (((s : ℤ) + 1) * ·)
    else mulLinearSub p ((s : ℤ) + 1)) [1]

/-- Whether two digit-list pairs agree on their first `Q` slots (missing digits read as `0`). -/
def eqAuxDigits (Q : ℕ) (u y : List ℕ × List ℕ) : Bool :=
  (List.range Q).all fun s => decide (u.1.getD s 0 = y.1.getD s 0 ∧ u.2.getD s 0 = y.2.getD s 0)

/-- Executable dense coefficient list (length `max R 1`) of `d_den · P⃗_u(T)_y` on digit lists,
cleared by `commonDenom Q R = (R - 1)! * Q! > 0` (at `R = 0`, `(R - 1)! = 1` and length is `1`;
missing digits read as `0`). -/
def auxReplacementRowCoeffsDigits (Q A₀ R : ℕ) (u y : List ℕ × List ℕ) : List ℤ :=
  let m0 := m0ScaledIntDigits Q A₀ R u y; let phi := mismatchAnnihilatorCoeffsDigits Q u y
  let c0 := (Q.factorial : ℤ) * ((if eqAuxDigits Q u y then ((R - 1).factorial : ℤ) else 0) - m0)
  (List.range (max R 1)).map fun k => (if k = 0 then c0 else 0) + m0 * phi.getD k 0

/-- Executable cleared integer replacement polynomial coefficients from mixed-radix indices. -/
def auxReplacementRowCoeffsIdx (Q r A₀ R u_idx y_idx : ℕ) : List ℤ :=
  auxReplacementRowCoeffsDigits Q A₀ R (decodeAuxDigits Q r u_idx) (decodeAuxDigits Q r y_idx)

/-- Executable dense coefficient list (length `max R 1`) of `auxReplacementRowScaledInt`, cleared
by `commonDenom Q R = (R - 1)! * Q! > 0` (at `R = 0`, `(R - 1)! = 1` and output length is `1`). -/
def auxReplacementRowCoeffs (Q r A₀ R : ℕ) (u y : AuxLabel Q r) : List ℤ :=
  auxReplacementRowCoeffsDigits Q A₀ R (auxLabelToDigits u) (auxLabelToDigits y)

/-- Executable `D_len × D_len × max R 1` table of cleared replacement polynomials guarded by unary
cap `D_cap` (truncating row and column indices to `< D_len = min D_cap (r ^ (2 * Q))`). -/
def auxReplacementTableBounded (D_cap Q r A₀ R : ℕ) : List (List (List ℤ)) :=
  let D_len := min D_cap (r ^ (2 * Q))
  (List.range D_len).map fun u_idx =>
    (List.range D_len).map fun y_idx => auxReplacementRowCoeffsIdx Q r A₀ R u_idx y_idx

/-- Full `D × D × max R 1` table of cleared integer replacement polynomials. -/
def auxReplacementTable (Q r A₀ R : ℕ) : List (List (List ℤ)) :=
  auxReplacementTableBounded (r ^ (2 * Q)) Q r A₀ R

/-! #### 4.1 Correctness of the 1D swap-orbit DP for `M0ScaledInt` -/

private def IsSwapOrbit {Q r : ℕ} (z y : AuxLabel Q r) : Prop :=
  ∀ s : Fin Q, (y.1 s = z.1 s ∧ y.2 s = z.2 s) ∨ (y.1 s = z.2 s ∧ y.2 s = z.1 s)
private instance {Q r : ℕ} (z y : AuxLabel Q r) : Decidable (IsSwapOrbit z y) :=
  inferInstanceAs (Decidable (∀ _ : Fin Q, _))
private def offDiagSet {Q r : ℕ} (z : AuxLabel Q r) : Finset (Fin Q) :=
  univ.filter fun s => z.1 s ≠ z.2 s
private def diffSet {Q r : ℕ} (z y : AuxLabel Q r) : Finset (Fin Q) :=
  univ.filter fun s => y.1 s ≠ z.1 s

private theorem isSwapOrbit_slotSwap {Q r : ℕ} (z y : AuxLabel Q r) (s : Fin Q) :
    IsSwapOrbit z (slotSwap s y) ↔ IsSwapOrbit z y := by
  have himp : ∀ {w : AuxLabel Q r}, IsSwapOrbit z w → IsSwapOrbit z (slotSwap s w) := by
    intro w h t; specialize h t; by_cases hts : t = s
    · subst hts; simp only [slotSwap, subsetSwap, Finset.mem_singleton, ↓reduceIte]; tauto
    · simp only [slotSwap, subsetSwap, Finset.mem_singleton, hts, ↓reduceIte]; exact h
  exact ⟨fun h => slotSwap_self s y ▸ himp h, himp⟩
private theorem diffSet_subset_offDiagSet {Q r : ℕ} {z y : AuxLabel Q r} (h : IsSwapOrbit z y) :
    diffSet z y ⊆ offDiagSet z := by
  intro s hs; simp only [diffSet, offDiagSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact (h s).elim (fun ⟨h1, _⟩ => absurd h1 hs) fun ⟨h1, _⟩ heq => hs (h1.trans heq.symm)
private theorem card_diffSet_slotSwap_of_notMem_offDiag {Q r : ℕ} {z y : AuxLabel Q r}
    (h : IsSwapOrbit z y) {s : Fin Q} (hs : s ∉ offDiagSet z) :
    #(diffSet z (slotSwap s y)) = #(diffSet z y) := by
  simp only [offDiagSet, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hs
  have hys : y.1 s = y.2 s := (h s).elim (fun ⟨h1, h2⟩ => (h1.trans hs).trans h2.symm)
    fun ⟨h1, h2⟩ => (h1.trans hs.symm).trans h2.symm
  suffices slotSwap s y = y by rw [this]
  ext t : 2 <;> (simp only [slotSwap, subsetSwap, Finset.mem_singleton]; split_ifs with hts) <;>
    [exact hts ▸ hys.symm; rfl; exact hts ▸ hys; rfl]
private theorem card_diffSet_slotSwap_of_mem_diffSet {Q r : ℕ} {z y : AuxLabel Q r}
    (h : IsSwapOrbit z y) {s : Fin Q} (hs : s ∈ diffSet z y) :
    #(diffSet z (slotSwap s y)) = #(diffSet z y) - 1 := by
  have hy2 : y.2 s = z.1 s :=
    (h s).elim (fun ⟨h1, _⟩ => absurd h1 (Finset.mem_filter.1 hs).2) And.right
  suffices diffSet z (slotSwap s y) = (diffSet z y).erase s by
    rw [this, Finset.card_erase_of_mem hs]
  ext t; simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
    slotSwap, subsetSwap, Finset.mem_singleton]
  by_cases hts : t = s
  · subst hts; simp only [↓reduceIte, hy2]; tauto
  · simp only [hts, ↓reduceIte]; tauto
private theorem card_diffSet_slotSwap_of_mem_offDiag_sdiff {Q r : ℕ} {z y : AuxLabel Q r}
    (h : IsSwapOrbit z y) {s : Fin Q} (hs : s ∈ offDiagSet z \ diffSet z y) :
    #(diffSet z (slotSwap s y)) = #(diffSet z y) + 1 := by
  obtain ⟨hoff, hnot⟩ := Finset.mem_sdiff.1 hs
  simp only [offDiagSet, Finset.mem_filter, Finset.mem_univ, true_and] at hoff
  have hy1 : y.1 s = z.1 s := by
    by_contra hne; exact hnot (Finset.mem_filter.2 ⟨Finset.mem_univ s, hne⟩)
  have hy2 : y.2 s ≠ z.1 s := (h s).elim (fun ⟨_, h2⟩ => h2 ▸ hoff.symm)
    fun ⟨h1, _⟩ => absurd (hy1.symm.trans h1) hoff
  suffices diffSet z (slotSwap s y) = insert s (diffSet z y) by
    rw [this, Finset.card_insert_of_notMem hnot]
  ext t; simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    slotSwap, subsetSwap, Finset.mem_singleton]
  by_cases hts : t = s
  · subst hts; simp only [↓reduceIte]; tauto
  · simp only [hts, ↓reduceIte]; tauto
private theorem mul_twoW0_sub_apply {Q r : ℕ} (P : Matrix (AuxLabel Q r) (AuxLabel Q r) ℤ)
    (c : ℤ) (z y : AuxLabel Q r) :
    (P * (twoW0 Q r ℤ - c • 1)) z y = ((Q : ℤ) - c) * P z y - ∑ s : Fin Q, P z (slotSwap s y) := by
  rw [Matrix.mul_sub, Matrix.sub_apply, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply,
    smul_eq_mul, twoW0, Matrix.mul_sum, Matrix.sum_apply]
  have hterm : ∀ s : Fin Q,
      (P * (1 - slotSwapMatrix Q r ℤ s)) z y = P z y - P z (slotSwap s y) := fun s => by
    let row : AuxLabel Q r → ℤ := P z
    have hinv : ∀ w : AuxLabel Q r, (y = slotSwap s w) ↔ (w = slotSwap s y) := fun w =>
      ⟨fun h => h ▸ (slotSwap_self s w).symm, fun h => h ▸ (slotSwap_self s y).symm⟩
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, Matrix.mul_apply]
    change row y - ∑ w, row w * (if y = slotSwap s w then 1 else 0) = row y - row (slotSwap s y)
    simp only [mul_ite, mul_one, mul_zero, hinv, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring
private theorem fallingProdMatrixInt_eq_fallingOrbitWeights (Q r A₀ j : ℕ) (z y : AuxLabel Q r) :
    fallingProdMatrixInt Q r A₀ j z y =
      if IsSwapOrbit z y then
        (fallingOrbitWeights #(offDiagSet z) A₀ j).getD #(diffSet z y) 0 else 0 := by
  induction j generalizing y with
  | zero =>
    simp only [fallingProdMatrixInt, List.range_zero, List.map_nil, List.prod_nil,
      fallingOrbitWeights, List.foldl_nil, Matrix.one_apply]
    by_cases hzy : z = y
    · subst hzy; have horb : IsSwapOrbit z z := fun _ => Or.inl ⟨rfl, rfl⟩
      have hd : #(diffSet z z) = 0 :=
        Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun _ _ h => h rfl)
      simp only [horb, hd, ↓reduceIte, List.getD_cons_zero]
    · simp only [hzy, ↓reduceIte]; by_cases horb : IsSwapOrbit z y
      · simp only [horb, ↓reduceIte]
        have hd_ne : #(diffSet z y) ≠ 0 := fun h0 => hzy (by
          have hemp := Finset.card_eq_zero.1 h0
          have hy1 : ∀ s : Fin Q, y.1 s = z.1 s := fun s => by
            by_contra hne; exact Finset.notMem_empty s
              (hemp ▸ Finset.mem_filter.2 ⟨Finset.mem_univ s, hne⟩)
          ext s : 2; · exact (hy1 s).symm
          exact (horb s).elim (fun ⟨_, h2⟩ => h2.symm)
            fun ⟨ha, hb⟩ => (ha.symm.trans (hy1 s)).trans hb.symm)
        have hd_le := Finset.card_le_card (diffSet_subset_offDiagSet horb)
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hd_ne
        rw [hk, List.getD_cons_succ, List.getD_eq_getElem (List.replicate #(offDiagSet z) 0) 0
          (by simp only [List.length_replicate]; omega), List.getElem_replicate]
      · simp only [horb, ↓reduceIte]
  | succ j ih =>
    have hstep_mat : fallingProdMatrixInt Q r A₀ (j + 1) =
        fallingProdMatrixInt Q r A₀ j * (twoW0 Q r ℤ - (2 * ((A₀ : ℤ) + (j : ℤ))) • 1) := by
      simp only [fallingProdMatrixInt, List.range_succ, List.map_append, List.map_singleton,
        List.prod_append, List.prod_singleton]
    have hstep_wt : fallingOrbitWeights #(offDiagSet z) A₀ (j + 1) =
        orbitWeightStep #(offDiagSet z) (2 * ((A₀ : ℤ) + (j : ℤ)))
          (fallingOrbitWeights #(offDiagSet z) A₀ j) := by
      simp only [fallingOrbitWeights, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    rw [hstep_mat, mul_twoW0_sub_apply, hstep_wt]
    set f : List ℤ := fallingOrbitWeights #(offDiagSet z) A₀ j
    by_cases horb : IsSwapOrbit z y
    · simp only [horb, ↓reduceIte]; rw [ih y]; simp only [horb, ↓reduceIte]
      have hsum : (∑ s : Fin Q, fallingProdMatrixInt Q r A₀ j z (slotSwap s y)) =
          ∑ s : Fin Q, f.getD #(diffSet z (slotSwap s y)) 0 :=
        Finset.sum_congr rfl fun s _ => by
          rw [ih (slotSwap s y)]; simp only [(isSwapOrbit_slotSwap z y s).2 horb, ↓reduceIte]
      rw [hsum]; set m := #(offDiagSet z); set d := #(diffSet z y)
      have hsub : diffSet z y ⊆ offDiagSet z := diffSet_subset_offDiagSet horb
      have hd_le : d ≤ m := Finset.card_le_card hsub
      have hm_le : m ≤ Q := (Finset.card_le_univ _).trans (by rw [Fintype.card_fin])
      have hsum_eval : (∑ s : Fin Q, f.getD #(diffSet z (slotSwap s y)) 0) =
          ((Q - m : ℕ) : ℤ) * f.getD d 0 + ((if 0 < d then (d : ℤ) * f.getD (d - 1) 0 else 0) +
            if d < m then ((m - d : ℕ) : ℤ) * f.getD (d + 1) 0 else 0) := by
        rw [← Finset.sum_add_sum_compl (offDiagSet z)]
        nth_rw 1 [← Finset.union_sdiff_of_subset hsub]
        rw [add_comm, Finset.sum_union Finset.disjoint_sdiff]
        refine congrArg₂ _ ?_ (congrArg₂ _ ?_ ?_)
        · rw [Finset.sum_congr rfl fun _ hs => congrArg (f.getD · 0)
              (card_diffSet_slotSwap_of_notMem_offDiag horb (Finset.mem_compl.1 hs)),
            Finset.sum_const, Finset.card_compl, Fintype.card_fin, nsmul_eq_mul]
        · rw [Finset.sum_congr rfl fun _ hs =>
              congrArg (f.getD · 0) (card_diffSet_slotSwap_of_mem_diffSet horb hs),
            Finset.sum_const, nsmul_eq_mul]
          change (d : ℤ) * f.getD (d - 1) 0 = _
          split_ifs <;> [rfl; simp only [show d = 0 by omega, Nat.cast_zero, zero_mul]]
        · rw [Finset.sum_congr rfl fun _ hs =>
              congrArg (f.getD · 0) (card_diffSet_slotSwap_of_mem_offDiag_sdiff horb hs),
            Finset.sum_const, Finset.card_sdiff, Finset.inter_eq_left.2 hsub, nsmul_eq_mul]
          change ((m - d : ℕ) : ℤ) * f.getD (d + 1) 0 = _
          split_ifs <;> [rfl; simp only [show m - d = 0 by omega, Nat.cast_zero, zero_mul]]
      rw [hsum_eval]; unfold orbitWeightStep
      rw [List.getD_map_range _ 0 (Nat.lt_succ_of_le hd_le), Nat.cast_sub hm_le]; ring
    · simp only [horb, ↓reduceIte]; rw [ih y]; simp only [horb, ↓reduceIte, mul_zero]
      rw [Finset.sum_eq_zero fun s _ => by
        rw [ih (slotSwap s y)]; simp only [show ¬ IsSwapOrbit z (slotSwap s y) from
          fun hs => horb ((isSwapOrbit_slotSwap z y s).1 hs), ↓reduceIte], sub_zero]

/-- `m0ScaledIntDigits` on `auxLabelToDigits` equals `M0ScaledInt Q r A₀ R u y`. -/
@[simp] theorem m0ScaledIntDigits_auxLabelToDigits (Q r A₀ R : ℕ) (u y : AuxLabel Q r) :
    m0ScaledIntDigits Q A₀ R (auxLabelToDigits u) (auxLabelToDigits y) =
      M0ScaledInt Q r A₀ R u y := by
  have horb_iff : isSwapOrbitDigits Q (auxLabelToDigits u) (auxLabelToDigits y) = true ↔
      IsSwapOrbit (fullSwap u) y := by
    unfold isSwapOrbitDigits IsSwapOrbit; rw [List.all_eq_true]; constructor
    · intro h s; simpa only [auxLabelToDigits, List.getD_ofFn, decide_eq_true_eq, fullSwap_fst,
        fullSwap_snd, Fin.ext_iff] using h s.1 (List.mem_range.2 s.2)
    · intro h s hs; let s' : Fin Q := ⟨s, List.mem_range.1 hs⟩; rw [show s = s'.1 from rfl]
      simpa only [auxLabelToDigits, List.getD_ofFn, decide_eq_true_eq, fullSwap_fst, fullSwap_snd,
        Fin.ext_iff] using h s'
  have hoff_eq : offDiagCountDigits Q (auxLabelToDigits u) = #(offDiagSet (fullSwap u)) := by
    unfold offDiagCountDigits offDiagSet; rw [List.countP_range_eq_card_filter]; congr 1; ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, auxLabelToDigits, List.getD_ofFn,
      decide_eq_true_eq, fullSwap_fst, fullSwap_snd, ne_eq, Fin.ext_iff]
  have hmis_eq : mismatchCountDigits Q (auxLabelToDigits u) (auxLabelToDigits y) =
      #(diffSet (fullSwap u) y) := by
    unfold mismatchCountDigits diffSet; rw [List.countP_range_eq_card_filter]; congr 1; ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, auxLabelToDigits, List.getD_ofFn,
      decide_eq_true_eq, fullSwap_fst, ne_eq, Fin.ext_iff]
  unfold m0ScaledIntDigits; by_cases horb : IsSwapOrbit (fullSwap u) y
  · simp only [horb_iff.2 horb, ↓reduceIte, hoff_eq, hmis_eq]
    rw [List.sum_map_range, Fin.sum_univ_eq_sum_range (fun j =>
      (((R - 1).factorial / j.factorial : ℕ) : ℤ) * (-1 : ℤ) ^ (A₀ + j) *
        (fallingOrbitWeights (#(offDiagSet (fullSwap u))) A₀ j).getD
          (#(diffSet (fullSwap u) y)) 0), M0ScaledInt, fullSwapMatrix_mul_apply]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => by simp only [fallingTermMatrixInt, Matrix.smul_apply,
      smul_eq_mul, fallingProdMatrixInt_eq_fallingOrbitWeights, horb, ↓reduceIte, mul_assoc]
  · have hfalse : isSwapOrbitDigits Q (auxLabelToDigits u) (auxLabelToDigits y) = false :=
      Bool.eq_false_iff.2 fun hb => horb (horb_iff.1 hb)
    simp only [hfalse, Bool.false_eq_true, ↓reduceIte, M0ScaledInt, fullSwapMatrix_mul_apply,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact (Finset.sum_eq_zero fun _ _ => by simp only [fallingTermMatrixInt, Matrix.smul_apply,
      smul_eq_mul, fallingProdMatrixInt_eq_fallingOrbitWeights, horb, ↓reduceIte, mul_zero]).symm

/-! #### 4.2 Correctness of `mismatchAnnihilatorCoeffsDigits` and `auxReplacementRowCoeffs` -/

private theorem ofCoeffList_mulLinearSub (p : List ℤ) (t : ℤ) :
    Polynomial.ofCoeffList (mulLinearSub p t) = (C t - X) * Polynomial.ofCoeffList p := by
  ext k; rw [coeff_ofCoeffList, sub_mul, coeff_sub, coeff_C_mul]
  have hX : (X * Polynomial.ofCoeffList p).coeff k =
      if 0 < k then (Polynomial.ofCoeffList p).coeff (k - 1) else 0 := by
    cases k <;> simp only [lt_self_iff_false, Nat.zero_lt_succ, ↓reduceIte, Nat.add_sub_cancel,
      mul_comm X, coeff_mul_X_zero, coeff_mul_X]
  rw [hX]; simp only [coeff_ofCoeffList]; by_cases hk : k < p.length + 1
  · unfold mulLinearSub; rw [List.getD_map_range _ 0 hk]
  · have hge : (mulLinearSub p t).length ≤ k := by
      simp only [mulLinearSub, List.length_map, List.length_range]; omega
    rw [List.getD_eq_default (mulLinearSub p t) 0 hge,
      List.getD_eq_default p 0 (by omega), mul_zero,
      ite_eq_left (by omega : 0 < k), List.getD_eq_default p 0 (by omega), sub_zero]
private theorem mismatchAnnihilatorCoeffsDigits_succ (k : ℕ) (u y : List ℕ × List ℕ) :
    mismatchAnnihilatorCoeffsDigits (k + 1) u y =
      if y.1.getD k 0 = u.2.getD k 0 then
        (mismatchAnnihilatorCoeffsDigits k u y).map (((k : ℤ) + 1) * ·)
      else mulLinearSub (mismatchAnnihilatorCoeffsDigits k u y) ((k : ℤ) + 1) := by
  simp only [mismatchAnnihilatorCoeffsDigits, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
private theorem ofCoeffList_mismatchAnnihilatorCoeffsDigits_eq_prod (Q : ℕ)
    (u y : List ℕ × List ℕ) :
    Polynomial.ofCoeffList (mismatchAnnihilatorCoeffsDigits Q u y) =
      ∏ s ∈ Finset.range Q,
        (if y.1.getD s 0 = u.2.getD s 0 then C ((s : ℤ) + 1) else C ((s : ℤ) + 1) - X) := by
  induction Q with
  | zero => simp only [mismatchAnnihilatorCoeffsDigits, List.range_zero, List.foldl_nil,
      Finset.range_zero, Finset.prod_empty, ofCoeffList_cons, ofCoeffList_nil, mul_zero, add_zero,
      C_1]
  | succ k ih =>
    rw [mismatchAnnihilatorCoeffsDigits_succ, Finset.prod_range_succ,
      mul_comm (∏ s ∈ Finset.range k, _)]
    split_ifs <;> [rw [ofCoeffList_map_mul, ih]; rw [ofCoeffList_mulLinearSub, ih]]

/-- Reconstructing a polynomial from `mismatchAnnihilatorCoeffsDigits` yields
`mismatchAnnihilatorScaledInt u y`. -/
@[simp] theorem ofCoeffList_mismatchAnnihilatorCoeffsDigits (Q r : ℕ) (u y : AuxLabel Q r) :
    Polynomial.ofCoeffList
        (mismatchAnnihilatorCoeffsDigits Q (auxLabelToDigits u) (auxLabelToDigits y)) =
      mismatchAnnihilatorScaledInt u y := by
  rw [ofCoeffList_mismatchAnnihilatorCoeffsDigits_eq_prod, ← Fin.prod_univ_eq_prod_range]
  have hcongr : (∏ s : Fin Q,
      if (auxLabelToDigits y).1.getD s 0 = (auxLabelToDigits u).2.getD s 0 then
        C ((s.1 : ℤ) + 1) else C ((s.1 : ℤ) + 1) - X) =
      ∏ s : Fin Q, if s ∈ mismatchSet u y then C ((s.1 : ℤ) + 1) - X else C ((s.1 : ℤ) + 1) :=
    Finset.prod_congr rfl fun s _ => by
      simp only [auxLabelToDigits, List.getD_ofFn, mismatchSet, Finset.mem_filter, Finset.mem_univ,
        true_and, ne_eq, Fin.ext_iff]
      by_cases h : (y.1 s).1 = (u.2 s).1 <;>
        simp only [h, not_true_eq_false, not_false_eq_true, ↓reduceIte]
  have huniv : (univ : Finset (Fin Q)) = (mismatchSet u y)ᶜ ∪ mismatchSet u y := by
    ext s; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_compl]; tauto
  rw [hcongr, huniv, Finset.prod_union disjoint_compl_left, mismatchAnnihilatorScaledInt,
    map_prod C]
  exact congrArg₂ _
    (Finset.prod_congr rfl fun _ hs => by simp only [Finset.mem_compl.1 hs, ↓reduceIte])
    (Finset.prod_congr rfl fun _ hs => by simp only [hs, ↓reduceIte])

private theorem eqAuxDigits_auxLabelToDigits {Q r : ℕ} (u y : AuxLabel Q r) :
    eqAuxDigits Q (auxLabelToDigits u) (auxLabelToDigits y) = decide (u = y) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]; unfold eqAuxDigits; rw [List.all_eq_true]; constructor
  · intro h; have hs : ∀ s : Fin Q, (u.1 s).1 = (y.1 s).1 ∧ (u.2 s).1 = (y.2 s).1 := fun s => by
      have hmem := h s.1 (List.mem_range.2 s.2)
      simpa only [auxLabelToDigits, List.getD_ofFn, decide_eq_true_eq] using hmem
    exact Prod.ext (funext fun s => Fin.ext (hs s).1) (funext fun s => Fin.ext (hs s).2)
  · rintro rfl _ _; simp only [decide_eq_true_eq, and_self]

/-- Length of `auxReplacementRowCoeffsDigits` is `max R 1`. -/
@[simp] theorem length_auxReplacementRowCoeffsDigits (Q A₀ R : ℕ) (u y : List ℕ × List ℕ) :
    (auxReplacementRowCoeffsDigits Q A₀ R u y).length = max R 1 := by
  simp only [auxReplacementRowCoeffsDigits, List.length_map, List.length_range]

/-- Length of `auxReplacementRowCoeffs` is `max R 1` (equal to `R` whenever `1 ≤ R`). -/
@[simp] theorem length_auxReplacementRowCoeffs (Q r A₀ R : ℕ) (u y : AuxLabel Q r) :
    (auxReplacementRowCoeffs Q r A₀ R u y).length = max R 1 :=
  length_auxReplacementRowCoeffsDigits Q A₀ R _ _

/-- Degree of `mismatchAnnihilatorScaledInt u y` is at most `#(mismatchSet u y)`. -/
theorem natDegree_mismatchAnnihilatorScaledInt_le {Q r : ℕ} (u y : AuxLabel Q r) :
    (mismatchAnnihilatorScaledInt u y).natDegree ≤ #(mismatchSet u y) := by
  unfold mismatchAnnihilatorScaledInt; refine Polynomial.natDegree_mul_le.trans ?_
  rw [natDegree_C, zero_add]; refine (Polynomial.natDegree_prod_le _ _).trans ?_
  exact (Finset.sum_le_card_nsmul _ _ 1 fun _ _ => (Polynomial.natDegree_sub_le _ _).trans
    (max_le (by simp only [natDegree_C, zero_le]) (by simp only [natDegree_X, le_refl]))).trans
    (by simp only [smul_eq_mul, mul_one, le_refl])

/-- **Exact coefficient equality** between `auxReplacementRowCoeffs` and
`auxReplacementRowScaledInt`. -/
theorem getD_auxReplacementRowCoeffs (Q r A₀ R : ℕ) (u y : AuxLabel Q r) (k : ℕ) :
    (auxReplacementRowCoeffs Q r A₀ R u y).getD k 0 =
      (auxReplacementRowScaledInt Q r A₀ R u y).coeff k := by
  have hphi : ∀ i : ℕ,
      (mismatchAnnihilatorCoeffsDigits Q (auxLabelToDigits u) (auxLabelToDigits y)).getD i 0 =
        (mismatchAnnihilatorScaledInt u y).coeff i := fun i => by
    rw [← ofCoeffList_mismatchAnnihilatorCoeffsDigits Q r u y, coeff_ofCoeffList]
  have hite : (if decide (u = y) = true then ((R - 1).factorial : ℤ) else 0) =
      if u = y then ((R - 1).factorial : ℤ) else 0 := by
    by_cases h : u = y <;> simp only [h, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
  by_cases hk : k < max R 1
  · unfold auxReplacementRowCoeffs auxReplacementRowCoeffsDigits auxReplacementRowScaledInt
    dsimp only; rw [List.getD_map_range _ 0 hk, m0ScaledIntDigits_auxLabelToDigits,
      eqAuxDigits_auxLabelToDigits, hite, coeff_add, coeff_C, coeff_C_mul, hphi k]
  · rw [List.getD_eq_default _ 0 (by rw [length_auxReplacementRowCoeffs]; omega)]
    unfold auxReplacementRowScaledInt; rw [coeff_add, coeff_C, coeff_C_mul]
    simp only [show k ≠ 0 by omega, ↓reduceIte, zero_add]
    by_cases hm0 : M0ScaledInt Q r A₀ R u y = 0
    · simp only [hm0, zero_mul]
    · have hdeg := (natDegree_mismatchAnnihilatorScaledInt_le u y).trans
        (card_mismatchSet_le_of_M0ScaledInt_ne_zero hm0)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]

/-- Reconstructing a polynomial from `auxReplacementRowCoeffs Q r A₀ R u y` gives
`auxReplacementRowScaledInt Q r A₀ R u y` unconditionally. -/
@[simp] theorem ofCoeffList_auxReplacementRowCoeffs (Q r A₀ R : ℕ) (u y : AuxLabel Q r) :
    Polynomial.ofCoeffList (auxReplacementRowCoeffs Q r A₀ R u y) =
      auxReplacementRowScaledInt Q r A₀ R u y := by
  ext k; rw [coeff_ofCoeffList, getD_auxReplacementRowCoeffs]

/-- When `r ^ (2 * Q) ≤ D_cap`, `auxReplacementTableBounded` equals `auxReplacementTable`. -/
theorem auxReplacementTableBounded_eq_auxReplacementTable {D_cap Q r A₀ R : ℕ}
    (h : r ^ (2 * Q) ≤ D_cap) :
    auxReplacementTableBounded D_cap Q r A₀ R = auxReplacementTable Q r A₀ R := by
  simp only [auxReplacementTable, auxReplacementTableBounded, Nat.min_eq_right h, Nat.min_self]

/-- Exact entry lookup in `auxReplacementTable Q r A₀ R` for `u_idx, y_idx < r ^ (2 * Q)`. -/
theorem getD_auxReplacementTable {Q r A₀ R u_idx y_idx : ℕ}
    (hu : u_idx < r ^ (2 * Q)) (hy : y_idx < r ^ (2 * Q)) :
    ((auxReplacementTable Q r A₀ R).getD u_idx []).getD y_idx [] =
      auxReplacementRowCoeffs Q r A₀ R (decodeAuxLabel (Nat.zero_lt_of_lt hu) u_idx)
        (decodeAuxLabel (Nat.zero_lt_of_lt hy) y_idx) := by
  simp only [auxReplacementTable, auxReplacementTableBounded, Nat.min_self]
  rw [List.getD_map_range _ [] hu, List.getD_map_range _ [] hy]
  simp only [auxReplacementRowCoeffsIdx, auxReplacementRowCoeffs, auxLabelToDigits_decodeAuxLabel]

/-! #### 4.3 Coefficient magnitude, `coeffNorm1` bridge, and bit-length bounds (Lemma 4.6) -/

private theorem length_fallingOrbitWeights (m A₀ j : ℕ) :
    (fallingOrbitWeights m A₀ j).length = m + 1 := by
  unfold fallingOrbitWeights; induction j with
  | zero => simp only [List.range_zero, List.foldl_nil, List.length_cons, List.length_replicate]
  | succ j _ =>
    rw [List.range_succ]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, orbitWeightStep,
      List.length_map, List.length_range]
private theorem natAbs_mem_fallingOrbitWeights_le (m A₀ j : ℕ) :
    ∀ x ∈ fallingOrbitWeights m A₀ j, x.natAbs ≤ (2 * (m + A₀ + j)) ^ j := by
  induction j with
  | zero =>
    intro x hx; simp only [fallingOrbitWeights, List.range_zero, List.foldl_nil, List.mem_cons,
      List.mem_replicate] at hx
    rcases hx with rfl | ⟨_, rfl⟩ <;>
      simp only [Int.natAbs_one, Int.natAbs_zero, pow_zero, Nat.zero_le, le_refl]
  | succ j ih =>
    intro x hx
    have hstep : fallingOrbitWeights m A₀ (j + 1) =
        orbitWeightStep m (2 * ((A₀ : ℤ) + (j : ℤ))) (fallingOrbitWeights m A₀ j) := by
      simp only [fallingOrbitWeights, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    rw [hstep] at hx; unfold orbitWeightStep at hx; obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
    have hdm : d ≤ m := Nat.lt_succ_iff.1 (List.mem_range.1 hd)
    set f := fallingOrbitWeights m A₀ j; set B := (2 * (m + A₀ + (j + 1))) ^ j
    have hfB : ∀ z ∈ f, z.natAbs ≤ B := fun z hz =>
      (ih z hz).trans (Nat.pow_le_pow_left (by omega) j)
    have hmain : (((m : ℤ) - 2 * ((A₀ : ℤ) + (j : ℤ))) * f.getD d 0).natAbs ≤
        (m + 2 * (A₀ + j)) * B := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega) (List.natAbs_getD_le_of_forall hfB d)
    have h1 : (if 0 < d then (d : ℤ) * f.getD (d - 1) 0 else 0).natAbs ≤ d * B := by
      split_ifs <;> simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_zero, Nat.zero_le]
      exact Nat.mul_le_mul_left d (List.natAbs_getD_le_of_forall hfB (d - 1))
    have h2 : (if d < m then ((m - d : ℕ) : ℤ) * f.getD (d + 1) 0 else 0).natAbs ≤ (m - d) * B := by
      split_ifs <;> simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_zero, Nat.zero_le]
      exact Nat.mul_le_mul_left (m - d) (List.natAbs_getD_le_of_forall hfB (d + 1))
    refine ((Int.natAbs_sub_le _ _).trans
      (Nat.add_le_add ((Int.natAbs_sub_le _ _).trans (Nat.add_le_add hmain h1)) h2)).trans ?_
    calc (m + 2 * (A₀ + j)) * B + d * B + (m - d) * B
        = (m + 2 * (A₀ + j) + (d + (m - d))) * B := by ring
      _ ≤ 2 * (m + A₀ + (j + 1)) * B := Nat.mul_le_mul_right B (by omega)
      _ = (2 * (m + A₀ + (j + 1))) ^ (j + 1) := by rw [pow_succ']

/-- Unconditional magnitude bound on `m0ScaledIntDigits Q A₀ R u y`. -/
theorem natAbs_m0ScaledIntDigits_le (Q A₀ R : ℕ) (u y : List ℕ × List ℕ) :
    (m0ScaledIntDigits Q A₀ R u y).natAbs ≤
      (R - 1).factorial * R * (2 * (Q + A₀ + R)) ^ (R - 1) := by
  unfold m0ScaledIntDigits; split_ifs with horb
  · have hm : offDiagCountDigits Q u ≤ Q :=
      List.countP_le_length.trans (by simp only [List.length_range, le_refl])
    let bound := (R - 1).factorial * (2 * (Q + A₀ + R)) ^ (R - 1)
    refine (List.natAbs_sum_le_length_mul (C := bound) ?_).trans ?_
    · intro x hx; obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx; have hj' := List.mem_range.1 hj
      rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow,
        mul_one, Int.natAbs_natCast]
      refine Nat.mul_le_mul (Nat.div_le_self _ _)
        ((List.natAbs_getD_le_of_forall (natAbs_mem_fallingOrbitWeights_le _ A₀ j) _).trans ?_)
      rcases Nat.eq_zero_or_pos (2 * (Q + A₀ + R)) with h0 | hpos <;> [omega;
        exact (Nat.pow_le_pow_left (by omega) j).trans (Nat.pow_le_pow_right hpos (by omega))]
    · simp only [List.length_map, List.length_range, bound]; ring_nf; exact le_refl _
  · simp only [Int.natAbs_zero, Nat.zero_le]
private theorem length_mismatchAnnihilatorCoeffsDigits_le (Q : ℕ) (u y : List ℕ × List ℕ) :
    (mismatchAnnihilatorCoeffsDigits Q u y).length ≤ Q + 1 := by
  induction Q with
  | zero => simp only [mismatchAnnihilatorCoeffsDigits, List.range_zero, List.foldl_nil,
      List.length_singleton, zero_add, le_refl]
  | succ k ih =>
    rw [mismatchAnnihilatorCoeffsDigits_succ]; split_ifs <;>
      simp only [mulLinearSub, List.length_map, List.length_range] <;> omega

/-- Polynomial `ℓ₁` bound `‖Q! φ_{u,y}‖₁ ≤ 2 ^ Q * Q!` on `mismatchAnnihilatorCoeffsDigits`
(Lemma 4.6, p. 33). -/
theorem sum_natAbs_mismatchAnnihilatorCoeffsDigits_le (Q : ℕ) (u y : List ℕ × List ℕ) :
    ((mismatchAnnihilatorCoeffsDigits Q u y).map Int.natAbs).sum ≤ 2 ^ Q * Q.factorial := by
  rw [← Polynomial.coeffNorm1_ofCoeffList]; induction Q with
  | zero => simp only [mismatchAnnihilatorCoeffsDigits, List.range_zero, List.foldl_nil,
      ofCoeffList_cons, ofCoeffList_nil, mul_zero, add_zero, C_1, coeffNorm1_one, pow_zero,
      Nat.factorial_zero, mul_one, le_refl]
  | succ k ih =>
    rw [mismatchAnnihilatorCoeffsDigits_succ]; set p := mismatchAnnihilatorCoeffsDigits k u y
    have hstep : (Polynomial.ofCoeffList
        (if y.1.getD k 0 = u.2.getD k 0 then p.map (((k : ℤ) + 1) * ·)
        else mulLinearSub p ((k : ℤ) + 1))).coeffNorm1 ≤
        (2 * (k + 1)) * (Polynomial.ofCoeffList p).coeffNorm1 := by
      split_ifs
      · rw [ofCoeffList_map_mul]
        exact (Polynomial.coeffNorm1_C_mul_le _ _).trans (Nat.mul_le_mul_right _ (by omega))
      · rw [ofCoeffList_mulLinearSub]
        exact (Polynomial.coeffNorm1_C_sub_X_mul_le _ _).trans (Nat.mul_le_mul_right _ (by omega))
    exact hstep.trans (calc (2 * (k + 1)) * (Polynomial.ofCoeffList p).coeffNorm1
        ≤ (2 * (k + 1)) * (2 ^ k * k.factorial) := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (k + 1) * (k + 1).factorial := by rw [pow_succ, Nat.factorial_succ]; ring)

/-- Exact equality between the list `ℓ₁` sum of `auxReplacementRowCoeffs` and
`Polynomial.coeffNorm1` of `auxReplacementRowScaledInt`. -/
@[simp] theorem sum_natAbs_auxReplacementRowCoeffs_eq_coeffNorm1 (Q r A₀ R : ℕ)
    (u y : AuxLabel Q r) :
    ((auxReplacementRowCoeffs Q r A₀ R u y).map Int.natAbs).sum =
      (auxReplacementRowScaledInt Q r A₀ R u y).coeffNorm1 := by
  rw [← Polynomial.coeffNorm1_ofCoeffList, ofCoeffList_auxReplacementRowCoeffs]

/-- Unconditional magnitude bound on every coefficient of `auxReplacementRowCoeffsDigits`. -/
theorem natAbs_mem_auxReplacementRowCoeffsDigits_le {Q A₀ R : ℕ} {u y : List ℕ × List ℕ} {c : ℤ}
    (hc : c ∈ auxReplacementRowCoeffsDigits Q A₀ R u y) :
    c.natAbs ≤ commonDenom Q R * (1 + (1 + 2 ^ Q) * R * (2 * (Q + A₀ + R)) ^ (R - 1)) := by
  unfold auxReplacementRowCoeffsDigits at hc; obtain ⟨k, _, rfl⟩ := List.mem_map.1 hc
  set m0 := m0ScaledIntDigits Q A₀ R u y; set phi := mismatchAnnihilatorCoeffsDigits Q u y
  have hphi : (phi.getD k 0).natAbs ≤ 2 ^ Q * Q.factorial := by
    rw [← coeff_ofCoeffList]; exact (Polynomial.natAbs_coeff_le_coeffNorm1 _ k).trans
      ((Polynomial.coeffNorm1_ofCoeffList phi).le.trans
        (sum_natAbs_mismatchAnnihilatorCoeffsDigits_le Q u y))
  have hc0 : (if k = 0 then (Q.factorial : ℤ) *
      ((if eqAuxDigits Q u y then ((R - 1).factorial : ℤ) else 0) - m0) else 0).natAbs ≤
      commonDenom Q R + Q.factorial * m0.natAbs := by
    split_ifs
    · rw [Int.natAbs_mul, Int.natAbs_natCast, commonDenom, mul_comm (R - 1).factorial, ← mul_add]
      exact Nat.mul_le_mul_left _ ((Int.natAbs_sub_le _ _).trans (by rw [Int.natAbs_natCast]))
    · rw [zero_sub, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_neg]; exact Nat.le_add_left _ _
    · simp only [Int.natAbs_zero, zero_le]
  refine (Int.natAbs_add_le _ _).trans ?_; rw [Int.natAbs_mul]
  calc _ ≤ (commonDenom Q R + Q.factorial * m0.natAbs) + m0.natAbs * (2 ^ Q * Q.factorial) :=
      Nat.add_le_add hc0 (Nat.mul_le_mul_left _ hphi)
    _ = commonDenom Q R + Q.factorial * (1 + 2 ^ Q) * m0.natAbs := by ring
    _ ≤ commonDenom Q R +
          Q.factorial * (1 + 2 ^ Q) * ((R - 1).factorial * R * (2 * (Q + A₀ + R)) ^ (R - 1)) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (natAbs_m0ScaledIntDigits_le Q A₀ R u y)) _
    _ = commonDenom Q R * (1 + (1 + 2 ^ Q) * R * (2 * (Q + A₀ + R)) ^ (R - 1)) := by
      unfold commonDenom; ring

/-- Explicit `encIntBin` bit-length bound for every coefficient of `auxReplacementRowCoeffs`
(Lemma 4.6, p. 33). -/
theorem length_encIntBin_mem_auxReplacementRowCoeffs_le {Q r A₀ R : ℕ} {u y : AuxLabel Q r}
    {c : ℤ} (hc : c ∈ auxReplacementRowCoeffs Q r A₀ R u y) :
    (encIntBin c).length ≤
      (commonDenom Q R).size + Q + R.size + (R - 1) * (2 * (Q + A₀ + R)).size + 5 := by
  rw [length_encIntBin]
  have h2Q : (1 + 2 ^ Q).size ≤ Q + 2 := Nat.size_le.2 (by
    have hlt : 2 ^ Q < 2 ^ (Q + 1) := Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self Q)
    rw [pow_succ _ (Q + 1)]; omega)
  have hX : ((1 + 2 ^ Q) * R * (2 * (Q + A₀ + R)) ^ (R - 1)).size ≤
      Q + R.size + (R - 1) * (2 * (Q + A₀ + R)).size + 3 := by
    have := Nat.size_mul_le ((1 + 2 ^ Q) * R) ((2 * (Q + A₀ + R)) ^ (R - 1))
    have := Nat.size_mul_le (1 + 2 ^ Q) R
    have := Nat.size_pow_le (2 * (Q + A₀ + R)) (R - 1); omega
  set X := (1 + 2 ^ Q) * R * (2 * (Q + A₀ + R)) ^ (R - 1)
  have hle : c.natAbs.size ≤ (commonDenom Q R).size + (1 + X).size :=
    (Nat.size_le_size (natAbs_mem_auxReplacementRowCoeffsDigits_le hc)).trans
      (Nat.size_mul_le (commonDenom Q R) (1 + X))
  have := Nat.size_add_le_max 1 X; have : (1 : ℕ).size = 1 := Nat.size_one; omega

/-- **Row-`ℓ₁` coefficient bound (Lemma 4.6, p. 33)**: when `0 < Q` and `∀ a < R - 1, A₀ + a ≤ Q`,
the sum of absolute values across row `u` of `auxReplacementRowCoeffs` is at most
`commonDenom Q R * (1 + (1 + 2 ^ Q) * R * (4 * Q) ^ (R - 1))`. -/
theorem sum_row_natAbs_auxReplacementRowCoeffs_le {Q r A₀ R : ℕ} (hQ : 0 < Q)
    (hI : ∀ a < R - 1, A₀ + a ≤ Q) (u : AuxLabel Q r) :
    (∑ y : AuxLabel Q r, ((auxReplacementRowCoeffs Q r A₀ R u y).map Int.natAbs).sum) ≤
      commonDenom Q R * (1 + (1 + 2 ^ Q) * R * (4 * Q) ^ (R - 1)) := by
  simp_rw [sum_natAbs_auxReplacementRowCoeffs_eq_coeffNorm1]
  exact Int.ofNat_le.1 (by push_cast; exact sum_coeffNorm1_auxReplacementRowScaledInt_le hQ hI u)

/-! ### 5. Plain polynomial-time certificates (Lemma 4.7, p. 34) -/

section PolyTime
open ComputableInPolyTime

local notation "CPT" => ComputableInPolyTime
local notation "encDigits" => encPair (encList encNat) (encList encNat)

variable {α : Type} {input : α ↪ List Bool}

@[local fun_prop] private theorem er_cond {β : Type} {encB : β ↪ List Bool}
    {c : α → Bool} {yes no : α → β} (hc : CPT c input encBool)
    (hyes : CPT yes input encB) (hno : CPT no input encB) :
    CPT (fun a => if c a then yes a else no a) input encB := hc.ite' hyes hno
@[local fun_prop] private theorem er_ite_decide {β : Type} {encB : β ↪ List Bool}
    {cond : α → Prop} [∀ a, Decidable (cond a)] {yes no : α → β}
    (hc : CPT (fun a => decide (cond a)) input encBool)
    (hyes : CPT yes input encB) (hno : CPT no input encB) :
    CPT (fun a => if cond a then yes a else no a) input encB := by
  simpa only [decide_eq_true_eq] using er_cond hc hyes hno
@[local fun_prop] private theorem er_bool_not {x : α → Bool} (hx : CPT x input encBool) :
    CPT (fun a => !(x a)) input encBool := bool_not.comp hx
@[local fun_prop] private theorem er_bool_and {l r : α → Bool}
    (hl : CPT l input encBool) (hr : CPT r input encBool) :
    CPT (fun a => l a && r a) input encBool := bool_and.comp (hl.prod hr)
@[local fun_prop] private theorem er_decide_and {l r : α → Prop}
    [∀ a, Decidable (l a)] [∀ a, Decidable (r a)]
    (hl : CPT (fun a => decide (l a)) input encBool)
    (hr : CPT (fun a => decide (r a)) input encBool) :
    CPT (fun a => decide (l a ∧ r a)) input encBool := by
  simpa only [Bool.decide_and, Function.comp_def] using er_bool_and hl hr
@[local fun_prop] private theorem er_decide_ne {β : Type} {encB : β ↪ List Bool}
    [DecidableEq β] {l r : α → β} (hl : CPT l input encB) (hr : CPT r input encB) :
    CPT (fun a => decide (l a ≠ r a)) input encBool := by
  simpa only [Function.comp_def, _root_.decide_not] using bool_not.comp (hl.decide_eq' hr)
@[local fun_prop] private theorem er_allWithInput {β : Type} {encB : β ↪ List Bool}
    {test : α → β → Bool} {list : α → List β} (hl : CPT list input (encList encB))
    (ht : CPT (fun p : α × β => test p.1 p.2) (encPair input encB) encBool) :
    CPT (fun a => (list a).all (test a)) input encBool := allWithEncoding ht id' hl
@[local fun_prop] private theorem er_listReverse {β : Type} {encB : β ↪ List Bool}
    {l : α → List β} (hl : CPT l input (encList encB)) :
    CPT (fun a => (l a).reverse) input (encList encB) :=
  (show CPT List.reverse (encList encB) (encList encB) by fun_prop).comp hl
@[local fun_prop] private theorem er_listAppend {β : Type} {encB : β ↪ List Bool}
    {l r : α → List β} (hl : CPT l input (encList encB)) (hr : CPT r input (encList encB)) :
    CPT (fun a => l a ++ r a) input (encList encB) :=
  (show CPT (fun p : List β × List β => p.1 ++ p.2)
    (encPair (encList encB) (encList encB)) (encList encB) by fun_prop).comp (hl.prod hr)
@[local fun_prop] private theorem er_cons {β : Type} {encB : β ↪ List Bool}
    {h : α → β} {t : α → List β} (hh : CPT h input encB) (ht : CPT t input (encList encB)) :
    CPT (fun a => h a :: t a) input (encList encB) :=
  (show CPT (fun p : β × List β => p.1 :: p.2)
    (encPair encB (encList encB)) (encList encB) by fun_prop).comp (hh.prod ht)
@[local fun_prop] private theorem er_replicate {β : Type} {encB : β ↪ List Bool}
    {count : α → ℕ} {val : α → β} (hc : CPT count input encUnary) (hv : CPT val input encB) :
    CPT (fun a => List.replicate (count a) (val a)) input (encList encB) := by
  simpa only [Function.comp_def, List.map_const', List.length_range] using
    mapWithInput (f := fun a _ => val a) (range.comp hc) (hv.comp (fst input encUnary))
@[local fun_prop] private theorem er_range {n : α → ℕ} (hn : CPT n input encUnary) :
    CPT (fun a => List.range (n a)) input (encList encUnary) := range.comp hn
@[local fun_prop] private theorem er_unary_add {l r : α → ℕ} (hl : CPT l input encUnary)
    (hr : CPT r input encUnary) : CPT (fun a => l a + r a) input encUnary :=
  (show CPT (fun p : ℕ × ℕ => p.1 + p.2) (encPair encUnary encUnary) encUnary by fun_prop).comp
    (hl.prod hr)
@[local fun_prop] private theorem er_unary_sub {l r : α → ℕ} (hl : CPT l input encUnary)
    (hr : CPT r input encUnary) : CPT (fun a => l a - r a) input encUnary :=
  unary_sub.comp (hl.prod hr)
@[local fun_prop] private theorem er_unary_mul {l r : α → ℕ} (hl : CPT l input encUnary)
    (hr : CPT r input encUnary) : CPT (fun a => l a * r a) input encUnary :=
  (show CPT (fun p : ℕ × ℕ => p.1 * p.2) (encPair encUnary encUnary) encUnary by fun_prop).comp
    (hl.prod hr)
@[local fun_prop] private theorem er_unary_max {l r : α → ℕ} (hl : CPT l input encUnary)
    (hr : CPT r input encUnary) : CPT (fun a => max (l a) (r a)) input encUnary :=
  (show CPT (fun p : ℕ × ℕ => max p.1 p.2) (encPair encUnary encUnary) encUnary by fun_prop).comp
    (hl.prod hr)
@[local fun_prop] private theorem er_binary_pow {b e : α → ℕ} (hb : CPT b input encNat)
    (he : CPT e input encUnary) : CPT (fun a => b a ^ e a) input encNat := binary_pow' hb he
@[local fun_prop] private theorem er_binary_div {l r : α → ℕ} (hl : CPT l input encNat)
    (hr : CPT r input encNat) : CPT (fun a => l a / r a) input encNat :=
  binary_div.comp (hl.prod hr)
@[local fun_prop] private theorem er_binary_mod {l r : α → ℕ} (hl : CPT l input encNat)
    (hr : CPT r input encNat) : CPT (fun a => l a % r a) input encNat :=
  binary_mod.comp (hl.prod hr)
@[local fun_prop] private theorem er_binary_factorial {n : α → ℕ} (hn : CPT n input encUnary) :
    CPT (fun a => (n a).factorial) input encNat :=
  (show CPT Nat.factorial encUnary encNat by fun_prop).comp hn
@[local fun_prop] private theorem er_intBin_natCast {n : α → ℕ} (hn : CPT n input encNat) :
    CPT (fun a => (n a : ℤ)) input encIntBin := intBin_natCast.comp hn
@[local fun_prop] private theorem er_intBin_natCast_unary {n : α → ℕ}
    (hn : CPT n input encUnary) : CPT (fun a => (n a : ℤ)) input encIntBin :=
  intBin_natCast.comp (unary_to_binary.comp hn)
@[local fun_prop] private theorem er_intBin_add {l r : α → ℤ} (hl : CPT l input encIntBin)
    (hr : CPT r input encIntBin) : CPT (fun a => l a + r a) input encIntBin :=
  (show CPT (fun p : ℤ × ℤ => p.1 + p.2) (encPair encIntBin encIntBin) encIntBin by fun_prop).comp
    (hl.prod hr)
@[local fun_prop] private theorem er_intBin_sub {l r : α → ℤ} (hl : CPT l input encIntBin)
    (hr : CPT r input encIntBin) : CPT (fun a => l a - r a) input encIntBin :=
  intBin_sub.comp (hl.prod hr)
@[local fun_prop] private theorem er_intBin_neg {x : α → ℤ} (hx : CPT x input encIntBin) :
    CPT (fun a => -x a) input encIntBin :=
  (show CPT (fun z : ℤ => -z) encIntBin encIntBin by fun_prop).comp hx
@[local fun_prop] private theorem er_intBin_pow {b : α → ℤ} {e : α → ℕ}
    (hb : CPT b input encIntBin) (he : CPT e input encUnary) :
    CPT (fun a => b a ^ e a) input encIntBin :=
  (show CPT (fun p : ℤ × ℕ => p.1 ^ p.2) (encPair encIntBin encUnary) encIntBin by fun_prop).comp
    (hb.prod he)
@[local fun_prop] private theorem er_intBin_sum {l : α → List ℤ}
    (hl : CPT l input (encList encIntBin)) : CPT (fun a => (l a).sum) input encIntBin :=
  (show CPT List.sum (encList encIntBin) encIntBin by fun_prop).comp hl
@[local fun_prop] private theorem er_intBin_prod {l : α → List ℤ}
    (hl : CPT l input (encList encIntBin)) : CPT (fun a => (l a).prod) input encIntBin :=
  (show CPT List.prod (encList encIntBin) encIntBin by fun_prop).comp hl
@[local fun_prop] private theorem er_length_listIntBin {l : α → List ℤ}
    (hl : CPT l input (encList encIntBin)) : CPT (fun a => (l a).length) input encUnary :=
  (length_list encIntBin).comp hl
@[local fun_prop] private theorem er_radixDigit {r idx s : α → ℕ} (hr : CPT r input encNat)
    (hidx : CPT idx input encNat) (hs : CPT s input encUnary) :
    CPT (fun a => Cslib.Radix.digit (r a) (idx a) (s a)) input encNat := by
  simp_rw [Cslib.Radix.digit_eq_div_pow_mod]; fun_prop
@[local fun_prop] private theorem er_min_D_cap {D_cap Q r : α → ℕ}
    (hD : CPT D_cap input encUnary) (hQ : CPT Q input encUnary) (hr : CPT r input encUnary) :
    CPT (fun a => min (D_cap a) (r a ^ (2 * Q a))) input encUnary := by
  have hr_bin : CPT r input encNat := unary_to_binary.comp hr
  have hpow : CPT (fun a => r a ^ (2 * Q a)) input encNat := by fun_prop
  exact binary_min_unary' hD hpow

@[local fun_prop] private theorem er_decodeAuxDigits {Q r idx : α → ℕ}
    (hQ : CPT Q input encUnary) (hr : CPT r input encNat) (hidx : CPT idx input encNat) :
    CPT (fun a => decodeAuxDigits (Q a) (r a) (idx a)) input encDigits := by
  unfold decodeAuxDigits; fun_prop
@[local fun_prop] private theorem er_decodeAuxDigits_unary {Q r idx : α → ℕ}
    (hQ : CPT Q input encUnary) (hr : CPT r input encUnary) (hidx : CPT idx input encUnary) :
    CPT (fun a => decodeAuxDigits (Q a) (r a) (idx a)) input encDigits :=
  er_decodeAuxDigits hQ (unary_to_binary.comp hr) (unary_to_binary.comp hidx)
@[local fun_prop] private theorem er_eigenvecDigits {Q : α → ℕ} {β u : α → List ℕ × List ℕ}
    (hQ : CPT Q input encUnary) (hβ : CPT β input encDigits) (hu : CPT u input encDigits) :
    CPT (fun a => eigenvecDigits (Q a) (β a) (u a)) input encIntBin := by
  unfold eigenvecDigits pairBasisNat; fun_prop
@[local fun_prop] private theorem er_antisymCountDigits {Q : α → ℕ} {β : α → List ℕ × List ℕ}
    (hQ : CPT Q input encUnary) (hβ : CPT β input encDigits) :
    CPT (fun a => antisymCountDigits (Q a) (β a)) input encUnary := by
  unfold antisymCountDigits; fun_prop

/-- `decodeAuxDigits` is computable in polynomial time from unary `Q` and binary `(r, idx)`. -/
@[fun_prop] theorem computableInPolyTime_decodeAuxDigits {Q r idx : α → ℕ}
    (hQ : ComputableInPolyTime Q input encUnary) (hr : ComputableInPolyTime r input encNat)
    (hidx : ComputableInPolyTime idx input encNat) :
    ComputableInPolyTime (fun a => decodeAuxDigits (Q a) (r a) (idx a))
      input (encPair (encList encNat) (encList encNat)) :=
  er_decodeAuxDigits hQ hr hidx

/-- `encodeAuxDigits` is computable in polynomial time from binary `r` and digit lists `u`. -/
@[fun_prop] theorem computableInPolyTime_encodeAuxDigits {r : α → ℕ} {u : α → List ℕ × List ℕ}
    (hr : ComputableInPolyTime r input encNat)
    (hu : ComputableInPolyTime u input (encPair (encList encNat) (encList encNat))) :
    ComputableInPolyTime (fun a => encodeAuxDigits (r a) (u a)) input encNat := by
  have hlist : CPT (fun a => ((u a).1 ++ (u a).2).reverse) input (encList encNat) := by fun_prop
  have hstep : CPT (fun q : (ℕ × ℕ) × ℕ => q.2 + q.1.1 * q.1.2)
      (encPair (encPair encNat encNat) encNat) encNat :=
    binary_add.comp ((snd _ _).prod
      (binary_mul' ((fst encNat encNat).comp (fst _ _)) ((snd encNat encNat).comp (fst _ _))))
  have hfold := foldlWith_of_bounded_growth
    (encP := encNat) (encA := encNat) (encL := encList encNat) (encB := encNat)
    (par := r) (list := fun a => ((u a).1 ++ (u a).2).reverse) (init := fun _ => 0)
    (step := fun base acc d => d + base * acc) hr hlist (.const 0) hstep
    (growth := fun a => (encList encNat ((u a).1 ++ (u a).2).reverse).length +
      (encNat (r a)).length + 1)
    ((hlist.polyBounded_length.add hr.polyBounded_length).add (.const 1)) (fun a acc d hd => by
      have hd_len := SizedListEncoding.length_elem_le (encA := encNat) (encL := encList encNat)
        ((u a).1 ++ (u a).2).reverse d hd
      have hadd := Nat.size_add_le_max d (r a * acc); have hmul := Nat.size_mul_le (r a) acc
      simp only [encNat_apply, Nat.size_eq_bits_len] at hd_len ⊢; omega)
  simpa only [encodeAuxDigits, List.foldl_reverse, Nat.ofDigits_eq_foldr, Nat.cast_id] using hfold

/-- `commonDenom Q R = (R - 1)! * Q!` is computable in polynomial time from unary `(Q, R)`. -/
@[fun_prop] theorem computableInPolyTime_commonDenom {Q R : α → ℕ}
    (hQ : ComputableInPolyTime Q input encUnary) (hR : ComputableInPolyTime R input encUnary) :
    ComputableInPolyTime (fun a => commonDenom (Q a) (R a)) input encNat := by
  unfold commonDenom; fun_prop

/-- `(commonDenom Q R : ℤ)` is computable in polynomial time in `encIntBin` from unary `(Q, R)`. -/
theorem computableInPolyTime_commonDenom_int {Q R : α → ℕ}
    (hQ : ComputableInPolyTime Q input encUnary) (hR : ComputableInPolyTime R input encUnary) :
    ComputableInPolyTime (fun a => (commonDenom (Q a) (R a) : ℤ)) input encIntBin :=
  intBin_natCast.comp (computableInPolyTime_commonDenom hQ hR)

/-- `auxMeasurementRowsBounded` (`C^B`) is computable in polynomial time from unary
`(D_cap, Q, r, A₀, R)`. -/
@[fun_prop] theorem computableInPolyTime_auxMeasurementRowsBounded {D_cap Q r A₀ R : α → ℕ}
    (hD : ComputableInPolyTime D_cap input encUnary) (hQ : ComputableInPolyTime Q input encUnary)
    (hr : ComputableInPolyTime r input encUnary) (hA₀ : ComputableInPolyTime A₀ input encUnary)
    (hR : ComputableInPolyTime R input encUnary) :
    ComputableInPolyTime (fun a => auxMeasurementRowsBounded (D_cap a) (Q a) (r a) (A₀ a) (R a))
      input (encList (encList encIntBin)) := by
  unfold auxMeasurementRowsBounded auxMeasurementIndicesBounded; dsimp only; fun_prop

@[local fun_prop] private theorem er_orbitWeightStep {m : α → ℕ} {c : α → ℤ} {f : α → List ℤ}
    (hm : CPT m input encUnary) (hc : CPT c input encIntBin)
    (hf : CPT f input (encList encIntBin)) :
    CPT (fun a => orbitWeightStep (m a) (c a) (f a)) input (encList encIntBin) := by
  unfold orbitWeightStep; fun_prop

@[local fun_prop] private theorem er_fallingOrbitWeights {m A₀ j : α → ℕ}
    (hm : CPT m input encUnary) (hA₀ : CPT A₀ input encUnary) (hj : CPT j input encUnary) :
    CPT (fun a => fallingOrbitWeights (m a) (A₀ a) (j a)) input (encList encIntBin) := by
  let stepFn : (ℕ × ℕ) → List ℤ → ℕ → List ℤ := fun par f a =>
    orbitWeightStep par.1 (2 * ((par.2 : ℤ) + (a : ℤ))) f
  have hstep : CPT (fun q : ((ℕ × ℕ) × List ℤ) × ℕ => stepFn q.1.1 q.1.2 q.2)
      (encPair (encPair (encPair encUnary encUnary) (encList encIntBin)) encUnary)
      (encList encIntBin) := by dsimp only [stepFn]; fun_prop
  have pm := hm.polyBounded; have pA := hA₀.polyBounded; have pj := hj.polyBounded
  have hB : PolyBounded (fun a => (input a).length)
      (fun a => (m a + 1) * (2 * (j a * (2 * (m a + A₀ a + j a)) + 2) + 1)) :=
    (pm.add (.const 1)).mul (((PolyBounded.const 2).mul
      ((pj.mul ((PolyBounded.const 2).mul ((pm.add pA).add pj))).add (.const 2))).add (.const 1))
  exact foldlWith (encP := encPair encUnary encUnary) (encA := encUnary)
    (encL := encList encUnary) (encB := encList encIntBin) (par := fun a => (m a, A₀ a))
    (list := fun a => List.range (j a)) (init := fun a => (1 : ℤ) :: List.replicate (m a) 0)
    (step := stepFn) (hm.prod hA₀) (er_range hj)
    (er_cons (.const 1) (er_replicate hm (.const 0))) hstep hB fun a i _ => by
      rw [List.take_range]
      change (encList encIntBin (fallingOrbitWeights (m a) (A₀ a) (min i (j a)))).length ≤ _
      set k := min i (j a); have hk : k ≤ j a := Nat.min_le_right i (j a)
      refine Nat.le_trans (length_encList_le encIntBin (fallingOrbitWeights (m a) (A₀ a) k)
        (b := j a * (2 * (m a + A₀ a + j a)) + 2) ?_) ?_
      · intro z hz; rw [length_encIntBin]
        have hsz := (Nat.size_le_size (natAbs_mem_fallingOrbitWeights_le (m a) (A₀ a) k z hz)).trans
          (Nat.size_pow_le (2 * (m a + A₀ a + k)) k)
        have hmon : k * (2 * (m a + A₀ a + k)).size ≤ j a * (2 * (m a + A₀ a + j a)) :=
          Nat.mul_le_mul hk ((Nat.size_le_self _).trans (by omega))
        omega
      · rw [length_fallingOrbitWeights]

@[local fun_prop] private theorem er_isSwapOrbitDigits {Q : α → ℕ} {u y : α → List ℕ × List ℕ}
    (hQ : CPT Q input encUnary) (hu : CPT u input encDigits) (hy : CPT y input encDigits) :
    CPT (fun a => isSwapOrbitDigits (Q a) (u a) (y a)) input encBool := by
  unfold isSwapOrbitDigits; fun_prop
@[local fun_prop] private theorem er_offDiagCountDigits {Q : α → ℕ} {u : α → List ℕ × List ℕ}
    (hQ : CPT Q input encUnary) (hu : CPT u input encDigits) :
    CPT (fun a => offDiagCountDigits (Q a) (u a)) input encUnary := by
  unfold offDiagCountDigits; fun_prop
@[local fun_prop] private theorem er_mismatchCountDigits {Q : α → ℕ} {u y : α → List ℕ × List ℕ}
    (hQ : CPT Q input encUnary) (hu : CPT u input encDigits) (hy : CPT y input encDigits) :
    CPT (fun a => mismatchCountDigits (Q a) (u a) (y a)) input encUnary := by
  unfold mismatchCountDigits; fun_prop
@[local fun_prop] private theorem er_eqAuxDigits {Q : α → ℕ} {u y : α → List ℕ × List ℕ}
    (hQ : CPT Q input encUnary) (hu : CPT u input encDigits) (hy : CPT y input encDigits) :
    CPT (fun a => eqAuxDigits (Q a) (u a) (y a)) input encBool := by
  unfold eqAuxDigits; fun_prop
@[local fun_prop] private theorem er_m0ScaledIntDigits {Q A₀ R : α → ℕ}
    {u y : α → List ℕ × List ℕ} (hQ : CPT Q input encUnary) (hA₀ : CPT A₀ input encUnary)
    (hR : CPT R input encUnary) (hu : CPT u input encDigits) (hy : CPT y input encDigits) :
    CPT (fun a => m0ScaledIntDigits (Q a) (A₀ a) (R a) (u a) (y a)) input encIntBin := by
  unfold m0ScaledIntDigits; dsimp only; fun_prop

@[local fun_prop] private theorem er_mismatchAnnihilatorCoeffsDigits {Q : α → ℕ}
    {u y : α → List ℕ × List ℕ} (hQ : CPT Q input encUnary) (hu : CPT u input encDigits)
    (hy : CPT y input encDigits) :
    CPT (fun a => mismatchAnnihilatorCoeffsDigits (Q a) (u a) (y a))
      input (encList encIntBin) := by
  unfold mismatchAnnihilatorCoeffsDigits
  let stepFn : ((List ℕ × List ℕ) × (List ℕ × List ℕ)) → List ℤ → ℕ → List ℤ := fun par p s =>
    if par.2.1.getD s 0 = par.1.2.getD s 0 then p.map (((s : ℤ) + 1) * ·)
    else mulLinearSub p ((s : ℤ) + 1)
  have hstep : CPT
      (fun q : (((List ℕ × List ℕ) × (List ℕ × List ℕ)) × List ℤ) × ℕ => stepFn q.1.1 q.1.2 q.2)
      (encPair (encPair (encPair encDigits encDigits) (encList encIntBin)) encUnary)
      (encList encIntBin) := by dsimp only [stepFn]; unfold mulLinearSub; fun_prop
  have pQ := hQ.polyBounded
  have hB : PolyBounded (fun a => (input a).length)
      (fun a => (Q a + 1) * (2 * (Q a * Q a + Q a + 3) + 1)) :=
    (pQ.add (.const 1)).mul
      (((PolyBounded.const 2).mul (((pQ.mul pQ).add pQ).add (.const 3))).add (.const 1))
  refine foldlWith (encP := encPair encDigits encDigits) (encA := encUnary)
    (encL := encList encUnary) (encB := encList encIntBin) (step := stepFn) (hu.prod hy)
    (range.comp hQ) (init := fun _ => [1]) (const [1]) hstep hB ?_
  intro a i _; rw [List.take_range]
  have hfold_eq : (List.range (min i (Q a))).foldl (stepFn (u a, y a)) [1] =
      mismatchAnnihilatorCoeffsDigits (min i (Q a)) (u a) (y a) := rfl
  rw [hfold_eq]; set k := min i (Q a); have hk : k ≤ Q a := Nat.min_le_right i (Q a)
  refine (length_encList_le encIntBin _ (b := Q a * Q a + Q a + 3) ?_).trans ?_
  · intro z hz; rw [length_encIntBin]; obtain ⟨j, _, rfl⟩ := List.getElem_of_mem hz
    have hj_eq : (mismatchAnnihilatorCoeffsDigits k (u a) (y a))[j] =
        (Polynomial.ofCoeffList (mismatchAnnihilatorCoeffsDigits k (u a) (y a))).coeff j := by
      rw [coeff_ofCoeffList, List.getD_eq_getElem]
    have hle : (mismatchAnnihilatorCoeffsDigits k (u a) (y a))[j].natAbs ≤ 2 ^ k * k.factorial := by
      rw [hj_eq]; exact (Polynomial.natAbs_coeff_le_coeffNorm1 _ j).trans
        ((Polynomial.coeffNorm1_ofCoeffList _).le.trans
          (sum_natAbs_mismatchAnnihilatorCoeffsDigits_le k (u a) (y a)))
    have hsz := (Nat.size_le_size hle).trans (Nat.size_mul_le (2 ^ k) k.factorial)
    have h2k : (2 ^ k).size ≤ k + 1 :=
      Nat.size_le.2 (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self k))
    have hfac := Nat.size_factorial_le k
    have hkk : k * k.size ≤ Q a * Q a := Nat.mul_le_mul hk ((Nat.size_le_self k).trans hk)
    omega
  · exact Nat.mul_le_mul_right _
      ((length_mismatchAnnihilatorCoeffsDigits_le k _ _).trans (by omega))
@[local fun_prop] private theorem er_auxReplacementRowCoeffsDigits {Q A₀ R : α → ℕ}
    {u y : α → List ℕ × List ℕ} (hQ : CPT Q input encUnary) (hA₀ : CPT A₀ input encUnary)
    (hR : CPT R input encUnary) (hu : CPT u input encDigits) (hy : CPT y input encDigits) :
    CPT (fun a => auxReplacementRowCoeffsDigits (Q a) (A₀ a) (R a) (u a) (y a))
      input (encList encIntBin) := by
  unfold auxReplacementRowCoeffsDigits; dsimp only; fun_prop

/-- `auxReplacementRowCoeffsDigits` (`d_den · P⃗_u(T)_y`) is computable in polynomial time per
`(u, y)` pair from unary `(Q, A₀, R)` and digit lists `u, y`. -/
@[fun_prop] theorem computableInPolyTime_auxReplacementRowCoeffsDigits {Q A₀ R : α → ℕ}
    {u y : α → List ℕ × List ℕ} (hQ : ComputableInPolyTime Q input encUnary)
    (hA₀ : ComputableInPolyTime A₀ input encUnary) (hR : ComputableInPolyTime R input encUnary)
    (hu : ComputableInPolyTime u input (encPair (encList encNat) (encList encNat)))
    (hy : ComputableInPolyTime y input (encPair (encList encNat) (encList encNat))) :
    ComputableInPolyTime (fun a => auxReplacementRowCoeffsDigits (Q a) (A₀ a) (R a) (u a) (y a))
      input (encList encIntBin) :=
  er_auxReplacementRowCoeffsDigits hQ hA₀ hR hu hy

/-- `auxReplacementRowCoeffsIdx` is computable in polynomial time per `(u_idx, y_idx)` pair from
unary `(Q, A₀, R)` and binary `(r, u_idx, y_idx)`. -/
@[fun_prop] theorem computableInPolyTime_auxReplacementRowCoeffsIdx {Q r A₀ R u_idx y_idx : α → ℕ}
    (hQ : ComputableInPolyTime Q input encUnary) (hr : ComputableInPolyTime r input encNat)
    (hA₀ : ComputableInPolyTime A₀ input encUnary) (hR : ComputableInPolyTime R input encUnary)
    (hu : ComputableInPolyTime u_idx input encNat) (hy : ComputableInPolyTime y_idx input encNat) :
    ComputableInPolyTime
      (fun a => auxReplacementRowCoeffsIdx (Q a) (r a) (A₀ a) (R a) (u_idx a) (y_idx a))
      input (encList encIntBin) :=
  computableInPolyTime_auxReplacementRowCoeffsDigits hQ hA₀ hR
    (computableInPolyTime_decodeAuxDigits hQ hr hu)
    (computableInPolyTime_decodeAuxDigits hQ hr hy)

/-- The `D_len × D_len × max R 1` auxiliary replacement table (`auxReplacementTableBounded`,
with `D_len = min D_cap (r ^ (2 * Q))`, giving the full `D × D` table when `r ^ (2 * Q) ≤ D_cap`)
is computable in polynomial time from unary `(D_cap, Q, r, A₀, R)` (Lemma 4.7, p. 34). -/
@[fun_prop] theorem computableInPolyTime_auxReplacementTableBounded {D_cap Q r A₀ R : α → ℕ}
    (hD : ComputableInPolyTime D_cap input encUnary) (hQ : ComputableInPolyTime Q input encUnary)
    (hr : ComputableInPolyTime r input encUnary) (hA₀ : ComputableInPolyTime A₀ input encUnary)
    (hR : ComputableInPolyTime R input encUnary) :
    ComputableInPolyTime (fun a => auxReplacementTableBounded (D_cap a) (Q a) (r a) (A₀ a) (R a))
      input (encList (encList (encList encIntBin))) := by
  unfold auxReplacementTableBounded auxReplacementRowCoeffsIdx; dsimp only; fun_prop

end PolyTime
end Cslib.LinearAlgebra
