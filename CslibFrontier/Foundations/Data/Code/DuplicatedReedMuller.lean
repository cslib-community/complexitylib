/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Binary
public import CslibFrontier.Foundations.Data.Code.Concatenation
public import CslibFrontier.Foundations.Data.Code.Hadamard
public import CslibFrontier.Foundations.Data.Code.NearestDecoding
import Mathlib.Data.Finset.Max

/-!
# The duplicated first-order Reed–Muller code used by HQC

HQC uses the binary first-order Reed–Muller code `RM(1, 7)`, with parameters
`[128, 8, 64]`, as its inner code.  Each encoded byte is repeated `μ` times; the HQC-1
parameter set uses `μ = 3`, while HQC-3 and HQC-5 use `μ = 5`.  This gives the
`[384, 8, 192]` and `[640, 8, 320]` duplicated codes [HQC2026, §3.5.3, pp. 32–37].

The source decoder sums the repeated received bits, applies the Walsh–Hadamard transform,
subtracts `64 * μ` from its constant coefficient, and scans the coefficient magnitudes using a
strict comparison.  Consequently the first (smallest) index wins a tie.  A positive selected
coefficient sets the most significant message bit.

The byte layout is the one specified immediately before `RM.Encode` on p. 32 and in its lines
2–5 on p. 34: byte bit `7` is the affine constant and byte bits `0,…,6` are the coefficients of
the corresponding binary column bits.  `drmEncode` matches the repetition in `dRM.Encode`,
lines 2–6 (p. 33); `drmExpandAndSum` matches
`dRM.Decode.ExpandAndSum`, lines 2–6 (p. 35); `drmHadamardTransform` and the zero-coefficient
correction match `dRM.Decode.Hadamard`, lines 4–15 (p. 36); and `drmFindPeak`/`drmDecode` match
the strict scan and sign step in `dRM.Decode.FindPeaks`, lines 4–12 (p. 37).

This module exposes the typed bit-word and source-byte-layout mathematics of that codec.  Packing
whole messages into byte arrays and the shortened Reed–Solomon outer code are separate layers.  In
particular, it does not yet compose the actual outer decoder or establish the Model-2 calculation
in §6.1.4, Equation (9), or the numerical failure probabilities in Table 16.

## Main definitions

* `Cslib.Code.RMMessage`: one source byte as a sign bit and seven-bit slope.
* `Cslib.Code.rmMessageByteEquiv`: the exact source-byte layout.
* `Cslib.Code.rmEncode`: the `RM(1, 7)` affine evaluation word.
* `Cslib.Code.drmEncode`: multiplicity-parameterized duplication.
* `Cslib.Code.drmExpandAndSum`, `Cslib.Code.drmHadamardTransform`,
  `Cslib.Code.drmHadamardCoeff`: the source decoder's summed bits, staged transform and corrected
  coefficients.
* `Cslib.Code.drmDecode`: the deterministic smallest-peak decoder.

## Main results

* `Cslib.Code.drmDecode_isNearestDecoder`: the source decoder chooses a nearest duplicated
  Reed–Muller codeword.
* `Cslib.Code.drmDecode_add_eq_of_two_mul_weight_lt`: errors of weight `e` decode correctly when
  `2 * e < 64 * μ`.

## References

* [HQC specification, version 5.1][HQC2026], §3.5.3, pp. 32–37.
-/

@[expose] public section

namespace Cslib.Code

open Finset Matrix Cslib.BitString

/-- A byte for `RM(1, 7)`: the most significant bit is the affine constant and the remaining
seven bits select the linear character. -/
structure RMMessage where
  /-- The most significant source-byte bit. -/
  sign : Bool
  /-- The seven low source-byte bits, read least-significant bit first. -/
  slope : BitString 7
  deriving DecidableEq

/-- A source byte is equivalently its sign bit paired with its seven low bits. -/
def rmMessageEquiv : RMMessage ≃ Bool × BitString 7 where
  toFun m := (m.sign, m.slope)
  invFun m := ⟨m.1, m.2⟩
  left_inv m := by cases m; rfl
  right_inv m := by cases m; rfl

/-- The exact source-byte layout: the sign is bit `7` (the most significant bit), while slope
coordinate `i` is byte bit `i` for `0 ≤ i < 7`. -/
def rmMessageByteEquiv : RMMessage ≃ BitString 8 :=
  rmMessageEquiv.trans (Fin.snocEquiv fun _ : Fin 8 => Bool)

@[simp]
theorem rmMessageByteEquiv_apply_last (m : RMMessage) :
    rmMessageByteEquiv m (Fin.last 7) = m.sign := by
  change (Fin.snoc m.slope m.sign : Fin 8 → Bool) (Fin.last 7) = m.sign
  simp [Fin.snoc]

@[simp]
theorem rmMessageByteEquiv_apply_castSucc (m : RMMessage) (i : Fin 7) :
    rmMessageByteEquiv m i.castSucc = m.slope i := by
  simp [rmMessageByteEquiv, rmMessageEquiv]

instance : Fintype RMMessage := Fintype.ofEquiv (Bool × BitString 7) rmMessageEquiv.symm

/-- The 128 evaluation points of `RM(1, 7)`. -/
abbrev RMPoint := BitString 7

/-- One `RM(1, 7)` codeword. -/
abbrev RMWord := RMPoint → Bool

/-- A Reed–Muller word repeated `μ` times. -/
abbrev DRMWord (μ : ℕ) := Fin μ × RMPoint → Bool

/-- The source's `RM.Encode`: evaluate the affine Boolean function named by the byte. -/
def rmEncode (m : RMMessage) : RMWord :=
  fun x => m.sign ^^ hadamardCode m.slope x

/-- The source generator-matrix multiplication, stated in byte coordinates: byte bit `7`
multiplies the all-one row, while byte bit `i` multiplies coordinate `i` of the binary column.
Thus this also records the reversal between the source's top-to-bottom matrix rows and its
least-significant-bit-first byte indices. -/
theorem rmEncode_apply_generatorMatrix (m : RMMessage) (x : RMPoint) :
    rmEncode m x = (rmMessageByteEquiv m (Fin.last 7) ^^
      ∑ i : Fin 7, (rmMessageByteEquiv m i.castSucc && x i)) := by
  simp only [rmEncode, rmMessageByteEquiv_apply_last, rmMessageByteEquiv_apply_castSucc,
    hadamardCode_apply, dotProduct, Bool.mul_eq_and]

/-- The source's `dRM.Encode`: repeat the same `RM(1, 7)` word `μ` times. -/
def drmEncode (μ : ℕ) (m : RMMessage) : DRMWord μ :=
  fun x => rmEncode m x.2

/-- `RM.Encode` with zero slope is the constant sign word. -/
@[simp]
theorem rmEncode_zero_slope (b : Bool) : rmEncode ⟨b, 0⟩ = fun _ => b := by
  funext x
  simp only [rmEncode, hadamardCode_apply, zero_dotProduct]
  exact Bool.xor_false b

/-- The encoder is the Hadamard word shifted by the source byte's most significant bit. -/
theorem rmEncode_eq_add_hadamardCode (m : RMMessage) :
    rmEncode m = (fun _ => m.sign) + hadamardCode m.slope := by
  funext x
  rw [rmEncode]
  rfl

/-- The 128 points of `RM(1, 7)`. -/
theorem card_rmPoint : Fintype.card RMPoint = 128 := by
  simp only [RMPoint, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  decide

/-- A duplicated word has `128 * μ` bits. -/
theorem card_drmWordIndex (μ : ℕ) : Fintype.card (Fin μ × RMPoint) = 128 * μ := by
  rw [Fintype.card_prod, Fintype.card_fin, card_rmPoint]
  omega

/-- Duplication does not change the bit within any repeated block. -/
@[simp]
theorem drmEncode_apply (μ : ℕ) (m : RMMessage) (r : Fin μ) (x : RMPoint) :
    drmEncode μ m (r, x) = rmEncode m x :=
  rfl

/-- The source's `dRM.Decode.ExpandAndSum`: count the received one-bits at each of the 128
positions across all duplicated blocks. -/
def drmExpandAndSum {μ : ℕ} (w : DRMWord μ) (x : RMPoint) : ℤ :=
  ∑ r : Fin μ, (w (r, x)).toNat

/-- A Walsh character, represented by `+1` for Boolean inner product zero and `-1` for one. -/
def walshSign {n : ℕ} (a x : BitString n) : ℤ :=
  if a ⬝ᵥ x then -1 else 1

/-- The in-place butterfly computation in `dRM.Decode.Hadamard`, expressed recursively: first
combine adjacent entries (coordinate `0`, the least significant index bit), then perform the
remaining stages on the two resulting halves.  At width `7` this is exactly the source's seven
Walsh–Hadamard rounds. -/
def drmHadamardTransform : {n : ℕ} → (BitString n → ℤ) → BitString n → ℤ
  | 0, v, a => v a
  | _n + 1, v, a =>
      let v₀ := fun x => v (Fin.cons false x)
      let v₁ := fun x => v (Fin.cons true x)
      if a 0 then
        drmHadamardTransform (fun x => v₀ x - v₁ x) (Fin.tail a)
      else
        drmHadamardTransform (fun x => v₀ x + v₁ x) (Fin.tail a)

private theorem sum_bitString_succ {n : ℕ} (f : BitString (n + 1) → ℤ) :
    (∑ x, f x) = ∑ y : BitString n, (f (Fin.cons false y) + f (Fin.cons true y)) := by
  calc
    (∑ x, f x) = ∑ p : Bool × BitString n, f (Fin.cons p.1 p.2) := by
      symm
      exact Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => Bool) _ _ fun _ => rfl
    _ = ∑ b : Bool, ∑ y : BitString n, f (Fin.cons b y) := Fintype.sum_prod_type _
    _ = ∑ y : BitString n, (f (Fin.cons false y) + f (Fin.cons true y)) := by
      rw [Fintype.sum_bool, sum_add_distrib, add_comm]

private theorem walshSign_cons {n : ℕ} (b c : Bool) (a x : BitString n) :
    walshSign (Fin.cons b a) (Fin.cons c x) =
      (if b && c then -1 else 1) * walshSign a x := by
  have hdot : (Fin.cons b a) ⬝ᵥ (Fin.cons c x) = ((b && c) ^^ (a ⬝ᵥ x)) := by
    simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Bool.mul_eq_and, Bool.add_eq_xor]
  simp only [walshSign, hdot]
  cases hbc : b && c <;> cases hax : a ⬝ᵥ x <;>
    simp_all only [Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true,
      ite_true] <;> norm_num

/-- The staged transform computes the direct Walsh correlation.  This pins the source's butterfly
implementation to the mathematical transform used in the decoder proof. -/
theorem drmHadamardTransform_eq_sum {n : ℕ} (v : BitString n → ℤ) (a : BitString n) :
    drmHadamardTransform v a = ∑ x, walshSign a x * v x := by
  induction n with
  | zero =>
      have ha : a = fun i => Fin.elim0 i := Subsingleton.elim _ _
      subst a
      let z : BitString 0 := fun i => Fin.elim0 i
      have huniv : (univ : Finset (BitString 0)) = {z} := by
        ext x
        simp only [mem_univ, mem_singleton, true_iff]
        exact Subsingleton.elim _ _
      change v z = (univ : Finset (BitString 0)).sum fun x => walshSign z x * v x
      rw [huniv, sum_singleton]
      simp [walshSign, dotProduct]
  | succ n ih =>
      rw [← Fin.cons_self_tail a]
      cases a 0
      · simp only [drmHadamardTransform, Fin.cons_zero, Fin.tail_cons]
        simp only [Bool.false_eq_true, ite_false]
        rw [ih, sum_bitString_succ]
        refine sum_congr rfl fun x _ => ?_
        rw [walshSign_cons, walshSign_cons]
        norm_num
        ring
      · simp only [drmHadamardTransform, Fin.cons_zero, Fin.tail_cons]
        simp only [ite_true]
        rw [ih, sum_bitString_succ]
        refine sum_congr rfl fun x _ => ?_
        rw [walshSign_cons, walshSign_cons]
        norm_num
        ring

/-- The corrected Walsh–Hadamard coefficient used by the source decoder.  The subtraction at
the zero slope is line 15 of `dRM.Decode.Hadamard`. -/
def drmHadamardCoeff {μ : ℕ} (w : DRMWord μ) (a : RMPoint) : ℤ :=
  drmHadamardTransform (drmExpandAndSum w) a -
    if a = 0 then 64 * μ else 0

private theorem walshSign_mul_toNat (p q : Bool) :
    (if p then (-1 : ℤ) else 1) * q.toNat =
      ((if p ≠ q then 1 else 0 : ℕ) : ℤ) - p.toNat := by
  cases p <;> cases q <;> decide

private theorem card_dotProduct_eq_true (a : RMPoint) :
    #{x | a ⬝ᵥ x = true} = if a = 0 then 0 else 64 := by
  by_cases ha : a = 0
  · subst a
    change #{_x : RMPoint | false = true} = 0
    simp only [Bool.false_eq_true, filter_false, card_empty]
  · rw [ite_eq_right ha]
    have h := two_mul_card_dotProduct_eq_true_add a
    simp only [Fintype.card_fin, ha, ite_false] at h
    norm_num at h
    omega

/-- The corrected coefficient at `a` is the distance from the received word to the unsigned
affine word of slope `a`, centered at half the duplicated block length. -/
theorem drmHadamardCoeff_eq_hammingDist_sub {μ : ℕ} (w : DRMWord μ) (a : RMPoint) :
    drmHadamardCoeff w a =
      (hammingDist (drmEncode μ ⟨false, a⟩) w : ℤ) - 64 * μ := by
  have hpoint (x : RMPoint) (r : Fin μ) :
      walshSign a x * (w (r, x)).toNat =
        ((if drmEncode μ ⟨false, a⟩ (r, x) ≠ w (r, x) then 1 else 0 : ℕ) : ℤ) -
          (a ⬝ᵥ x).toNat := by
    simpa only [walshSign, drmEncode_apply, rmEncode, Bool.false_xor, hadamardCode_apply] using
      walshSign_mul_toNat (a ⬝ᵥ x) (w (r, x))
  have hraw :
      (∑ x : RMPoint, walshSign a x * drmExpandAndSum w x) =
        (hammingDist (drmEncode μ ⟨false, a⟩) w : ℤ) -
          μ * #{x | a ⬝ᵥ x = true} := by
    rw [hammingDist, card_filter]
    push_cast
    rw [Fintype.sum_prod_type]
    simp only [drmExpandAndSum, mul_sum, hpoint, sum_sub_distrib]
    have hmismatch :
        (∑ x : RMPoint, ∑ r : Fin μ,
          ((if drmEncode μ ⟨false, a⟩ (r, x) ≠ w (r, x) then 1 else 0 : ℕ) : ℤ)) =
          ∑ r : Fin μ,
            (#{x | drmEncode μ ⟨false, a⟩ (r, x) ≠ w (r, x)} : ℤ) := by
      rw [sum_comm]
      refine sum_congr rfl fun r _ => ?_
      exact_mod_cast (card_filter _ _).symm
    have hdot :
        (∑ x : RMPoint, ∑ _r : Fin μ, ((a ⬝ᵥ x).toNat : ℤ)) =
          μ * #{x | a ⬝ᵥ x = true} := by
      have hbool :
          (∑ x : RMPoint, ((a ⬝ᵥ x).toNat : ℤ)) = #{x | a ⬝ᵥ x = true} := by
        rw [← Nat.cast_sum]
        exact_mod_cast (weight_eq_sum_toNat (hadamardCode a)).symm
      calc
        (∑ x : RMPoint, ∑ _r : Fin μ, ((a ⬝ᵥ x).toNat : ℤ)) =
            ∑ x : RMPoint, (μ : ℤ) * ((a ⬝ᵥ x).toNat : ℤ) := by
              refine sum_congr rfl fun x _ => ?_
              simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = (μ : ℤ) * ∑ x : RMPoint, ((a ⬝ᵥ x).toNat : ℤ) := by rw [mul_sum]
        _ = (μ : ℤ) * #{x | a ⬝ᵥ x = true} := by rw [hbool]
    rw [hmismatch, hdot]
    congr 1
    refine sum_congr rfl fun r _ => ?_
    simpa only [mem_univ, true_and] using
      (natCast_card_filter (R := ℤ)
        (fun x : RMPoint => drmEncode μ ⟨false, a⟩ (r, x) ≠ w (r, x)) univ)
  rw [drmHadamardCoeff, drmHadamardTransform_eq_sum, hraw]
  rw [card_dotProduct_eq_true]
  split_ifs <;> push_cast <;> ring

/-- The largest absolute corrected Hadamard coefficient. -/
def drmPeakMagnitude {μ : ℕ} (w : DRMWord μ) : ℕ :=
  (univ.image fun a : RMPoint => (drmHadamardCoeff w a).natAbs).max' <| by
    simp

/-- Slopes attaining the largest corrected coefficient magnitude. -/
def drmPeakSlopes {μ : ℕ} (w : DRMWord μ) : Finset RMPoint :=
  univ.filter fun a => (drmHadamardCoeff w a).natAbs = drmPeakMagnitude w

theorem drmPeakSlopes_nonempty {μ : ℕ} (w : DRMWord μ) :
    (drmPeakSlopes w).Nonempty := by
  let S := univ.image fun a : RMPoint => (drmHadamardCoeff w a).natAbs
  have hS : S.Nonempty := by simp [S]
  obtain ⟨a, ha, hvalue⟩ := mem_image.mp (max'_mem S hS)
  refine ⟨a, mem_filter.2 ⟨ha, ?_⟩⟩
  simpa only [drmPeakMagnitude, S] using hvalue

/-- The source's strict left-to-right peak scan: the smallest slope attaining maximum absolute
coefficient. -/
def drmFindPeak {μ : ℕ} (w : DRMWord μ) : RMPoint :=
  (BitString.equivFin 7).symm <|
    ((drmPeakSlopes w).image (BitString.equivFin 7)).min' <| (drmPeakSlopes_nonempty w).image _

theorem drmFindPeak_mem_peakSlopes {μ : ℕ} (w : DRMWord μ) :
    drmFindPeak w ∈ drmPeakSlopes w := by
  let hnonempty := (drmPeakSlopes_nonempty w).image (BitString.equivFin 7)
  have hmin := min'_mem ((drmPeakSlopes w).image (BitString.equivFin 7)) hnonempty
  obtain ⟨a, ha, heq⟩ := mem_image.mp hmin
  have hback :
      (BitString.equivFin 7).symm
          (((drmPeakSlopes w).image (BitString.equivFin 7)).min' hnonempty) = a := by
    rw [← heq, Equiv.symm_apply_apply]
  simpa only [drmFindPeak, hnonempty, hback] using ha

/-- If slope zero attains the maximum magnitude, the strict left-to-right scan returns it,
including when other slopes tie it. -/
theorem drmFindPeak_eq_zero_of_max {μ : ℕ} (w : DRMWord μ)
    (hmax : ∀ a, (drmHadamardCoeff w a).natAbs ≤ (drmHadamardCoeff w 0).natAbs) :
    drmFindPeak w = 0 := by
  have hzeroImage : (drmHadamardCoeff w 0).natAbs ∈
      univ.image fun a : RMPoint => (drmHadamardCoeff w a).natAbs :=
    mem_image.mpr ⟨0, mem_univ _, rfl⟩
  have hpeakMagnitude : drmPeakMagnitude w = (drmHadamardCoeff w 0).natAbs := by
    unfold drmPeakMagnitude
    apply le_antisymm
    · exact max'_le _ _ _ fun y hy => by
        obtain ⟨a, _, rfl⟩ := mem_image.mp hy
        exact hmax a
    · exact le_max' _ _ hzeroImage
  have hzeroPeak : 0 ∈ drmPeakSlopes w := by
    exact mem_filter.mpr ⟨mem_univ _, hpeakMagnitude.symm⟩
  let hnonempty := (drmPeakSlopes_nonempty w).image (BitString.equivFin 7)
  have hzeroFin : BitString.equivFin 7 (0 : RMPoint) = 0 := by
    apply Fin.eq_of_val_eq
    exact BitString.val_equivFin_false 7
  have hmemZero : (0 : Fin (2 ^ 7)) ∈
      (drmPeakSlopes w).image (BitString.equivFin 7) := by
    rw [← hzeroFin]
    exact mem_image_of_mem _ hzeroPeak
  have hmin :
      ((drmPeakSlopes w).image (BitString.equivFin 7)).min' hnonempty = 0 := by
    apply Fin.eq_of_val_eq
    exact Nat.eq_zero_of_le_zero <| Fin.le_iff_val_le_val.mp <| min'_le _ _ hmemZero
  unfold drmFindPeak
  rw [hmin, ← hzeroFin, Equiv.symm_apply_apply]

/-- The selected peak has coefficient magnitude at least that of every slope. -/
theorem drmHadamardCoeff_natAbs_le_findPeak {μ : ℕ} (w : DRMWord μ) (a : RMPoint) :
    (drmHadamardCoeff w a).natAbs ≤ (drmHadamardCoeff w (drmFindPeak w)).natAbs := by
  have hmem : (drmHadamardCoeff w a).natAbs ∈
      univ.image fun b : RMPoint => (drmHadamardCoeff w b).natAbs :=
    mem_image.mpr ⟨a, mem_univ _, rfl⟩
  have hmax := le_max' (univ.image fun b : RMPoint => (drmHadamardCoeff w b).natAbs)
    (drmHadamardCoeff w a).natAbs hmem
  have hpeak := (mem_filter.mp (drmFindPeak_mem_peakSlopes w)).2
  exact hmax.trans_eq hpeak.symm

private theorem drmEncode_true_eq_not (μ : ℕ) (a : RMPoint) :
    drmEncode μ ⟨true, a⟩ = fun i => !drmEncode μ ⟨false, a⟩ i := by
  funext i
  simp only [drmEncode, rmEncode]
  cases hadamardCode a i.2 <;> decide

private theorem hammingDist_not_left_add {I : Type*} [Fintype I] (f g : I → Bool) :
    hammingDist (fun i => !f i) g + hammingDist f g = Fintype.card I := by
  rw [hammingDist, hammingDist, card_filter, card_filter, ← sum_add_distrib]
  calc
    (∑ i : I, ((if (!f i) ≠ g i then 1 else 0) + (if f i ≠ g i then 1 else 0))) =
        ∑ _i : I, 1 := by
          refine sum_congr rfl fun i _ => ?_
          cases f i <;> cases g i <;> decide
    _ = Fintype.card I := by simp

private theorem hammingDist_drmEncode_true_add_false {μ : ℕ} (w : DRMWord μ) (a : RMPoint) :
    hammingDist (drmEncode μ ⟨true, a⟩) w +
        hammingDist (drmEncode μ ⟨false, a⟩) w = 128 * μ := by
  rw [drmEncode_true_eq_not, hammingDist_not_left_add, card_drmWordIndex]

/-- At the encoded slope, the corrected coefficient is `-64 * μ` for a clear source sign bit and
`64 * μ` for a set sign bit.  This pins the source decoder's coefficient-sign convention. -/
theorem drmHadamardCoeff_encode (μ : ℕ) (m : RMMessage) :
    drmHadamardCoeff (drmEncode μ m) m.slope =
      if m.sign then (64 * μ : ℤ) else -(64 * μ : ℤ) := by
  rcases m with ⟨b, a⟩
  rw [drmHadamardCoeff_eq_hammingDist_sub]
  cases b
  · simp only [Bool.false_eq_true, ite_false, hammingDist_self, Nat.cast_zero, zero_sub]
  · simp only [ite_true]
    have htotal := hammingDist_drmEncode_true_add_false (drmEncode μ ⟨true, a⟩) a
    rw [hammingDist_self, zero_add] at htotal
    omega

private theorem hammingDist_chosenSign_add_natAbs {μ : ℕ} (w : DRMWord μ) (a : RMPoint) :
    hammingDist (drmEncode μ ⟨0 < drmHadamardCoeff w a, a⟩) w +
        (drmHadamardCoeff w a).natAbs = 64 * μ := by
  have hcoeff := drmHadamardCoeff_eq_hammingDist_sub w a
  have htotal := hammingDist_drmEncode_true_add_false w a
  by_cases hpos : 0 < drmHadamardCoeff w a
  · simp only [hpos, decide_true]
    have habs : ((drmHadamardCoeff w a).natAbs : ℤ) = drmHadamardCoeff w a :=
      Int.natAbs_of_nonneg hpos.le
    omega
  · simp only [hpos, decide_false]
    have habs : ((drmHadamardCoeff w a).natAbs : ℤ) = -drmHadamardCoeff w a :=
      Int.ofNat_natAbs_of_nonpos (not_lt.mp hpos)
    omega

/-- The source's deterministic best-effort duplicated Reed–Muller decoder. -/
def drmDecode {μ : ℕ} (w : DRMWord μ) : RMMessage :=
  let a := drmFindPeak w
  ⟨0 < drmHadamardCoeff w a, a⟩

private theorem hammingDist_chosenSign_le {μ : ℕ} (w : DRMWord μ) (m : RMMessage) :
    hammingDist (drmEncode μ ⟨0 < drmHadamardCoeff w m.slope, m.slope⟩) w ≤
      hammingDist (drmEncode μ m) w := by
  rcases m with ⟨b, a⟩
  cases b <;> by_cases hpos : 0 < drmHadamardCoeff w a
  · simp only [hpos, decide_true]
    have hcoeff := drmHadamardCoeff_eq_hammingDist_sub w a
    have htotal := hammingDist_drmEncode_true_add_false w a
    omega
  · simp only [hpos, decide_false]
    exact le_rfl
  · simp only [hpos, decide_true]
    exact le_rfl
  · simp only [hpos, decide_false]
    have hcoeff := drmHadamardCoeff_eq_hammingDist_sub w a
    have htotal := hammingDist_drmEncode_true_add_false w a
    omega

/-- The source decoder chooses a nearest duplicated Reed–Muller codeword.  Its strict peak update
fixes one deterministic member when several messages are tied. -/
theorem drmDecode_isNearestDecoder (μ : ℕ) :
    BitString.IsNearestDecoder (drmEncode μ) drmDecode := by
  intro w m
  let a := drmFindPeak w
  change hammingDist (drmEncode μ ⟨0 < drmHadamardCoeff w a, a⟩) w ≤
    hammingDist (drmEncode μ m) w
  have hchosen := hammingDist_chosenSign_add_natAbs w a
  have hmagnitude := drmHadamardCoeff_natAbs_le_findPeak w m.slope
  have hmchosen := hammingDist_chosenSign_add_natAbs w m.slope
  have hslopemin := hammingDist_chosenSign_le w m
  have hcross :
      hammingDist (drmEncode μ ⟨0 < drmHadamardCoeff w a, a⟩) w ≤
        hammingDist (drmEncode μ ⟨0 < drmHadamardCoeff w m.slope, m.slope⟩) w := by
    dsimp only [a] at hchosen hmagnitude ⊢
    omega
  exact hcross.trans hslopemin

@[simp] private theorem rmEncode_false (a : RMPoint) :
    rmEncode ⟨false, a⟩ = hadamardCode a := by
  funext x
  simp only [rmEncode, Bool.false_xor]

private theorem rmEncode_true (a : RMPoint) :
    rmEncode ⟨true, a⟩ = fun x => !hadamardCode a x := by
  funext x
  simp only [rmEncode]
  cases hadamardCode a x <;> decide

private theorem two_mul_hammingDist_rmEncode_of_slope_ne (b c : Bool) {a a' : RMPoint}
    (haa' : a ≠ a') :
    2 * hammingDist (rmEncode ⟨b, a⟩) (rmEncode ⟨c, a'⟩) = 128 := by
  have hhalf := two_mul_hammingDist_hadamardCode haa'
  simp only [Fintype.card_fin] at hhalf
  norm_num at hhalf
  cases b <;> cases c
  · simpa only [rmEncode_false] using hhalf
  · rw [rmEncode_false, rmEncode_true, hammingDist_comm]
    have htotal := hammingDist_not_left_add (hadamardCode a') (hadamardCode a)
    have hhalf' : 2 * hammingDist (hadamardCode a') (hadamardCode a) = 128 := by
      rw [hammingDist_comm]
      exact hhalf
    rw [show Fintype.card RMPoint = 128 by exact card_rmPoint] at htotal
    omega
  · rw [rmEncode_true, rmEncode_false]
    have htotal := hammingDist_not_left_add (hadamardCode a) (hadamardCode a')
    rw [show Fintype.card RMPoint = 128 by exact card_rmPoint] at htotal
    omega
  · simpa only [rmEncode_true, hammingDist_not] using hhalf

/-- Distinct affine `RM(1, 7)` messages have Hamming distance at least `64`. -/
theorem sixtyFour_le_hammingDist_rmEncode {m m' : RMMessage} (hmm' : m ≠ m') :
    64 ≤ hammingDist (rmEncode m) (rmEncode m') := by
  rcases m with ⟨b, a⟩
  rcases m' with ⟨b', a'⟩
  by_cases haa' : a = a'
  · subst a'
    have hbb' : b ≠ b' := fun h => hmm' (by cases h; rfl)
    cases b <;> cases b'
    · exact absurd rfl hbb'
    · rw [rmEncode_false, rmEncode_true, hammingDist_comm]
      have htotal := hammingDist_not_left_add (hadamardCode a) (hadamardCode a)
      rw [hammingDist_self, add_zero,
        show Fintype.card RMPoint = 128 by exact card_rmPoint] at htotal
      omega
    · rw [rmEncode_true, rmEncode_false]
      have htotal := hammingDist_not_left_add (hadamardCode a) (hadamardCode a)
      rw [hammingDist_self, add_zero,
        show Fintype.card RMPoint = 128 by exact card_rmPoint] at htotal
      omega
    · exact absurd rfl hbb'
  · have h := two_mul_hammingDist_rmEncode_of_slope_ne b b' haa'
    omega

/-- Duplication multiplies the inner Reed–Muller distance by its parameter `μ`. -/
theorem hammingDist_drmEncode (μ : ℕ) (m m' : RMMessage) :
    hammingDist (drmEncode μ m) (drmEncode μ m') =
      μ * hammingDist (rmEncode m) (rmEncode m') := by
  change hammingDist (concat rmEncode (fun _ : Fin μ => m))
      (concat rmEncode (fun _ : Fin μ => m')) = _
  rw [hammingDist_concat]
  simp

/-- Messages with distinct slopes are exactly `64 * μ` bits apart, independently of their sign
bits.  Thus the lower bound is attained for every positive multiplicity. -/
theorem hammingDist_drmEncode_of_slope_ne (μ : ℕ) {m m' : RMMessage}
    (hslopes : m.slope ≠ m'.slope) :
    hammingDist (drmEncode μ m) (drmEncode μ m') = 64 * μ := by
  rcases m with ⟨b, a⟩
  rcases m' with ⟨b', a'⟩
  rw [hammingDist_drmEncode]
  have h : 2 * hammingDist (rmEncode ⟨b, a⟩) (rmEncode ⟨b', a'⟩) = 128 :=
    two_mul_hammingDist_rmEncode_of_slope_ne b b' hslopes
  have hinner : hammingDist (rmEncode ⟨b, a⟩) (rmEncode ⟨b', a'⟩) = 64 := by omega
  rw [hinner, mul_comm]

/-- Distinct messages in the multiplicity-`μ` code are at distance at least `64 * μ`. -/
theorem sixtyFour_mul_le_hammingDist_drmEncode (μ : ℕ) {m m' : RMMessage} (hmm' : m ≠ m') :
    64 * μ ≤ hammingDist (drmEncode μ m) (drmEncode μ m') := by
  rw [hammingDist_drmEncode, mul_comm μ]
  exact Nat.mul_le_mul_right μ (sixtyFour_le_hammingDist_rmEncode hmm')

private theorem hammingDist_drmEncode_add (μ : ℕ) (m : RMMessage) (error : DRMWord μ) :
    hammingDist (drmEncode μ m) (drmEncode μ m + error) = weight error := by
  calc
    hammingDist (drmEncode μ m) (drmEncode μ m + error) =
        hammingDist (drmEncode μ m + 0) (drmEncode μ m + error) := by rw [add_zero]
    _ = hammingDist 0 error := hammingDist_add_left _ _ _
    _ = weight error := by rw [hammingDist_eq_weight_add, zero_add]

/-- **Unique decoding below half distance.**  The actual HQC duplicated Reed–Muller decoder
recovers a message after adding any error word whose weight `e` satisfies `2 * e < 64 * μ`. -/
theorem drmDecode_add_eq_of_two_mul_weight_lt {μ : ℕ} (m : RMMessage) (error : DRMWord μ)
    (herror : 2 * weight error < 64 * μ) :
    drmDecode (drmEncode μ m + error) = m := by
  let w := drmEncode μ m + error
  by_contra hne
  change drmDecode w ≠ m at hne
  have hlower := sixtyFour_mul_le_hammingDist_drmEncode μ hne
  have hnearest := drmDecode_isNearestDecoder μ w m
  have herr : hammingDist (drmEncode μ m) w = weight error := by
    exact hammingDist_drmEncode_add μ m error
  have htriangle := hammingDist_triangle (drmEncode μ (drmDecode w)) w (drmEncode μ m)
  rw [hammingDist_comm w] at htriangle
  omega

/-- For every positive multiplicity, decoding is a left inverse to duplicated encoding. -/
theorem drmDecode_leftInverse {μ : ℕ} (hμ : 0 < μ) :
    Function.LeftInverse drmDecode (drmEncode μ) := by
  intro m
  have hweight : weight (0 : DRMWord μ) = 0 := by
    rw [weight]
    simp only [Pi.zero_apply, Bool.zero_eq_false, Bool.false_eq_true, filter_false, card_empty]
  simpa only [add_zero] using
    drmDecode_add_eq_of_two_mul_weight_lt m (0 : DRMWord μ) (by rw [hweight]; omega)

end Cslib.Code
