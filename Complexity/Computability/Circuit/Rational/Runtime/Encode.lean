/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Rational.Defs
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Polynomial-time canonical binary encodings of naturals and rationals

This module bridges the self-delimiting binary encodings `Cslib.Circuits.Rational.encodeNat` and
`Cslib.Circuits.Rational.encodeRat` from `Complexity/Computability/Circuit/Rational/Defs.lean` to
the `fun_prop`
polynomial-time calculus over `Turing.MultiTapeTM.encNat` and `Turing.MultiTapeTM.encIntBin`.

First, `encodeNat a` is shown to equal `List.replicate a.bits.length true ++ false :: a.bits`
(`encodeNat_eq`), yielding a polynomial-time certificate `encodeNat_polytime`. Next, the reduced
numerator magnitude, denominator, and sign bit of `Rat.divInt a b` are expressed in terms of
`a.natAbs`, `b.natAbs`, and `Nat.gcd a.natAbs b.natAbs` (`divInt_num_abs`, `divInt_den`,
`divInt_sign`, and `encodeRat_divInt`). Combining binary integer operations with `binary_div` and
`binary_gcd` then certifies `(p, q) ↦ encodeRat (Rat.divInt p q)` on binary integer pairs
(`encodeDivInt_polytime`).

## Main results

* `Cslib.Circuits.Rational.digits_two_map_bne_zero`: `(Nat.digits 2 a).map (· != 0) = a.bits`.
* `Cslib.Circuits.Rational.encodeNat_eq`: `encodeNat a` in terms of `a.bits`.
* `Cslib.Circuits.Rational.encodeNat_polytime`, `.encodeNat_polytime'`: polynomial-time
  certificates for `encodeNat`.
* `Cslib.Circuits.Rational.divInt_num_abs`, `.divInt_den`, `.divInt_sign`: reduced components of
  `Rat.divInt a b` via `Nat.gcd a.natAbs b.natAbs`.
* `Cslib.Circuits.Rational.encodeRat_divInt`: unconditional expansion of
  `encodeRat (Rat.divInt a b)`.
* `Cslib.Circuits.Rational.encodeDivInt_polytime`, `.encodeDivInt_polytime'`: polynomial-time
  certificates for `(p, q) ↦ encodeRat (Rat.divInt p q)`.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/RationalBinary.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits.Rational

open Turing.MultiTapeTM

/-- Mapping `· != 0` over the base-2 digits of `a` recovers `a.bits`. -/
theorem digits_two_map_bne_zero (a : ℕ) :
    (Nat.digits 2 a).map (fun b => b != 0) = a.bits := by
  rw [Nat.digits_two_eq_bits, List.map_map]
  have hfn : ((fun b : ℕ => b != 0) ∘ fun b : Bool => bif b then 1 else 0) = id := by
    funext b
    cases b <;> rfl
  rw [hfn, List.map_id]

/-- `encodeNat a` is the unary length of `a.bits`, a `false` delimiter, and `a.bits`. -/
theorem encodeNat_eq (a : ℕ) :
    encodeNat a = List.replicate a.bits.length true ++ false :: a.bits := by
  simp [encodeNat, digits_two_map_bne_zero]

/-- Self-delimiting binary encoding of a binary natural is computable in polynomial time. -/
@[fun_prop, program_certificate]
theorem encodeNat_polytime :
    ComputableInPolyTime encodeNat encNat encBits := by
  refine .of_tidy ?_
  have h : ComputableTidilyInPolyTime
      (fun a : ℕ => List.replicate a.bits.length true ++ false :: a.bits) encNat encBits := by
    fun_prop
  exact h.of_enc_eq fun a => congrArg encBits (encodeNat_eq a)

/-- Self-delimiting binary encoding of a computed binary natural. -/
@[fun_prop, program_certificate]
theorem encodeNat_polytime' {α : Type} {input : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f input encNat) :
    ComputableInPolyTime (fun a => encodeNat (f a)) input encBits :=
  encodeNat_polytime.comp hf

/-- Reduced numerator magnitude of `Rat.divInt a b` for `b ≠ 0`. -/
theorem divInt_num_abs (a b : ℤ) (hb : b ≠ 0) :
    (Rat.divInt a b).num.natAbs = a.natAbs / Nat.gcd a.natAbs b.natAbs := by
  rw [Rat.num_divInt,
    Int.natAbs_ediv_of_dvd (dvd_mul_of_dvd_right (Int.gcd_dvd_right b a) b.sign),
    Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hb, Int.natAbs_natCast, one_mul]
  simp only [Int.gcd, Nat.gcd_comm]

/-- Reduced denominator of `Rat.divInt a b` for `b ≠ 0`. -/
theorem divInt_den (a b : ℤ) (hb : b ≠ 0) :
    (Rat.divInt a b).den = b.natAbs / Nat.gcd a.natAbs b.natAbs := by
  simp [Rat.den_divInt, hb, Int.gcd, Nat.gcd_comm]

/-- Sign bit of `Rat.divInt a b` for `b ≠ 0`. -/
theorem divInt_sign (a b : ℤ) (hb : b ≠ 0) :
    decide ((Rat.divInt a b).num < 0) =
      if a = 0 then false else (decide (a < 0) ^^ decide (b < 0)) := by
  have hs : (Rat.divInt a b).num < 0 ↔ (a : ℚ) / (b : ℚ) < 0 := by
    rw [← Rat.num_neg, Rat.divInt_eq_div]
  simp only [hs]
  by_cases ha : a = 0
  · simp [ha]
  · simp only [ha, ↓reduceIte]
    rcases lt_or_gt_of_ne ha with hna | hpa <;> rcases lt_or_gt_of_ne hb with hnb | hpb
    · have hp : (0 : ℚ) < (a : ℚ) / (b : ℚ) :=
        div_pos_of_neg_of_neg (by exact_mod_cast hna) (by exact_mod_cast hnb)
      simp [hna, hnb, not_lt_of_ge hp.le]
    · have hn : (a : ℚ) / (b : ℚ) < 0 :=
        div_neg_of_neg_of_pos (by exact_mod_cast hna) (by exact_mod_cast hpb)
      simp [hna, not_lt_of_gt hpb, hn]
    · have hn : (a : ℚ) / (b : ℚ) < 0 :=
        div_neg_of_pos_of_neg (by exact_mod_cast hpa) (by exact_mod_cast hnb)
      simp [not_lt_of_gt hpa, hnb, hn]
    · have hp : (0 : ℚ) < (a : ℚ) / (b : ℚ) :=
        div_pos (by exact_mod_cast hpa) (by exact_mod_cast hpb)
      simp [not_lt_of_gt hpa, not_lt_of_gt hpb, not_lt_of_ge hp.le]

/-- Reduced numerator magnitude of `Rat.divInt a b` for arbitrary integers `a, b`. -/
private theorem divInt_num_abs_eq (a b : ℤ) :
    (Rat.divInt a b).num.natAbs =
      if b = 0 then 0 else a.natAbs / Nat.gcd a.natAbs b.natAbs := by
  by_cases hb : b = 0
  · subst hb; simp
  · simp [hb, divInt_num_abs a b hb]

/-- Reduced denominator of `Rat.divInt a b` for arbitrary integers `a, b`. -/
private theorem divInt_den_eq (a b : ℤ) :
    (Rat.divInt a b).den =
      if b = 0 then 1 else b.natAbs / Nat.gcd a.natAbs b.natAbs := by
  by_cases hb : b = 0
  · subst hb; simp
  · simp [hb, divInt_den a b hb]

/-- Sign bit of `Rat.divInt a b` for arbitrary integers `a, b`. -/
private theorem divInt_sign_eq (a b : ℤ) :
    decide ((Rat.divInt a b).num < 0) =
      if a = 0 then false else if b = 0 then false else (decide (a < 0) ^^ decide (b < 0)) := by
  by_cases hb : b = 0
  · subst hb; simp
  · simp only [hb, ↓reduceIte, divInt_sign a b hb]

/-- Explicit expansion of `encodeRat (Rat.divInt a b)` in terms of integer magnitudes and
`Nat.gcd`. -/
theorem encodeRat_divInt (a b : ℤ) :
    encodeRat (Rat.divInt a b) =
      (if a = 0 then false else if b = 0 then false else (decide (a < 0) ^^ decide (b < 0))) ::
        (encodeNat (if b = 0 then 0 else a.natAbs / Nat.gcd a.natAbs b.natAbs) ++
          encodeNat (if b = 0 then 1 else b.natAbs / Nat.gcd a.natAbs b.natAbs)) := by
  simp only [encodeRat, List.cons_append, List.nil_append, divInt_sign_eq,
    divInt_num_abs_eq, divInt_den_eq]

attribute [local irreducible] encodeNat encodeRat

/-- Encoding the reduced rational quotient `Rat.divInt p.1 p.2` of two binary integers is
computable in polynomial time. -/
@[fun_prop, program_certificate]
theorem encodeDivInt_polytime :
    ComputableInPolyTime (fun p : ℤ × ℤ => encodeRat (Rat.divInt p.1 p.2))
      (encPair encIntBin encIntBin) encBits := by
  refine .of_tidy ?_
  have ha0 : ComputableTidilyInPolyTime (fun p : ℤ × ℤ => decide (p.1 = 0))
      (encPair encIntBin encIntBin) encBool :=
    ComputableTidilyInPolyTime.intBin_isZero.comp (ComputableTidilyInPolyTime.fst _ _)
  have hb0 : ComputableTidilyInPolyTime (fun p : ℤ × ℤ => decide (p.2 = 0))
      (encPair encIntBin encIntBin) encBool :=
    ComputableTidilyInPolyTime.intBin_isZero.comp (ComputableTidilyInPolyTime.snd _ _)
  have hxor : ComputableTidilyInPolyTime
      (fun p : ℤ × ℤ => decide (p.1 < 0) ^^ decide (p.2 < 0))
      (encPair encIntBin encIntBin) encBool :=
    ComputableTidilyInPolyTime.bool_xor.comp
      ((ComputableTidilyInPolyTime.intBin_isNeg.comp (ComputableTidilyInPolyTime.fst _ _)).prod
        (ComputableTidilyInPolyTime.intBin_isNeg.comp (ComputableTidilyInPolyTime.snd _ _)))
  have hsign : ComputableTidilyInPolyTime
      (fun p : ℤ × ℤ =>
        if p.1 = 0 then false
        else if p.2 = 0 then false
        else (decide (p.1 < 0) ^^ decide (p.2 < 0)))
      (encPair encIntBin encIntBin) encBool :=
    ha0.ite_decide (.const false) (hb0.ite_decide (.const false) hxor)
  have hnum : ComputableTidilyInPolyTime
      (fun p : ℤ × ℤ => if p.2 = 0 then 0 else p.1.natAbs / Nat.gcd p.1.natAbs p.2.natAbs)
      (encPair encIntBin encIntBin) encNat :=
    hb0.ite_decide (.const 0) (by fun_prop)
  have hden : ComputableTidilyInPolyTime
      (fun p : ℤ × ℤ => if p.2 = 0 then 1 else p.2.natAbs / Nat.gcd p.1.natAbs p.2.natAbs)
      (encPair encIntBin encIntBin) encNat :=
    hb0.ite_decide (.const 1) (by fun_prop)
  have h := hsign.bitsCons
    ((encodeNat_polytime.tidy.comp hnum).bitsAppend (encodeNat_polytime.tidy.comp hden))
  exact h.of_enc_eq fun p => congrArg encBits (encodeRat_divInt p.1 p.2)

/-- Encode the reduced rational quotient of two computed binary integers. -/
@[fun_prop, program_certificate]
theorem encodeDivInt_polytime' {α : Type} {input : α ↪ List Bool} {num den : α → ℤ}
    (hnum : ComputableInPolyTime num input encIntBin)
    (hden : ComputableInPolyTime den input encIntBin) :
    ComputableInPolyTime (fun a => encodeRat (Rat.divInt (num a) (den a))) input encBits :=
  encodeDivInt_polytime.comp (hnum.prod hden)

end Cslib.Circuits.Rational
