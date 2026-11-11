/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.Rat.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Lemmas

/-!
# Polynomial-time primitives and arithmetic on rational numbers

Polynomial-time certificates for `Turing.MultiTapeTM.encRat`: extracting the signed binary
numerator and binary denominator, casting integers, constructing normalized quotients
`Rat.divInt`, arithmetic (`-`, `⁻¹`, `+`, `-`, `*`, `/`), and zero/order comparisons.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.rat_pair`: projecting `q : ℚ` to `(q.num, q.den)`.
* `Turing.MultiTapeTM.ComputableInPolyTime.rat_num`, `.rat_den`: extracting numerator/denominator.
* `Turing.MultiTapeTM.ComputableInPolyTime.rat_intCast`: casting `ℤ → ℚ`.
* `Turing.MultiTapeTM.ComputableInPolyTime.rat_divInt`, `.rat_divInt'`: normalized quotient.
* `Turing.MultiTapeTM.ComputableInPolyTime.rat_neg`, `.rat_inv`, `.rat_add`, `.rat_sub`,
  `.rat_mul`, `.rat_div` and primed composition rules: rational field operations.
* `Turing.MultiTapeTM.ComputableInPolyTime.rat_isZero`, `.rat_eq`, `.rat_le`, `.rat_lt` and primed
  composition rules: rational zero, equality, and order tests.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Projecting a rational number `q` to its numerator-denominator pair `(q.num, q.den)` is
computable in polynomial time under `encRat` and `encRatData`. -/
theorem rat_pair :
    ComputableInPolyTime (fun q : ℚ => (q.num, q.den)) encRat encRatData :=
  (ComputableTidilyInPolyTime.of_eq (f := fun q : ℚ => (q.num, q.den))
    (encIn := encRat) (encMid := encRatData) fun _ => rfl).computableInPolyTime

/-- Extracting the binary numerator `q.num` from `encRat q` is computable in polynomial time. -/
@[fun_prop]
theorem rat_num : ComputableInPolyTime Rat.num encRat encIntBin :=
  rat_pair.fst'

/-- Extracting the binary denominator `q.den` from `encRat q` is computable in polynomial time. -/
@[fun_prop]
theorem rat_den : ComputableInPolyTime Rat.den encRat encNat :=
  rat_pair.snd'

/-- Casting a binary integer `z : ℤ` to `(z : ℚ)` is computable in polynomial time under
`encIntBin` and `encRat`. -/
@[fun_prop]
theorem rat_intCast :
    ComputableInPolyTime (fun z : ℤ => (z : ℚ)) encIntBin encRat := by
  have h : ComputableInPolyTime (fun z : ℤ => (z, (1 : ℕ))) encIntBin encRatData := by
    fun_prop
  exact h.of_enc_eq fun z => by
    change encPair encIntBin encNat ((z : ℚ).num, (z : ℚ).den) =
      encPair encIntBin encNat (z, 1)
    rw [Rat.num_intCast, Rat.den_intCast]

private theorem int_eq_signMagnitude_self (z : ℤ) :
    z = if decide (z < 0) then -(z.natAbs : ℤ) else (z.natAbs : ℤ) := by
  split_ifs <;> lia

attribute [local irreducible] encRat encIntBin encNat

/-- Forming the normalized rational quotient `Rat.divInt p.1 p.2` from signed binary integers is
computable in polynomial time under `encRat`. -/
@[fun_prop]
theorem rat_divInt :
    ComputableInPolyTime (fun p : ℤ × ℤ => Rat.divInt p.1 p.2)
      (encPair encIntBin encIntBin) encRat := by
  have ha0 : ComputableInPolyTime (fun p : ℤ × ℤ => decide (p.1 = 0))
      (encPair encIntBin encIntBin) encBool :=
    intBin_isZero.comp (fst encIntBin encIntBin)
  have hb0 : ComputableInPolyTime (fun p : ℤ × ℤ => decide (p.2 = 0))
      (encPair encIntBin encIntBin) encBool :=
    intBin_isZero.comp (snd encIntBin encIntBin)
  have hs : ComputableInPolyTime
      (fun p : ℤ × ℤ =>
        if p.1 = 0 then false else if p.2 = 0 then false
        else (decide (p.1 < 0) ^^ decide (p.2 < 0)))
      (encPair encIntBin encIntBin) encBool :=
    ha0.ite_decide (.const false)
      (hb0.ite_decide (.const false)
        (bool_xor.comp ((intBin_isNeg.comp (fst encIntBin encIntBin)).prod
          (intBin_isNeg.comp (snd encIntBin encIntBin)))))
  have hg : ComputableInPolyTime
      (fun p : ℤ × ℤ => Nat.gcd p.1.natAbs p.2.natAbs)
      (encPair encIntBin encIntBin) encNat :=
    binary_gcd' (intBin_natAbs.comp (fst encIntBin encIntBin))
      (intBin_natAbs.comp (snd encIntBin encIntBin))
  have hm : ComputableInPolyTime
      (fun p : ℤ × ℤ => if p.2 = 0 then 0 else p.1.natAbs / Nat.gcd p.1.natAbs p.2.natAbs)
      (encPair encIntBin encIntBin) encNat :=
    hb0.ite_decide (.const 0)
      (binary_div' (intBin_natAbs.comp (fst encIntBin encIntBin)) hg)
  have hnum : ComputableInPolyTime
      (fun p : ℤ × ℤ =>
        if (if p.1 = 0 then false else if p.2 = 0 then false
            else (decide (p.1 < 0) ^^ decide (p.2 < 0)))
        then -((if p.2 = 0 then 0 else p.1.natAbs / Nat.gcd p.1.natAbs p.2.natAbs : ℕ) : ℤ)
        else ((if p.2 = 0 then 0 else p.1.natAbs / Nat.gcd p.1.natAbs p.2.natAbs : ℕ) : ℤ))
      (encPair encIntBin encIntBin) encIntBin :=
    intBin_signMagnitude.comp (hs.prod hm)
  have hden : ComputableInPolyTime
      (fun p : ℤ × ℤ => if p.2 = 0 then 1 else p.2.natAbs / Nat.gcd p.1.natAbs p.2.natAbs)
      (encPair encIntBin encIntBin) encNat :=
    hb0.ite_decide (.const 1)
      (binary_div' (intBin_natAbs.comp (snd encIntBin encIntBin)) hg)
  have henc : ∀ p : ℤ × ℤ,
      encRat (Rat.divInt p.1 p.2) =
        encRatData
          (if (if p.1 = 0 then false else if p.2 = 0 then false
              else (decide (p.1 < 0) ^^ decide (p.2 < 0)))
          then -((if p.2 = 0 then 0 else p.1.natAbs / Nat.gcd p.1.natAbs p.2.natAbs : ℕ) : ℤ)
          else ((if p.2 = 0 then 0 else p.1.natAbs / Nat.gcd p.1.natAbs p.2.natAbs : ℕ) : ℤ),
          if p.2 = 0 then 1 else p.2.natAbs / Nat.gcd p.1.natAbs p.2.natAbs) := fun p => by
    rw [encRat_apply]
    refine congrArg encRatData (Prod.ext ?_ ?_)
    · rw [int_eq_signMagnitude_self (Rat.divInt p.1 p.2).num, Rat.decide_num_divInt_lt_zero,
        Rat.natAbs_num_divInt]
    · rw [Rat.den_divInt, Int.gcd, Nat.gcd_comm]
  exact (hnum.prod hden).of_enc_eq henc

/-- Normalized quotient `Rat.divInt` of computed binary integers. -/
@[fun_prop]
theorem rat_divInt' {α : Type} {input : α ↪ List Bool} {num den : α → ℤ}
    (hnum : ComputableInPolyTime num input encIntBin)
    (hden : ComputableInPolyTime den input encIntBin) :
    ComputableInPolyTime (fun x => Rat.divInt (num x) (den x)) input encRat :=
  rat_divInt.comp (hnum.prod hden)

/-- Negation on `ℚ` is computable in polynomial time. -/
@[fun_prop]
theorem rat_neg : ComputableInPolyTime (fun q : ℚ => -q) encRat encRat := by
  have h : ComputableInPolyTime (fun q : ℚ => (-q.num, q.den)) encRat encRatData :=
    (intBin_neg.comp rat_num).prod rat_den
  exact h.of_enc_eq fun q => by
    rw [encRat_apply]
    exact congrArg encRatData <| Prod.ext (Rat.num_neg_eq_neg_num q) (Rat.den_neg_eq_den q)

/-- Negation of a computed rational number. -/
@[fun_prop]
theorem rat_neg' {α : Type} {input : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun x => -f x) input encRat :=
  rat_neg.comp hf

/-- Multiplicative inverse on `ℚ` is computable in polynomial time. -/
@[fun_prop]
theorem rat_inv : ComputableInPolyTime (fun q : ℚ => q⁻¹) encRat encRat := by
  have h : ComputableInPolyTime (fun q : ℚ => Rat.divInt (q.den : ℤ) q.num) encRat encRat :=
    rat_divInt' (intBin_natCast.comp rat_den) rat_num
  exact h.of_enc_eq fun q => congrArg encRat (Rat.inv_def q)

/-- Multiplicative inverse of a computed rational number. -/
@[fun_prop]
theorem rat_inv' {α : Type} {input : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun x => (f x)⁻¹) input encRat :=
  rat_inv.comp hf

private theorem rat_fst_num :
    ComputableInPolyTime (fun p : ℚ × ℚ => p.1.num) (encPair encRat encRat) encIntBin :=
  rat_num.comp (fst encRat encRat)

private theorem rat_snd_num :
    ComputableInPolyTime (fun p : ℚ × ℚ => p.2.num) (encPair encRat encRat) encIntBin :=
  rat_num.comp (snd encRat encRat)

private theorem rat_fst_denInt :
    ComputableInPolyTime (fun p : ℚ × ℚ => (p.1.den : ℤ)) (encPair encRat encRat) encIntBin :=
  intBin_natCast.comp (rat_den.comp (fst encRat encRat))

private theorem rat_snd_denInt :
    ComputableInPolyTime (fun p : ℚ × ℚ => (p.2.den : ℤ)) (encPair encRat encRat) encIntBin :=
  intBin_natCast.comp (rat_den.comp (snd encRat encRat))

private theorem rat_mul_dens :
    ComputableInPolyTime (fun p : ℚ × ℚ => ((p.1.den * p.2.den : ℕ) : ℤ))
      (encPair encRat encRat) encIntBin :=
  intBin_natCast.comp (binary_mul' (rat_den.comp (fst encRat encRat))
    (rat_den.comp (snd encRat encRat)))

/-- Addition on `ℚ` is computable in polynomial time. -/
@[fun_prop]
theorem rat_add :
    ComputableInPolyTime (fun p : ℚ × ℚ => p.1 + p.2) (encPair encRat encRat) encRat := by
  have h : ComputableInPolyTime
      (fun p : ℚ × ℚ =>
        Rat.divInt (p.1.num * (p.2.den : ℤ) + p.2.num * (p.1.den : ℤ))
          ((p.1.den * p.2.den : ℕ) : ℤ))
      (encPair encRat encRat) encRat :=
    rat_divInt'
      (intBin_add' (intBin_mul' rat_fst_num rat_snd_denInt)
        (intBin_mul' rat_snd_num rat_fst_denInt))
      rat_mul_dens
  exact h.of_enc_eq fun p => congrArg encRat (by rw [Rat.add_def', Rat.mkRat_eq_divInt])

/-- Addition of computed rational numbers. -/
@[fun_prop]
theorem rat_add' {α : Type} {input : α ↪ List Bool} {left right : α → ℚ}
    (hleft : ComputableInPolyTime left input encRat)
    (hright : ComputableInPolyTime right input encRat) :
    ComputableInPolyTime (fun x => left x + right x) input encRat :=
  rat_add.comp (hleft.prod hright)

/-- Subtraction on `ℚ` is computable in polynomial time. -/
@[fun_prop]
theorem rat_sub :
    ComputableInPolyTime (fun p : ℚ × ℚ => p.1 - p.2) (encPair encRat encRat) encRat := by
  have h : ComputableInPolyTime
      (fun p : ℚ × ℚ =>
        Rat.divInt (p.1.num * (p.2.den : ℤ) - p.2.num * (p.1.den : ℤ))
          ((p.1.den * p.2.den : ℕ) : ℤ))
      (encPair encRat encRat) encRat :=
    rat_divInt'
      (intBin_sub' (intBin_mul' rat_fst_num rat_snd_denInt)
        (intBin_mul' rat_snd_num rat_fst_denInt))
      rat_mul_dens
  exact h.of_enc_eq fun p => congrArg encRat (by rw [Rat.sub_def', Rat.mkRat_eq_divInt])

/-- Subtraction of computed rational numbers. -/
@[fun_prop]
theorem rat_sub' {α : Type} {input : α ↪ List Bool} {left right : α → ℚ}
    (hleft : ComputableInPolyTime left input encRat)
    (hright : ComputableInPolyTime right input encRat) :
    ComputableInPolyTime (fun x => left x - right x) input encRat :=
  rat_sub.comp (hleft.prod hright)

/-- Multiplication on `ℚ` is computable in polynomial time. -/
@[fun_prop]
theorem rat_mul :
    ComputableInPolyTime (fun p : ℚ × ℚ => p.1 * p.2) (encPair encRat encRat) encRat := by
  have h : ComputableInPolyTime
      (fun p : ℚ × ℚ =>
        Rat.divInt (p.1.num * p.2.num) ((p.1.den * p.2.den : ℕ) : ℤ))
      (encPair encRat encRat) encRat :=
    rat_divInt' (intBin_mul' rat_fst_num rat_snd_num) rat_mul_dens
  exact h.of_enc_eq fun p => congrArg encRat (by rw [Rat.mul_def', Rat.mkRat_eq_divInt])

/-- Multiplication of computed rational numbers. -/
@[fun_prop]
theorem rat_mul' {α : Type} {input : α ↪ List Bool} {left right : α → ℚ}
    (hleft : ComputableInPolyTime left input encRat)
    (hright : ComputableInPolyTime right input encRat) :
    ComputableInPolyTime (fun x => left x * right x) input encRat :=
  rat_mul.comp (hleft.prod hright)

/-- Division on `ℚ` is computable in polynomial time. -/
@[fun_prop]
theorem rat_div :
    ComputableInPolyTime (fun p : ℚ × ℚ => p.1 / p.2) (encPair encRat encRat) encRat := by
  have h : ComputableInPolyTime
      (fun p : ℚ × ℚ =>
        Rat.divInt (p.1.num * (p.2.den : ℤ)) ((p.1.den : ℤ) * p.2.num))
      (encPair encRat encRat) encRat :=
    rat_divInt' (intBin_mul' rat_fst_num rat_snd_denInt)
      (intBin_mul' rat_fst_denInt rat_snd_num)
  exact h.of_enc_eq fun p => congrArg encRat (Rat.div_def' p.1 p.2)

/-- Division of computed rational numbers. -/
@[fun_prop]
theorem rat_div' {α : Type} {input : α ↪ List Bool} {left right : α → ℚ}
    (hleft : ComputableInPolyTime left input encRat)
    (hright : ComputableInPolyTime right input encRat) :
    ComputableInPolyTime (fun x => left x / right x) input encRat :=
  rat_div.comp (hleft.prod hright)

/-- Zero test on `ℚ` is computable in polynomial time. -/
@[fun_prop]
theorem rat_isZero :
    ComputableInPolyTime (fun q : ℚ => decide (q = 0)) encRat encBool :=
  (intBin_isZero.comp rat_num).of_enc_eq fun _ =>
    congrArg encBool (decide_eq_decide.2 Rat.num_eq_zero.symm)

/-- Zero test on a computed rational number. -/
@[fun_prop]
theorem rat_isZero' {α : Type} {input : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun x => decide (f x = 0)) input encBool :=
  rat_isZero.comp hf

/-- Strict order comparison (`<`) on `ℚ` is computable in polynomial time. -/
@[fun_prop]
theorem rat_lt :
    ComputableInPolyTime (fun p : ℚ × ℚ => decide (p.1 < p.2)) (encPair encRat encRat) encBool := by
  have h : ComputableInPolyTime
      (fun p : ℚ × ℚ => decide (p.1.num * (p.2.den : ℤ) < p.2.num * (p.1.den : ℤ)))
      (encPair encRat encRat) encBool :=
    intBin_lt' (intBin_mul' rat_fst_num rat_snd_denInt) (intBin_mul' rat_snd_num rat_fst_denInt)
  exact h.of_enc_eq fun p => congrArg encBool <| Bool.eq_iff_iff.2 (by
    simp only [decide_eq_true_eq]
    exact Rat.lt_iff p.1 p.2)

/-- Strict order comparison on computed rational numbers. -/
@[fun_prop]
theorem rat_lt' {α : Type} {input : α ↪ List Bool} {left right : α → ℚ}
    (hleft : ComputableInPolyTime left input encRat)
    (hright : ComputableInPolyTime right input encRat) :
    ComputableInPolyTime (fun x => decide (left x < right x)) input encBool :=
  rat_lt.comp (hleft.prod hright)

/-- Non-strict order comparison (`≤`) on `ℚ` is computable in polynomial time. -/
@[fun_prop]
theorem rat_le :
    ComputableInPolyTime (fun p : ℚ × ℚ => decide (p.1 ≤ p.2)) (encPair encRat encRat) encBool := by
  have h : ComputableInPolyTime
      (fun p : ℚ × ℚ => !decide (p.2 < p.1)) (encPair encRat encRat) encBool :=
    bool_not.comp (rat_lt.comp ((snd encRat encRat).prod (fst encRat encRat)))
  exact h.of_enc_eq fun p => congrArg encBool (by
    simp only [← decide_not, not_lt])

/-- Non-strict order comparison on computed rational numbers. -/
@[fun_prop]
theorem rat_le' {α : Type} {input : α ↪ List Bool} {left right : α → ℚ}
    (hleft : ComputableInPolyTime left input encRat)
    (hright : ComputableInPolyTime right input encRat) :
    ComputableInPolyTime (fun x => decide (left x ≤ right x)) input encBool :=
  (bool_not.comp (rat_lt' hright hleft)).of_enc_eq fun _ =>
    congrArg encBool <| Bool.eq_iff_iff.2 (by
      simp only [Function.comp_apply, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq]
      exact not_lt.symm)

/-- Equality test on `ℚ` is computable in polynomial time. -/
@[fun_prop]
theorem rat_eq :
    ComputableInPolyTime (fun p : ℚ × ℚ => decide (p.1 = p.2)) (encPair encRat encRat) encBool := by
  have h : ComputableInPolyTime
      (fun p : ℚ × ℚ => decide (p.1 ≤ p.2) && decide (p.2 ≤ p.1))
      (encPair encRat encRat) encBool :=
    bool_and' rat_le (rat_le' (snd encRat encRat) (fst encRat encRat))
  exact h.of_enc_eq fun p => congrArg encBool <| Bool.eq_iff_iff.2 (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact le_antisymm_iff)

/-- Equality test on computed rational numbers. -/
@[fun_prop]
theorem rat_eq' {α : Type} {input : α ↪ List Bool} {left right : α → ℚ}
    (hleft : ComputableInPolyTime left input encRat)
    (hright : ComputableInPolyTime right input encRat) :
    ComputableInPolyTime (fun x => decide (left x = right x)) input encBool :=
  rat_eq.comp (hleft.prod hright)

end Turing.MultiTapeTM.ComputableInPolyTime
