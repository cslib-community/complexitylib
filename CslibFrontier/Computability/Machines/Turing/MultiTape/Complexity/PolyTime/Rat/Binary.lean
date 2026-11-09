/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.RatBinary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.PolyTime
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic

/-!
# Native polynomial-time binary rational arithmetic

Rationals use the canonical framed signed numerator/positive denominator encoding
`encRatBin`. Normalization computes Euclid's gcd and binary quotients, rather than
calling a unit-cost rational primitive. The certificates use actual multitape
machines through the existing plain polynomial-time calculus.

## Main results

* `ratBin_mkRat`: normalization of an arbitrary signed numerator and natural denominator.
* `ratBin_add`, `ratBin_mul`, `ratBin_sub`: exact normalized arithmetic.
* `ratBin_le`, `ratBin_lt`: exact binary rational comparison.
* `ratBin_sum`, `ratBin_prod`: runtime list folds with normalization and all list work charged.
-/

public section
namespace Turing.MultiTapeTM.ComputableInPolyTime

private def normalizePair (p : ℤ × ℕ) : ℤ × ℕ :=
  if p.2 = 0 then (0,1) else
    (p.1.sign * (p.1.natAbs / p.1.natAbs.gcd p.2 : ℕ),
      p.2 / p.1.natAbs.gcd p.2)

private theorem normalizePair_eq (n : ℤ) (d : ℕ) :
    normalizePair (n,d) = ((mkRat n d).num,(mkRat n d).den) := by
  by_cases hd : d = 0
  · simp [normalizePair, hd]
  · simp only [normalizePair, hd, ite_false]
    rw [← Rat.normalize_eq_mkRat hd]
    rw [Rat.num_normalize, Rat.den_normalize]
    congr 1
    have hg : (n.natAbs.gcd d : ℤ) ∣ (n.natAbs : ℤ) :=
      Int.ofNat_dvd.mpr (Nat.gcd_dvd_left ..)
    calc
      n.sign * (n.natAbs / n.natAbs.gcd d : ℕ) =
          n.sign * ((n.natAbs : ℤ) / (n.natAbs.gcd d : ℤ)) := by simp
      _ = (n.sign * (n.natAbs : ℤ)) / (n.natAbs.gcd d : ℤ) :=
        (Int.mul_ediv_assoc n.sign hg).symm
      _ = n / (n.natAbs.gcd d : ℤ) := by rw [Int.sign_mul_natAbs]

/-- The input word already is the framed canonical numerator/denominator pair. -/
@[fun_prop, program_certificate]
theorem ratBin_num_den : ComputableInPolyTime (fun q : ℚ => (q.num,q.den))
    encRatBin (encPair encIntBin encNat) := .of_eq fun _ => rfl

/-- Extract a signed numerator from a binary rational. -/
@[fun_prop, program_certificate]
theorem ratBin_num : ComputableInPolyTime Rat.num encRatBin encIntBin :=
  ratBin_num_den.fst'

/-- Extract a positive denominator from a binary rational. -/
@[fun_prop, program_certificate]
theorem ratBin_den : ComputableInPolyTime Rat.den encRatBin encNat :=
  ratBin_num_den.snd'

/-- Normalize arbitrary binary operands using binary gcd and division. A zero
denominator returns zero, agreeing with `mkRat`; no magnitude bound is assumed. -/
@[fun_prop, program_certificate]
theorem ratBin_mkRat : ComputableInPolyTime (fun p : ℤ × ℕ => mkRat p.1 p.2)
    (encPair encIntBin encNat) encRatBin := by
  have hn : ComputableInPolyTime normalizePair (encPair encIntBin encNat)
      (encPair encIntBin encNat) := by
    unfold normalizePair
    fun_prop (config := { maxSteps := 64 })
  refine of_tidy (hn.tidy.of_enc_eq ?_)
  intro p
  change encPair encIntBin encNat ((mkRat p.1 p.2).num,(mkRat p.1 p.2).den) = _
  rw [normalizePair_eq]

/-- Addition, including gcd normalization, on canonical binary rationals. -/
@[fun_prop, program_certificate]
theorem ratBin_add : ComputableInPolyTime (fun p : ℚ × ℚ => p.1 + p.2)
    (encPair encRatBin encRatBin) encRatBin := by
  have h : ComputableInPolyTime (fun p : ℚ × ℚ =>
      mkRat (p.1.num * p.2.den + p.2.num * p.1.den) (p.1.den * p.2.den))
      (encPair encRatBin encRatBin) encRatBin := by fun_prop
  simpa only [← Rat.add_def'] using h

/-- Multiplication, including gcd normalization, on canonical binary rationals. -/
@[fun_prop, program_certificate]
theorem ratBin_mul : ComputableInPolyTime (fun p : ℚ × ℚ => p.1 * p.2)
    (encPair encRatBin encRatBin) encRatBin := by
  have h : ComputableInPolyTime (fun p : ℚ × ℚ =>
      mkRat (p.1.num * p.2.num) (p.1.den * p.2.den))
      (encPair encRatBin encRatBin) encRatBin := by fun_prop
  simpa only [← Rat.mul_def'] using h

/-- Negation on canonical binary rationals. -/
@[fun_prop, program_certificate]
theorem ratBin_neg : ComputableInPolyTime Neg.neg encRatBin encRatBin := by
  have h : ComputableInPolyTime (fun q : ℚ => mkRat (-q.num) q.den)
      encRatBin encRatBin := by fun_prop
  convert h using 1
  funext q
  simp only [Rat.mkRat_eq_divInt, Rat.neg_def]

/-- Exact subtraction on canonical binary rationals. -/
@[fun_prop, program_certificate]
theorem ratBin_sub : ComputableInPolyTime (fun p : ℚ × ℚ => p.1 - p.2)
    (encPair encRatBin encRatBin) encRatBin := by
  have h := ratBin_add.comp ((fst encRatBin encRatBin).prod
    (ratBin_neg.comp (snd encRatBin encRatBin)))
  simpa only [Function.comp_def, sub_eq_add_neg] using h

/-- Exact comparison by cross multiplication of binary integers. -/
@[fun_prop, program_certificate]
theorem ratBin_le : ComputableInPolyTime (fun p : ℚ × ℚ => decide (p.1 ≤ p.2))
    (encPair encRatBin encRatBin) encBool := by
  have h : ComputableInPolyTime (fun p : ℚ × ℚ =>
      decide (p.1.num * (p.2.den : ℤ) ≤ p.2.num * (p.1.den : ℤ)))
      (encPair encRatBin encRatBin) encBool := by
    have hl : ComputableInPolyTime (fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ))
        (encPair encRatBin encRatBin) encIntBin := by fun_prop
    have hr : ComputableInPolyTime (fun p : ℚ × ℚ => p.2.num * (p.1.den : ℤ))
        (encPair encRatBin encRatBin) encIntBin := by fun_prop
    exact of_tidy (ComputableTidilyInPolyTime.intBin_le.comp (hl.tidy.prod hr.tidy))
  simpa only [← Rat.le_iff] using h

/-- Inversion on binary rationals; zero is handled by the canonical representation. -/
@[fun_prop, program_certificate]
theorem ratBin_inv : ComputableInPolyTime Inv.inv encRatBin encRatBin := by
  have h : ComputableInPolyTime (fun q : ℚ =>
      (q.num.sign * (q.den : ℤ), if q.num.natAbs = 0 then 1 else q.num.natAbs))
      encRatBin (encPair encIntBin encNat) := by fun_prop
  refine of_tidy (h.tidy.of_enc_eq ?_)
  intro q
  change encPair encIntBin encNat ((q⁻¹).num,(q⁻¹).den) = _
  simp only [Rat.num_inv, Rat.den_inv, Int.natAbs_eq_zero]

/-- Exact division on canonical binary rationals, including zero denominators. -/
@[fun_prop, program_certificate]
theorem ratBin_div : ComputableInPolyTime (fun p : ℚ × ℚ => p.1 / p.2)
    (encPair encRatBin encRatBin) encRatBin := by
  have h := ratBin_mul.comp ((fst encRatBin encRatBin).prod
    (ratBin_inv.comp (snd encRatBin encRatBin)))
  simpa only [Function.comp_def, div_eq_mul_inv] using h

/-- A binary natural represented as a binary rational with denominator one. -/
@[fun_prop, program_certificate]
theorem ratBin_natCast : ComputableInPolyTime (fun n : ℕ => (n : ℚ)) encNat encRatBin := by
  have h := ratBin_mkRat.comp ((intBin_natCast).prod (const 1))
  simpa only [Function.comp_def, Rat.mkRat_eq_divInt, Nat.cast_one, Rat.divInt_one,
    Rat.intCast_natCast] using h

/-- Natural flooring uses exact binary division of the nonnegative numerator
by the positive denominator; negative rationals truncate to zero. -/
@[fun_prop, program_certificate]
theorem ratBin_floor : ComputableInPolyTime Nat.floor encRatBin encNat := by
  have h : ComputableInPolyTime (fun q : ℚ => q.num.toNat / q.den)
      encRatBin encNat := by fun_prop
  convert h using 1
  funext q
  have hq : q = (q.num : ℚ) / q.den := by
    have hh := Rat.divInt_eq_div q.num (q.den : ℤ)
    simpa only [Rat.num_divInt_den, Int.cast_natCast] using hh
  conv_lhs => rw [hq]
  rw [Nat.floor_div_natCast, ← Int.floor_toNat, Int.floor_intCast]

private theorem ratBin_fold (op : ℚ → ℚ → ℚ) (neutral : ℚ)
    (hop : ComputableInPolyTime (Function.uncurry op)
      (encPair encRatBin encRatBin) encRatBin)
    (hwidth : ∀ a b, (op a b).binaryWidth ≤ a.binaryWidth + b.binaryWidth + 1) :
    ComputableInPolyTime (fun xs : List ℚ => xs.foldl op neutral)
      (encList encRatBin) encRatBin := by
  have hf := ComputableTidilyInPolyTime.foldl_spec
    (encA := encRatBin) (encL := encList encRatBin) (encB := encRatBin)
    (list := id) (init := fun _ => neutral) (step := op)
    ComputableTidilyInPolyTime.id' (ComputableTidilyInPolyTime.const neutral) hop.tidy
    (fun _ consumed acc => acc.binaryWidth ≤ neutral.binaryWidth +
      (consumed.map (fun q => q.binaryWidth + 1)).sum)
    (by intro _; simp) (by
      intro xs consumed acc q _ ha
      have hh := hwidth acc q
      simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
      omega)
    (size := fun xs => 3 * (neutral.binaryWidth + 2 * (encList encRatBin xs).length) + 3)
    (by exact ((PolyBounded.const 3).mul ((PolyBounded.const neutral.binaryWidth).add
      ((PolyBounded.const 2).mul .self))).add (.const 3)) ?_
  · exact of_tidy hf.1
  · intro xs consumed acc hp ha
    have hs := List.Sublist.sum_le_sum
      (hp.sublist.map (fun q => q.binaryWidth + 1)) (by intro a _; exact Nat.zero_le a)
    have hw : (xs.map (fun q => q.binaryWidth + 1)).sum ≤
        2 * (encList encRatBin xs).length := by
      have hh := List.sum_le_sum (fun q (_ : q ∈ xs) =>
        Nat.add_le_add_right (binaryWidth_le_length_encRatBin q) 1)
      have hl := sum_length_le_length_encList encRatBin xs
      have hn := SizedListEncoding.length_le (encA := encRatBin)
        (encL := encList encRatBin) xs
      have hconst : (xs.map (fun _ => (1 : ℕ))).sum = xs.length := by simp
      have hadd : (xs.map (fun q => (encRatBin q).length + 1)).sum =
          (xs.map (fun q => (encRatBin q).length)).sum + xs.length := by
        rw [List.sum_map_add, hconst]
      exact hh.trans (by omega)
    simp only [id_eq] at hs
    exact (length_encRatBin_le acc).trans (by omega)

/-- Sum an arbitrary runtime list of binary rationals, charging every traversal,
addition and gcd normalization. Intermediate numerators and denominators have
polynomial length even when the rational magnitudes are exponentially large. -/
@[fun_prop, program_certificate]
theorem ratBin_sum : ComputableInPolyTime (List.sum (α := ℚ))
    (encList encRatBin) encRatBin := by
  have h := ratBin_fold (· + ·) 0 ratBin_add Rat.binaryWidth_add_le
  simpa only [← List.sum_eq_foldl] using h

/-- Multiply an arbitrary runtime list of binary rationals, including zero and
negative factors, with all exact reduction and list work charged. -/
@[fun_prop, program_certificate]
theorem ratBin_prod : ComputableInPolyTime (List.prod (α := ℚ))
    (encList encRatBin) encRatBin := by
  have h := ratBin_fold (· * ·) 1 ratBin_mul
    (fun a b => (Rat.binaryWidth_mul_le a b).trans (Nat.le_succ _))
  simpa only [← List.prod_eq_foldl] using h

/-- Strict comparison on canonical binary rationals. -/
@[fun_prop, program_certificate]
theorem ratBin_lt : ComputableInPolyTime (fun p : ℚ × ℚ => decide (p.1 < p.2))
    (encPair encRatBin encRatBin) encBool := by
  have h := decide_not (ratBin_le.comp ((snd _ _).prod (fst _ _)))
  simpa only [not_le] using h

end Turing.MultiTapeTM.ComputableInPolyTime
