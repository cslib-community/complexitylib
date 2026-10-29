/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time reduction of signed binary integers

Reduce a signed binary integer modulo a binary natural and return the nonnegative residue.
The construction first computes `r = z.natAbs % q`. For a negative integer it returns
`(q - r) % q`; otherwise it returns `r`. This reuses binary natural division, subtraction
and the sign-magnitude interface, without enumerating the modulus or constructing a new machine.

The certificate is total: at modulus zero the result is `z.toNat`, matching Lean's integer
remainder convention followed by truncation at zero.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.intBin_emodNat`: signed reduction with both
  operands and the result encoded in binary.
* `Turing.MultiTapeTM.ComputableInPolyTime.intBin_emodNat'`: composition with computed inputs.

## References

The proof uses Lean's `Int.emod_natAbs_of_nonneg` and `Int.emod_natAbs_of_neg` and the native
arithmetic certificates in `PolyTime/Int/Binary` and `PolyTime/Nat/BinaryDiv`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

private theorem emodNat_eq (z : ℤ) (q : ℕ) :
    (z % (q : ℤ)).toNat =
      if z < 0 then (q - z.natAbs % q) % q else z.natAbs % q := by
  by_cases hz : z < 0
  · rw [ite_eq_left hz]
    by_cases hq : q = 0
    · subst q
      simp only [Nat.cast_zero, Int.emod_zero, Nat.zero_sub, Nat.mod_zero]
      omega
    · rw [Int.emod_natAbs_of_neg hz hq]
      split_ifs with hdiv
      · simp [Int.emod_eq_zero_of_dvd hdiv]
      · have hrem : (z % (q : ℤ)).toNat < q := by
          have := Int.emod_lt_of_pos z (by omega : 0 < (q : ℤ))
          omega
        rw [Nat.sub_sub_self hrem.le, Nat.mod_eq_of_lt hrem]
  · rw [ite_eq_right hz]
    exact (Int.emod_natAbs_of_nonneg (by omega : 0 ≤ z)).symm

/-- Reduce a signed binary integer modulo a binary natural. At modulus zero the result is
the integer truncated at zero; no positive-modulus hypothesis is required. -/
@[fun_prop, program_certificate]
theorem intBin_emodNat :
    ComputableInPolyTime (fun p : ℤ × ℕ => (p.1 % (p.2 : ℤ)).toNat)
      (encPair encIntBin encNat) encNat := by
  refine .of_tidy ?_
  have hsign := ComputableTidilyInPolyTime.intBin_isNeg.comp
    (ComputableTidilyInPolyTime.fst encIntBin encNat)
  have hmodulus := ComputableTidilyInPolyTime.snd encIntBin encNat
  have hremainder := ComputableTidilyInPolyTime.binary_mod.comp
    ((ComputableTidilyInPolyTime.intBin_natAbs.comp
      (ComputableTidilyInPolyTime.fst encIntBin encNat)).prod hmodulus)
  have h := hsign.ite'
    (ComputableTidilyInPolyTime.binary_mod.comp
      ((ComputableTidilyInPolyTime.binary_sub.comp (hmodulus.prod hremainder)).prod hmodulus))
    hremainder
  refine h.of_enc_eq fun p => congrArg encNat ?_
  simpa only [Function.comp_apply, decide_eq_true_eq] using emodNat_eq p.1 p.2

/-- Reduce computed signed integers by computed binary natural moduli, fixing the intermediate
encodings for proof search. -/
@[fun_prop, program_certificate]
theorem intBin_emodNat' {α : Type} {input : α ↪ List Bool} {value : α → ℤ} {modulus : α → ℕ}
    (hvalue : ComputableInPolyTime value input encIntBin)
    (hmodulus : ComputableInPolyTime modulus input encNat) :
    ComputableInPolyTime (fun a => (value a % (modulus a : ℤ)).toNat) input encNat :=
  intBin_emodNat.comp (hvalue.prod hmodulus)

end Turing.MultiTapeTM.ComputableInPolyTime
