/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Polynomial.CoeffList
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Binary-digit coefficients and natural Horner evaluation in polynomial time

The binary digits of a binary natural can be returned as a framed list of natural coefficients.
Conversely, evaluating a list of arbitrary binary natural coefficients at `2` is polynomial-time:
Horner's step adds at most the coefficient's bit length plus three to the accumulator's length.
These certificates use the ordinary multitape polynomial-time predicate.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.binary_digitCoeffs`: binary-digit coefficients.
* `Turing.MultiTapeTM.ComputableInPolyTime.evalCoeffList_two`: Horner evaluation at `2`.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Return the binary digits of a binary natural as natural coefficients. -/
@[fun_prop] theorem binary_digitCoeffs :
    ComputableInPolyTime (fun n : ℕ => n.bits.map Bool.toNat) encNat (encList encNat) := by
  have hbits : ComputableInPolyTime Nat.bits encNat encBits := of_eq fun _ => rfl
  exact (map (of_finite (encIn := encBool) (encOut := encNat) Bool.toNat)).comp
    (bitsToList.comp hbits)

/-- Evaluate a list of binary natural coefficients at `2` by Horner's rule. -/
@[fun_prop] theorem evalCoeffList_two :
    ComputableInPolyTime (Polynomial.evalCoeffList 2) (encList encNat) encNat := by
  have hq := fst (encPair (encList encNat) encNat) encNat
  have hacc := hq.snd'
  have hval := snd (encPair (encList encNat) encNat) encNat
  have hstep := binary_add.comp (hval.prod
    (binary_mul' (const 2) hacc))
  have h := foldlWith_of_bounded_growth (encA := encNat) (encL := encList encNat)
    (encB := encNat) (par := fun l : List ℕ => l) (list := fun l => l.reverse)
    (step := fun _ acc a => a + 2 * acc) id' (listReverseWithInput id') (const 0) hstep
    (growth := fun l => (encList encNat l).length + 3) (.add .self (.const 3))
    (fun l acc a ha => by
      have hlen := length_le_encList_of_mem encNat (List.mem_reverse.mp ha)
      simp only [encNat_apply, Nat.size_eq_bits_len] at hlen ⊢
      have hadd := Nat.size_add_le a (2 * acc)
      have hmul := Nat.size_mul_le 2 acc
      have htwo : Nat.size 2 = 2 := rfl
      omega)
  change ComputableInPolyTime (fun l : List ℕ => l.foldr (fun a acc => a + 2 * acc) 0)
    (encList encNat) encNat
  simpa only [List.foldl_reverse] using h

end Turing.MultiTapeTM.ComputableInPolyTime
