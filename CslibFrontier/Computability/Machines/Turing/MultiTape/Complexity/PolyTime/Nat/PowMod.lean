/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Tactic.PolyTime.Init
import Mathlib.Data.ZMod.Basic

/-!
# Polynomial-time modular exponentiation

Square-and-multiply computes `a ^ e % m` on binary naturals with a positive modulus. It folds over
the exponent's binary digits from the most significant one, squaring the accumulator and
multiplying by `a` at each `1` digit, reducing modulo `m` after every product. Every intermediate
value is below `m`, so the work is polynomial in the lengths of `a`, `e` and `m`.

Without a modulus, `a ^ e` has about `e` times as many digits as `a`, exponentially many in the
length of `e`; the statement therefore requires a positive modulus. The total function `powMod`
returns `1` at the modulus `0` instead, so it is polynomial-time on every input. This is where it
differs from core's `Nat.powMod`, which returns the unreduced power at the modulus `0`.

## Main definitions

* `Turing.MultiTapeTM.powMod`: modular exponentiation, returning `1` at the modulus `0`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.binary_powMod`: modular exponentiation of computed
  binary values with a positive modulus.
* `Turing.MultiTapeTM.computableInPolyTime_powMod`: `powMod` of computed binary values, with no
  condition on the modulus.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Turing.MultiTapeTM

namespace BinaryPowMod

/-- One square-and-multiply step modulo `m` for the base `a`: square the accumulator, and
multiply by `a` when the next exponent digit, most significant first, is `1`. -/
private def step (par : ℕ × ℕ) (acc : ℕ) (bit : Bool) : ℕ :=
  acc * acc % par.2 * (if bit then par.1 else 1) % par.2

/-- Folding `step` over a most-significant-first word computes the power of its value. -/
private theorem foldl_step (a m : ℕ) (word : List Bool) :
    word.foldl (step (a, m)) (1 % m) = a ^ Cslib.BitString.binaryValue word % m := by
  induction word using List.reverseRecOn with
  | nil => simp [Cslib.BitString.binaryValue]
  | append_singleton word bit ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Cslib.BitString.binaryValue_snoc, step, ← ZMod.natCast_eq_natCast_iff']
    cases bit <;> simp only [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_pow, Bool.toNat_false,
      Bool.toNat_true, Bool.false_eq_true, ite_false, ite_true, pow_add, pow_mul, add_zero, pow_one,
      mul_one] <;> ring

/-- The exponent's digits, most significant first, give `a ^ e % m`. -/
private theorem powMod_eq (a e m : ℕ) :
    e.bits.reverse.foldl (step (a, m)) (1 % m) = a ^ e % m := by
  rw [foldl_step, Cslib.BitString.binaryValue_reverse_bits]

/-- Modular exponentiation with the modulus `m + 1`, which is positive. -/
private theorem computableTidilyInPolyTime_powMod_succ :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ => p.1 ^ p.2.1 % (p.2.2 + 1))
      (encPair encNat (encPair encNat encNat)) encNat := by
  have hpar : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ => (p.1, p.2.2 + 1))
      (encPair encNat (encPair encNat encNat)) (encPair encNat encNat) := by
    fun_prop
  have hlist : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ => p.2.1.bits.reverse)
      (encPair encNat (encPair encNat encNat)) encBits := by
    fun_prop
  have hinit : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ => 1 % (p.2.2 + 1))
      (encPair encNat (encPair encNat encNat)) encNat := by
    fun_prop
  have hstep : ComputableTidilyInPolyTime
      (fun q : ((ℕ × ℕ) × ℕ) × Bool => step q.1.1 q.1.2 q.2)
      (encPair (encPair (encPair encNat encNat) encNat) encBool) encNat := by
    unfold step
    fun_prop
  have hfold := ComputableTidilyInPolyTime.foldlWith (encP := encPair encNat encNat)
    (encA := encBool) (encL := encBits) (encB := encNat) hpar hlist hinit hstep
    (B := fun p => (encPair encNat (encPair encNat encNat) p).length)
    (PolyBounded.self)
    (fun p i _ => by
      rw [foldl_step]
      have hle : p.1 ^ Cslib.BitString.binaryValue (p.2.1.bits.reverse.take i) % (p.2.2 + 1) ≤
          p.2.2 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (Nat.succ_pos _))
      calc (encNat _).length ≤ (encNat p.2.2).length := by
            simp only [encNat_apply]
            rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
            exact Nat.size_le_size hle
        _ ≤ (encPair encNat encNat p.2).length := length_le_encPair_right encNat encNat p.2
        _ ≤ (encPair encNat (encPair encNat encNat) p).length :=
          length_le_encPair_right encNat (encPair encNat encNat) p)
  simpa only [powMod_eq] using hfold

end BinaryPowMod

/-- **Modular exponentiation** of computed binary values with a positive modulus, by
square-and-multiply. -/
theorem ComputableInPolyTime.binary_powMod {α : Type} {input : α ↪ List Bool}
    {base exponent modulus : α → ℕ} (hbase : ComputableInPolyTime base input encNat)
    (hexponent : ComputableInPolyTime exponent input encNat)
    (hmodulus : ComputableInPolyTime modulus input encNat) (hpos : ∀ a, 0 < modulus a) :
    ComputableInPolyTime (fun a => base a ^ exponent a % modulus a) input encNat := by
  have hpred : ComputableTidilyInPolyTime (fun a => modulus a - 1) input encNat :=
    ComputableTidilyInPolyTime.binary_sub' hmodulus.tidy (ComputableTidilyInPolyTime.const 1)
  have hcomp := BinaryPowMod.computableTidilyInPolyTime_powMod_succ.comp
    (hbase.tidy.prod (hexponent.tidy.prod hpred))
  refine ComputableInPolyTime.of_tidy ?_
  simpa only [Function.comp_def, Nat.sub_add_cancel (hpos _)] using hcomp

/-! ### Total modular exponentiation -/

/-- Modular exponentiation `x ^ e mod M`. For the degenerate modulus `M = 0` it returns `1`
instead of the unreduced power, so that it is computable in polynomial time on every input. -/
@[expose] def powMod (M x e : ℕ) : ℕ := if M = 0 then 1 else x ^ e % M

theorem powMod_of_ne_zero {M : ℕ} (hM : M ≠ 0) (x e : ℕ) : powMod M x e = x ^ e % M := by
  simp [powMod, hM]

/-- `powMod` is computable in polynomial time. -/
theorem computableInPolyTime_powMod {α : Type} {input : α ↪ List Bool} {M x e : α → ℕ}
    (hM : ComputableInPolyTime M input encNat) (hx : ComputableInPolyTime x input encNat)
    (he : ComputableInPolyTime e input encNat) :
    ComputableInPolyTime (fun a => powMod (M a) (x a) (e a)) input encNat := by
  have hpow := ComputableInPolyTime.binary_powMod hx he
    (ComputableInPolyTime.binary_add'
      (ComputableInPolyTime.binary_sub' hM (ComputableInPolyTime.const 1))
      (ComputableInPolyTime.const 1)) fun _ => Nat.succ_pos _
  have h := ComputableInPolyTime.ite_decide (condition := fun a => M a = 0)
    (ComputableInPolyTime.decide_eq' hM (ComputableInPolyTime.const 0))
    (ComputableInPolyTime.const 1) hpow
  have heq : (fun a => powMod (M a) (x a) (e a)) =
      fun a => if M a = 0 then 1 else x a ^ e a % (M a - 1 + 1) := by
    funext a
    unfold powMod
    split_ifs with h0
    · rfl
    · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h0)]
  rw [heq]
  exact h

end Turing.MultiTapeTM

end
