/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
import Complexity.Computability.Machines.Turing.MultiTape.Universal.Bound
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lengths, comparisons and unary conversion within given bounds

Routines that compute resource bounds from an input, with computability up to constants
(`Turing.MultiTapeTM.ComputableInO`): the length of a bit word in binary, by a binary
counter; the comparison of two unary numbers, by counting down; and the conversion of a number from
binary to unary, by counting up. They are the building blocks of constructible resource bounds and
of the diagonal machines of the hierarchy theorems. The number of binary digits of `m` is
logarithmic in `m`, so every power of it is `O(m + 1)`; this absorbs the binary counters into
bounds linear in the counted value.

## Main results

* `Turing.MultiTapeTM.two_pow_length_encNat_le`: the binary digits of `m` are logarithmic.
* `Turing.MultiTapeTM.exists_pow_length_encNat_le`: every power of the number of binary digits of
  `m` is `O(m + 1)`.
* `Turing.MultiTapeTM.ComputableInO.lengthNat`: the length of a bit word in binary, within
  quadratic time and linear space.
* `Turing.MultiTapeTM.ComputableInO.unaryLe`: the comparison of unary numbers, within
  quadratic time and linear space.
* `Turing.MultiTapeTM.ComputableInO.natToUnary`: from binary to unary, within quadratic time
  and linear space.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- The binary digits of `m` are logarithmic: `2 ^ (encNat m).length ≤ 2 * (m + 1)`. -/
theorem two_pow_length_encNat_le (m : ℕ) : 2 ^ (encNat m).length ≤ 2 * (m + 1) := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h₁ : 2 ^ (m.size - 1) ≤ m := Nat.lt_size.mp (by
      have := Nat.size_pos.mpr hm
      omega)
    have h₂ : 1 ≤ m.size := Nat.size_pos.mpr hm
    rw [show m.size = (m.size - 1) + 1 by omega, pow_succ]
    omega

/-- Every power of the number of binary digits of `m` is `O(m + 1)`. -/
theorem exists_pow_length_encNat_le (d : ℕ) :
    ∃ C, ∀ m, ((encNat m).length + 1) ^ d ≤ C * (m + 1) := by
  obtain ⟨C, hC⟩ := Cslib.PolynomiallyBounded.exists_le_mul_two_pow (p := fun L => (L + 1) ^ d)
    (by fun_prop)
  refine ⟨2 * C, fun m => (hC _).trans ?_⟩
  calc C * 2 ^ (encNat m).length ≤ C * (2 * (m + 1)) :=
        Nat.mul_le_mul_left _ (two_pow_length_encNat_le m)
    _ = 2 * C * (m + 1) := by ring

/-! ### Lengths and comparisons, computed -/

namespace ComputableInO

/-- The length of a bit word in binary, by a binary counter, within quadratic time and linear
space. -/
theorem lengthNat : ComputableInO (fun l : List Bool => l.length) encBits encNat
    (fun l => (l.length + 1) ^ 2) fun l => l.length + 1 := by
  obtain ⟨C, hC⟩ := exists_pow_length_encNat_le 2
  have hstep := natSucc.comp (fst encNat encBool)
  have hlen (x : List Bool) (i : ℕ) :
      (List.take i x).foldl (fun n _ => n + 1) 0 = min i x.length := by
    simp [List.foldl_const]
  have h := foldl (encA := encBool) (encL := encBits) (encB := encNat) (list := id)
    (init := fun _ => 0) (step := fun n _ => n + 1) (of_linear (.of_eq fun _ => rfl)) (const 0)
    hstep (R := fun x => (C + 3) * (x.length + 1)) (Q := fun x => 3 * (x.length + 1))
    (B := fun x => x.length)
    (fun x i hi => by
      simp only [id] at hi ⊢
      rw [hlen]
      have h₁ := hC (min i x.length)
      have h₂ := Universal.length_encNat_le (min i x.length)
      have h₃ : C * (min i x.length + 1) ≤ C * (x.length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have e : (C + 3) * (x.length + 1) = C * (x.length + 1) + 3 * (x.length + 1) := by ring
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega)
    (fun x i hi => by
      simp only [id] at hi ⊢
      rw [hlen]
      have h₂ := Universal.length_encNat_le (min i x.length)
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega)
    (fun x i hi => by
      simp only [id] at hi ⊢
      rw [hlen]
      exact (Universal.length_encNat_le _).trans (Nat.min_le_right _ _))
  refine (h.mono (C + 16) (fun x => ?_) fun x => ?_).of_enc_eq fun x => ?_
  · simp only [id, encBits_apply]
    nlinarith
  · simp only [id, encBits_apply]
    nlinarith
  · simp [List.foldl_const]

/-- The comparison of unary numbers, by counting down, within quadratic time and linear space. -/
theorem unaryLe : ComputableInO (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
    (encPair encUnary encUnary) encBool (fun p => ((encPair encUnary encUnary p).length + 1) ^ 2)
    fun p => (encPair encUnary encUnary p).length + 1 := by
  have hstep :=
    ComputableTidilyInDegree.unary_pred.inO_one.computableInO.comp (fst encUnary encBool)
  have hrep (a b : ℕ) : (List.replicate b true).foldl (fun n _ => n - 1) a = a - b := by
    induction b generalizing a with
    | zero => rfl
    | succ b ih => rw [List.replicate_succ, List.foldl_cons, ih]; omega
  have h := foldl (encA := encBool) (encL := encBits) (encB := encUnary)
    (list := fun p : ℕ × ℕ => List.replicate p.2 true) (init := fun p => p.1)
    (step := fun n _ => n - 1)
    ((of_linear (.of_eq (f := fun n => List.replicate n true) (encIn := encUnary)
      (encMid := encBits) fun _ => rfl)).comp (snd encUnary encUnary))
    (fst encUnary encUnary) hstep
    (R := fun p => 3 * ((encPair encUnary encUnary p).length + 1))
    (Q := fun p => 3 * ((encPair encUnary encUnary p).length + 1))
    (B := fun p => (encPair encUnary encUnary p).length)
    (fun p i hi => by
      rw [List.take_replicate, hrep]
      simp only [length_encPair, encUnary_apply, List.length_replicate,
        encBool_apply, List.length_singleton]
      omega)
    (fun p i hi => by
      rw [List.take_replicate, hrep]
      simp only [length_encPair, encUnary_apply, List.length_replicate,
        encBool_apply, List.length_singleton]
      omega)
    (fun p i hi => by
      rw [List.take_replicate, hrep]
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      omega)
  have hz := ComputableTidilyInDegree.unary_isZero.inO_one.computableInO.comp_linear h
  refine (hz.mono 16 (fun p => ?_) fun p => ?_).of_enc_eq fun p => ?_
  · simp only [length_encPair, encUnary_apply, List.length_replicate,
      encBits_apply]
    nlinarith
  · simp only [length_encPair, encUnary_apply, List.length_replicate,
      encBits_apply]
    omega
  · simp only [Function.comp_apply, hrep, Nat.sub_eq_zero_iff_le]

end ComputableInO

/-- **From binary to unary**, by counting down: within time `O((n + 1) ^ 2)` and space `O(n)`.
The counter's squared binary length is `O(n + 1)`, so each of the `n` rounds costs `O(n + 1)`. -/
theorem ComputableInO.natToUnary : ComputableInO (fun n : ℕ => n) encNat encUnary
    (fun n => (n + 1) ^ 2) fun n => n := by
  have hiter (n : ℕ) : (· + 1)^[n] 0 = n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]
  have h := (ComputableInO.iterate (n := fun n : ℕ => n) (init := fun _ => 0)
    (step := (· + 1)) (encIn := encNat) (encB := encUnary)
    (.of_linear (.of_eq fun _ => rfl)) (.const 0)
    ComputableTidilyInDegree.unary_succ.inO_one.computableInO (R := fun n => n) (Q := fun n => n)
    (B := fun n => n)
    (fun n k hk => by simp only [hiter, encUnary_apply, List.length_replicate]; exact hk)
    (fun n k hk => by simp only [hiter, encUnary_apply, List.length_replicate]; exact hk)
    (fun n k hk => by simp only [hiter, encUnary_apply, List.length_replicate]; exact hk))
  obtain ⟨C, hC⟩ := exists_pow_length_encNat_le 2
  refine (h.of_enc_eq fun n => by rw [hiter]).mono (C + 8) (fun n => ?_) fun n => ?_
  all_goals
    have := Universal.length_encNat_le n
  · have hc := Nat.mul_le_mul_left (n + 1) (hC n)
    nlinarith
  · nlinarith

end Turing.MultiTapeTM
