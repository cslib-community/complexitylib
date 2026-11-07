/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.NatPolynomial
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Universal.Bound
import Mathlib.Tactic.Linarith

/-!
# Polynomial padding with explicit native costs

Writing a polynomial number of padding bits and checking that an input is sufficiently padded
have independent native machine certificates. The test only compares lengths; it does not run
the algorithm on the unpadded word. This lets padding arguments charge a slow computation only
on inputs long enough to pay for it.

## Main results

* `Turing.MultiTapeTM.computableInO_polynomialPadding`: append `(n + 1) ^ k` bits to a framed
  word in time `O((n + 1) ^ (2 * k))` and space `O((n + 1) ^ k)`, for `k ≥ 1`.
* `Turing.MultiTapeTM.computableInO_unary_roundedPower`: write the rounded power
  `2 ^ (k * Nat.size (n + 1) + s)` of a binary natural in unary in time `O((n + 1) ^ (k + 1))`.
* `Turing.MultiTapeTM.computableInO_roundedPolynomialPadding`: round the padding length up to
  `2 ^ (k * Nat.size (n + 1))` and write it in time `O((n + 1) ^ (k + 1))`.
* `Turing.MultiTapeTM.computableInO_polynomialPaddingGuard`: compare the `k`th power of the
  decoded word length plus one with the full input length in quadratic time and linear space.

The binary arithmetic is polynomial in its bit length, hence linear in its numeric input by
`ComputableInPolyTime.nat_inO` and `ComputableInPolyTime.natPair_inO`. The quadratic padding
bound uses `ComputableInO.natToUnary`.
Rounding the length permits repeated unary doubling, whose cost is linear in the output
length times the number of doublings.
-/

public section

namespace Turing.MultiTapeTM

private theorem computableInO_length_succ_pow (k : ℕ) :
    ComputableInO (fun x : List Bool => (x.length + 1) ^ k) encBits encNat
      (fun x => (x.length + 1) ^ 2) (fun x => x.length + 1) := by
  have hp : ComputableInPolyTime (fun n : ℕ => (n + 1) ^ k) encNat encNat :=
    ComputableInPolyTime.binary_pow' (by fun_prop) (.const k)
  have h := hp.nat_inO.tidy.comp ComputableInO.lengthNat.tidy
  refine .of_tidy (h.mono 2 (fun x => ?_) fun x => ?_)
  · nlinarith
  · omega

/-- Frame a word and append `(n + 1) ^ k` padding bits, in time quadratic in the padded length
and space linear in it. -/
theorem computableInO_polynomialPadding {k : ℕ} (hk : 1 ≤ k) :
    ComputableInO
      (fun x : List Bool => frame x ++ List.replicate ((x.length + 1) ^ k) true)
      encBits encBits (fun x => (x.length + 1) ^ (2 * k))
      (fun x => (x.length + 1) ^ k) := by
  have hu := ComputableInO.natToUnary.tidy.comp (computableInO_length_succ_pow k).tidy
  have h := (ComputableTidilyInO.of_linear
    (.of_frame (f := id) (encOut := encFramed encBits) fun _ => rfl)).append hu
      (g := fun x : List Bool => frame x ++ List.replicate ((x.length + 1) ^ k) true)
      (encOut := encBits) fun _ => rfl
  refine .of_tidy (h.mono 8 (fun x => ?_) fun x => ?_)
  all_goals
    have hp : x.length + 1 ≤ (x.length + 1) ^ k := Nat.le_self_pow (by omega) _
    dsimp only [Function.comp_apply, id_eq, encBits_apply]
  · have hs := Nat.pow_le_pow_left hp 2
    rw [show 2 * k = k * 2 by omega, pow_mul]
    nlinarith
  · omega

/-- Rounding a power up using the binary size changes it by at most the fixed factor `2 ^ k`.
The use of `n + 1` includes an empty original input. -/
theorem polynomialPaddingPower_bounds (k n : ℕ) :
    (n + 1) ^ k ≤ 2 ^ (k * Nat.size (n + 1)) ∧
      2 ^ (k * Nat.size (n + 1)) ≤ 2 ^ k * (n + 1) ^ k := by
  have hs : 0 < Nat.size (n + 1) := Nat.size_pos.mpr (by omega)
  have hlower : 2 ^ (Nat.size (n + 1) - 1) ≤ n + 1 := Nat.lt_size.mp (by omega)
  have hupper : 2 ^ Nat.size (n + 1) ≤ 2 * (n + 1) := by
    calc
      _ = 2 ^ (Nat.size (n + 1) - 1 + 1) := by congr 1; omega
      _ = 2 ^ (Nat.size (n + 1) - 1) * 2 := by rw [pow_succ]
      _ ≤ (n + 1) * 2 := Nat.mul_le_mul_right 2 hlower
      _ = 2 * (n + 1) := Nat.mul_comm _ _
  rw [Nat.mul_comm k _, pow_mul]
  constructor
  · exact Nat.pow_le_pow_left (Nat.lt_size_self (n + 1)).le k
  · simpa only [mul_pow] using Nat.pow_le_pow_left hupper k

/-- Write the rounded power `2 ^ (k * Nat.size (n + 1) + s)` of a binary natural `n` in unary.
It is at least `2 ^ s * (n + 1) ^ k` and at most `2 ^ (k + s) * (n + 1) ^ k`
(`Turing.MultiTapeTM.polynomialPaddingPower_bounds`). Repeated unary doubling gives time
`O((n + 1) ^ (k + 1))` and space `O((n + 1) ^ k)`, for `k ≥ 1`; the constants depend on `k`
and `s`. -/
theorem computableInO_unary_roundedPower {k : ℕ} (hk : 1 ≤ k) (s : ℕ) :
    ComputableInO (fun n : ℕ => 2 ^ (k * Nat.size (n + 1) + s)) encNat encUnary
      (fun n => (n + 1) ^ (k + 1)) (fun n => (n + 1) ^ k) := by
  have hp : ComputableInPolyTime (fun n : ℕ => k * Nat.size (n + 1) + s) encNat encUnary :=
    ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' (.const k)
      (ComputableInPolyTime.binary_size.comp (by fun_prop))) (.const s)
  refine (ComputableInO.unary_two_pow.comp hp.nat_inO).mono ((k + s + 1) * 2 ^ (k + s) + 1)
    (fun n => ?_) fun n => ?_
  all_goals
    have hb := (polynomialPaddingPower_bounds k n).2
    have hp : n + 1 ≤ (n + 1) ^ k := Nat.le_self_pow (by omega) _
    have hN : 2 ^ (k * Nat.size (n + 1) + s) ≤ 2 ^ (k + s) * (n + 1) ^ k := by
      rw [pow_add, pow_add]
      nlinarith [Nat.one_le_two_pow (n := s)]
  · have hsz : k * Nat.size (n + 1) + s + 1 ≤ (k + s + 1) * (n + 1) := by
      have := Nat.size_le_self (n + 1)
      nlinarith
    calc
      _ ≤ (n + 1) ^ (k + 1) + ((k + s + 1) * (n + 1)) * (2 ^ (k + s) * (n + 1) ^ k) :=
        Nat.add_le_add ((Nat.le_succ n).trans (Nat.le_self_pow (by omega) _))
          (Nat.mul_le_mul hsz hN)
      _ = ((k + s + 1) * 2 ^ (k + s) + 1) * (n + 1) ^ (k + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_succ _)
  · calc
      _ ≤ (n + 1) ^ k + 2 ^ (k + s) * (n + 1) ^ k :=
        Nat.add_le_add ((Nat.le_succ n).trans hp) hN
      _ = (2 ^ (k + s) + 1) * (n + 1) ^ k := by ring
      _ ≤ _ := by
        apply Nat.mul_le_mul _ (Nat.le_succ _)
        nlinarith [Nat.one_le_two_pow (n := k + s)]

/-- Frame a word and append a rounded polynomial number of padding bits. Repeated unary
doubling gives time `O((n + 1) ^ (k + 1))` while the space remains `O((n + 1) ^ k)`. -/
theorem computableInO_roundedPolynomialPadding {k : ℕ} (hk : 1 ≤ k) :
    ComputableInO
      (fun x : List Bool => frame x ++
        List.replicate (2 ^ (k * Nat.size (x.length + 1))) true)
      encBits encBits (fun x => (x.length + 1) ^ (k + 1))
      (fun x => (x.length + 1) ^ k) := by
  have h := (ComputableInO.of_linear
    (.of_frame (f := id) (encMid := encFramed encBits) fun _ => rfl)).append
      ((computableInO_unary_roundedPower hk 0).comp ComputableInO.lengthNat)
      (g := fun x : List Bool => frame x ++
        List.replicate (2 ^ (k * Nat.size (x.length + 1))) true)
      (encOut := encBits) fun _ => by simp
  refine h.mono 3 (fun x => ?_) fun x => ?_
  all_goals
    have hp : x.length + 1 ≤ (x.length + 1) ^ k := Nat.le_self_pow (by omega) _
    dsimp only [Function.comp_apply, id_eq, encBits_apply]
  · have hs : (x.length + 1) ^ 2 ≤ (x.length + 1) ^ (k + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hl : x.length + 1 ≤ (x.length + 1) ^ (k + 1) := Nat.le_self_pow (by omega) _
    omega
  · omega

/-- Testing whether a framed word has polynomially sufficient padding takes quadratic time and
linear space in the full input length, independently of the fixed exponent. -/
theorem computableInO_polynomialPaddingGuard (k : ℕ) :
    ComputableInO
      (fun x : List Bool => decide (((unframe x).length + 1) ^ k ≤ x.length))
      encBits encBool (fun x => (x.length + 1) ^ 2) (fun x => x.length + 1) := by
  have hp : ComputableInPolyTime
      (fun p : ℕ × ℕ => decide ((p.1 + 1) ^ k ≤ p.2))
      (encPair encNat encNat) encBool :=
    ComputableInPolyTime.binary_le'
      (ComputableInPolyTime.binary_pow' (by fun_prop) (.const k))
      (.snd encNat encNat)
  have hu : ComputableTidilyInO unframe encBits encBits
      (fun x => x.length) (fun x => x.length) :=
    .of_linear (.of_unframe fun _ => rfl)
  have h := hp.natPair_inO.tidy.comp
    ((ComputableInO.lengthNat.tidy.comp hu).prod ComputableInO.lengthNat.tidy)
  refine .of_tidy (h.mono 12 (fun x => ?_) fun x => ?_)
  all_goals
    have hu := length_unframe_le x
    have h₁ := Universal.length_encNat_le (unframe x).length
    have h₂ := Universal.length_encNat_le x.length
    dsimp only [Function.comp_apply, encBits_apply]
  · have hs := Nat.pow_le_pow_left (Nat.add_le_add_right hu 1) 2
    nlinarith
  · omega

end Turing.MultiTapeTM
