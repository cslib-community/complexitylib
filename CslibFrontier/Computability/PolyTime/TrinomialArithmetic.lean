/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Probability.KWiseIndependent.Trinomial
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Uniform binary arithmetic for trinomial field codes

Carryless multiplication runs in polynomial time in the binary input lengths. The proof folds
only over the multiplier's bits, with a linear bound on accumulator growth. It does not enumerate
the finite field. Trinomial reduction takes its limb width in unary: polynomial time in the
binary representation of the exponent defining that width would be an incorrect bound.
-/

public section

namespace Cslib

/-- Carryless multiplication is Horner evaluation of the multiplier's binary digits. -/
theorem clmul_eq_foldr_bits (a b : ℕ) :
    clmul a b = b.bits.foldr (fun bit acc => (if bit then a else 0) ^^^ (acc * 2)) 0 := by
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    rcases eq_or_ne b 0 with rfl | hb
    · simp
    · rw [clmul, ite_eq_right hb]
      have hbits : b.bits = decide (b % 2 = 1) :: (b / 2).bits := by
        conv_lhs => rw [show b = Nat.bit (decide (b % 2 = 1)) (b / 2) by
          by_cases hp : b % 2 = 1 <;> simp [Nat.bit, hp] <;> omega]
        apply Nat.bits_append_bit
        intro hz
        simp only [decide_eq_true_eq]
        omega
      rw [hbits, List.foldr_cons, ← ih (b / 2) (by omega)]
      simp [Nat.shiftLeft_eq]

end Cslib

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Carryless multiplication on binary polynomial codes is uniformly polynomial-time. -/
@[fun_prop]
theorem binary_clmul : ComputableInPolyTime (fun p : ℕ × ℕ => Cslib.clmul p.1 p.2)
    (encPair encNat encNat) encNat := by
  have hbits : ComputableInPolyTime Nat.bits encNat encBits := of_eq fun _ => rfl
  have hlist := bitsToList.comp (hbits.comp (snd encNat encNat))
  have hq := fst (encPair (encPair encNat encNat) encNat) encBool
  have ha := (fst encNat encNat).comp hq.fst'
  have hacc := hq.snd'
  have hbit := snd (encPair (encPair encNat encNat) encNat) encBool
  have hstep := binary_xor' (ite hbit ha (const 0)) (binary_mul' hacc (const 2))
  have h := foldlWithInput_of_bounded_growth
    (encA := encBool) (encL := encList encBool) (encB := encNat)
    (list := fun p : ℕ × ℕ => p.2.bits.reverse)
    (step := fun p acc bit => (if bit then p.1 else 0) ^^^ (acc * 2))
    (const 0) ⟨listReverseWithInput hlist, hstep, inferInstance, inferInstance⟩
    (growth := fun p => (encPair encNat encNat p).length + 1)
    ⟨.add .self (.const 1), fun p acc bit _ => by
      apply length_encNat_le_of_lt_two_pow
      have ha : p.1 < 2 ^ (encPair encNat encNat p).length := by
        apply lt_of_lt_of_le (Nat.lt_size_self p.1)
        apply Nat.pow_le_pow_right (by omega)
        simp only [length_encPair, encNat_apply, Nat.size_eq_bits_len]
        omega
      have hc := Nat.lt_size_self acc
      have hpow : 2 ^ Nat.size acc * 2 ≤
          2 ^ ((encNat acc).length + ((encPair encNat encNat p).length + 1)) := by
        rw [← pow_succ]
        apply Nat.pow_le_pow_right (by omega)
        simp only [encNat_apply, Nat.size_eq_bits_len]
        omega
      apply Nat.xor_lt_two_pow
      · have : 2 ^ (encPair encNat encNat p).length ≤
            2 ^ ((encNat acc).length + ((encPair encNat encNat p).length + 1)) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        split <;> omega
      · omega⟩
  simpa only [Cslib.clmul_eq_foldr_bits, List.foldl_reverse] using h

end Turing.MultiTapeTM.ComputableInPolyTime

namespace Cslib.TrinomialArithmetic

/-- Bit-code reduction, with the limb width supplied explicitly. -/
@[expose] def reduce (r c : ℕ) : ℕ :=
  let c3 := c >>> (3 * r)
  let c2 := (c >>> (2 * r)) &&& (2 ^ r - 1)
  let cLow := c &&& (2 ^ (2 * r) - 1)
  ((cLow ^^^ c3) ^^^ c2) ^^^ (c2 * 2 ^ r)

/-- The explicit-width reduction is the existing trinomial reduction. -/
theorem reduce_eq (t c : ℕ) : reduce (3 ^ t) c = reduceTrinomialCode t c := by
  simp only [reduce, reduceTrinomialCode, Nat.shiftLeft_eq]

/-- Binary multiplication of field codes at a supplied limb width. -/
@[expose] def mul (r a b : ℕ) : ℕ := reduce r (clmul a b)

/-- The executable multiplication agrees with multiplication in the exact finite field. -/
theorem mul_eq (t : ℕ) (x y : TrinomialField t) :
    mul (3 ^ t) (TrinomialField.equivFin t x).val (TrinomialField.equivFin t y).val =
      (TrinomialField.equivFin t (x * y)).val := by
  rw [mul, reduce_eq, TrinomialField.val_equivFin_mul]

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Reduction is uniformly polynomial-time in the unary width and binary code. -/
@[fun_prop]
theorem computableInPolyTime_reduce {α : Type} {enc : α ↪ List Bool} {r c : α → ℕ}
    (hr : ComputableInPolyTime r enc encUnary)
    (hc : ComputableInPolyTime c enc encNat) :
    ComputableInPolyTime (fun x => reduce (r x) (c x)) enc encNat := by
  have h2r := unary_mul' (const 2) hr
  have h3r := unary_mul' (const 3) hr
  have hp := binary_two_pow.comp hr
  have hc3 := binary_shiftRight' hc (unary_to_binary.comp h3r)
  have hc2 := binary_and' (binary_shiftRight' hc (unary_to_binary.comp h2r))
    (binary_sub' hp (const 1))
  have hlow := binary_and' hc (binary_sub' (binary_two_pow.comp h2r) (const 1))
  exact binary_xor' (binary_xor' (binary_xor' hlow hc3) hc2) (binary_mul' hc2 hp)

/-- Field-code multiplication is uniformly polynomial-time with a unary limb width. -/
@[fun_prop]
theorem computableInPolyTime_mul {α : Type} {enc : α ↪ List Bool} {r a b : α → ℕ}
    (hr : ComputableInPolyTime r enc encUnary)
    (ha : ComputableInPolyTime a enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun x => mul (r x) (a x) (b x)) enc encNat :=
  computableInPolyTime_reduce hr (binary_clmul.comp (ha.prod hb))

/-- Degree-three Horner evaluation on four binary coefficient codes. -/
@[expose] def eval4 (r c₀ c₁ c₂ c₃ u : ℕ) : ℕ :=
  c₀ ^^^ mul r u (c₁ ^^^ mul r u (c₂ ^^^ mul r u c₃))

/-- Four-coefficient evaluation agrees with the exact seeded polynomial family. -/
theorem eval4_eq (t U : ℕ) (c : Fin 4 → Fin (2 ^ (2 * 3 ^ t))) (u : Fin U)
    (hu : u.val < 2 ^ (2 * 3 ^ t)) :
    eval4 (3 ^ t) (c 0).val (c 1).val (c 2).val (c 3).val u.val =
      (Probability.trinomialPolyEval t 4 U c u).val := by
  let x : TrinomialField t := AdjoinRoot.mk (trinomial t) (polyOfCode u.val)
  let d (i : Fin 4) : TrinomialField t := (TrinomialField.equivFin t).symm (c i)
  have hx : (TrinomialField.equivFin t x).val = u.val :=
    TrinomialField.val_equivFin_mk_polyOfCode t hu
  have hd (i : Fin 4) : (TrinomialField.equivFin t (d i)).val = (c i).val := by
    simp [d]
  have heval : Probability.polynomialHash d x =
      d 0 + x * (d 1 + x * (d 2 + x * d 3)) := by
    simp [Probability.polynomialHash, Fin.sum_univ_succ]
    ring
  change _ = (TrinomialField.equivFin t (Probability.polynomialHash d x)).val
  rw [heval]
  simp only [TrinomialField.val_equivFin_add, ← mul_eq, hd, hx, eval4]

/-- Truncated four-coefficient hash on binary codes. -/
@[expose] def hash4 (r bits c₀ c₁ c₂ c₃ u : ℕ) : ℕ :=
  eval4 r c₀ c₁ c₂ c₃ u % 2 ^ bits

/-- The native arithmetic expression computes the same hash used for packet labels. -/
theorem hash4_eq (t U bits : ℕ) (c : Fin 4 → Fin (2 ^ (2 * 3 ^ t))) (u : Fin U)
    (hu : u.val < 2 ^ (2 * 3 ^ t)) :
    hash4 (3 ^ t) bits (c 0).val (c 1).val (c 2).val (c 3).val u.val =
      (Probability.trinomialPolyHash t 4 U bits c u).val := by
  rw [hash4, eval4_eq t U c u hu]
  rfl

/-- Fixed-degree polynomial evaluation is uniformly polynomial-time on binary coefficient codes. -/
@[fun_prop]
theorem computableInPolyTime_eval4 {α : Type} {enc : α ↪ List Bool}
    {r c₀ c₁ c₂ c₃ u : α → ℕ}
    (hr : ComputableInPolyTime r enc encUnary)
    (h₀ : ComputableInPolyTime c₀ enc encNat) (h₁ : ComputableInPolyTime c₁ enc encNat)
    (h₂ : ComputableInPolyTime c₂ enc encNat) (h₃ : ComputableInPolyTime c₃ enc encNat)
    (hu : ComputableInPolyTime u enc encNat) :
    ComputableInPolyTime (fun x => eval4 (r x) (c₀ x) (c₁ x) (c₂ x) (c₃ x) (u x))
      enc encNat :=
  binary_xor' h₀ (computableInPolyTime_mul hr hu
    (binary_xor' h₁ (computableInPolyTime_mul hr hu
      (binary_xor' h₂ (computableInPolyTime_mul hr hu h₃)))))

/-- Truncated hash evaluation charges unary limb and output widths, and binary data. -/
@[fun_prop]
theorem computableInPolyTime_hash4 {α : Type} {enc : α ↪ List Bool}
    {r bits c₀ c₁ c₂ c₃ u : α → ℕ}
    (hr : ComputableInPolyTime r enc encUnary) (hbits : ComputableInPolyTime bits enc encUnary)
    (h₀ : ComputableInPolyTime c₀ enc encNat) (h₁ : ComputableInPolyTime c₁ enc encNat)
    (h₂ : ComputableInPolyTime c₂ enc encNat) (h₃ : ComputableInPolyTime c₃ enc encNat)
    (hu : ComputableInPolyTime u enc encNat) :
    ComputableInPolyTime
      (fun x => hash4 (r x) (bits x) (c₀ x) (c₁ x) (c₂ x) (c₃ x) (u x)) enc encNat :=
  binary_mod.comp ((computableInPolyTime_eval4 hr h₀ h₁ h₂ h₃ hu).prod
    (binary_two_pow.comp hbits))

/-- Widths, seed coefficients, and key for explicit-field hash evaluation. -/
structure Input where
  /-- One half of the field's bit width. -/
  limbWidth : ℕ
  /-- Number of output bits retained. -/
  outputBits : ℕ
  /-- Constant coefficient. -/
  c0 : ℕ
  /-- Linear coefficient. -/
  c1 : ℕ
  /-- Quadratic coefficient. -/
  c2 : ℕ
  /-- Cubic coefficient. -/
  c3 : ℕ
  /-- Evaluation key as a binary polynomial code. -/
  key : ℕ

/-- Widths are unary; coefficients and key are binary. -/
enc_structure encInput : Input where
  limbWidth : encUnary, outputBits : encUnary, c0 : encNat, c1 : encNat,
  c2 : encNat, c3 : encNat, key : encNat

/-- Evaluate an explicitly encoded hash input. -/
@[expose] def run (p : Input) : ℕ :=
  hash4 p.limbWidth p.outputBits p.c0 p.c1 p.c2 p.c3 p.key

/-- One uniform native machine evaluates all supplied widths, coefficients, and keys. -/
theorem computableInPolyTime_run : ComputableInPolyTime run encInput encNat := by
  unfold run
  apply computableInPolyTime_hash4 <;> fun_prop

/-- For the selected field the supplied unary width is linear in the logarithmic parameters.
This size bound does not itself implement the parameter selector. -/
theorem selected_width_le (U bits : ℕ) :
    3 ^ Probability.trinomialStep U bits + bits ≤
      4 * max (Nat.clog 2 (max U 2)) (max bits 1) := by
  have hd := Probability.trinomialDeg_le_three_mul U bits
  have hb := Probability.le_trinomialDeg U bits
  have hb' : bits ≤ max (Nat.clog 2 (max U 2)) (max bits 1) :=
    (Nat.le_max_left bits 1).trans (Nat.le_max_right _ _)
  unfold Probability.trinomialDeg at hd hb
  omega

end Cslib.TrinomialArithmetic
