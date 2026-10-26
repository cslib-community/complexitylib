/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Foundations.Data.BitString.List.Binary
public import Complexity.Tactic.PolyTime.Init

/-!
# Polynomial-time division and remainder on binary naturals

Schoolbook shift-and-subtract long division over the binary encoding `Turing.MultiTapeTM.encNat`.
The dividend's binary digits are reversed to most-significant-bit-first order and folded with
`Turing.MultiTapeTM.BinaryDiv.divModStep`, which shifts the running remainder by one bit, adds the
next dividend bit, and subtracts the divisor whenever it fits. A zero divisor never subtracts, so
the quotient stays `0` and the remainder reconstructs the dividend, matching `a / 0 = 0` and
`a % 0 = a`.

After consuming any prefix `word` of the reversed digits, the state `(q, r)` is the quotient and
remainder of `Cslib.BitString.binaryValue word` by the divisor (`BinaryDiv.foldl_divModStep`). Both
components are therefore at most `binaryValue word < 2 ^ word.length`, so their binary encodings
have length at most `word.length`, keeping the encoded pair linearly bounded throughout the fold.

## Main definitions

* `Turing.MultiTapeTM.BinaryDiv.divModStep`: one shift-and-subtract step of binary long division.

## Main results

* `Turing.MultiTapeTM.BinaryDiv.foldl_divModStep`: folding `divModStep` over a
  most-significant-first bit word computes the quotient and remainder of its `binaryValue`.
* `Turing.MultiTapeTM.BinaryDiv.divMod_eq`: folding over `a.bits.reverse` computes
  `(a / b, a % b)`.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_divMod`: joint quotient and remainder on
  `encNat`.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_div`, `.binary_mod`: binary division and
  remainder on `encNat`.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_div'`, `.binary_mod'`: composition rules
  for `fun_prop` and `polytime`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM.BinaryDiv

/-- One shift-and-subtract step of binary long division with divisor `b`, state `(q, r)`, and next
most-significant dividend bit `bit`. When `b = 0`, the quotient remains `0` and the remainder
accumulates the binary value of the dividend. -/
def divModStep (b : ℕ) (state : ℕ × ℕ) (bit : Bool) : ℕ × ℕ :=
  let r' := 2 * state.2 + if bit then 1 else 0
  if b = 0 then (0, r')
  else if b ≤ r' then (2 * state.1 + 1, r' - b)
  else (2 * state.1, r')

lemma divModStep_div_mod (v b : ℕ) (bit : Bool) :
    divModStep b (v / b, v % b) bit = ((2 * v + bit.toNat) / b, (2 * v + bit.toNat) % b) := by
  have hbit : (if bit then 1 else 0) = bit.toNat := by cases bit <;> rfl
  have hdiv := Nat.div_add_mod v b
  have hbit_le : bit.toNat ≤ 1 := Bool.toNat_le bit
  have hmul₀ : 2 * (v / b) * b = 2 * (b * (v / b)) := by ring
  have hmul₁ : (2 * (v / b) + 1) * b = 2 * (b * (v / b)) + b := by ring
  have hmul₂ : (2 * (v / b) + 1 + 1) * b = 2 * (b * (v / b)) + 2 * b := by ring
  have hmul₃ : b * (2 * (v / b)) = 2 * (b * (v / b)) := by ring
  have hmul₄ : b * (2 * (v / b) + 1) = 2 * (b * (v / b)) + b := by ring
  dsimp only [divModStep]
  rw [hbit]
  split_ifs with hb hle
  · subst hb
    simp
  · have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
    have hmod_lt : v % b < b := Nat.mod_lt v hb_pos
    have hq : (2 * v + bit.toNat) / b = 2 * (v / b) + 1 := by
      apply Nat.div_eq_of_lt_le <;> lia
    have hr : (2 * v + bit.toNat) % b = 2 * (v % b) + bit.toNat - b := by
      have := Nat.div_add_mod (2 * v + bit.toNat) b
      rw [hq] at this
      lia
    exact Prod.ext hq.symm hr.symm
  · have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
    have hq : (2 * v + bit.toNat) / b = 2 * (v / b) := by
      apply Nat.div_eq_of_lt_le <;> lia
    have hr : (2 * v + bit.toNat) % b = 2 * (v % b) + bit.toNat := by
      have := Nat.div_add_mod (2 * v + bit.toNat) b
      rw [hq] at this
      lia
    exact Prod.ext hq.symm hr.symm

/-- Folding `divModStep` over any most-significant-first bit word computes the quotient and
remainder of `Cslib.BitString.binaryValue word` by `b`. -/
theorem foldl_divModStep (b : ℕ) (word : List Bool) :
    word.foldl (divModStep b) (0, 0) =
      (Cslib.BitString.binaryValue word / b, Cslib.BitString.binaryValue word % b) := by
  induction word using List.reverseRecOn with
  | nil => simp [Cslib.BitString.binaryValue]
  | append_singleton word bit ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Cslib.BitString.binaryValue_snoc, divModStep_div_mod]

/-- Folding `divModStep` over the reversed binary digits of `p.1` computes
`(p.1 / p.2, p.1 % p.2)`. -/
theorem divMod_eq (p : ℕ × ℕ) :
    p.1.bits.reverse.foldl (divModStep p.2) (0, 0) = (p.1 / p.2, p.1 % p.2) := by
  rw [foldl_divModStep, Cslib.BitString.binaryValue_reverse_bits]

/-- The encoded state after folding `word` has length at most `3 * word.length + 1`. -/
theorem length_encPair_foldl_divModStep_le (b : ℕ) (word : List Bool) :
    (encPair encNat encNat (word.foldl (divModStep b) (0, 0))).length ≤ 3 * word.length + 1 := by
  rw [foldl_divModStep]
  have hlt := Cslib.BitString.binaryValue_lt_two_pow word
  have hq : (Cslib.BitString.binaryValue word / b).size ≤ word.length :=
    Nat.size_le.2 ((Nat.div_le_self _ _).trans_lt hlt)
  have hr : (Cslib.BitString.binaryValue word % b).size ≤ word.length :=
    Nat.size_le.2 ((Nat.mod_le _ _).trans_lt hlt)
  simp only [length_encPair, encNat_apply, Nat.size_eq_bits_len]
  lia

end Turing.MultiTapeTM.BinaryDiv

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Compute both quotient and remainder of binary naturals by shift-and-subtract long division. -/
theorem binary_divMod : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2))
    (encPair encNat encNat) (encPair encNat encNat) := by
  have hlist : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1.bits.reverse)
      (encPair encNat encNat) encBits := by
    fun_prop
  have hstep : ComputableTidilyInPolyTime
      (fun q : (ℕ × (ℕ × ℕ)) × Bool => BinaryDiv.divModStep q.1.1 q.1.2 q.2)
      (encPair (encPair encNat (encPair encNat encNat)) encBool)
      (encPair encNat encNat) := by
    unfold BinaryDiv.divModStep
    fun_prop
  have hfold := foldlWith (encP := encNat) (encA := encBool) (encL := encBits)
    (encB := encPair encNat encNat) (par := Prod.snd) (list := fun p : ℕ × ℕ => p.1.bits.reverse)
    (init := fun _ => (0, 0)) (step := BinaryDiv.divModStep)
    (snd encNat encNat) hlist (const (0, 0)) hstep
    (B := fun p => 3 * (encPair encNat encNat p).length + 1)
    (((PolyBounded.const 3).mul .self).add (.const 1))
    (fun p i _ => by
      have hlen := BinaryDiv.length_encPair_foldl_divModStep_le p.2 (p.1.bits.reverse.take i)
      have htake : (p.1.bits.reverse.take i).length ≤ (encPair encNat encNat p).length := by
        calc (p.1.bits.reverse.take i).length
            ≤ p.1.bits.reverse.length := List.length_take_le' _ _
          _ = (encNat p.1).length := by simp
          _ ≤ (encPair encNat encNat p).length := length_le_encPair_left encNat encNat p
      lia)
  simpa only [BinaryDiv.divMod_eq] using hfold

/-- Division of binary naturals. -/
@[fun_prop, program_certificate]
theorem binary_div : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 / p.2)
    (encPair encNat encNat) encNat :=
  binary_divMod.fst'

/-- Remainder of binary naturals. -/
@[fun_prop, program_certificate]
theorem binary_mod : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 % p.2)
    (encPair encNat encNat) encNat :=
  binary_divMod.snd'

/-- Divide computed binary values, fixing their intermediate encodings for proof search. -/
@[fun_prop, program_certificate]
theorem binary_div' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => left a / right a) input encNat :=
  binary_div.comp (hleft.prod hright)

/-- Remainder of computed binary values, fixing their intermediate encodings for proof search. -/
@[fun_prop, program_certificate]
theorem binary_mod' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => left a % right a) input encNat :=
  binary_mod.comp (hleft.prod hright)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
