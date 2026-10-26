/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Karn Seth
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Binary word arithmetic and comparison

The carry fold, its value and length laws, and the highest-differing-bit characterization of
strict order are pure facts about least-significant-first binary words. They do not import a
computability calculus. The multiplication bit fold and its prefix-size laws are shared with
the direct and legacy resource proofs, retaining the original shift-and-add data.
-/

@[expose] public section
namespace Turing.MultiTapeTM
open NatSucc

namespace NatAdd

/-- The binary digits of `2 * n + b`, if they do not end in a zero. -/
lemma bits_bit (b : Bool) (n : ℕ) (h : n = 0 → b = true) :
    (2 * n + b.toNat).bits = b :: n.bits := by
  rw [← Nat.bit_val]
  exact Nat.bits_append_bit n b h

/-- The carry of adding three digits. -/
def carry (a b c : Bool) : Bool := a && b || c && (a ^^ b)

/-- Adds the digits `l` and `r` with the carry `c`, least significant first; `r` is padded with
zeros. -/
def addBits : Bool → List Bool → List Bool → List Bool
  | c, [], r => incr c r
  | c, a :: l, r => (a ^^ (r.headD false ^^ c)) :: addBits (carry a (r.headD false) c) l r.tail

/-- Incrementing a canonical word represents addition of its incoming carry. -/
lemma incr_bits (c : Bool) (n : ℕ) : incr c n.bits = (n + c.toNat).bits := by
  cases c
  · simp [incr]
  · exact (bits_succ n).symm

/-- The word adder computes the sum of two natural numbers and an incoming carry. -/
lemma addBits_bits (c : Bool) (m n : ℕ) : addBits c m.bits n.bits = (m + n + c.toNat).bits := by
  induction m using Nat.binaryRec' generalizing c n with
  | zero => simp [addBits, incr_bits]
  | bit a m hm ih =>
    rw [Nat.bits_append_bit _ _ hm, addBits]
    induction n using Nat.binaryRec' with
    | zero =>
      have h := ih (carry a false c) 0
      rw [Nat.zero_bits] at h
      rw [Nat.zero_bits, List.headD_nil, List.tail_nil, h, Nat.bit_val,
        show 2 * m + a.toNat + 0 + c.toNat = 2 * (m + 0 + (carry a false c).toNat) +
          (a ^^ (false ^^ c)).toNat by cases a <;> cases c <;> simp [carry]; omega,
        bits_bit]
      cases a <;> cases c <;> simp_all [carry]
    | bit b n hn _ =>
      rw [Nat.bits_append_bit _ _ hn, List.headD_cons, List.tail_cons, ih, Nat.bit_val,
        Nat.bit_val, show 2 * m + a.toNat + (2 * n + b.toNat) + c.toNat =
          2 * (m + n + (carry a b c).toNat) + (a ^^ (b ^^ c)).toNat by
          cases a <;> cases b <;> cases c <;> simp [carry] <;> omega, bits_bit]
      cases a <;> cases b <;> cases c <;> simp_all [carry]

/-- One round: add the digit `a`, the next digit of the rest `r` and the carry `c`. -/
def addStep (s : Bool × List Bool × List Bool) (a : Bool) : Bool × List Bool × List Bool :=
  (carry a (s.2.1.headD false) s.1, s.2.1.tail, s.2.2 ++ [a ^^ (s.2.1.headD false ^^ s.1)])

/-- The fold invariant splits the accumulated digits from the remaining carry addition. -/
lemma foldl_addStep (l : List Bool) (c : Bool) (r out : List Bool) :
    let s := l.foldl addStep (c, r, out)
    out ++ addBits c l r = s.2.2 ++ incr s.1 s.2.1 := by
  induction l generalizing c r out with
  | nil => rfl
  | cons a l ih => simp [addBits, ← ih, addStep]

/-- Each round consumes at most one remaining digit and emits exactly one output digit. -/
lemma length_foldl_addStep (l : List Bool) (s : Bool × List Bool × List Bool) :
    (l.foldl addStep s).2.1.length ≤ s.2.1.length ∧
      (l.foldl addStep s).2.2.length = s.2.2.length + l.length := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h₁, h₂⟩ := ih (addStep s a)
    exact ⟨h₁.trans (by simp [addStep]), h₂.trans (by simp [addStep]; omega)⟩

end NatAdd

/-! ### Binary multiplication fold

The existing NatMul word-fold data and laws are moved from Complexity/Arith with Christian
Reitwiessner's source and proof bodies unchanged. Only these four previously module-private
names are exposed for shared direct and legacy resource proofs.
-/

namespace NatMul

/-- One round: add the shifted factor `s.2` to the product `s.1` if the digit `a` is `1`, and shift
the factor. -/
def mulStep (s : ℕ × ℕ) (a : Bool) : ℕ × ℕ := (if a then s.1 + s.2 else s.1, s.2 + s.2)

/-- The bit fold multiplies the shifted factor and adds the initial accumulator. -/
lemma foldl_mulStep (m acc sh : ℕ) : (m.bits.foldl mulStep (acc, sh)).1 = acc + m * sh := by
  induction m using Nat.binaryRec' generalizing acc sh with
  | zero => simp
  | bit a m hm ih =>
    rw [Nat.bits_append_bit _ _ hm, List.foldl_cons, mulStep, ih, Nat.bit_val]
    cases a <;> simp <;> ring

/-- Prefix accumulators and shifts are bounded by the number of processed binary digits. -/
lemma foldl_mulStep_le (l : List Bool) (acc sh : ℕ) :
    (l.foldl mulStep (acc, sh)).1 + sh ≤ acc + 2 ^ l.length * sh ∧
      (l.foldl mulStep (acc, sh)).2 = 2 ^ l.length * sh := by
  induction l generalizing acc sh with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h₁, h₂⟩ := ih (if a then acc + sh else acc) (sh + sh)
    have h : (if a then acc + sh else acc) ≤ acc + sh := by split <;> omega
    simp only [List.foldl_cons, mulStep, List.length_cons, pow_succ] at h₁ h₂ ⊢
    refine ⟨?_, by rw [h₂]; ring⟩
    nlinarith

/-- A shifted numerical bound gives an additive bound on binary size. -/
lemma size_le_of_le {x n : ℕ} (i : ℕ) (h : x ≤ 2 ^ i * n) : x.size ≤ i + n.size :=
  Nat.size_le.2 (h.trans_lt (by
    rw [pow_add]; exact Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self n) (Nat.two_pow_pos i)))

end NatMul

end Turing.MultiTapeTM

namespace Nat

/-- `m < n` exactly when some bit position below the length of `n` holds a zero in `m` and a one
in `n`, and every higher position below the total length agrees. -/
theorem lt_iff_exists_testBit (m n : ℕ) :
    m < n ↔ ∃ i < n.size, m.testBit i = false ∧ n.testBit i = true ∧
      ∀ j < m.size + n.size, i < j → m.testBit j = n.testBit j := by
  have hbig {k j : ℕ} (hj : k.size ≤ j) : k.testBit j = false :=
    Nat.testBit_eq_false_of_lt ((Nat.lt_size_self k).trans_le (Nat.pow_le_pow_right (by lia) hj))
  constructor
  · intro hlt
    obtain ⟨i, hi, hhigh⟩ := Nat.exists_most_significant_bit
      (show m ^^^ n ≠ 0 from fun h => hlt.ne (Nat.eq_of_testBit_eq fun j => by
        have := Nat.testBit_xor m n j
        rw [h, Nat.zero_testBit] at this
        revert this
        cases m.testBit j <;> cases n.testBit j <;> simp))
    rw [Nat.testBit_xor] at hi
    have heq : ∀ j, i < j → m.testBit j = n.testBit j := fun j hj => by
      have := hhigh j hj
      rw [Nat.testBit_xor] at this
      revert this
      cases m.testBit j <;> cases n.testBit j <;> simp
    cases hmi : m.testBit i <;> cases hni : n.testBit i <;> rw [hmi, hni] at hi
    · simp at hi
    · refine ⟨i, ?_, hmi, hni, fun j _ hj => heq j hj⟩
      by_contra h
      rw [hbig (Nat.le_of_not_lt h)] at hni
      exact Bool.false_ne_true hni
    · exact absurd (Nat.lt_of_testBit i hni hmi fun j hj => (heq j hj).symm) (Nat.lt_asymm hlt)
    · simp at hi
  · rintro ⟨i, -, hm, hn, h⟩
    refine Nat.lt_of_testBit i hm hn fun j hj => ?_
    by_cases hj' : j < m.size + n.size
    · exact h j hj' hj
    · rw [hbig (by lia), hbig (by lia)]


end Nat
