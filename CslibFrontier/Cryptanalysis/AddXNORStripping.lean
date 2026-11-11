/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORChain
import Mathlib.Tactic.Ring

/-!
# Stripping a common power of two

[WangLvShenZhang2027], Lemma 4 (PDF p. 7). Appending s zero low bits
to every noninitial operand is precisely multiplication by 2 ^ s. For every
operator string, the high state is the width-m chain, while the initial low
field is either unchanged or complemented according to XNOR parity. The exact
zero-target criterion includes both parity branches, without an existential
solution or a desired conclusion among the hypotheses.

## Main definitions

* `scaled`, `strip`: append a zero low field or extract the actual high operands.

## Main results

* `eval_scaled`: full-state factorization for every operator string.
* `solvable_scaled_iff`: unrestricted decision equivalence with both parity branches.
* `eval_strip_eq_zero_iff`: direct criterion for arbitrary divisible operands.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR

/-- Multiply all noninitial operands by 2 ^ s by appending s zero bits. -/
@[expose] def scaled {m : ℕ} (s : ℕ) (xs : List (Bool × BitVec m)) :
    List (Bool × BitVec (m + s)) := xs.map fun (b, a) => (b, a ++ 0#s)

private theorem append_add_zero {m s : ℕ} (x a : BitVec m) (c : BitVec s) :
    (x ++ c) + (a ++ 0#s) = (x+a) ++ c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_append_eq_mul_add, BitVec.toNat_zero,
    Nat.add_zero, Nat.pow_add]
  have modlow (v : ℕ) :
      (v * 2 ^ s + c.toNat) % (2 ^ m * 2 ^ s) = v % 2 ^ m * 2 ^ s + c.toNat := by
    rw [Nat.add_mod, Nat.mul_mod_mul_right]
    have hc : c.toNat < 2 ^ m * 2 ^ s :=
      lt_of_lt_of_le c.isLt (by
        simpa using Nat.mul_le_mul_right (2 ^ s) (Nat.one_le_two_pow (n := m)))
    rw [Nat.mod_eq_of_lt hc]
    apply Nat.mod_eq_of_lt
    calc
      _ < v % 2 ^ m * 2 ^ s + 2 ^ s := Nat.add_lt_add_left c.isLt _
      _ = (v % 2 ^ m + 1) * 2 ^ s := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos m)))
  convert modlow (x.toNat + a.toNat) using 1; congr 1; ring

private theorem step_append_zero {m s : ℕ} (b : Bool) (x a : BitVec m) (c : BitVec s) :
    step b (x ++ c) (a ++ 0#s) = step b x a ++ (if b then ~~~c else c) := by
  cases b <;> simp [step, append_add_zero, BitVec.xor_append, BitVec.not_append]

/-- Exact full-state factorization, for every operator string and initial low field. -/
theorem eval_scaled {m s : ℕ} (xs : List (Bool × BitVec m)) (x : BitVec m) (c : BitVec s) :
    eval (scaled s xs) (x ++ c) =
      eval xs x ++ (if xnorParity xs then ~~~c else c) := by
  induction xs generalizing x c with
  | nil => simp [scaled, eval, xnorParity]
  | cons h xs ih =>
    rcases h with ⟨b, a⟩
    change eval ((b, a ++ 0#s) :: scaled s xs) (x ++ c) = _
    rw [eval, step_append_zero, ih]
    simp only [eval, xnorParity]
    cases b <;> by_cases hp : xnorParity xs = true <;> simp [hp]

private theorem append_eq_zero_iff {m s : ℕ} (x : BitVec m) (c : BitVec s) :
    x ++ c = 0 ↔ x = 0 ∧ c = 0 := by
  constructor
  · intro h
    have hh := congrArg (fun w : BitVec (m + s) => w.extractLsb' s m) h
    have hl := congrArg (fun w : BitVec (m + s) => w.setWidth s) h
    simpa [BitVec.extractLsb'_append_eq_left, BitVec.setWidth_append_eq_right] using And.intro hh hl
  · rintro ⟨rfl, rfl⟩
    simp

/-- Lemma 4, at the level of each actual operator string. The original chain
solves zero exactly when the stripped chain solves zero and the initial low
field is zero for even parity or all ones for odd parity. -/
theorem eval_scaled_eq_zero_iff {m s : ℕ} (xs : List (Bool × BitVec m))
    (x : BitVec m) (c : BitVec s) :
    eval (scaled s xs) (x ++ c) = 0 ↔
      (xnorParity xs = false ∧ c = 0 ∧ eval xs x = 0) ∨
      (xnorParity xs = true ∧ c = ~~~0 ∧ eval xs x = 0) := by
  rw [eval_scaled, append_eq_zero_iff]
  have hn : ~~~c = 0 ↔ c = ~~~0 := by
    constructor
    · intro h
      rw [← BitVec.not_not (b := c), h]
    · intro h
      rw [h, BitVec.not_not]
  cases xnorParity xs <;> simp only [hn, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
    false_and, true_and, false_or, or_false, and_comm]

private theorem zip_scaled {m s : ℕ} (bs : List Bool) (as : List (BitVec m)) :
    bs.zip (as.map fun a => a ++ 0#s) = scaled s (bs.zip as) := by
  induction bs generalizing as with
  | nil => simp [scaled]
  | cons b bs ih =>
    cases as with
    | nil => simp [scaled]
    | cons a as => simp [scaled, ih, scaled] at *

/-- Full decision form of Lemma 4. All operator strings of the appropriate length
are quantified; even/odd parity remains an explicit constraint on the stripped
instance. There are no bounds on the number of operands or the retained width. -/
theorem solvable_scaled_iff {m s : ℕ} (as : List (BitVec m))
    (x : BitVec m) (c : BitVec s) :
    Solvable (as.map fun a => a ++ 0#s) (x ++ c) 0 ↔
      (c = 0 ∧ ∃ bs : List Bool, bs.length = as.length ∧
        xnorParity (bs.zip as) = false ∧ eval (bs.zip as) x = 0) ∨
      (c = ~~~0 ∧ ∃ bs : List Bool, bs.length = as.length ∧
        xnorParity (bs.zip as) = true ∧ eval (bs.zip as) x = 0) := by
  simp only [Solvable, List.length_map, zip_scaled, eval_scaled_eq_zero_iff]
  constructor
  · rintro ⟨bs, hl, he | ho⟩
    · exact Or.inl ⟨he.2.1, bs, hl, he.1, he.2.2⟩
    · exact Or.inr ⟨ho.2.1, bs, hl, ho.1, ho.2.2⟩
  · rintro (⟨hc, bs, hl, hp, he⟩ | ⟨hc, bs, hl, hp, he⟩)
    · exact ⟨bs, hl, Or.inl ⟨hp, hc, he⟩⟩
    · exact ⟨bs, hl, Or.inr ⟨hp, hc, he⟩⟩

/-- Remove the common low field from all noninitial operands. -/
@[expose] def strip (m s : ℕ) (xs : List (Bool × BitVec (m + s))) :
    List (Bool × BitVec m) := xs.map fun (b, a) => (b, a.extractLsb' s m)

private theorem split_word {m s : ℕ} (a : BitVec (m + s)) :
    a = a.extractLsb' s m ++ a.setWidth s := by
  apply BitVec.eq_of_toNat_eq
  have ha : a.toNat / 2 ^ s < 2 ^ m :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s)).2 (by simpa [Nat.pow_add] using a.isLt)
  simp only [BitVec.toNat_append_eq_mul_add, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth, Nat.mod_eq_of_lt ha]
  simpa only [Nat.mul_comm] using (Nat.div_add_mod a.toNat (2 ^ s)).symm

private theorem scaled_strip {m s : ℕ} (xs : List (Bool × BitVec (m + s)))
    (h : ∀ p ∈ xs, p.2.toNat % 2 ^ s = 0) : scaled s (strip m s xs) = xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨b, a⟩
    have ha : a.setWidth s = 0 := by
      apply BitVec.eq_of_toNat_eq
      simpa [BitVec.toNat_setWidth] using h (b, a) (by simp)
    have he : a.extractLsb' s m ++ 0#s = a := by
      simpa [ha] using (split_word a).symm
    have ht : ∀ p ∈ xs, p.2.toNat % 2 ^ s = 0 := fun p hp => h p (by simp [hp])
    simpa only [strip, List.map_cons, scaled, he] using congrArg (List.cons (b, a)) (ih ht)

/-- Lemma 4 for an arbitrary input whose noninitial operands share a power of
two. The initial low field is extracted from the actual word, and all high
operands are the actual quotients, rather than supplied replacement values. -/
theorem eval_strip_eq_zero_iff {m s : ℕ} (xs : List (Bool × BitVec (m + s)))
    (h : ∀ p ∈ xs, p.2.toNat % 2 ^ s = 0) (a : BitVec (m + s)) :
    eval xs a = 0 ↔
      (xnorParity (strip m s xs) = false ∧ a.setWidth s = 0 ∧
        eval (strip m s xs) (a.extractLsb' s m) = 0) ∨
      (xnorParity (strip m s xs) = true ∧ a.setWidth s = ~~~0 ∧
        eval (strip m s xs) (a.extractLsb' s m) = 0) := by
  conv_lhs => rw [← scaled_strip xs h, split_word a]
  exact eval_scaled_eq_zero_iff _ _ _

end Cslib.Cryptanalysis.AddXNOR
