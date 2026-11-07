/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORChain
public import Mathlib.Data.FinEnum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Adjacent Add/XNOR transpositions

[WangLvShenZhang2027], Theorem 6, PDF pp. 19–20. The collision experiment
uses three independent uniform full-width words and actual modular operations.
The proof derives the two-state carry recurrence by splitting off one low bit.

## Main results

* `swap_collision`: exact adjacent-swap probability for independent uniform words.
* `swap_collision_context`: the same formula for arbitrary common prefix and suffix.
-/

public section

open scoped BigOperators

namespace Cslib.Cryptanalysis.AddXNOR

private theorem concat_add_carry {n : ℕ} (x y : BitVec n) (a b c : Bool) :
    x.concat a + y.concat b + BitVec.ofNat (n + 1) c.toNat =
    (x + y + BitVec.ofNat n (Bool.atLeastTwo a b c).toNat).concat (a ^^ b ^^ c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_concat, BitVec.toNat_ofNat,
    Nat.mod_add_mod, Nat.add_mod_mod, Nat.pow_succ]
  have modlow (v b : Nat) (hb : b < 2) :
      (v * 2 + b) % (2 ^ n * 2) = v % 2 ^ n * 2 + b := by
    rw [Nat.add_mod, Nat.mul_mod_mul_right]
    have hv := Nat.mod_lt v (Nat.two_pow_pos n)
    rw [Nat.mod_eq_of_lt (by omega : b < 2 ^ n * 2)]
    exact Nat.mod_eq_of_lt (by omega)
  cases a <;> cases b <;> cases c <;>
    simp only [Bool.toNat_false, add_zero, Bool.or_self_right, Bool.and_self,
      Bool.or_self, bne_self_eq_false, Bool.toNat_true, Bool.and_true, Bool.bne_true,
      Bool.not_false, Bool.atLeastTwo_false_right, Bool.bne_false,
      Bool.atLeastTwo_true_right, Bool.or_true, Bool.and_false, Bool.or_false]
  all_goals first
    | solve | convert modlow (x.toNat + y.toNat) 0 (by decide) using 1; congr 1; ring
    | solve | convert modlow (x.toNat + y.toNat) 1 (by decide) using 1; congr 1; ring
    | solve | convert modlow (x.toNat + y.toNat + 1) 0 (by decide) using 1; congr 1; ring
    | solve | convert modlow (x.toNat + y.toNat + 1) 1 (by decide) using 1; congr 1; ring

private theorem concat_eq_iff {n : ℕ} (x y : BitVec n) (a b : Bool) :
    x.concat a = y.concat b ↔ x = y ∧ a = b := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_concat] at hn
    have hb := congrArg (fun w => w.getLsbD 0) h
    simp only [BitVec.getLsbD_concat, ↓reduceIte] at hb
    rw [hb] at hn
    exact ⟨BitVec.eq_of_toNat_eq (by omega), hb⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem concat_bijective (n : ℕ) : Function.Bijective
    (fun p : BitVec n × Bool => p.1.concat p.2) := by
  constructor
  · rintro ⟨x, a⟩ ⟨y, b⟩ h
    exact Prod.ext (concat_eq_iff x y a b |>.mp h).1
      (concat_eq_iff x y a b |>.mp h).2
  · intro w
    refine ⟨(BitVec.ofNat n (w.toNat / 2), w.getLsbD 0), ?_⟩
    apply BitVec.eq_of_toNat_eq
    have hw := w.isLt
    rw [Nat.pow_succ] at hw
    have hd : w.toNat / 2 < 2 ^ n := by omega
    simp only [BitVec.toNat_concat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd,
      BitVec.getLsbD, Nat.testBit_zero]
    have hm := Nat.mod_lt w.toNat (by decide : 0 < 2)
    by_cases h : w.toNat % 2 = 1 <;> simp [h] <;> omega

private theorem expect_concat (n : ℕ) (f : BitVec (n + 1) → ℚ) :
    (𝔼 w, f w) = 𝔼 x : BitVec n, 𝔼 b : Bool, f (x.concat b) := by
  rw [← Fintype.expect_bijective _ (concat_bijective n)
    (fun p : BitVec n × Bool => f (p.1.concat p.2)) f (fun _ => rfl)]
  exact Finset.expect_product _ _ _

private def swapIndicator {n : ℕ} (t a b : BitVec n) (c d : Bool) : ℚ :=
  if ~~~((t + a + BitVec.ofNat n c.toNat) ^^^ b) =
      ~~~(t ^^^ a) + b + BitVec.ofNat n d.toNat then 1 else 0

private theorem swapIndicator_concat {n : ℕ} (t a b : BitVec n)
    (u v w c d : Bool) :
    swapIndicator (t.concat u) (a.concat v) (b.concat w) c d =
      if c = d then swapIndicator t a b (Bool.atLeastTwo u v c)
        (Bool.atLeastTwo (!(u ^^ v)) w d) else 0 := by
  simp only [swapIndicator, concat_add_carry, BitVec.concat_xor_concat,
    BitVec.not_concat, concat_eq_iff]
  cases u <;> cases v <;> cases w <;> cases c <;> cases d <;> simp

private def swapMass (n : ℕ) (c d : Bool) : ℚ :=
  𝔼 t : BitVec n, 𝔼 a : BitVec n, 𝔼 b : BitVec n, swapIndicator t a b c d

private theorem swapMass_ne (n : ℕ) (c d : Bool) (h : c ≠ d) :
    swapMass (n + 1) c d = 0 := by
  unfold swapMass
  simp only [expect_concat, swapIndicator_concat, ite_eq_right h, Finset.expect_const,
    Finset.univ_nonempty]

private theorem swapMass_succ (n : ℕ) (c : Bool) :
    swapMass (n + 2) c c = if c then swapMass (n + 1) true true / 2
      else (5 * swapMass (n + 1) false false + swapMass (n + 1) true true) / 8 := by
  have hft := swapMass_ne n false true (by decide)
  have htf := swapMass_ne n true false (by decide)
  unfold swapMass at *
  simp only [expect_concat (n + 1), swapIndicator_concat, ↓reduceIte]
  simp_rw [Finset.expect_comm (Finset.univ : Finset Bool)
    (Finset.univ : Finset (BitVec (n + 1)))]
  have eb (f : Bool → ℚ) : (𝔼 b, f b) = (f false + f true) / 2 := by
    simp [Finset.expect_eq_sum_div_card, Fintype.univ_bool, add_comm]
  cases c <;> simp only [eb, Bool.atLeastTwo, ↓reduceIte,
    Bool.and_false, Bool.and_true, Bool.or_false, Bool.or_true, Bool.false_xor,
    Bool.true_xor, Bool.not_false, Bool.not_true, Bool.false_eq_true]
  all_goals
    simp only [div_eq_mul_inv, Finset.expect_add_distrib, ← Finset.expect_mul, hft, htf]
    ring

private theorem swapMass_one (c : Bool) : swapMass 1 c c = 1 := by
  unfold swapMass
  have hi (t a b : BitVec 1) : swapIndicator t a b c c = 1 := by
    rcases t with ⟨t⟩
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    fin_cases t <;> fin_cases a <;> fin_cases b <;> cases c <;> decide
  simp only [hi, Finset.expect_const, Finset.univ_nonempty]

private theorem swapMass_closed (n : ℕ) :
    swapMass (n + 1) false false = 2 * (5/8 : ℚ)^n - (1/2 : ℚ)^n ∧
    swapMass (n + 1) true true = (1/2 : ℚ)^n := by
  induction n with
  | zero => norm_num [swapMass_one]
  | succ n ih =>
    rw [swapMass_succ, swapMass_succ]
    simp only [Bool.false_eq_true, ↓reduceIte, ih.1, ih.2, pow_succ]
    constructor <;> ring

/-- Exact probability of an adjacent addition/XNOR swap collision over three
independent uniform words. Width is n + 1, including the width-one edge case. -/
theorem swap_collision (n : ℕ) :
    (𝔼 t : BitVec (n + 1), 𝔼 a : BitVec (n + 1), 𝔼 b : BitVec (n + 1),
      if step true (step false t a) b = step false (step true t a) b
      then (1 : ℚ) else 0) = 2 * (5/8 : ℚ)^n - (1/2 : ℚ)^n := by
  have h := (swapMass_closed n).1
  simpa only [swapMass, swapIndicator, step, Bool.toNat_false, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Bool.false_eq_true, ↓reduceIte] using h

/-- The transposition formula is unchanged by arbitrary common prefix and suffix
steps. Prefix operands are fixed arbitrarily; the initial word and both window
operands are independent uniform full-width words. Thus the statement also holds
conditionally on every choice of all operands outside the window. -/
theorem swap_collision_context (n : ℕ)
    (pre post : List (Bool × BitVec (n + 1))) :
    (𝔼 s : BitVec (n + 1), 𝔼 a : BitVec (n + 1), 𝔼 b : BitVec (n + 1),
      if eval post (step true (step false (eval pre s) a) b) =
          eval post (step false (step true (eval pre s) a) b)
      then (1 : ℚ) else 0) = 2 * (5/8 : ℚ)^n - (1/2 : ℚ)^n := by
  simp only [(eval_bijective post).injective.eq_iff]
  calc
    _ = (𝔼 t : BitVec (n + 1), 𝔼 a : BitVec (n + 1), 𝔼 b : BitVec (n + 1),
        if step true (step false t a) b = step false (step true t a) b
        then (1 : ℚ) else 0) :=
      Fintype.expect_bijective _ (eval_bijective pre) _ _ (fun _ => rfl)
    _ = _ := swap_collision n

end Cslib.Cryptanalysis.AddXNOR
