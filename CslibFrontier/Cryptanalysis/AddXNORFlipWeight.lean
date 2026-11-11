/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORDifference
import all CslibFrontier.Cryptanalysis.AddXNORSwap
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Expected weight of an operator-flip difference

[WangLvShenZhang2027], Proposition 3 (PDF p. 19). The experiment uses
independent uniform actual running and operand words. The result is the weight
immediately after the flipped step; a later bijection preserves nonvanishing but
need not preserve Hamming weight. No random-difference or independent-carry
hypothesis is used. The proof derives the two carry-in recurrences from actual
word addition and averages the independent operand bits.
-/

public section

open scoped BigOperators

namespace Cslib.Cryptanalysis.AddXNOR

private def carryFlip {m : ℕ} (t a : BitVec m) (c : Bool) : BitVec m :=
  ~~~((t + a + BitVec.ofNat m c.toNat) ^^^ t ^^^ a)

private noncomputable def flipMass (m : ℕ) (c : Bool) : ℚ :=
  𝔼 t : BitVec m, 𝔼 a : BitVec m,
    (Cslib.BitString.weight (fun i : Fin m => (carryFlip t a c).getLsbD i) : ℚ)

private theorem weight_concat {m : ℕ} (s : BitVec m) (b : Bool) :
    Cslib.BitString.weight (fun i : Fin (m + 1) => (s.concat b).getLsbD i) =
      b.toNat + Cslib.BitString.weight (fun i : Fin m => s.getLsbD i) := by
  simp [Cslib.BitString.weight_eq_sum_toNat, Fin.sum_univ_succ]

private theorem carryFlip_concat {m : ℕ} (t a : BitVec m) (u v c : Bool) :
    carryFlip (t.concat u) (a.concat v) c =
      (carryFlip t a (Bool.atLeastTwo u v c)).concat (!c) := by
  simp only [carryFlip, concat_add_carry, BitVec.concat_xor_concat, BitVec.not_concat]
  congr 1
  cases u <;> cases v <;> cases c <;> rfl

private theorem flipMass_succ (m : ℕ) (c : Bool) :
    flipMass (m + 1) c =
      if c then (flipMass m false + 3 * flipMass m true) / 4
      else 1 + (3 * flipMass m false + flipMass m true) / 4 := by
  unfold flipMass
  simp only [expect_concat m, carryFlip_concat, weight_concat, Nat.cast_add]
  simp_rw [Finset.expect_comm (Finset.univ : Finset Bool)
    (Finset.univ : Finset (BitVec m))]
  have eb (f : Bool → ℚ) : (𝔼 b, f b) = (f false + f true) / 2 := by
    simp [Finset.expect_eq_sum_div_card, Fintype.univ_bool, add_comm]
  cases c <;> simp only [eb, Bool.atLeastTwo, Bool.not_false, Bool.not_true,
    Bool.toNat_true, Bool.toNat_false, Nat.cast_one, Nat.cast_zero, Bool.false_eq_true,
    ↓reduceIte, Bool.and_false, Bool.or_false, Bool.and_true, Bool.or_true]
  all_goals
    simp only [div_eq_mul_inv, Finset.expect_add_distrib, Finset.expect_const,
      Finset.univ_nonempty, ← Finset.expect_mul]
    ring

private theorem flipMass_closed (m : ℕ) (c : Bool) :
    flipMass m c = (m : ℚ) / 2 + (if c then -1 else 1) * (1 - (1/2 : ℚ) ^ m) := by
  induction m generalizing c with
  | zero => simp [flipMass, Cslib.BitString.weight]
  | succ m ih =>
    rw [flipMass_succ, ih, ih]
    cases c <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one,
      pow_succ]
    all_goals ring

/-- Proposition 3's exact expected flip weight, for independent uniform actual
words. Width zero is included; no claim about the weight after a common suffix
is made. This does not rely on the source's incorrect total-weight parenthetical. -/
theorem expected_operator_flip_weight (m : ℕ) :
    (𝔼 t : BitVec m, 𝔼 a : BitVec m,
      (Cslib.BitString.weight (fun i : Fin m =>
        (step false t a ^^^ step true t a).getLsbD i) : ℚ)) =
      ((m : ℚ) + 2) / 2 - (1/2 : ℚ) ^ m := by
  have he (t a : BitVec m) : step false t a ^^^ step true t a = carryFlip t a false := by
    rw [operator_flip_difference]
    simp [carryFlip, carryWord]
  simp only [he]
  change flipMass m false = _
  rw [flipMass_closed]
  norm_num only [Bool.false_eq_true, ↓reduceIte]
  ring

end Cslib.Cryptanalysis.AddXNOR
