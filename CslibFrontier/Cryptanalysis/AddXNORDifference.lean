/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORChain
public import CslibFrontier.Foundations.Data.BitString.Weight
public import Mathlib.Data.FinEnum
import all CslibFrontier.Cryptanalysis.AddXNORSwap
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# XOR-difference propagation through actual Add/XNOR steps

[WangLvShenZhang2027], Lemma 7 and Proposition 3 (PDF pp. 18–19).
The probability is over two independent uniform words, with a fixed difference.
Bits below the most significant bit constrain the carry; the most significant
bit itself imposes no condition. Proof-only low-bit splitting uses the already
proved carry/expectation helpers of `AddXNORSwap`, without changing that module.

## Main results

* `xnor_difference`, `msb_addition_difference`: deterministic difference propagation.
* `addition_difference_probability`: exact arbitrary-difference propagation probability.
* `operator_flip_difference`, `operator_flip_ne`: actual flip difference and nonvanishing.
-/

public section

open scoped BigOperators

namespace Cslib.Cryptanalysis.AddXNOR

/-- XNOR transports every XOR difference exactly. -/
theorem xnor_difference {m : ℕ} (t a δ : BitVec m) :
    step true (t ^^^ δ) a = step true t a ^^^ δ := by
  simp only [step, ↓reduceIte, BitVec.not_xor_left, BitVec.xor_assoc]
  rw [BitVec.xor_comm δ a]

/-- The difference caused at a single operator flip is the complemented actual carry word. -/
theorem operator_flip_difference {m : ℕ} (t a : BitVec m) :
    step false t a ^^^ step true t a = ~~~(carryWord t a) := by
  simp only [step, Bool.false_eq_true, ↓reduceIte, carryWord, ← BitVec.not_xor_right,
    BitVec.xor_assoc]

/-- A single flip cannot vanish at positive width. Common subsequent steps
are injective, so they cannot erase this nonzero difference. -/
theorem operator_flip_ne {m : ℕ} (hm : 0 < m) (t a : BitVec m)
    (post : List (Bool × BitVec m)) :
    eval post (step false t a) ≠ eval post (step true t a) := by
  intro h
  have he := (eval_bijective post).injective h
  have hb := congrArg (fun w : BitVec m => w.getLsbD 0) he
  change (eval [(false, a)] t).getLsbD 0 = (eval [(true, a)] t).getLsbD 0 at hb
  rw [eval_bit_zero hm, eval_bit_zero hm] at hb
  simp only [operandsXor, xnorParity, Bool.xor_false] at hb
  cases t.getLsbD 0 <;> cases a.getLsbD 0 <;> simp at hb

private def differenceIndicator {m : ℕ} (δ t a : BitVec m) (c d : Bool) : ℚ :=
  if (t ^^^ δ) + a + BitVec.ofNat m c.toNat =
      (t + a + BitVec.ofNat m d.toNat) ^^^ δ then 1 else 0

private def differenceMass {m : ℕ} (δ : BitVec m) (c d : Bool) : ℚ :=
  𝔼 t : BitVec m, 𝔼 a : BitVec m, differenceIndicator δ t a c d

private theorem differenceIndicator_concat {n : ℕ} (δ t a : BitVec n)
    (b u v c d : Bool) :
    differenceIndicator (δ.concat b) (t.concat u) (a.concat v) c d =
      if c = d then differenceIndicator δ t a
        (Bool.atLeastTwo (u ^^ b) v c) (Bool.atLeastTwo u v d) else 0 := by
  simp only [differenceIndicator, BitVec.concat_xor_concat, concat_add_carry, concat_eq_iff]
  cases b <;> cases u <;> cases v <;> cases c <;> cases d <;> simp

private theorem differenceMass_ne {n : ℕ} (δ : BitVec (n + 1)) (c d : Bool) (h : c ≠ d) :
    differenceMass δ c d = 0 := by
  obtain ⟨⟨δ, b⟩, rfl⟩ := (concat_bijective n).2 δ
  simp only [differenceMass, expect_concat, differenceIndicator_concat, ite_eq_right h,
    Finset.expect_const, Finset.univ_nonempty]

private theorem differenceMass_cons {n : ℕ} (δ : BitVec (n + 1)) (b c : Bool) :
    differenceMass (δ.concat b) c c =
      if b then differenceMass δ c c / 2
      else if c then (differenceMass δ false false + 3 * differenceMass δ true true) / 4
        else (3 * differenceMass δ false false + differenceMass δ true true) / 4 := by
  have hft := differenceMass_ne δ false true (by decide)
  have htf := differenceMass_ne δ true false (by decide)
  unfold differenceMass at *
  simp only [expect_concat (n + 1), differenceIndicator_concat, ↓reduceIte]
  simp_rw [Finset.expect_comm (Finset.univ : Finset Bool)
    (Finset.univ : Finset (BitVec (n + 1)))]
  have eb (f : Bool → ℚ) : (𝔼 b, f b) = (f false + f true) / 2 := by
    simp [Finset.expect_eq_sum_div_card, Fintype.univ_bool, add_comm]
  cases b <;> cases c <;> simp only [eb, Bool.atLeastTwo, ↓reduceIte,
    Bool.and_false, Bool.and_true, Bool.or_false, Bool.or_true, Bool.false_xor,
    Bool.true_xor, Bool.not_false, Bool.not_true, Bool.false_eq_true]
  all_goals
    simp only [div_eq_mul_inv, Finset.expect_add_distrib, ← Finset.expect_mul, hft, htf]
    ring

/-- Number of active difference bits strictly below the MSB. -/
@[expose] def activeDifferenceBits {m : ℕ} (δ : BitVec m) : ℕ :=
  ∑ i : Fin (m - 1), (δ.getLsbD i).toNat

private theorem activeDifferenceBits_concat {n : ℕ} (δ : BitVec (n + 1)) (b : Bool) :
    activeDifferenceBits (δ.concat b) = b.toNat + activeDifferenceBits δ := by
  simp [activeDifferenceBits, Fin.sum_univ_succ]

private theorem differenceMass_one (δ : BitVec 1) (c : Bool) : differenceMass δ c c = 1 := by
  unfold differenceMass
  have hi (t a : BitVec 1) : differenceIndicator δ t a c c = 1 := by
    rcases δ with ⟨δ⟩; rcases t with ⟨t⟩; rcases a with ⟨a⟩
    fin_cases δ <;> fin_cases t <;> fin_cases a <;> cases c <;> decide
  simp only [hi, Finset.expect_const, Finset.univ_nonempty]

private theorem differenceMass_closed (n : ℕ) (δ : BitVec (n + 1)) (c : Bool) :
    differenceMass δ c c = (1/2 : ℚ) ^ activeDifferenceBits δ := by
  induction n generalizing c with
  | zero => simp [differenceMass_one, activeDifferenceBits]
  | succ n ih =>
    obtain ⟨⟨δ, b⟩, rfl⟩ := (concat_bijective (n + 1)).2 δ
    rw [differenceMass_cons, activeDifferenceBits_concat]
    simp only [ih]
    cases b <;> cases c <;> simp only [Bool.toNat_false, Bool.toNat_true,
      Bool.false_eq_true, ↓reduceIte, zero_add, pow_add, pow_one]
    all_goals ring

/-- Lemma 7(iii): every active non-MSB difference bit halves the exact
preservation probability. No uniform/independent carry assumption is used. -/
theorem addition_difference_probability (n : ℕ) (δ : BitVec (n + 1)) :
    (𝔼 t : BitVec (n + 1), 𝔼 a : BitVec (n + 1),
      if (t ^^^ δ) + a = (t + a) ^^^ δ then (1 : ℚ) else 0) =
      (1/2 : ℚ) ^ activeDifferenceBits δ := by
  simpa only [differenceMass, differenceIndicator, Bool.toNat_false,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero] using differenceMass_closed n δ false

/-- With no active non-MSB bits, preservation holds for every pair of words. -/
theorem addition_difference_of_no_active (n : ℕ) (δ : BitVec (n + 1))
    (hδ : activeDifferenceBits δ = 0) (t a : BitVec (n + 1)) :
    (t ^^^ δ) + a = (t + a) ^^^ δ := by
  have hp := addition_difference_probability n δ
  rw [hδ, pow_zero] at hp
  let failure (t a : BitVec (n + 1)) : ℚ :=
    if (t ^^^ δ) + a = (t + a) ^^^ δ then 0 else 1
  have hf : (𝔼 t, 𝔼 a, failure t a) = 0 := by
    have hi (t a : BitVec (n + 1)) : failure t a =
        1 - (if (t ^^^ δ) + a = (t + a) ^^^ δ then (1 : ℚ) else 0) := by
      unfold failure
      split <;> norm_num
    simp only [hi, Finset.expect_sub_distrib, Finset.expect_const, Finset.univ_nonempty, hp,
      sub_self]
  have hn (t a : BitVec (n + 1)) : 0 ≤ failure t a := by unfold failure; split <;> norm_num
  have ht := (Finset.expect_eq_zero_iff_of_nonneg
    (fun t _ => Finset.expect_nonneg fun a _ => hn t a)).1 hf t (Finset.mem_univ t)
  have ha := (Finset.expect_eq_zero_iff_of_nonneg (fun a _ => hn t a)).1 ht a (Finset.mem_univ a)
  simpa [failure] using ha

/-- Lemma 7(ii): the most significant bit difference commutes with addition. -/
theorem msb_addition_difference (n : ℕ) (t a : BitVec (n + 1)) :
    (t ^^^ BitVec.ofNat (n + 1) (2 ^ n)) + a =
      (t + a) ^^^ BitVec.ofNat (n + 1) (2 ^ n) := by
  apply addition_difference_of_no_active n
  unfold activeDifferenceBits
  apply Finset.sum_eq_zero
  intro i _
  have hi := i.isLt
  simp only [Nat.add_sub_cancel] at hi
  rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
  simp only [show n ≠ i.val by omega, decide_false, Bool.and_false, Bool.toNat_false]

end Cslib.Cryptanalysis.AddXNOR
