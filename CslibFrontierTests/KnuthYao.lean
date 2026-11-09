/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (test driver)

import CslibFrontier.Probability.DDGTree.KnuthYao
import CslibFrontier.Languages.Probabilistic.BitString
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum

/-!
# Tests for DDG trees and the Knuth–Yao entropy bounds

* A fair coin generates the uniform bit with exactly one expected flip.
* The dyadic distribution `(1/2, 1/4, 1/4)` is generated with `3/2 = H` expected flips.
* The non-dyadic distribution `(2/3, 1/3)` has Knuth–Yao cost exactly `2`, strictly above its
  entropy.
* A tree that never stops generates nothing and has infinite expected cost.
* `run` agrees with the `ProbComp` program that samples `n` fair bits and reads the tree.
-/

namespace CslibFrontierTests.KnuthYao

open scoped ENNReal
open Cslib Cslib.Probability Cslib.Probability.DDGTree

/-! ## The fair coin -/

/-- Fair coin: output the first bit. -/
def fairCoin : DDGTree Bool where
  output
    | [] => none
    | b :: _ => some b
  output_append_singleton w a b h := by
    cases w with
    | nil => simp at h
    | cons c w => simpa using h

theorem fairCoin_run_succ (n : ℕ) (o : Option Bool) :
    fairCoin.run (n + 1) o = if o = none then 0 else 2⁻¹ := by
  rw [run_succ, PMF.bind_apply, tsum_fintype (L := SummationFilter.unconditional _),
    Fintype.sum_bool, run_eq_pure_of_output_nil (a := true) rfl,
    run_eq_pure_of_output_nil (a := false) rfl]
  cases o with
  | none => simp
  | some b => cases b <;> simp

example : fairCoin.Generates (PMF.uniformOfFintype Bool) := by
  intro b
  refine le_antisymm (iSup_le fun n => ?_) ?_
  · cases n with
    | zero => simp [fairCoin]
    | succ n => simp [fairCoin_run_succ]
  · simpa [fairCoin_run_succ] using fairCoin.run_le_outputProb 1 b

example : fairCoin.expectedFlips = 1 := by
  rw [expectedFlips, tsum_eq_single 0]
  · simp [fairCoin]
  · intro n hn
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [fairCoin_run_succ]

/-! ## The dyadic distribution `(1/2, 1/4, 1/4)` -/

/-- The dyadic distribution `(1/2, 1/4, 1/4)`. -/
noncomputable def dyadic3 : PMF (Fin 3) :=
  PMF.ofFintype (fun i => 2⁻¹ ^ (if i = 0 then 1 else 2)) (by
    simp only [Fin.sum_univ_three, Fin.isValue, ite_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
      ite_false, Fin.reduceEq]
    rw [pow_one, add_assoc, ← two_mul, pow_two, ← mul_assoc,
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul,
      ENNReal.inv_two_add_inv_two])

example : (knuthYao dyadic3).expectedFlips = 3 / 2 := by
  have h : (3 / 2 : ℝ≥0∞) = ENNReal.ofReal (3 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [expectedFlips_knuthYao, h]
  congr 1
  simp only [dyadic3, PMF.ofFintype_apply, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, knuthYaoCost_inv_two_pow, Fin.sum_univ_three]
  norm_num

/-- The Knuth–Yao tree meets the entropy bound with equality on a dyadic distribution. -/
example : (knuthYao dyadic3).expectedFlips = ENNReal.ofReal (PMF.entropy dyadic3) :=
  (expectedFlips_knuthYao_eq_entropy_iff _).mpr fun _ _ => ⟨_, rfl⟩

/-! ## The non-dyadic distribution `(2/3, 1/3)` -/

/-- The distribution `(2/3, 1/3)` on `Bool`. -/
noncomputable def twoThirds : PMF Bool :=
  PMF.ofFintype (fun b => if b then 2 / 3 else 1 / 3) (by
    simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
    rw [← ENNReal.add_div, show (2 : ℝ≥0∞) + 1 = 3 by norm_num]
    exact ENNReal.div_self (by norm_num) (by simp))

private theorem three_not_dvd_two_pow (n : ℕ) : ¬ 3 ∣ 2 ^ n := by
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

private theorem floor_two_thirds_add (n : ℕ) :
    ⌊(2 : ℝ) ^ n * (2 / 3)⌋₊ + ⌊(2 : ℝ) ^ n * (1 / 3)⌋₊ + 1 = 2 ^ n := by
  have h1 : ⌊(2 : ℝ) ^ n * (2 / 3)⌋₊ = 2 * 2 ^ n / 3 := by
    rw [← Nat.floor_div_eq_div (K := ℝ)]
    push_cast; ring_nf
  have h2 : ⌊(2 : ℝ) ^ n * (1 / 3)⌋₊ = 2 ^ n / 3 := by
    rw [← Nat.floor_div_eq_div (K := ℝ)]
    push_cast; ring_nf
  rw [h1, h2]
  have := three_not_dvd_two_pow n
  omega

/-- After `n` flips the Knuth–Yao tree for `(2/3, 1/3)` is still running with probability `2⁻ⁿ`:
the binary expansions `0.101010…` and `0.010101…` have exactly one `1` at each position. -/
private theorem truncErr_twoThirds (n : ℕ) :
    truncErr (2 / 3) n + truncErr (1 / 3) n = 2⁻¹ ^ n := by
  have h := floor_two_thirds_add n
  have h' : (⌊(2 : ℝ) ^ n * (2 / 3)⌋₊ : ℝ) + ⌊(2 : ℝ) ^ n * (1 / 3)⌋₊ + 1 = 2 ^ n := by
    exact_mod_cast h
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hab : (⌊(2 : ℝ) ^ n * (2 / 3)⌋₊ : ℝ) / 2 ^ n + ⌊(2 : ℝ) ^ n * (1 / 3)⌋₊ / 2 ^ n =
      1 - (2 ^ n)⁻¹ := by
    rw [← add_div, div_eq_iff hpos.ne', sub_mul, inv_mul_cancel₀ hpos.ne', one_mul]
    linarith
  rw [truncErr, truncErr, inv_pow]
  linarith

private theorem expectedFlips_knuthYao_twoThirds : (knuthYao twoThirds).expectedFlips = 2 := by
  rw [expectedFlips_knuthYao]
  simp only [twoThirds, PMF.ofFintype_apply, Fintype.sum_bool, ite_true, Bool.false_eq_true,
    ite_false]
  rw [ENNReal.toReal_div, ENNReal.toReal_div]
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_one]
  rw [knuthYaoCost, knuthYaoCost, ← Summable.tsum_add (summable_truncErr (by norm_num))
    (summable_truncErr (by norm_num))]
  simp only [truncErr_twoThirds, tsum_geometric_inv_two]
  norm_num

/-- The Knuth–Yao tree for `(2/3, 1/3)` uses exactly `2` expected flips. -/
example : (knuthYao twoThirds).expectedFlips = 2 := expectedFlips_knuthYao_twoThirds

/-- No tree generates `(2/3, 1/3)` with fewer than `2` expected flips. -/
example {T : DDGTree Bool} (hT : T.Generates twoThirds) : 2 ≤ T.expectedFlips :=
  expectedFlips_knuthYao_twoThirds ▸ expectedFlips_knuthYao_le hT

/-- `(2/3, 1/3)` is not dyadic, so its entropy is strictly below the optimal cost `2`. -/
example : ENNReal.ofReal (PMF.entropy twoThirds) < 2 := by
  refine lt_of_le_of_ne (expectedFlips_knuthYao_twoThirds ▸
    entropy_le_expectedFlips (knuthYao_generates twoThirds)) fun h => ?_
  have hdy := (expectedFlips_knuthYao_eq_entropy_iff twoThirds).mp
    (expectedFlips_knuthYao_twoThirds.trans h.symm)
  obtain ⟨m, hm⟩ := hdy false (by simp [twoThirds])
  have hm' : (3 : ℝ≥0∞)⁻¹ = (2 ^ m)⁻¹ := by
    simpa [twoThirds, PMF.ofFintype_apply, ENNReal.inv_pow] using hm
  have h32 : (3 : ℝ≥0∞) = ((2 ^ m : ℕ) : ℝ≥0∞) := by
    rw [← inv_inj, hm']
    push_cast
    rfl
  have h32' : 3 = 2 ^ m := by exact_mod_cast h32
  exact three_not_dvd_two_pow m (h32' ▸ dvd_refl 3)

/-! ## Non-vacuity: a tree that never stops -/

/-- The tree that never reaches a leaf. -/
def never : DDGTree Bool where
  output _ := none
  output_append_singleton _ _ _ h := by simp at h

example (p : PMF Bool) : ¬ never.Generates p := by
  intro h
  have hzero : ∀ b, never.outputProb b = 0 := fun b => by
    simp [outputProb, run, never]
  have h1 := p.tsum_coe
  rw [tsum_fintype (L := SummationFilter.unconditional _), Fintype.sum_bool, ← h true,
    ← h false, hzero, hzero, add_zero] at h1
  exact zero_ne_one h1

example : never.expectedFlips = ⊤ :=
  never.expectedFlips_eq_top (by simp [run, never])

/-! ## Agreement with the fair-bit program model -/

/-- `run T n` is the law of the program that samples `n` fair bits and reads the tree. -/
example {α : Type} (T : DDGTree α) (n : ℕ) :
    ProbComp.eval (T.output <$> BitString.sampleList n) = T.run n := by
  simp [run]

end CslibFrontierTests.KnuthYao
