/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Tribes
public import Complexity.Foundations.BooleanAnalysis.Variance
import Complexity.Foundations.Data.BitString.AgreeExpect
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The influences of Tribes

Flipping bit `i₀` of tribe `j₀` changes the value of the Tribes function `Tribes_{w,s}` exactly
when the other bits of tribe `j₀` are `true` and every other tribe has a `false` bit
(`Cslib.BitString.tribes_update_ne_iff`). These events concern the separate tribes, which are
independent (`Cslib.BitString.expect_prod_tribe`), so every bit has influence
`2 ^ (-(w - 1)) (1 - 2 ^ (-w)) ^ (s - 1)` (`Cslib.BitString.influence_tribes`), the value computed
in the proof of [O'Donnell, Proposition 4.13][ODonnell2014]; the total influence is `s w` times this
(`Cslib.BitString.totalInfluence_tribes`).

For the nearly balanced choice `s = tribesSize w` of [O'Donnell, Definition 4.11][ODonnell2014] and
`n = s w` bits, O'Donnell states that each influence is `(ln n / n) (1 ± o(1))`
[O'Donnell, Proposition 4.13][ODonnell2014]. We prove the explicit non-asymptotic form
`log n / (4 n) ≤ Inf_k[Tribes] ≤ 6 log n / n` (`Cslib.BitString.log_div_le_influence_tribes`,
`Cslib.BitString.influence_tribes_le`), from `2 ^ (w - 1) ≤ s < 2 ^ w`; the constants `1 / 4` and
`6` are ours. Tribes then has variance at least `3 / 4` read as signs
(`Cslib.BitString.three_div_four_le_expect_sub_expect_sq_tribes`, with our constant), so every
influence is at most `8 Var log n / n` (`Cslib.BitString.influence_tribes_le_mul_log_div`). This is
the sense in which the Kahn–Kalai–Linial theorem
`Cslib.BitString.exists_expect_sub_expect_sq_mul_log_card_div_le_influence`, which finds an
influence of at least `Var log n / (12 n)`, is sharp up to the constant
[KahnKalaiLinial1988] [O'Donnell, Section 9.6][ODonnell2014]: no constant above `8` can replace
`1 / 12` for all large `n` (`Cslib.BitString.exists_forall_influence_lt_mul_log_div`). The
asymptotic `1 ± o(1)` form is not formalized.

## Main results

* `Cslib.BitString.tribes_update_ne_iff`: when a bit is pivotal for Tribes.
* `Cslib.BitString.influence_finProdFinEquiv_tribes`, `Cslib.BitString.influence_tribes`,
  `Cslib.BitString.totalInfluence_tribes`: the influences and total influence of Tribes.
* `Cslib.BitString.totalInfluence_tribes_le`: the nearly balanced Tribes on `s w` bits has total
  influence at most `2 w`.
* `Cslib.BitString.influence_tribes_le`, `Cslib.BitString.log_div_le_influence_tribes`: every
  influence of the nearly balanced Tribes on `n` bits lies in `[log n / (4 n), 6 log n / n]`.
* `Cslib.BitString.three_div_four_le_expect_sub_expect_sq_tribes`: its variance is at least
  `3 / 4`.
* `Cslib.BitString.influence_tribes_le_mul_log_div`,
  `Cslib.BitString.exists_forall_influence_lt_mul_log_div`: the Kahn–Kalai–Linial theorem is sharp
  up to the constant.

## References

* [J. Kahn, G. Kalai, N. Linial, *The influence of variables on Boolean
  functions*][KahnKalaiLinial1988]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

variable {w s : ℕ}

/-! ### Pivotal bits -/

/-- Tribes after setting bit `i₀` of tribe `j₀` to `b`: some other tribe is all `true`, or the
other bits of tribe `j₀` are `true` and `b` is. -/
private theorem tribes_update (x : BitString (s * w)) (j₀ : Fin s) (i₀ : Fin w) (b : Bool) :
    tribes w s (update x (finProdFinEquiv (j₀, i₀)) b) =
      decide ((∃ j ≠ j₀, ∀ i, x (finProdFinEquiv (j, i)) = true) ∨
        ((∀ i ≠ i₀, x (finProdFinEquiv (j₀, i)) = true) ∧ b = true)) := by
  rw [tribes]
  refine decide_eq_decide.2 ?_
  simp only [update_apply, finProdFinEquiv.injective.eq_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hj0 : j = j₀
    · subst hj0
      right
      exact ⟨fun i hi => by simpa [hi] using hj i, by simpa using hj i₀⟩
    · left
      exact ⟨j, hj0, fun i => by simpa [hj0] using hj i⟩
  · rintro (⟨j, hj0, hj⟩ | ⟨hB, hb⟩)
    · exact ⟨j, fun i => by simpa [hj0] using hj i⟩
    · refine ⟨j₀, fun i => ?_⟩
      by_cases hi : i = i₀
      · simp [hi, hb]
      · simp [hi, hB i hi]

/-- **Pivotality in Tribes**: flipping bit `i₀` of tribe `j₀` changes the value of Tribes exactly
when the other bits of tribe `j₀` are `true` and every other tribe has a `false` bit. -/
theorem tribes_update_ne_iff (x : BitString (s * w)) (j₀ : Fin s) (i₀ : Fin w) :
    tribes w s (update x (finProdFinEquiv (j₀, i₀)) (!x (finProdFinEquiv (j₀, i₀)))) ≠
        tribes w s x ↔
      (∀ i ≠ i₀, x (finProdFinEquiv (j₀, i)) = true) ∧
        ∀ j ≠ j₀, ∃ i, x (finProdFinEquiv (j, i)) = false := by
  conv_lhs => rhs; rw [← update_eq_self (finProdFinEquiv (j₀, i₀)) x]
  rw [tribes_update, tribes_update]
  have hA : (¬∃ j ≠ j₀, ∀ i, x (finProdFinEquiv (j, i)) = true) ↔
      ∀ j ≠ j₀, ∃ i, x (finProdFinEquiv (j, i)) = false := by
    simp only [not_exists, not_and, not_forall, Bool.not_eq_true]
  rw [← hA]
  cases x (finProdFinEquiv (j₀, i₀)) <;>
    by_cases h1 : ∃ j ≠ j₀, ∀ i, x (finProdFinEquiv (j, i)) = true <;>
    by_cases h2 : ∀ i ≠ i₀, x (finProdFinEquiv (j₀, i)) = true <;> simp [h1, h2]

/-! ### The influences -/

/-- **The influence of a bit on Tribes** [O'Donnell, proof of Proposition 4.13][ODonnell2014]:
bit `i₀` of tribe `j₀` has influence `2 ^ (-(w - 1)) (1 - 2 ^ (-w)) ^ (s - 1)` on `Tribes_{w,s}`,
the probability that the other bits of its tribe are `true` and every other tribe has a `false`
bit. -/
theorem influence_finProdFinEquiv_tribes (j₀ : Fin s) (i₀ : Fin w) :
    influence (finProdFinEquiv (j₀, i₀)) (fun x => signVal (tribes w s x)) =
      2⁻¹ ^ (w - 1) * (1 - 2⁻¹ ^ w) ^ (s - 1) := by
  set g : Fin s → (Fin w → Bool) → ℝ := fun j z =>
    if j = j₀ then (if ∀ i ∈ univ.erase i₀, z i = true then 1 else 0)
    else (if ∃ i ∈ univ, z i = false then 1 else 0) with hg
  have hpt (x : BitString (s * w)) :
      (if tribes w s (update x (finProdFinEquiv (j₀, i₀)) (!x (finProdFinEquiv (j₀, i₀)))) =
        tribes w s x then (0 : ℝ) else 1) = ∏ j, g j (fun i => x (finProdFinEquiv (j, i))) := by
    rw [← mul_prod_erase univ _ (mem_univ j₀)]
    simp only [hg, ite_true]
    rw [prod_congr rfl fun j hj => ite_eq_right (ne_of_mem_erase hj), prod_boole,
      ite_zero_mul_ite_zero, mul_one]
    have key := tribes_update_ne_iff x j₀ i₀
    simp only [ne_eq] at key
    simp only [mem_erase, ne_eq, mem_univ, and_true, true_and]
    split_ifs with h1 h2 h2
    · exact absurd h1 (key.2 ⟨h2.1, fun j hj => h2.2 j hj⟩)
    · rfl
    · rfl
    · exact absurd ⟨(key.1 h1).1, fun j hj => (key.1 h1).2 j hj⟩ h2
  have h0 : 𝔼 z, g j₀ z = 2⁻¹ ^ (w - 1) := by
    simp only [hg, ite_true]
    rw [expect_ite_forall_mem_eq, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have h1 (j : Fin s) (hj : j ≠ j₀) : 𝔼 z, g j z = 1 - 2⁻¹ ^ w := by
    simp only [hg, hj, ite_false]
    rw [expect_ite_exists_mem_eq, card_univ, Fintype.card_fin]
  rw [influence_signVal, expect_congr rfl fun x _ => hpt x, expect_prod_tribe,
    ← mul_prod_erase univ _ (mem_univ j₀), h0,
    prod_congr rfl fun j hj => h1 j (ne_of_mem_erase hj), prod_const,
    card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

/-- **The influences of Tribes** [O'Donnell, proof of Proposition 4.13][ODonnell2014]: every bit
has influence `2 ^ (-(w - 1)) (1 - 2 ^ (-w)) ^ (s - 1)` on `Tribes_{w,s}`. -/
theorem influence_tribes (k : Fin (s * w)) :
    influence k (fun x => signVal (tribes w s x)) = 2⁻¹ ^ (w - 1) * (1 - 2⁻¹ ^ w) ^ (s - 1) := by
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  exact influence_finProdFinEquiv_tribes j i

/-- **The total influence of Tribes**: `s w 2 ^ (-(w - 1)) (1 - 2 ^ (-w)) ^ (s - 1)`. -/
theorem totalInfluence_tribes (w s : ℕ) :
    totalInfluence (fun x => signVal (tribes w s x)) =
      (s * w : ℕ) * (2⁻¹ ^ (w - 1) * (1 - 2⁻¹ ^ w) ^ (s - 1)) := by
  rw [totalInfluence]
  simp only [influence_tribes]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Explicit bounds for the nearly balanced Tribes -/

private theorem one_sub_inv_two_pow_nonneg (w : ℕ) : 0 ≤ 1 - (2⁻¹ : ℝ) ^ w :=
  sub_nonneg.2 (pow_le_one₀ (by norm_num) (by norm_num))

private theorem one_sub_inv_two_pow_le_one (w : ℕ) : 1 - (2⁻¹ : ℝ) ^ w ≤ 1 :=
  sub_le_self _ (by positivity)

private theorem two_pow_eq_two_mul (hw : 1 ≤ w) : (2 : ℝ) ^ w = 2 * 2 ^ (w - 1) := by
  rw [← pow_succ']
  congr 1
  omega

/-- The nearly balanced Tribes on `s w` bits has total influence at most `2 w`. The bound is
ours. -/
theorem totalInfluence_tribes_le (w : ℕ) :
    totalInfluence (fun x => signVal (tribes w (tribesSize w) x)) ≤ 2 * w := by
  rw [totalInfluence_tribes]
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp
  have hA : (1 - (2⁻¹ : ℝ) ^ w) ^ (tribesSize w - 1) ≤ 1 :=
    pow_le_one₀ (one_sub_inv_two_pow_nonneg w) (one_sub_inv_two_pow_le_one w)
  have h2 : (tribesSize w : ℝ) < 2 ^ w := by exact_mod_cast tribesSize_lt_two_pow w
  have hpow := two_pow_eq_two_mul hw
  have hy : (2⁻¹ : ℝ) ^ (w - 1) * 2 ^ (w - 1) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [Nat.cast_mul]
  have hy0 : (0 : ℝ) ≤ 2⁻¹ ^ (w - 1) := by positivity
  have hsy : (tribesSize w : ℝ) * 2⁻¹ ^ (w - 1) ≤ 2 := by nlinarith
  calc (tribesSize w * w : ℝ) * (2⁻¹ ^ (w - 1) * (1 - 2⁻¹ ^ w) ^ (tribesSize w - 1))
      ≤ (tribesSize w * w : ℝ) * (2⁻¹ ^ (w - 1) * 1) := by gcongr
    _ = (tribesSize w * 2⁻¹ ^ (w - 1)) * w := by ring
    _ ≤ 2 * w := by gcongr

private theorem influence_tribes_le_of (hw : 2 ≤ w) (hs₁ : 2 ^ (w - 1) ≤ s) (hs₂ : s < 2 ^ w)
    (k : Fin (s * w)) :
    influence k (fun x => signVal (tribes w s x)) ≤ 6 * Real.log (s * w : ℕ) / (s * w : ℕ) := by
  have hinf : influence k (fun x => signVal (tribes w s x)) ≤ 2⁻¹ ^ (w - 1) := by
    rw [influence_tribes]
    exact mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (one_sub_inv_two_pow_nonneg w) (one_sub_inv_two_pow_le_one w))
  have hw' : (2 : ℝ) ≤ w := by exact_mod_cast hw
  have hN₁ : ((2 : ℝ) ^ (w - 1)) ≤ ((s * w : ℕ) : ℝ) := by
    have : 2 ^ (w - 1) ≤ s * w := hs₁.trans (Nat.le_mul_of_pos_right _ (by omega))
    exact_mod_cast this
  have hNpos : (0 : ℝ) < ((s * w : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hN₁
  have hyN : (2⁻¹ : ℝ) ^ (w - 1) * ((s * w : ℕ) : ℝ) ≤ 2 * w := by
    have h2 : (s : ℝ) < 2 ^ w := by exact_mod_cast hs₂
    have hpow := two_pow_eq_two_mul (show 1 ≤ w by omega)
    rw [Nat.cast_mul, inv_pow, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    nlinarith
  have hlog : ((w - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log ((s * w : ℕ) : ℝ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hN₁
  have hl2 := Real.log_two_gt_d9
  have hcast : ((w - 1 : ℕ) : ℝ) = w - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast] at hlog
  refine hinf.trans ?_
  rw [le_div_iff₀ hNpos]
  nlinarith

/-- **Upper bound on the influences of Tribes** [O'Donnell, Proposition 4.13][ODonnell2014], in
explicit form: on `n = s w` bits with `s = tribesSize w` and `w ≥ 2`, every bit has influence at
most `6 log n / n`. The constant is ours. -/
theorem influence_tribes_le (hw : 2 ≤ w) (k : Fin (tribesSize w * w)) :
    influence k (fun x => signVal (tribes w (tribesSize w) x)) ≤
      6 * Real.log (tribesSize w * w : ℕ) / (tribesSize w * w : ℕ) :=
  influence_tribes_le_of hw (two_pow_sub_one_le_tribesSize (by omega)) (tribesSize_lt_two_pow w) k

private theorem log_div_le_influence_tribes_of (hw : 1 ≤ w) (hs₁ : 2 ^ (w - 1) ≤ s)
    (hs₂ : s < 2 ^ w) (hq : 1 / 2 ≤ (1 - (2⁻¹ : ℝ) ^ w) ^ s) (k : Fin (s * w)) :
    Real.log (s * w : ℕ) / (4 * (s * w : ℕ)) ≤ influence k (fun x => signVal (tribes w s x)) := by
  have hA : 1 / 2 ≤ (1 - (2⁻¹ : ℝ) ^ w) ^ (s - 1) :=
    hq.trans (pow_le_pow_of_le_one (one_sub_inv_two_pow_nonneg w) (one_sub_inv_two_pow_le_one w)
      (Nat.sub_le _ _))
  rw [influence_tribes]
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hs₁' : (2 : ℝ) ^ (w - 1) ≤ s := by exact_mod_cast hs₁
  have hs₂' : (s : ℝ) < 2 ^ w := by exact_mod_cast hs₂
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le (by positivity) hs₁'
  have hNpos : (0 : ℝ) < ((s * w : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    positivity
  -- `log n ≤ 2 w - 1`
  have hlog : Real.log ((s * w : ℕ) : ℝ) ≤ 2 * w - 1 := by
    rw [Nat.cast_mul, Real.log_mul hspos.ne' (by positivity)]
    have h1 : Real.log s ≤ w * Real.log 2 := by
      rw [← Real.log_pow]
      exact Real.log_le_log hspos hs₂'.le
    have h2 : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      norm_num at this ⊢
      linarith
    nlinarith
  -- `w ≤ 2 ^ (-(w - 1)) n`
  have hyN : (w : ℝ) ≤ (2⁻¹ : ℝ) ^ (w - 1) * ((s * w : ℕ) : ℝ) := by
    rw [Nat.cast_mul, inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  have hy0 : (0 : ℝ) ≤ 2⁻¹ ^ (w - 1) := by positivity
  nlinarith

/-- **Lower bound on the influences of Tribes** [O'Donnell, Proposition 4.13][ODonnell2014], in
explicit form: on `n = s w` bits with `s = tribesSize w` and `w ≥ 1`, every bit has influence at
least `log n / (4 n)`. The constant is ours. -/
theorem log_div_le_influence_tribes (hw : 1 ≤ w) (k : Fin (tribesSize w * w)) :
    Real.log (tribesSize w * w : ℕ) / (4 * (tribesSize w * w : ℕ)) ≤
      influence k (fun x => signVal (tribes w (tribesSize w) x)) :=
  log_div_le_influence_tribes_of hw (two_pow_sub_one_le_tribesSize hw) (tribesSize_lt_two_pow w)
    (one_div_two_le_pow_tribesSize w) k

/-- The nearly balanced Tribes with `w ≥ 2` has variance at least `3 / 4`, read as signs. The
bound is ours. -/
theorem three_div_four_le_expect_sub_expect_sq_tribes (hw : 2 ≤ w) :
    3 / 4 ≤ 𝔼 x, (signVal (tribes w (tribesSize w) x) -
      𝔼 y, signVal (tribes w (tribesSize w) y)) ^ 2 := by
  rw [expect_sub_expect_sq_signVal]
  have hb := abs_expect_bitVal_tribes_sub_half_le (one_div_two_le_pow_tribesSize w)
    (pow_tribesSize_add_one_lt_one_div_two w)
  have hw4 : (2⁻¹ : ℝ) ^ w ≤ 1 / 4 := by
    calc (2⁻¹ : ℝ) ^ w ≤ 2⁻¹ ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hw
      _ = 1 / 4 := by norm_num
  have he : 𝔼 x, signVal (tribes w (tribesSize w) x) =
      1 - 2 * 𝔼 x, bitVal ℝ (tribes w (tribesSize w) x) := by
    simp only [signVal_eq_one_sub_two_mul_bitVal]
    rw [expect_sub_distrib, Fintype.expect_const, ← mul_expect]
  rw [he]
  have := abs_le.1 (hb.trans hw4)
  nlinarith

/-! ### Sharpness of the Kahn–Kalai–Linial theorem -/

/-- **Tribes witnesses the sharpness of KKL** [O'Donnell, Section 9.6][ODonnell2014]: on `n = s w`
bits with `s = tribesSize w` and `w ≥ 2`, every influence of Tribes is at most `8 Var log n / n`,
against the influence of at least `Var log n / (12 n)` that
`Cslib.BitString.exists_expect_sub_expect_sq_mul_log_card_div_le_influence` provides for every
Boolean function. The constant `8` is ours. -/
theorem influence_tribes_le_mul_log_div (hw : 2 ≤ w) (k : Fin (tribesSize w * w)) :
    influence k (fun x => signVal (tribes w (tribesSize w) x)) ≤
      8 * (𝔼 x, (signVal (tribes w (tribesSize w) x) -
        𝔼 y, signVal (tribes w (tribesSize w) y)) ^ 2) *
        Real.log (tribesSize w * w : ℕ) / (tribesSize w * w : ℕ) := by
  refine (influence_tribes_le hw k).trans ?_
  have hV := three_div_four_le_expect_sub_expect_sq_tribes hw
  have hlog : 0 ≤ Real.log ((tribesSize w * w : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hN : (0 : ℝ) < (tribesSize w * w : ℕ) := by
    have : 0 < tribesSize w * w :=
      Nat.mul_pos (lt_of_lt_of_le Nat.one_le_two_pow (two_pow_sub_one_le_tribesSize (by omega)))
        (by omega)
    exact_mod_cast this
  rw [div_le_div_iff_of_pos_right hN]
  nlinarith

/-- **The constant in KKL is at most `8`**: for every `c > 8` and every `n₀` there are `n ≥ n₀` and
a Boolean function on `n` bits all of whose influences are less than `c Var log n / n`, so no
constant above `8` can replace `1 / 12` in
`Cslib.BitString.exists_expect_sub_expect_sq_mul_log_card_div_le_influence` for all large `n`
[KahnKalaiLinial1988] [O'Donnell, Section 9.6][ODonnell2014]. The constant `8` is ours. -/
theorem exists_forall_influence_lt_mul_log_div {c : ℝ} (hc : 8 < c) (n₀ : ℕ) :
    ∃ (n : ℕ) (f : BitString n → Bool), n₀ ≤ n ∧ ∀ k,
      influence k (fun x => signVal (f x)) <
        c * (𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) * Real.log n / n := by
  set w := n₀ + 2
  have hw : 2 ≤ w := by omega
  have hs : 1 ≤ tribesSize w :=
    le_trans Nat.one_le_two_pow (two_pow_sub_one_le_tribesSize (by omega))
  have hN : 2 ≤ tribesSize w * w := le_trans hw (Nat.le_mul_of_pos_left _ hs)
  refine ⟨tribesSize w * w, tribes w (tribesSize w), ?_, fun k => ?_⟩
  · exact le_trans (by omega) (Nat.le_mul_of_pos_left _ hs)
  · refine lt_of_le_of_lt (influence_tribes_le_mul_log_div hw k) ?_
    have hV := three_div_four_le_expect_sub_expect_sq_tribes hw
    have hN' : (2 : ℝ) ≤ (tribesSize w * w : ℕ) := by exact_mod_cast hN
    have hlog : 0 < Real.log ((tribesSize w * w : ℕ) : ℝ) := Real.log_pos (by linarith)
    rw [div_lt_div_iff_of_pos_right (by linarith)]
    have : 0 < (𝔼 x, (signVal (tribes w (tribesSize w) x) -
        𝔼 y, signVal (tribes w (tribesSize w) y)) ^ 2) * Real.log (tribesSize w * w : ℕ) := by
      positivity
    nlinarith

end Cslib.BitString
