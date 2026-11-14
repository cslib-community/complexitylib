/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.Data.BitString.Single
import Mathlib.Tactic.LinearCombination

/-!
# Odd-parity forms on the cube

For `f : (ι → Bool) → ℝ`, the odd-parity form `oddForm f S = ∑_c f(c) [S · c odd]` sums `f`
over the points whose parity on `S` is odd. Writing `[S · c odd] = (1 - χ_S(c)) / 2` and summing
characters over all sets gives the identities
`2 ∑_S L_f(S) = 2 ^ |ι| (∑ f - f 0)` and
`4 ∑_S L_f(S) L_h(S) = 2 ^ |ι| ((F - f 0)(H - h 0) + ∑_c f c h c - f 0 h 0)`.
The functions `onSingles a`, supported on the unit vectors recognized by `BitString.IsSingle`,
have
`oddForm (onSingles a) S = ∑_{i ∈ S} a i`.

These are used for the sharper score of Andreev's function
(`WeightedThreshold.AndreevSharpScore`).

## Main definitions

* `Cslib.BitString.oddForm`: odd-parity forms.
* `Cslib.BitString.onSingles`: functions supported on unit vectors;
  `Cslib.BitString.not_isSingle_zero`.

## Main results

* `Cslib.BitString.four_mul_sum_toNat_parityOn_mul`: four times the number of sets on which two
  points are both odd.
* `Cslib.BitString.two_mul_sum_oddForm`, `Cslib.BitString.four_mul_sum_oddForm_mul_oddForm`: sums
  of odd-parity forms and their products over all sets.
* `Cslib.BitString.parityOn_single`, `Cslib.BitString.oddForm_onSingles`: parities of unit vectors.
-/

@[expose] public section

namespace Cslib.BitString

open Finset

/-! ### Odd-parity forms and their character sums -/

section OddForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- The indicator `[S · c odd]` is `(1 - χ_S(c)) / 2`. -/
theorem two_mul_toNat_parityOn (S : Finset ι) (c : ι → Bool) :
    2 * ((parityOn S c).toNat : ℝ) = 1 - chi ℝ S c := by
  rw [chi_eq_signVal_parityOn]
  cases parityOn S c <;> norm_num [signVal]

omit [DecidableEq ι] in
/-- Summed over all sets, the characters at `c` detect `c = 0`. -/
theorem sum_chi_eq_ite (c : ι → Bool) :
    ∑ S, chi ℝ S c = if c = 0 then 2 ^ Fintype.card ι else 0 := by
  simpa only [chi_zero, mul_one] using sum_chi_mul_chi c 0

omit [DecidableEq ι] in
/-- **Pair counts of odd sets.** The number of sets `S` with both `S · c` and `S · d` odd,
times four, is `2 ^ |ι| * (1 - [c = 0] - [d = 0] + [c = d])`. -/
theorem four_mul_sum_toNat_parityOn_mul (c d : ι → Bool) :
    4 * ∑ S, ((parityOn S c).toNat : ℝ) * (parityOn S d).toNat =
      2 ^ Fintype.card ι * (1 - (if c = 0 then 1 else 0) - (if d = 0 then 1 else 0) +
        (if c = d then 1 else 0)) := by
  have h (S : Finset ι) : 4 * (((parityOn S c).toNat : ℝ) * (parityOn S d).toNat) =
      1 - chi ℝ S c - chi ℝ S d + chi ℝ S (c + d) := by
    rw [chi_add]
    linear_combination (2 * ((parityOn S d).toNat : ℝ)) * two_mul_toNat_parityOn S c +
      (1 - chi ℝ S c) * two_mul_toNat_parityOn S d
  rw [mul_sum, sum_congr rfl fun S _ => h S, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
    sum_chi_eq_ite, sum_chi_eq_ite, sum_chi_eq_ite]
  have hcd : c + d = 0 ↔ c = d := by
    simp only [funext_iff, Pi.add_apply, Pi.zero_apply, BooleanRing.add_eq_zero']
  simp only [sum_const, card_univ, Fintype.card_finset, nsmul_eq_mul, mul_one, Nat.cast_pow,
    Nat.cast_ofNat, hcd]
  split_ifs <;> ring

omit [DecidableEq ι] in
/-- The number of sets `S` with `S · c` odd, times two, is `2 ^ |ι| * (1 - [c = 0])`. -/
theorem two_mul_sum_toNat_parityOn (c : ι → Bool) :
    2 * ∑ S, ((parityOn S c).toNat : ℝ) = 2 ^ Fintype.card ι * (1 - if c = 0 then 1 else 0) := by
  rw [mul_sum, sum_congr rfl fun S _ => two_mul_toNat_parityOn S c, sum_sub_distrib,
    sum_chi_eq_ite]
  simp only [sum_const, card_univ, Fintype.card_finset, nsmul_eq_mul, mul_one, Nat.cast_pow,
    Nat.cast_ofNat]
  split_ifs <;> ring

/-- The odd-parity form `L_f(S) = ∑_c f(c) [S · c odd]` of a function on the cube. -/
def oddForm (f : (ι → Bool) → ℝ) (S : Finset ι) : ℝ :=
  ∑ c, f c * (parityOn S c).toNat

/-- **Sum of an odd-parity form** over all sets. -/
theorem two_mul_sum_oddForm (f : (ι → Bool) → ℝ) :
    2 * ∑ S, oddForm f S = 2 ^ Fintype.card ι * (∑ c, f c - f 0) := by
  have hexp : 2 * ∑ S, oddForm f S =
      ∑ c, f c * (2 * ∑ S, ((parityOn S c).toNat : ℝ)) := by
    simp only [oddForm, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun c _ => sum_congr rfl fun S _ => by ring
  rw [hexp]
  simp_rw [two_mul_sum_toNat_parityOn]
  have h (c : ι → Bool) : f c * (2 ^ Fintype.card ι * (1 - if c = 0 then (1 : ℝ) else 0)) =
      2 ^ Fintype.card ι * f c - if c = 0 then 2 ^ Fintype.card ι * f 0 else 0 := by
    split_ifs with hc <;> [subst hc; skip] <;> ring
  simp_rw [h, sum_sub_distrib, sum_ite_eq', mem_univ, ite_true, ← mul_sum]
  ring

/-- **Bilinear character sum.** For functions `f, h` on the cube,
`4 ∑_S L_f(S) L_h(S) = 2 ^ |ι| ((F - f 0)(H - h 0) + ∑_c f c h c - f 0 h 0)` with `F = ∑ f` and
`H = ∑ h`. -/
theorem four_mul_sum_oddForm_mul_oddForm (f h : (ι → Bool) → ℝ) :
    4 * ∑ S, oddForm f S * oddForm h S =
      2 ^ Fintype.card ι * ((∑ c, f c - f 0) * (∑ c, h c - h 0) + ∑ c, f c * h c - f 0 * h 0) := by
  have hexp : 4 * ∑ S, oddForm f S * oddForm h S =
      ∑ c, ∑ d, f c * h d * (4 * ∑ S, ((parityOn S c).toNat : ℝ) * (parityOn S d).toNat) := by
    calc 4 * ∑ S, oddForm f S * oddForm h S
        = ∑ S, ∑ c, ∑ d, f c * h d * (4 * (((parityOn S c).toNat : ℝ) * (parityOn S d).toNat)) := by
          rw [mul_sum]
          refine sum_congr rfl fun S _ => ?_
          rw [oddForm, oddForm, sum_mul_sum, mul_sum]
          exact sum_congr rfl fun c _ => by
            rw [mul_sum]; exact sum_congr rfl fun d _ => by ring
      _ = _ := by
          rw [sum_comm]
          refine sum_congr rfl fun c _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun d _ => ?_
          simp only [mul_sum]
  rw [hexp]
  simp_rw [four_mul_sum_toNat_parityOn_mul]
  set N : ℝ := 2 ^ Fintype.card ι
  have h1 (c d : ι → Bool) : f c * h d * (N * (1 - (if c = 0 then 1 else 0) -
      (if d = 0 then 1 else 0) + (if c = d then 1 else 0))) =
      N * (f c * h d) - (if 0 = c then N * (f c * h d) else 0) -
        (if 0 = d then N * (f c * h d) else 0) + (if c = d then N * (f c * h d) else 0) := by
    simp only [eq_comm (a := (0 : ι → Bool))]
    split_ifs <;> ring
  simp_rw [h1, sum_add_distrib, sum_sub_distrib, sum_ite_eq, mem_univ, ite_true]
  simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ, ite_true]
  simp only [← mul_sum, ← sum_mul]
  ring

end OddForm


/-! ### Unit vectors and functions supported on them -/

section Single

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The parity of `Pi.single i true` on `S` is membership of `i` in `S`. -/
theorem parityOn_single (S : Finset ι) (i : ι) :
    parityOn S (Pi.single i true) = decide (i ∈ S) := by
  have hf : ({j ∈ S | (Pi.single i true : ι → Bool) j = true} : Finset ι) =
      if i ∈ S then {i} else ∅ := by
    ext j
    by_cases hji : j = i <;> split_ifs with hi <;> simp [Pi.single_apply, hji] <;> grind
  rw [parityOn, hf]
  split_ifs with hi <;> simp [hi]

/-- The function that takes the value `a i` at the unit vector `Pi.single i true` and `0`
elsewhere. -/
def onSingles (a : ι → ℝ) (c : ι → Bool) : ℝ :=
  ∑ i, if c = Pi.single i true then a i else 0

/-- `onSingles a` takes the value `a i` at `Pi.single i true`. -/
@[simp]
theorem onSingles_single (a : ι → ℝ) (i : ι) : onSingles a (Pi.single i true) = a i := by
  simp [onSingles, Pi.single_left_inj (show (true : Bool) ≠ 0 by decide), eq_comm (a := i)]

/-- `onSingles a` vanishes off the unit vectors. -/
theorem onSingles_of_not_isSingle (a : ι → ℝ) {c : ι → Bool} (hc : ¬IsSingle c) :
    onSingles a c = 0 :=
  sum_eq_zero fun i _ => ite_eq_right_iff.mpr fun h => (hc ⟨i, h⟩).elim

omit [Fintype ι] in
/-- The zero vector is not a unit vector. -/
theorem not_isSingle_zero : ¬IsSingle (0 : ι → Bool) :=
  fun ⟨_, h⟩ => Pi.single_ne_zero_iff.mpr (by decide) h.symm

/-- `onSingles a` vanishes at the zero vector. -/
@[simp]
theorem onSingles_zero (a : ι → ℝ) : onSingles a 0 = 0 :=
  onSingles_of_not_isSingle a not_isSingle_zero

/-- Summing against `onSingles a` evaluates at the unit vectors. -/
theorem sum_onSingles_mul (a : ι → ℝ) (F : (ι → Bool) → ℝ) :
    ∑ c, onSingles a c * F c = ∑ i, a i * F (Pi.single i true) := by
  simp only [onSingles, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp

/-- The indicator of unit vectors is `onSingles 1`. -/
theorem ite_isSingle_eq_onSingles (c : ι → Bool) :
    (if IsSingle c then (1 : ℝ) else 0) = onSingles 1 c := by
  split_ifs with hc
  · obtain ⟨i, rfl⟩ := hc
    simp
  · rw [onSingles_of_not_isSingle _ hc]

/-- The odd-parity form of `onSingles a` is the sum `∑_{i ∈ S} a i`. -/
theorem oddForm_onSingles (a : ι → ℝ) (S : Finset ι) :
    oddForm (onSingles a) S = ∑ i ∈ S, a i := by
  rw [oddForm, sum_onSingles_mul]
  have h (i : ι) : a i * ((decide (i ∈ S)).toNat : ℝ) = if i ∈ S then a i else 0 := by
    split_ifs <;> simp [*]
  simp only [parityOn_single, h, sum_ite_mem, univ_inter]

end Single

end Cslib.BitString
