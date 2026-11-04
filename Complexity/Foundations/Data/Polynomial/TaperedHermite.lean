/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Polynomial.HermiteInterpolation
public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat

/-!
# Two-adic size of tapered Hermite basis values

The tapered Hermite recovery of [OpenAI2026ETH, Lemma D.5, §D.4.4, pp. 60–61] interpolates on the
dyadic grid `S = [-2 ^ a, 2 ^ a)`, a complete residue system modulo `2 ^ (a + 1)`. The nodes are
the points `q ≠ 0` of `S`, and the multiplicity of `q` depends only on its 2-adic valuation,
`q_q = m (v₂ q)`. Its precision analysis needs a lower bound on the 2-adic valuation of the
Hermite basis values `E_t(0) = ∏_{q ∈ S \ {0, t}} (-q / (t - q)) ^ m (v₂ q)` of the
Chinese-remainder form (D.9) (`Polynomial.eval_eq_sum_hermiteBasis_mul_hermiteQuotient`).

For a node `t` of valuation `i`,
`v₂ (E_t(0)) = ∑_{i < j ≤ a} 2 ^ (a - j) (j - i) (m j - m i)`
(`Polynomial.padicValRat_eval_zero_hermiteBasis_dyadic`), the middle expression of (D.10). The
proof pairs `q` with the reflection of `t - q` into the grid: points of valuation below `i`
contribute `0`, and the points of valuation `i` cancel the `i`-part of those above `i`. Counting
the points of each valuation on the grid (`sum_Ico_erase_zero_padicValInt_two`) gives
the closed form. If `m` drops by at most `h` per level, as the taper `m i = h * max(0, u - i)`
does, then `v₂ (E_t(0)) ≥ -6 h 2 ^ (a - i)`, since `∑_{j ≥ 1} j ^ 2 / 2 ^ j = 6`
(`Polynomial.neg_le_padicValRat_eval_zero_hermiteBasis_dyadic`,
`Polynomial.neg_le_padicValRat_eval_zero_hermiteBasis_taper`). This is (D.10), with
`D = 2 ^ (a - i) = L / 2 ^ i` for `L = 2 ^ a`.

`E_t(0)` is rational, so this uses `padicValRat` and needs no valuation on the coefficient ring of
Lemma D.5.

## Main results

* `padicValRat.prod`: the `p`-adic valuation of a product of nonzero rationals.
* `sum_Ico_erase_zero_padicValInt_two`: the valuation `j ≤ a` occurs `2 ^ (a - j)`
  times on the nonzero points of `[-2 ^ a, 2 ^ a)`.
* `Polynomial.padicValRat_eval_zero_hermiteBasis_dyadic`: the exact valuation of `E_t(0)`.
* `Polynomial.neg_le_padicValRat_eval_zero_hermiteBasis_dyadic`,
  `Polynomial.neg_le_padicValRat_eval_zero_hermiteBasis_taper`: the bound (D.10).

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
-/

public section

open Finset

/-- The `p`-adic valuation of a finite product of nonzero rationals is the sum of the
valuations. -/
theorem padicValRat.prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) {f : ι → ℚ}
    (hf : ∀ i ∈ s, f i ≠ 0) : padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, sum_insert hj,
      padicValRat.mul (hf j (mem_insert_self j s))
        (prod_ne_zero_iff.mpr fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

namespace Polynomial

/-! ### Two-adic valuations of integers -/

/-- The 2-adic valuation of `x` is `n` when `2 ^ n`, but not `2 ^ (n + 1)`, divides `x`. -/
private theorem padicValInt_two_eq {x : ℤ} {n : ℕ} (h1 : (2 : ℤ) ^ n ∣ x)
    (h2 : ¬(2 : ℤ) ^ (n + 1) ∣ x) : padicValInt 2 x = n := by
  have hx : x ≠ 0 := by rintro rfl; exact h2 (dvd_zero _)
  have hle : n ≤ padicValInt 2 x :=
    ((padicValInt_dvd_iff (p := 2) n x).mp (by exact_mod_cast h1)).resolve_left hx
  have hlt : ¬n + 1 ≤ padicValInt 2 x := fun h =>
    h2 (by exact_mod_cast (padicValInt_dvd_iff (p := 2) (n + 1) x).mpr (Or.inr h))
  omega

private theorem two_pow_padicValInt_dvd (x : ℤ) : (2 : ℤ) ^ padicValInt 2 x ∣ x := by
  exact_mod_cast padicValInt_dvd (p := 2) x

private theorem not_two_pow_succ_padicValInt_dvd {x : ℤ} (hx : x ≠ 0) :
    ¬(2 : ℤ) ^ (padicValInt 2 x + 1) ∣ x := fun h => by
  have := ((padicValInt_dvd_iff (p := 2) (padicValInt 2 x + 1) x).mp
    (by exact_mod_cast h)).resolve_left hx
  omega

private theorem le_padicValInt_two {x : ℤ} {n : ℕ} (hx : x ≠ 0) (h : (2 : ℤ) ^ n ∣ x) :
    n ≤ padicValInt 2 x :=
  ((padicValInt_dvd_iff (p := 2) n x).mp (by exact_mod_cast h)).resolve_left hx

/-- A nonzero integer of absolute value less than `2 ^ n` has 2-adic valuation less than `n`. -/
private theorem padicValInt_two_lt {x : ℤ} {n : ℕ} (hx : x ≠ 0) (h : x.natAbs < 2 ^ n) :
    padicValInt 2 x < n := by
  have h2 : 2 ^ padicValInt 2 x ∣ x.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr (two_pow_padicValInt_dvd x)
    rwa [Int.natAbs_pow] at this
  exact (pow_lt_pow_iff_right₀ (by norm_num : 1 < 2)).mp
    ((Nat.le_of_dvd (Int.natAbs_pos.mpr hx) h2).trans_lt h)

/-- Adding a multiple of `2 ^ n` to a nonzero integer of absolute value less than `2 ^ n` keeps
its 2-adic valuation. -/
private theorem padicValInt_two_add_mul {x : ℤ} {n : ℕ} (hx : x ≠ 0) (h : x.natAbs < 2 ^ n)
    (c : ℤ) : padicValInt 2 (x + 2 ^ n * c) = padicValInt 2 x := by
  have hlt := padicValInt_two_lt hx h
  refine padicValInt_two_eq (dvd_add (two_pow_padicValInt_dvd x)
    (dvd_mul_of_dvd_left (pow_dvd_pow 2 hlt.le) c)) fun hd => ?_
  refine not_two_pow_succ_padicValInt_dvd hx ?_
  have := dvd_sub hd (dvd_mul_of_dvd_left (pow_dvd_pow 2 (Nat.succ_le_of_lt hlt)) c)
  rwa [add_sub_cancel_right] at this

/-- If `v₂ x < v₂ y` then `x - y` and `y - x` have the valuation of `x`. -/
private theorem padicValInt_two_sub_of_lt {x y : ℤ} (hx : x ≠ 0)
    (h : padicValInt 2 x < padicValInt 2 y) :
    padicValInt 2 (x - y) = padicValInt 2 x ∧ padicValInt 2 (y - x) = padicValInt 2 x := by
  have hy : (2 : ℤ) ^ (padicValInt 2 x + 1) ∣ y :=
    (pow_dvd_pow 2 (Nat.succ_le_of_lt h)).trans (two_pow_padicValInt_dvd y)
  have hx1 := two_pow_padicValInt_dvd x
  have hx2 := not_two_pow_succ_padicValInt_dvd hx
  refine ⟨padicValInt_two_eq (dvd_sub hx1 ((pow_dvd_pow 2 (Nat.le_succ _)).trans hy))
    fun hd => hx2 ?_, padicValInt_two_eq (dvd_sub ((pow_dvd_pow 2 (Nat.le_succ _)).trans hy) hx1)
    fun hd => hx2 ?_⟩
  · have := dvd_add hd hy; rwa [sub_add_cancel] at this
  · have := dvd_sub hy hd; rwa [sub_sub_cancel] at this

/-- Two integers of the same 2-adic valuation `i` differ by a multiple of `2 ^ (i + 1)`. -/
private theorem two_pow_succ_dvd_sub {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : padicValInt 2 x = padicValInt 2 y) : (2 : ℤ) ^ (padicValInt 2 x + 1) ∣ x - y := by
  have hdx := two_pow_padicValInt_dvd x
  have hdy := two_pow_padicValInt_dvd y
  have hnx := not_two_pow_succ_padicValInt_dvd hx
  have hny := not_two_pow_succ_padicValInt_dvd hy
  rw [← h] at hdy hny
  generalize padicValInt 2 x = i at hdx hnx hdy hny ⊢
  obtain ⟨x', rfl⟩ := hdx
  obtain ⟨y', rfl⟩ := hdy
  have hox : ¬(2 : ℤ) ∣ x' := fun ⟨c, hc⟩ => hnx ⟨c, by rw [hc, pow_succ]; ring⟩
  have hoy : ¬(2 : ℤ) ∣ y' := fun ⟨c, hc⟩ => hny ⟨c, by rw [hc, pow_succ]; ring⟩
  obtain ⟨c, hc⟩ : (2 : ℤ) ∣ x' - y' := by omega
  exact ⟨c, by rw [pow_succ, mul_assoc, ← hc, mul_sub]⟩

/-! ### The dyadic grid -/

/-- The 2-adic valuation of `2 x` is one more than that of a nonzero `x`. -/
private theorem padicValInt_two_mul {x : ℤ} (hx : x ≠ 0) :
    padicValInt 2 (2 * x) = padicValInt 2 x + 1 := by
  rw [padicValInt.mul two_ne_zero hx, add_comm, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl,
    padicValInt.self (by norm_num)]

private theorem natAbs_sub_lt {a : ℕ} {t q : ℤ} (ht : t ∈ Ico (-(2 : ℤ) ^ a) (2 ^ a))
    (hq : q ∈ Ico (-(2 : ℤ) ^ a) (2 ^ a)) : (t - q).natAbs < 2 ^ (a + 1) := by
  rw [mem_Ico] at ht hq
  have : |t - q| < (2 : ℤ) ^ (a + 1) := by
    rw [abs_lt, pow_succ]
    constructor <;> omega
  rw [← Int.natCast_natAbs] at this
  exact_mod_cast this

/-- **The distribution of 2-adic valuations on the dyadic grid.** On the nonzero points of
`[-2 ^ a, 2 ^ a)`, the valuation `j ≤ a` occurs `2 ^ (a - j)` times. -/
theorem _root_.sum_Ico_erase_zero_padicValInt_two (a : ℕ) (f : ℕ → ℤ) :
    ∑ q ∈ (Ico (-(2 : ℤ) ^ a) (2 ^ a)).erase 0, f (padicValInt 2 q) =
      ∑ j ∈ range (a + 1), 2 ^ (a - j) * f j := by
  induction a generalizing f with
  | zero =>
    rw [show (Ico (-(2 : ℤ) ^ 0) (2 ^ 0)).erase 0 = {-1} by
      ext q; simp only [mem_erase, mem_Ico, mem_singleton]; omega, sum_singleton,
      padicValInt.eq_zero_of_not_dvd (by norm_num), sum_range_one, pow_zero, one_mul]
  | succ a ih =>
    have hpow : (2 : ℤ) ^ (a + 1) = 2 * 2 ^ a := by rw [pow_succ, mul_comm]
    rw [← sum_filter_add_sum_filter_not _ (fun q : ℤ => (2 : ℤ) ∣ q)]
    -- even points are `2 q` for nonzero `q ∈ [-2 ^ a, 2 ^ a)`
    have heven : ∑ q ∈ ((Ico (-(2 : ℤ) ^ (a + 1)) (2 ^ (a + 1))).erase 0).filter
        (fun q : ℤ => (2 : ℤ) ∣ q), f (padicValInt 2 q) =
        ∑ q ∈ (Ico (-(2 : ℤ) ^ a) (2 ^ a)).erase 0, f (padicValInt 2 q + 1) := by
      refine sum_nbij' (fun q => q / 2) (fun q => 2 * q) (fun q hq => ?_) (fun q hq => ?_)
        (fun q hq => ?_) (fun q hq => ?_) (fun q hq => ?_)
      all_goals simp only [mem_filter, mem_erase, mem_Ico, hpow] at hq ⊢
      · omega
      · omega
      · omega
      · omega
      · obtain ⟨⟨hq0, -⟩, hq2⟩ := hq
        rw [← padicValInt_two_mul (by omega), Int.mul_ediv_cancel' hq2]
    -- odd points have valuation `0`; there are `2 ^ (a + 1)` of them
    have hodd : ∑ q ∈ ((Ico (-(2 : ℤ) ^ (a + 1)) (2 ^ (a + 1))).erase 0).filter
        (fun q : ℤ => ¬(2 : ℤ) ∣ q), f (padicValInt 2 q) = 2 ^ (a + 1) * f 0 := by
      rw [sum_congr rfl fun q hq => by
        rw [padicValInt.eq_zero_of_not_dvd (by exact_mod_cast (mem_filter.mp hq).2)], sum_const,
        nsmul_eq_mul]
      congr 1
      have hcard : #(((Ico (-(2 : ℤ) ^ (a + 1)) (2 ^ (a + 1))).erase 0).filter
          (fun q : ℤ => ¬(2 : ℤ) ∣ q)) = #(Ico (-(2 : ℤ) ^ a) (2 ^ a)) := by
        refine card_nbij' (fun q => (q - 1) / 2) (fun q => 2 * q + 1) (fun q hq => ?_)
          (fun q hq => ?_) (fun q hq => ?_) (fun q hq => ?_)
        all_goals simp only [coe_filter, mem_erase, mem_Ico, Set.mem_ofPred_eq, coe_Ico,
          Set.mem_Ico, hpow] at hq ⊢
        all_goals omega
      rw [hcard, Int.card_Ico, show (2 : ℤ) ^ a - -2 ^ a = ((2 ^ (a + 1) : ℕ) : ℤ) by
        push_cast; ring, Int.toNat_natCast]
      push_cast
      rfl
    rw [heven, hodd, ih fun j => f (j + 1), sum_range_succ' _ (a + 1), Nat.sub_zero]
    simp only [Nat.add_sub_add_right]

/-- The reflection `q ↦ t - q` of the grid `[-L, L)`, reduced modulo `2 L` back into the grid. -/
private def gridFlip (L t q : ℤ) : ℤ :=
  if t - q < -L then t - q + 2 * L else if t - q < L then t - q else t - q - 2 * L

section gridFlip

variable {L t q : ℤ}

private theorem gridFlip_mem (ht : t ∈ Ico (-L) L) (hq : q ∈ Ico (-L) L) :
    gridFlip L t q ∈ Ico (-L) L := by
  rw [mem_Ico] at ht hq ⊢
  unfold gridFlip
  split_ifs <;> omega

private theorem gridFlip_gridFlip (ht : t ∈ Ico (-L) L) (hq : q ∈ Ico (-L) L) :
    gridFlip L t (gridFlip L t q) = q := by
  rw [mem_Ico] at ht hq
  unfold gridFlip
  split_ifs <;> omega

private theorem gridFlip_eq_zero_iff (ht : t ∈ Ico (-L) L) (hq : q ∈ Ico (-L) L) :
    gridFlip L t q = 0 ↔ q = t := by
  rw [mem_Ico] at ht hq
  unfold gridFlip
  split_ifs <;> omega

private theorem gridFlip_eq_self_iff (ht : t ∈ Ico (-L) L) (hq : q ∈ Ico (-L) L) :
    gridFlip L t q = t ↔ q = 0 := by
  rw [mem_Ico] at ht hq
  unfold gridFlip
  split_ifs <;> omega

private theorem exists_gridFlip_eq (L t q : ℤ) : ∃ c : ℤ, gridFlip L t q = t - q + 2 * L * c := by
  unfold gridFlip
  split_ifs
  · exact ⟨1, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨-1, by ring⟩

end gridFlip

section Dyadic

variable {a : ℕ} {t q : ℤ}

/-- On the dyadic grid, the reflection of `q ≠ t` has the valuation of `t - q`. -/
private theorem padicValInt_gridFlip (ht : t ∈ Ico (-(2 : ℤ) ^ a) (2 ^ a))
    (hq : q ∈ Ico (-(2 : ℤ) ^ a) (2 ^ a)) (hqt : q ≠ t) :
    padicValInt 2 (gridFlip (2 ^ a) t q) = padicValInt 2 (t - q) := by
  obtain ⟨c, hc⟩ := exists_gridFlip_eq (2 ^ a) t q
  rw [hc, show 2 * (2 : ℤ) ^ a * c = 2 ^ (a + 1) * c by ring]
  exact padicValInt_two_add_mul (sub_ne_zero.mpr hqt.symm) (natAbs_sub_lt ht hq) c

/-- On the dyadic grid, `t` minus the reflection of `q ≠ 0` has the valuation of `q`. -/
private theorem padicValInt_sub_gridFlip (ht : t ∈ Ico (-(2 : ℤ) ^ a) (2 ^ a))
    (hq : q ∈ Ico (-(2 : ℤ) ^ a) (2 ^ a)) (hq0 : q ≠ 0) :
    padicValInt 2 (t - gridFlip (2 ^ a) t q) = padicValInt 2 q := by
  have h := padicValInt_gridFlip ht (gridFlip_mem ht hq)
    (fun h => hq0 ((gridFlip_eq_self_iff ht hq).mp h))
  rwa [gridFlip_gridFlip ht hq, eq_comm] at h

/-- **The tapered sum on the dyadic grid.** For a nonzero grid point `t` of valuation `i` and any
multiplicities `m` by valuation, `∑_{q ≠ 0, t} m(v₂ q) (v₂ q - v₂ (t - q))` is
`∑_{q ≠ 0, v₂ q > i} (v₂ q - i) (m (v₂ q) - m i)`: pairing `q` with the reflection of `t - q`
into the grid cancels the points of valuation `i` against those of valuation above `i`. -/
private theorem sum_tapered_eq (m : ℕ → ℕ) (ht : t ∈ Ico (-(2 : ℤ) ^ a) (2 ^ a)) (ht0 : t ≠ 0) :
    ∑ q ∈ ((Ico (-(2 : ℤ) ^ a) (2 ^ a)).erase 0).erase t,
        (m (padicValInt 2 q) : ℤ) * ((padicValInt 2 q : ℤ) - padicValInt 2 (t - q)) =
      ∑ q ∈ (Ico (-(2 : ℤ) ^ a) (2 ^ a)).erase 0,
        if padicValInt 2 t < padicValInt 2 q then
          ((padicValInt 2 q : ℤ) - padicValInt 2 t) *
            ((m (padicValInt 2 q) : ℤ) - m (padicValInt 2 t))
        else 0 := by
  set S := Ico (-(2 : ℤ) ^ a) (2 ^ a)
  set v : ℤ → ℕ := padicValInt 2
  set i := v t
  set φ := gridFlip (2 ^ a) t
  have hmem : ∀ {q}, q ∈ (S.erase 0).erase t ↔ q ∈ S ∧ q ≠ 0 ∧ q ≠ t := fun {q} => by
    simp only [mem_erase]; tauto
  have hφ : ∀ {q}, q ∈ (S.erase 0).erase t → φ q ∈ (S.erase 0).erase t := fun {q} hq => by
    rw [hmem] at hq ⊢
    exact ⟨gridFlip_mem ht hq.1, fun h => hq.2.2 ((gridFlip_eq_zero_iff ht hq.1).mp h),
      fun h => hq.2.1 ((gridFlip_eq_self_iff ht hq.1).mp h)⟩
  have hφφ : ∀ {q}, q ∈ (S.erase 0).erase t → φ (φ q) = q := fun {q} hq =>
    gridFlip_gridFlip ht (hmem.mp hq).1
  have hvφ : ∀ {q}, q ∈ (S.erase 0).erase t → v (φ q) = v (t - q) := fun {q} hq =>
    padicValInt_gridFlip ht (hmem.mp hq).1 (hmem.mp hq).2.2
  have hvsubφ : ∀ {q}, q ∈ (S.erase 0).erase t → v (t - φ q) = v q := fun {q} hq =>
    padicValInt_sub_gridFlip ht (hmem.mp hq).1 (hmem.mp hq).2.1
  -- a point of valuation above `i` has `v₂ (t - q) = i`, and one of valuation `i` has more
  have hgt : ∀ {q}, i < v q → v (t - q) = i := fun h => (padicValInt_two_sub_of_lt ht0 h).1
  have hlt : ∀ {q}, q ≠ 0 → v q < i → v (t - q) = v q := fun hq0 h =>
    (padicValInt_two_sub_of_lt hq0 h).2
  have heq : ∀ {q}, q ≠ 0 → q ≠ t → v q = i → i < v (t - q) := fun hq0 hqt h =>
    le_padicValInt_two (sub_ne_zero.mpr hqt.symm) (two_pow_succ_dvd_sub ht0 hq0 h.symm)
  set g : ℤ → ℤ := fun q => (v q : ℤ) * ((m (v q) : ℤ) - m (v (t - q)))
  -- reflect the second half of the sum
  have h1 : ∑ q ∈ (S.erase 0).erase t, (m (v q) : ℤ) * ((v q : ℤ) - v (t - q)) =
      ∑ q ∈ (S.erase 0).erase t, g q := by
    have hrefl : ∑ q ∈ (S.erase 0).erase t, (m (v q) : ℤ) * (v (t - q) : ℤ) =
        ∑ q ∈ (S.erase 0).erase t, (m (v (t - q)) : ℤ) * (v q : ℤ) :=
      sum_nbij' φ φ (fun q hq => hφ hq) (fun q hq => hφ hq) (fun q hq => hφφ hq)
        (fun q hq => hφφ hq) fun q hq => by rw [hvφ hq, hvsubφ hq]
    simp only [g, mul_sub, sum_sub_distrib, hrefl]
    congr 1
    · exact sum_congr rfl fun q _ => mul_comm _ _
    · exact sum_congr rfl fun q _ => mul_comm _ _
  -- points of valuation `i` are reflections of points of valuation above `i`
  have h2 : ∑ q ∈ ((S.erase 0).erase t).filter (fun q => ¬i < v q), g q =
      ∑ q ∈ ((S.erase 0).erase t).filter (fun q => i < v q), g (φ q) := by
    rw [← sum_subset (s₁ := ((S.erase 0).erase t).filter (fun q => v q = i))
      (fun q hq => by
        simp only [mem_filter] at hq ⊢
        exact ⟨hq.1, by omega⟩)
      fun q hq hq' => by
        simp only [mem_filter, not_and, not_lt] at hq hq'
        have hlt' : v q < i := lt_of_le_of_ne hq.2 (hq' hq.1)
        simp only [g, hlt (hmem.mp hq.1).2.1 hlt', sub_self, mul_zero]]
    refine sum_nbij' φ φ (fun q hq => ?_) (fun q hq => ?_) (fun q hq => hφφ (mem_filter.mp hq).1)
      (fun q hq => hφφ (mem_filter.mp hq).1) fun q hq => by rw [hφφ (mem_filter.mp hq).1]
    · rw [mem_filter] at hq ⊢
      refine ⟨hφ hq.1, ?_⟩
      rw [hvφ hq.1]
      exact heq (hmem.mp hq.1).2.1 (hmem.mp hq.1).2.2 hq.2
    · rw [mem_filter] at hq ⊢
      exact ⟨hφ hq.1, by rw [hvφ hq.1, hgt hq.2]⟩
  rw [h1, ← sum_filter_add_sum_filter_not _ (fun q => i < v q), h2, ← sum_add_distrib,
    ← sum_erase (S.erase 0) (a := t) (by simp only [i, lt_irrefl, ite_false]), sum_filter]
  refine sum_congr rfl fun q hq => ?_
  split_ifs with hiq
  · simp only [g, hgt hiq, hvφ hq, hvsubφ hq]
    ring
  · rfl

/-- **The two-adic valuation of a tapered Hermite basis value, exactly (D.10).** On the grid
`S = [-2 ^ a, 2 ^ a)`, take the nodes `S \ {0}`, a node `q` having multiplicity `m (v₂ q)`. For a
node `t` of valuation `i`, the value at `0` of its Hermite basis polynomial
`E_t(T) = ∏_{q ∈ S \ {0, t}} ((T - q) / (t - q)) ^ m (v₂ q)` has valuation
`∑_{i < j ≤ a} 2 ^ (a - j) (j - i) (m j - m i)`. This is the middle expression of (D.10) in
[OpenAI2026ETH, §D.4.4, p. 61] with `j = i + j'` and `D = 2 ^ (a - i)`. -/
theorem padicValRat_eval_zero_hermiteBasis_dyadic (m : ℕ → ℕ)
    (ht : t ∈ Ico (-(2 : ℤ) ^ a) (2 ^ a)) (ht0 : t ≠ 0) :
    padicValRat 2 ((hermiteBasis ((Ico (-(2 : ℤ) ^ a) (2 ^ a)).erase 0) (fun q : ℤ => (q : ℚ))
        (fun q => m (padicValInt 2 q)) t).eval 0) =
      ∑ j ∈ Ioc (padicValInt 2 t) a,
        2 ^ (a - j) * (((j : ℤ) - padicValInt 2 t) * ((m j : ℤ) - m (padicValInt 2 t))) := by
  have hfac : ∀ q ∈ ((Ico (-(2 : ℤ) ^ a) (2 ^ a)).erase 0).erase t,
      (Ring.inverse ((t : ℚ) - q) * (0 - q)) ^ m (padicValInt 2 q) ≠ 0 ∧
      padicValRat 2 ((Ring.inverse ((t : ℚ) - q) * (0 - q)) ^ m (padicValInt 2 q)) =
        (m (padicValInt 2 q) : ℤ) * ((padicValInt 2 q : ℤ) - padicValInt 2 (t - q)) := by
    intro q hq
    simp only [mem_erase] at hq
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.2.1
    have htq : ((t : ℚ) - q) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hq.1.symm)
    have hx : Ring.inverse ((t : ℚ) - q) * (0 - q) ≠ 0 := by
      rw [Ring.inverse_eq_inv, zero_sub]
      exact mul_ne_zero (inv_ne_zero htq) (neg_ne_zero.mpr hq0)
    refine ⟨pow_ne_zero _ hx, ?_⟩
    rw [padicValRat.pow, Ring.inverse_eq_inv, zero_sub,
      padicValRat.mul (inv_ne_zero htq) (neg_ne_zero.mpr hq0), padicValRat.inv, padicValRat.neg,
      show (t : ℚ) - q = ((t - q : ℤ) : ℚ) by push_cast; ring, padicValRat.of_int,
      padicValRat.of_int]
    ring
  rw [eval_hermiteBasis, padicValRat.prod _ fun q hq => (hfac q hq).1,
    sum_congr rfl fun q hq => (hfac q hq).2, sum_tapered_eq m ht ht0,
    sum_Ico_erase_zero_padicValInt_two a fun j => if padicValInt 2 t < j then
      ((j : ℤ) - padicValInt 2 t) * ((m j : ℤ) - m (padicValInt 2 t)) else 0]
  simp only [mul_ite, mul_zero]
  rw [← sum_filter]
  refine sum_congr (Finset.ext fun j => ?_) fun _ _ => rfl
  simp only [mem_filter, mem_range, mem_Ioc]
  omega

/-- `∑_{k < n} 2 ^ (n - 1 - k) (k + 1) ^ 2 + n ^ 2 + 4 n + 6 = 6 * 2 ^ n`, so the sum is at most
`6 * 2 ^ n`: the finite form of `∑_{j ≥ 1} j ^ 2 / 2 ^ j = 6`. -/
private theorem sum_two_pow_mul_sq (n : ℕ) :
    ∑ k ∈ range n, 2 ^ (n - 1 - k) * (k + 1) ^ 2 + n ^ 2 + 4 * n + 6 = 6 * 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul,
      sum_congr rfl fun k hk => by
        rw [show n - k = n - 1 - k + 1 by have := mem_range.mp hk; omega, pow_succ, mul_comm _ 2,
          mul_assoc],
      ← mul_sum, pow_succ 2 n]
    ring_nf
    ring_nf at ih
    omega

/-- **The valuation bound (D.10).** If the multiplicity by valuation `m` drops by at most `h` per
level, `m k ≤ m (k + 1) + h`, then the Hermite basis value at `0` of a nonzero grid node `t`
satisfies `v₂ (E_t(0)) ≥ -6 h D` with `D = 2 ^ (a - v₂ t)`
([OpenAI2026ETH, Lemma D.5, (D.10), p. 61]). -/
theorem neg_le_padicValRat_eval_zero_hermiteBasis_dyadic {h : ℕ} {m : ℕ → ℕ}
    (hm : ∀ k, m k ≤ m (k + 1) + h) (ht : t ∈ Ico (-(2 : ℤ) ^ a) (2 ^ a)) (ht0 : t ≠ 0) :
    -(6 * (h : ℤ) * 2 ^ (a - padicValInt 2 t)) ≤
      padicValRat 2 ((hermiteBasis ((Ico (-(2 : ℤ) ^ a) (2 ^ a)).erase 0)
        (fun q : ℤ => (q : ℚ)) (fun q => m (padicValInt 2 q)) t).eval 0) := by
  rw [padicValRat_eval_zero_hermiteBasis_dyadic m ht ht0]
  set i := padicValInt 2 t
  have hdrop : ∀ k j, m k ≤ m (k + j) + h * j := fun k j => by
    induction j with
    | zero => simp
    | succ j ih => have := hm (k + j); rw [← add_assoc]; nlinarith
  -- each level loses at most `h (j - i) ^ 2` times its count
  have hterm : ∀ j ∈ Ioc i a, -((h : ℤ) * (2 ^ (a - j) * ((j : ℤ) - i) ^ 2)) ≤
      2 ^ (a - j) * (((j : ℤ) - i) * ((m j : ℤ) - m i)) := fun j hj => by
    have hij : i ≤ j := (mem_Ioc.mp hj).1.le
    have hd := hdrop i (j - i)
    rw [Nat.add_sub_cancel' hij] at hd
    have hd' : (m i : ℤ) ≤ m j + h * ((j : ℤ) - i) := by
      have := (Nat.cast_le (α := ℤ)).mpr hd
      push_cast [Nat.cast_sub hij] at this
      exact this
    have hji : (0 : ℤ) ≤ (j : ℤ) - i := sub_nonneg.mpr (by exact_mod_cast hij)
    have key : 0 ≤ (2 : ℤ) ^ (a - j) * ((j : ℤ) - i) * ((m j : ℤ) - m i + h * ((j : ℤ) - i)) :=
      mul_nonneg (mul_nonneg (by positivity) hji) (by linarith)
    nlinarith [key]
  refine le_trans ?_ (sum_le_sum hterm)
  rw [sum_neg_distrib, neg_le_neg_iff, ← mul_sum,
    show (6 : ℤ) * h * 2 ^ (a - i) = h * (6 * 2 ^ (a - i)) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (α := ℤ) h)
  -- reindex `j = i + 1 + k` and use `∑ j ^ 2 / 2 ^ j ≤ 6`
  have hreindex : ∑ j ∈ Ioc i a, (2 : ℤ) ^ (a - j) * ((j : ℤ) - i) ^ 2 =
      ((∑ k ∈ range (a - i), 2 ^ (a - i - 1 - k) * (k + 1) ^ 2 : ℕ) : ℤ) := by
    rw [show Ioc i a = Ico (i + 1) (a + 1) by ext; simp only [mem_Ioc, mem_Ico]; omega,
      sum_Ico_eq_sum_range]
    push_cast
    refine sum_congr (by congr 1) fun k hk => ?_
    rw [show a - (i + 1 + k) = a - i - 1 - k by omega]
    ring
  rw [hreindex]
  have := sum_two_pow_mul_sq (a - i)
  exact_mod_cast (by omega : ∑ k ∈ range (a - i), 2 ^ (a - i - 1 - k) * (k + 1) ^ 2 ≤
    6 * 2 ^ (a - i))

/-- **The tapered multiplicities of Lemma D.5.** With `q(i) = h * max(0, u - i)` (natural
subtraction), the Hermite basis value at `0` of a nonzero grid node `t` satisfies
`v₂ (E_t(0)) ≥ -6 h D` with `D = 2 ^ (a - v₂ t)`: (D.10) of
[OpenAI2026ETH, Lemma D.5, p. 61]. -/
theorem neg_le_padicValRat_eval_zero_hermiteBasis_taper (u h : ℕ)
    (ht : t ∈ Ico (-(2 : ℤ) ^ a) (2 ^ a)) (ht0 : t ≠ 0) :
    -(6 * (h : ℤ) * 2 ^ (a - padicValInt 2 t)) ≤
      padicValRat 2 ((hermiteBasis ((Ico (-(2 : ℤ) ^ a) (2 ^ a)).erase 0)
        (fun q : ℤ => (q : ℚ)) (fun q => h * (u - padicValInt 2 q)) t).eval 0) :=
  neg_le_padicValRat_eval_zero_hermiteBasis_dyadic (m := fun k => h * (u - k))
    (fun k => by
      rw [← mul_add_one]
      exact Nat.mul_le_mul_left h (by omega)) ht ht0

end Dyadic

end Polynomial
