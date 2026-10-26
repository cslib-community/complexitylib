import Mathlib

/-! Scratch: §5.1–5.2 parity amplifier (research only). -/

open Polynomial Finset

namespace Scratch1226P

/-- `p_ℓ(Y) = Σ_{i<ℓ} C(2ℓ-1, i) Y^i (1-Y)^{2ℓ-1-i}`: the terms of `(Y + (1 - Y))^(2ℓ-1)` with
fewer than `ℓ` factors `Y`. -/
noncomputable def parityAmp (ℓ : ℕ) : ℤ[X] :=
  ∑ i ∈ range ℓ, C ((2 * ℓ - 1).choose i : ℤ) * X ^ i * (1 - X) ^ (2 * ℓ - 1 - i)

theorem one_sub_parityAmp {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    1 - parityAmp ℓ =
      ∑ i ∈ Ico ℓ (2 * ℓ), C ((2 * ℓ - 1).choose i : ℤ) * X ^ i * (1 - X) ^ (2 * ℓ - 1 - i) := by
  have h : ∑ i ∈ range (2 * ℓ), C ((2 * ℓ - 1).choose i : ℤ) * X ^ i * (1 - X) ^ (2 * ℓ - 1 - i)
      = 1 := by
    have := (add_pow (X : ℤ[X]) (1 - X) (2 * ℓ - 1)).symm
    rw [add_sub_cancel, one_pow, show 2 * ℓ - 1 + 1 = 2 * ℓ by omega] at this
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← C_eq_natCast]; ring
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : ℓ ≤ 2 * ℓ)] at h
  rw [parityAmp]
  linear_combination (-1 : ℤ[X]) * h

theorem X_pow_dvd_one_sub_parityAmp {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : X ^ ℓ ∣ 1 - parityAmp ℓ := by
  rw [one_sub_parityAmp hℓ]
  refine Finset.dvd_sum fun i hi => ?_
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow X (mem_Ico.mp hi).1) _) _

theorem one_sub_X_pow_dvd_parityAmp (ℓ : ℕ) : (1 - X) ^ ℓ ∣ parityAmp ℓ := by
  refine Finset.dvd_sum fun i hi => ?_
  exact Dvd.dvd.mul_left (pow_dvd_pow _ (by have := mem_range.mp hi; omega)) _

/-- **Lemma 5.1 congruence.** `p_ℓ(y) ≡ [2 ∣ y] (mod 2^ℓ)` for every integer `y`. -/
theorem parityAmp_eval_modEq {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (y : ℤ) :
    (parityAmp ℓ).eval y ≡ if 2 ∣ y then 1 else 0 [ZMOD 2 ^ ℓ] := by
  rw [Int.modEq_iff_dvd]
  split_ifs with hy
  · obtain ⟨g, hg⟩ := X_pow_dvd_one_sub_parityAmp hℓ
    have := congrArg (eval y) hg
    simp only [eval_sub, eval_one, eval_mul, eval_pow, eval_X] at this
    rw [this]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hy ℓ) _
  · obtain ⟨g, hg⟩ := one_sub_X_pow_dvd_parityAmp ℓ
    have := congrArg (eval y) hg
    simp only [eval_sub, eval_one, eval_mul, eval_pow, eval_X] at this
    rw [zero_sub, this, dvd_neg]
    have h2 : (2 : ℤ) ∣ 1 - y := by omega
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd h2 ℓ) _

/-- `h`-adic digits: division by a monic `h` of degree 2. -/
theorem exists_hAdic {R : Type*} [CommRing R] [Nontrivial R] {h : R[X]} (hm : h.Monic)
    (hd : h.natDegree = 2) :
    ∀ (ℓ : ℕ) (p : R[X]), p.degree < ↑(2 * ℓ) →
      ∃ e : ℕ → R[X], (∀ j, (e j).degree < 2) ∧ p = ∑ j ∈ range ℓ, e j * h ^ j := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro p hp
    refine ⟨0, fun _ => by simp, ?_⟩
    simpa [degree_lt_iff_coeff_zero] using hp
  | succ ℓ ih =>
    intro p hp
    have hq : (p /ₘ h).degree < ↑(2 * ℓ) := by
      by_cases hp0 : p /ₘ h = 0
      · simp [hp0]; exact WithBot.bot_lt_coe _
      rw [degree_eq_natDegree hp0, natDegree_divByMonic _ hm, hd]
      have : p ≠ 0 := fun h0 => hp0 (by simp [h0])
      rw [degree_eq_natDegree this] at hp
      have := WithBot.coe_lt_coe.mp hp
      exact WithBot.coe_lt_coe.mpr (by omega)
    obtain ⟨e', he', hsum⟩ := ih _ hq
    refine ⟨fun j => Nat.casesOn j (p %ₘ h) e', fun j => ?_, ?_⟩
    · cases j with
      | zero => simpa [hd] using degree_modByMonic_lt p hm
      | succ j => exact he' j
    · rw [Finset.sum_range_succ', pow_zero, mul_one]
      conv_lhs => rw [← modByMonic_add_div p hm, hsum, Finset.mul_sum]
      simp only [pow_succ]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

/-- Coefficients graded by powers of two. -/
def Graded (P : ℤ[X]) : Prop := ∀ s, (2 : ℤ) ^ s ∣ P.coeff s

theorem Graded.mul {P Q : ℤ[X]} (hP : Graded P) (hQ : Graded Q) : Graded (P * Q) := fun s => by
  rw [coeff_mul]
  refine Finset.dvd_sum fun x hx => ?_
  rw [← mem_antidiagonal.mp hx, pow_add]
  exact mul_dvd_mul (hP _) (hQ _)

theorem Graded.prod {ι : Type*} (s : Finset ι) (P : ι → ℤ[X]) (h : ∀ i ∈ s, Graded (P i)) :
    Graded (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro n; rw [prod_empty, coeff_one]; split_ifs with hn <;> simp [← hn]
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

/-- Truncated coefficient sum agrees with the value at `1` modulo `2^ℓ`. -/
theorem Graded.sum_coeff_modEq {P : ℤ[X]} (hP : Graded P) (ℓ : ℕ) :
    ∑ s ∈ range ℓ, P.coeff s ≡ P.eval 1 [ZMOD 2 ^ ℓ] := by
  rw [eval_eq_sum_range, Int.modEq_iff_dvd]
  have hle : ℓ ≤ max ℓ (P.natDegree + 1) := le_max_left _ _
  rw [eval_eq_sum_range' (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)) 1]
  rw [← Finset.sum_range_add_sum_Ico _ hle, add_sub_cancel_left]
  refine Finset.dvd_sum fun s hs => ?_
  rw [one_pow, mul_one]
  exact (pow_dvd_pow 2 (mem_Ico.mp hs).1).trans (hP s)

end Scratch1226P
