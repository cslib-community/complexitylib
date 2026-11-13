/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Discrepancy
public import CslibFrontier.Probability.MinEntropy
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Low discrepancy extracts from independent sources

The signed expectation of a Boolean gadget under independent sources is bounded by its uniform
discrepancy times the product of the largest atom bounds and the input alphabet sizes
(`abs_sum_mul_signVal_le_discrepancy_of_mass_le`). Substituting the min-entropy atom bounds gives
`abs_sum_mul_signVal_le_discrepancy_mul_rpow_minEntropy`, the quantitative extractor estimate
underlying [Chattopadhyay, Filmus, Koroth, Meir and Pitassi, Lemma 2.9]
[ChattopadhyayFilmusKorothMeirPitassi2021]. The exact parameter substitution is
`abs_sum_mul_signVal_le_rpow_of_minEntropy`.

The source uses convex combinations of flat distributions. Here an elementary alternative
selects the positive row sums, then the positive column sums. This proves the estimate for
arbitrary real atom bounds without rounding min-entropies to integers. Independence is represented
explicitly by the product of the two marginal masses in the expectation. This module does not
prove the lifting simulation or the discrepancy XOR lemma.

Splitting rows according to the sign of their bias gives an averaged absolute-bias bound.
Strict Markov on the event where the row bias exceeds the threshold then gives the sampling
lemma with its strict probability bound, including the source's one-bit entropy overhead.

## Main results

* `abs_sum_mul_signVal_le_discrepancy_of_weight_le`: the bound for nonnegative product weights.
* `abs_sum_mul_signVal_le_rpow_of_minEntropy`: the extraction lemma (CFKMP Lemma 2.9).
* `sum_mul_abs_sum_signVal_le_discrepancy`: an averaged absolute row-bias estimate.
* `sum_mass_filter_rowBias_lt_rpow_of_minEntropy`: the sampling lemma (CFKMP Lemma 2.10).

## References

* [Chattopadhyay, Filmus, Koroth, Meir and Pitassi, *Query-to-Communication Lifting Using
  Low-Discrepancy Gadgets*, arXiv:1904.13056v4][ChattopadhyayFilmusKorothMeirPitassi2021]
-/

public section

namespace Cslib.Communication

open Finset BitString Probability

variable {X Y : Type*} [Fintype X] [Fintype Y]

private theorem sum_mul_le_cap_mul_sum_pos {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) {a : ℝ} (hw₀ : ∀ i, 0 ≤ w i) (hw : ∀ i, w i ≤ a) :
    ∑ i, w i * v i ≤ a * ∑ i with 0 < v i, v i := by
  classical
  rw [mul_sum, sum_filter]
  refine sum_le_sum fun i _ => ?_
  by_cases hi : 0 < v i
  · rw [ite_eq_left hi]
    exact mul_le_mul_of_nonneg_right (hw i) hi.le
  · rw [ite_eq_right hi]
    exact mul_nonpos_of_nonneg_of_nonpos (hw₀ i) (le_of_not_gt hi)

private theorem sum_mul_mul_le_of_rectangle_sum_le (M : X → Y → ℝ)
    (p : X → ℝ) (q : Y → ℝ) {a b K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp₀ : ∀ x, 0 ≤ p x) (hp : ∀ x, p x ≤ a)
    (hq₀ : ∀ y, 0 ≤ q y) (hq : ∀ y, q y ≤ b)
    (hM : ∀ A : Finset X, ∀ B : Finset Y, ∑ x ∈ A, ∑ y ∈ B, M x y ≤ K) :
    ∑ x, ∑ y, p x * q y * M x y ≤ a * b * K := by
  classical
  let A := univ.filter fun x => 0 < ∑ y, q y * M x y
  have h₁ := sum_mul_le_cap_mul_sum_pos p (fun x => ∑ y, q y * M x y) hp₀ hp
  have h₂ := sum_mul_le_cap_mul_sum_pos q (fun y => ∑ x ∈ A, M x y) hq₀ hq
  have h₃ := hM A (univ.filter fun y => 0 < ∑ x ∈ A, M x y)
  calc
    ∑ x, ∑ y, p x * q y * M x y = ∑ x, p x * ∑ y, q y * M x y := by
      simp only [mul_sum, mul_assoc]
    _ ≤ a * ∑ x ∈ A, ∑ y, q y * M x y := h₁
    _ = a * ∑ y, q y * ∑ x ∈ A, M x y := by
      rw [sum_comm]
      simp only [mul_sum]
    _ ≤ a * (b * ∑ y with 0 < ∑ x ∈ A, M x y, ∑ x ∈ A, M x y) :=
      mul_le_mul_of_nonneg_left h₂ ha
    _ ≤ a * (b * K) := by
      apply mul_le_mul_of_nonneg_left _ ha
      apply mul_le_mul_of_nonneg_left _ hb
      rw [sum_comm]
      exact h₃
    _ = a * b * K := (mul_assoc _ _ _).symm

/-- The rectangle discrepancy bound extends to nonnegative, possibly subnormalized product
weights. This form also applies after restricting one source to an event. -/
theorem abs_sum_mul_signVal_le_discrepancy_of_weight_le [Nonempty X] [Nonempty Y]
    (p : X → ℝ) (q : Y → ℝ) (g : X → Y → Bool) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp₀ : ∀ x, 0 ≤ p x) (hp : ∀ x, p x ≤ a)
    (hq₀ : ∀ y, 0 ≤ q y) (hq : ∀ y, q y ≤ b) :
    |∑ x, ∑ y, p x * q y * signVal (g x y)| ≤
      a * b * (Fintype.card X * Fintype.card Y) *
        discrepancy (PMF.uniformOfFintype (X × Y)) g := by
  classical
  let D := discrepancy (PMF.uniformOfFintype (X × Y)) g
  let N : ℝ := Fintype.card X * Fintype.card Y
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hrect (A : Finset X) (B : Finset Y) :
      |∑ x ∈ A, ∑ y ∈ B, signVal (g x y)| ≤ N * D := by
    have h := abs_sum_le_discrepancy (PMF.uniformOfFintype (X × Y)) g A B
    simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, ENNReal.toReal_inv,
      Nat.cast_mul, ← mul_sum] at h
    change |N⁻¹ * ∑ x ∈ A, ∑ y ∈ B, signVal (g x y)| ≤ D at h
    rw [abs_mul, abs_of_pos (inv_pos.mpr hN), inv_mul_le_iff₀ hN] at h
    exact h
  have hupper (M : X → Y → ℝ)
      (hM : ∀ A : Finset X, ∀ B : Finset Y, ∑ x ∈ A, ∑ y ∈ B, M x y ≤ N * D) :
      ∑ x, ∑ y, p x * q y * M x y ≤ a * b * (N * D) :=
    sum_mul_mul_le_of_rectangle_sum_le M p q ha hb hp₀ hp hq₀ hq hM
  rw [mul_assoc (a * b)]
  apply abs_le.mpr
  constructor
  · have h := hupper (fun x y => -signVal (g x y)) fun A B => by
      simp only [sum_neg_distrib]
      exact (neg_le_abs _).trans (hrect A B)
    simp only [mul_neg, sum_neg_distrib] at h
    linarith
  · exact hupper (fun x y => signVal (g x y)) fun A B =>
      (le_abs_self _).trans (hrect A B)

/-- Uniform discrepancy bounds the bias of a gadget under independent sources with atom caps
`a` and `b`. The alphabets may differ, and the atom caps are arbitrary nonnegative reals. -/
theorem abs_sum_mul_signVal_le_discrepancy_of_mass_le [Nonempty X] [Nonempty Y]
    (p : PMF X) (q : PMF Y) (g : X → Y → Bool) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : ∀ x, (p x).toReal ≤ a) (hq : ∀ y, (q y).toReal ≤ b) :
    |∑ x, ∑ y, (p x).toReal * (q y).toReal * signVal (g x y)| ≤
      a * b * (Fintype.card X * Fintype.card Y) *
        discrepancy (PMF.uniformOfFintype (X × Y)) g :=
  abs_sum_mul_signVal_le_discrepancy_of_weight_le _ _ g ha hb
    (fun _ => ENNReal.toReal_nonneg) hp (fun _ => ENNReal.toReal_nonneg) hq

/-- The extractor estimate in CFKMP, Lemma 2.9, before substituting the discrepancy and entropy
parameters: the bias is at most `|X| |Y| disc(g) 2^(-H∞(p)-H∞(q))`. -/
theorem abs_sum_mul_signVal_le_discrepancy_mul_rpow_minEntropy [Nonempty X] [Nonempty Y]
    (p : PMF X) (q : PMF Y) (g : X → Y → Bool) :
    |∑ x, ∑ y, (p x).toReal * (q y).toReal * signVal (g x y)| ≤
      2 ^ (-PMF.minEntropy p - PMF.minEntropy q) *
        (Fintype.card X * Fintype.card Y) *
        discrepancy (PMF.uniformOfFintype (X × Y)) g := by
  have h := abs_sum_mul_signVal_le_discrepancy_of_mass_le p q g
    (by positivity : (0 : ℝ) ≤ 2 ^ (-PMF.minEntropy p))
    (by positivity : (0 : ℝ) ≤ 2 ^ (-PMF.minEntropy q))
    (PMF.toReal_apply_le_rpow_neg_minEntropy p) (PMF.toReal_apply_le_rpow_neg_minEntropy q)
  rwa [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← sub_eq_add_neg] at h

private theorem rpow_minEntropy_mul_discrepancy_le [Nonempty X]
    (p q : PMF X) (g : X → X → Bool) {b : ℕ} {η s : ℝ}
    (hcard : Fintype.card X = 2 ^ b)
    (hdisc : discrepancy (PMF.uniformOfFintype (X × X)) g ≤ 2 ^ (-η * b))
    (hentropy : (2 - η) * b + s ≤ PMF.minEntropy p + PMF.minEntropy q) :
    2 ^ (-PMF.minEntropy p - PMF.minEntropy q) *
      (Fintype.card X * Fintype.card X) *
      discrepancy (PMF.uniformOfFintype (X × X)) g ≤ 2 ^ (-s) := by
  calc
    _ ≤ (2 : ℝ) ^ (-PMF.minEntropy p - PMF.minEntropy q) *
        (Fintype.card X * Fintype.card X) * 2 ^ (-η * b) :=
      mul_le_mul_of_nonneg_left hdisc (by positivity)
    _ = (2 : ℝ) ^ (-PMF.minEntropy p - PMF.minEntropy q + 2 * b - η * b) := by
      rw [hcard]
      push_cast
      simp only [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ 2 ^ (-s) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hentropy])

/-- **Low-discrepancy extraction**, CFKMP, arXiv:1904.13056v4, Lemma 2.9, for an alphabet
of size `2^b`. If the gadget has discrepancy at most `2^(-η b)` and the two independent inputs
have combined min-entropy at least `(2 - η + lam)b`, its output has bias at most `2^(-lam b)`.
No integrality assumption on either min-entropy is used. -/
theorem abs_sum_mul_signVal_le_rpow_of_minEntropy [Nonempty X]
    (p q : PMF X) (g : X → X → Bool) {b : ℕ} {η lam : ℝ}
    (hcard : Fintype.card X = 2 ^ b)
    (hdisc : discrepancy (PMF.uniformOfFintype (X × X)) g ≤ 2 ^ (-η * b))
    (hentropy : (2 - η + lam) * b ≤ PMF.minEntropy p + PMF.minEntropy q) :
    |∑ x, ∑ y, (p x).toReal * (q y).toReal * signVal (g x y)| ≤ 2 ^ (-lam * b) := by
  have h := rpow_minEntropy_mul_discrepancy_le p q g hcard hdisc
    (s := lam * b) (by nlinarith [hentropy])
  simpa only [neg_mul] using
    (abs_sum_mul_signVal_le_discrepancy_mul_rpow_minEntropy p q g).trans h

/-- Averaged row bias is at most twice the independent-source discrepancy bound. The factor
two pays for the two possible signs of the row expectation. -/
theorem sum_mul_abs_sum_signVal_le_discrepancy [Nonempty X] [Nonempty Y]
    (p : PMF X) (q : PMF Y) (g : X → Y → Bool) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : ∀ x, (p x).toReal ≤ a) (hq : ∀ y, (q y).toReal ≤ b) :
    ∑ x, (p x).toReal * |∑ y, (q y).toReal * signVal (g x y)| ≤
      2 * (a * b * (Fintype.card X * Fintype.card Y) *
        discrepancy (PMF.uniformOfFintype (X × Y)) g) := by
  classical
  let r (x : X) := ∑ y, (q y).toReal * signVal (g x y)
  let pPos (x : X) := if 0 ≤ r x then (p x).toReal else 0
  let pNeg (x : X) := if 0 ≤ r x then 0 else (p x).toReal
  have hPos := abs_sum_mul_signVal_le_discrepancy_of_weight_le
    pPos (fun y => (q y).toReal) g ha hb
    (fun x => by dsimp [pPos]; split_ifs <;> positivity)
    (fun x => by dsimp [pPos]; split_ifs <;> first | exact hp x | exact ha)
    (fun _ => ENNReal.toReal_nonneg) hq
  have hNeg := abs_sum_mul_signVal_le_discrepancy_of_weight_le
    pNeg (fun y => (q y).toReal) g ha hb
    (fun x => by dsimp [pNeg]; split_ifs <;> positivity)
    (fun x => by dsimp [pNeg]; split_ifs <;> first | exact hp x | exact ha)
    (fun _ => ENNReal.toReal_nonneg) hq
  have hsplit : (∑ x, (p x).toReal * |r x|) =
      (∑ x, ∑ y, pPos x * (q y).toReal * signVal (g x y)) -
        (∑ x, ∑ y, pNeg x * (q y).toReal * signVal (g x y)) := by
    simp only [mul_assoc, ← mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro x _
    change (p x).toReal * |r x| = pPos x * r x - pNeg x * r x
    by_cases hr : 0 ≤ r x
    · simp [pPos, pNeg, hr, abs_of_nonneg hr]
    · simp [pPos, pNeg, hr, abs_of_neg (lt_of_not_ge hr)]
  change (∑ x, (p x).toReal * |r x|) ≤ _
  rw [hsplit]
  linarith [le_abs_self (∑ x, ∑ y, pPos x * (q y).toReal * signVal (g x y)),
    neg_le_abs (∑ x, ∑ y, pNeg x * (q y).toReal * signVal (g x y))]

private theorem sum_mass_filter_lt_of_sum_mul_le {α : Type*} [Fintype α]
    (p : PMF α) (f : α → ℝ) {t β : ℝ} (hf : ∀ x, 0 ≤ f x)
    (ht : 0 < t) (hβ : 0 < β) (h : ∑ x, (p x).toReal * f x ≤ t * β) :
    (∑ x with t < f x, (p x).toReal) < β := by
  classical
  let A := univ.filter fun x => t < f x
  by_cases hA : (∑ x ∈ A, (p x).toReal) = 0
  · change (∑ x ∈ A, (p x).toReal) < β
    rw [hA]
    exact hβ
  have hApos : 0 < ∑ x ∈ A, (p x).toReal :=
    lt_of_le_of_ne (sum_nonneg fun _ _ => ENNReal.toReal_nonneg) (Ne.symm hA)
  obtain ⟨x, hx, hpx⟩ := sum_pos_iff_of_nonneg (fun x (_ : x ∈ A) =>
    ENNReal.toReal_nonneg) |>.mp hApos
  have hstrict : t * (∑ x ∈ A, (p x).toReal) < ∑ x ∈ A, (p x).toReal * f x := by
    rw [mul_sum]
    apply sum_lt_sum
    · intro x hx
      exact (mul_comm _ _).trans_le
        (mul_le_mul_of_nonneg_left (mem_filter.mp hx).2.le ENNReal.toReal_nonneg)
    · refine ⟨x, hx, ?_⟩
      rw [mul_comm]
      exact mul_lt_mul_of_pos_left (mem_filter.mp hx).2 hpx
  have hsub : (∑ x ∈ A, (p x).toReal * f x) ≤ ∑ x, (p x).toReal * f x :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun x _ _ => mul_nonneg ENNReal.toReal_nonneg (hf x))
  exact (mul_lt_mul_iff_right₀ ht).mp (hstrict.trans_le (hsub.trans h))

/-- A strict tail bound for the bias of a row sampled from an independent source. This is the
sampling step of CFKMP Lemma 2.10 in atom-cap form. -/
theorem sum_mass_filter_rowBias_lt [Nonempty X] [Nonempty Y]
    (p : PMF X) (q : PMF Y) (g : X → Y → Bool) {a b t β : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : ∀ x, (p x).toReal ≤ a) (hq : ∀ y, (q y).toReal ≤ b)
    (ht : 0 < t) (hβ : 0 < β)
    (hbound : 2 * (a * b * (Fintype.card X * Fintype.card Y) *
      discrepancy (PMF.uniformOfFintype (X × Y)) g) ≤ t * β) :
    (∑ x with t < |∑ y, (q y).toReal * signVal (g x y)|, (p x).toReal) < β :=
  sum_mass_filter_lt_of_sum_mul_le p _ (fun _ => abs_nonneg _) ht hβ
    ((sum_mul_abs_sum_signVal_le_discrepancy p q g ha hb hp hq).trans hbound)

/-- **Low-discrepancy sampling**, CFKMP, arXiv:1904.13056v4, Lemma 2.10. The probability
that the conditional output bias exceeds `2^(-lam b)` is strictly less than `2^(-γ b)`.
The one-bit entropy overhead accounts for positive and negative row biases. -/
theorem sum_mass_filter_rowBias_lt_rpow_of_minEntropy [Nonempty X]
    (p q : PMF X) (g : X → X → Bool) {b : ℕ} {η γ lam : ℝ}
    (hcard : Fintype.card X = 2 ^ b)
    (hdisc : discrepancy (PMF.uniformOfFintype (X × X)) g ≤ 2 ^ (-η * b))
    (hentropy : (2 - η + γ + lam) * b + 1 ≤ PMF.minEntropy p + PMF.minEntropy q) :
    (∑ x with 2 ^ (-lam * b) < |∑ y, (q y).toReal * signVal (g x y)|,
      (p x).toReal) < 2 ^ (-γ * b) := by
  apply sum_mass_filter_rowBias_lt p q g
    (by positivity : (0 : ℝ) ≤ 2 ^ (-PMF.minEntropy p))
    (by positivity : (0 : ℝ) ≤ 2 ^ (-PMF.minEntropy q))
    (PMF.toReal_apply_le_rpow_neg_minEntropy p) (PMF.toReal_apply_le_rpow_neg_minEntropy q)
    (by positivity) (by positivity)
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← sub_eq_add_neg]
  have h := rpow_minEntropy_mul_discrepancy_le p q g hcard hdisc
    (s := (γ + lam) * b + 1) (by nlinarith [hentropy])
  calc
    _ ≤ 2 * 2 ^ (-((γ + lam) * b + 1)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 2 ^ (-lam * b) * 2 ^ (-γ * b) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        show -lam * b + -γ * b = 1 + -((γ + lam) * b + 1) by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]

end Cslib.Communication
