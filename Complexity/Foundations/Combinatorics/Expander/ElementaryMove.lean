/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.PairShearTranslation
public import Mathlib.Data.ZMod.Basic
import Complexity.Foundations.Probability.EfronStein

/-!
# Elementary moves on the nonzero vectors of `𝔽_P ^ H`

The elementary move `elementaryMove a b` adds the coordinate `b` of a vector `F : Fin H → ZMod P`
to its coordinate `a`: it is the action of the elementary matrix `1 + E_ab` of `SL_H(ℤ)`. For a
prime `P` and `H ≥ 3`, these moves mix the nonzero vectors uniformly in `P`: every real function `g`
is close to a constant on the nonzero vectors, with second moment about that constant at most
`36864 H²` times the total squared change of `g` along the elementary moves
(`exists_expect_sq_sub_le_elementaryMove`). These vectors are the frames of length one, the
channel coefficients that the sampling environment moves by left multiplication.

The proof reduces to the gap of the shear-translation graph on `ZMod P × ZMod P`:

* **Fibers.** On the vectors with `F k = c ≠ 0`, write `F = c • w` off the coordinate `k`. In
  these coordinates the moves `1 + E_ij` with `i, j ≠ k` are the elementary shears of `w`, and the
  moves `1 + E_ik` are the unit translations of `w`, since they add `F k = c`. The pair bound
  `expect_sq_sub_expect_update_le_pairShearTranslation` and the Efron–Stein inequality therefore
  make `g` close to its fiber averages `h_k (F k)` on `{F k ≠ 0}`, with the values `c` as the
  spectator. This needs a partner coordinate different from `i` and `k`, hence `H ≥ 3`.
* **Gluing.** On `{F k ≠ 0, F l ≠ 0}` with `k ≠ l`, the coordinates `F k` and `F l` are independent
  and uniform, so `h_k (F k) ≈ h_l (F l)` forces both functions to be close to one constant, the
  average of `h_0` over the nonzero values. Every nonzero vector has a nonzero coordinate.

This is the frame part of the averaging walk in the OpenAI preprint on derandomizing logarithmic
space, for frames of length one: the preprint gets it from property (T) of `SL_H(ℤ)` for `H ≥ 3`
[OpenAI, Lemma 6.1][OpenAI2026LogSpace] and the transitivity of the action on frames
[OpenAI, proof of Lemma 6.2][OpenAI2026LogSpace]. An elementary lift of the relative gap to frames
is in OpenAI's Lean development, the file
[`AffineSampling.lean`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/Logspace/AffineSampling.lean)
at revision `7ef5c0cc` (`slice_frame`, `frame_gap`, `slice_gap`). The statements and the proof
here are independent of that code, which was not consulted. The fiber-and-gluing argument is ours.

## Main definitions

* `Cslib.RotationMap.elementaryMove`: the move `F ↦ F + F b • e a`.

## Main results

* `Cslib.RotationMap.exists_expect_sq_sub_le_elementaryMove`: the Poincaré inequality for the
  elementary moves on the nonzero vectors of `(ZMod P) ^ H`, uniformly in the prime `P`.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace]
-/

public section

open Finset Function
open scoped BigOperators

namespace Cslib.RotationMap

variable {P H : ℕ}

/-- The elementary move `F ↦ F + F b • e a`: the action of the elementary matrix `1 + E_ab`. -/
@[expose]
def elementaryMove (a b : Fin H) (F : Fin H → ZMod P) : Fin H → ZMod P :=
  update F a (F a + F b)

variable [Fact P.Prime]

/-- The indicator of the nonzero elements of `ZMod P`. -/
private noncomputable def nz (c : ZMod P) : ℝ := if c = 0 then 0 else 1

private theorem nz_nonneg (c : ZMod P) : 0 ≤ nz c := by
  unfold nz; split_ifs <;> norm_num

private theorem nz_le_one (c : ZMod P) : nz c ≤ 1 := by
  unfold nz; split_ifs <;> norm_num

private theorem nz_mul_self (c : ZMod P) : nz c * nz c = nz c := by
  unfold nz; split_ifs <;> norm_num

/-- At least half of the elements of `ZMod P` are nonzero. -/
private theorem half_le_expect_nz : (1 / 2 : ℝ) ≤ 𝔼 c : ZMod P, nz c := by
  have h (c : ZMod P) : nz c = 1 - if c = 0 then 1 else 0 := by
    unfold nz; split_ifs <;> norm_num
  have hP : (2 : ℝ) ≤ P := by exact_mod_cast (Fact.out : P.Prime).two_le
  have hsum : (∑ _c : ZMod P, (1 : ℝ)) = P := by simp
  simp only [h, expect_sub_distrib, Fintype.expect_eq_sum_div_card, sum_ite_eq', mem_univ,
    ite_true, ZMod.card, hsum]
  rw [div_self (by positivity)]
  have : (1 : ℝ) / P ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

/-- The weighted second moment about `a` is the weighted second moment about the weighted mean plus
the squared distance of the mean from `a`. -/
private theorem expect_mul_sq_sub_eq {α : Type*} [Fintype α] (w X : α → ℝ) (a : ℝ)
    (hW : 𝔼 x, w x ≠ 0) :
    𝔼 x, w x * (X x - a) ^ 2 =
      𝔼 x, w x * (X x - (𝔼 y, w y * X y) / 𝔼 y, w y) ^ 2 +
        (𝔼 x, w x) * ((𝔼 y, w y * X y) / 𝔼 y, w y - a) ^ 2 := by
  set W := 𝔼 y, w y
  set m := (𝔼 y, w y * X y) / W
  have h0 : 𝔼 x, w x * (X x - m) = 0 := by
    simp only [mul_sub, expect_sub_distrib, ← expect_mul, m]
    field_simp
    ring
  calc 𝔼 x, w x * (X x - a) ^ 2
      = 𝔼 x, (w x * (X x - m) ^ 2 + 2 * (m - a) * (w x * (X x - m)) + w x * (m - a) ^ 2) :=
        expect_congr rfl fun x _ ↦ by ring
    _ = _ := by
        rw [expect_add_distrib, expect_add_distrib, ← mul_expect, h0, mul_zero, add_zero,
          ← expect_mul]

/-- In particular the weighted second moment about `a` is at least the total weight times the
squared distance of the weighted mean from `a`, and at least the weighted second moment about the
weighted mean. -/
private theorem expect_mul_sq_sub_ge {α : Type*} [Fintype α] (w X : α → ℝ) (a : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hW : 𝔼 x, w x ≠ 0) :
    (𝔼 x, w x) * ((𝔼 y, w y * X y) / 𝔼 y, w y - a) ^ 2 ≤ 𝔼 x, w x * (X x - a) ^ 2 ∧
      𝔼 x, w x * (X x - (𝔼 y, w y * X y) / 𝔼 y, w y) ^ 2 ≤ 𝔼 x, w x * (X x - a) ^ 2 := by
  rw [expect_mul_sq_sub_eq w X a hW]
  have h1 : 0 ≤ 𝔼 x, w x * (X x - (𝔼 y, w y * X y) / 𝔼 y, w y) ^ 2 :=
    expect_nonneg fun x _ ↦ mul_nonneg (hw x) (sq_nonneg _)
  have h2 : 0 ≤ (𝔼 x, w x) * ((𝔼 y, w y * X y) / 𝔼 y, w y - a) ^ 2 :=
    mul_nonneg (expect_nonneg fun x _ ↦ hw x) (sq_nonneg _)
  exact ⟨by linarith, by linarith⟩

/-- One coordinate of a uniformly random vector is uniform. -/
private theorem expect_comp_eval (k : Fin H) (φ : ZMod P → ℝ) :
    𝔼 F : Fin H → ZMod P, φ (F k) = 𝔼 c, φ c := by
  calc 𝔼 F : Fin H → ZMod P, φ (F k) = 𝔼 F : Fin H → ZMod P, 𝔼 c, φ (update F k c k) :=
        (Fintype.expect_expect_update (fun F ↦ φ (F k)) k).symm
    _ = 𝔼 c, φ c := by simp only [update_self, Fintype.expect_const]

/-- Two distinct coordinates of a uniformly random vector are independent and uniform. -/
private theorem expect_comp_eval_eval {k l : Fin H} (hkl : k ≠ l) (φ : ZMod P → ZMod P → ℝ) :
    𝔼 F : Fin H → ZMod P, φ (F k) (F l) = 𝔼 c, 𝔼 d, φ c d := by
  calc 𝔼 F : Fin H → ZMod P, φ (F k) (F l)
      = 𝔼 F : Fin H → ZMod P, 𝔼 c, φ (update F k c k) (update F k c l) :=
        (Fintype.expect_expect_update (fun F ↦ φ (F k) (F l)) k).symm
    _ = 𝔼 c, 𝔼 F : Fin H → ZMod P, φ c (F l) := by
        simp only [update_self, update_of_ne hkl.symm]
        exact expect_comm _ _ _
    _ = _ := expect_congr rfl fun c _ ↦ expect_comp_eval l (φ c)

/-- Scaling by a nonzero element preserves the uniform average. -/
private theorem expect_comp_smul {c : ZMod P} (hc : c ≠ 0) (φ : (Fin H → ZMod P) → ℝ) :
    𝔼 w, φ (c • w) = 𝔼 w, φ w := by
  let e : (Fin H → ZMod P) ≃ (Fin H → ZMod P) :=
    ⟨fun w ↦ c • w, fun w ↦ c⁻¹ • w, fun w ↦ by simp [smul_smul, inv_mul_cancel₀ hc],
      fun w ↦ by simp [smul_smul, mul_inv_cancel₀ hc]⟩
  exact Fintype.expect_equiv e _ _ fun _ ↦ rfl

/-- The total squared change of `g` along the elementary moves. -/
private noncomputable abbrev dir (g : (Fin H → ZMod P) → ℝ) : ℝ :=
  ∑ a, ∑ b ∈ univ.erase a, 𝔼 F, (g (elementaryMove a b F) - g F) ^ 2

private theorem le_dir (g : (Fin H → ZMod P) → ℝ) {a b : Fin H} (hab : b ≠ a) :
    𝔼 F, (g (elementaryMove a b F) - g F) ^ 2 ≤ dir g :=
  (single_le_sum (f := fun b ↦ 𝔼 F, (g (elementaryMove a b F) - g F) ^ 2)
    (fun _ _ ↦ expect_nonneg fun _ _ ↦ sq_nonneg _) (mem_erase.2 ⟨hab, mem_univ b⟩)).trans
    (single_le_sum (f := fun a ↦ ∑ b ∈ univ.erase a, 𝔼 F, (g (elementaryMove a b F) - g F) ^ 2)
      (fun _ _ ↦ sum_nonneg fun _ _ ↦ expect_nonneg fun _ _ ↦ sq_nonneg _) (mem_univ a))

/-- The average of `g` over the vectors with `F k = c`. -/
private noncomputable abbrev fib (g : (Fin H → ZMod P) → ℝ) (k : Fin H) (c : ZMod P) : ℝ :=
  𝔼 F, g (update F k c)

/-- In the coordinates `F = update (c • w) k c`, an elementary shear of `w` off `k` is an
elementary move of `F`. -/
private theorem update_smul_shear {i j k : Fin H} (hik : i ≠ k) (hjk : j ≠ k) (c : ZMod P)
    (w : Fin H → ZMod P) :
    update (c • update w i (w i + w j)) k c = elementaryMove i j (update (c • w) k c) := by
  funext t
  simp only [elementaryMove, update_apply, Pi.smul_apply, smul_eq_mul]
  by_cases htk : t = k
  · simp [htk, hik.symm]
  · by_cases hti : t = i <;> simp [hti, htk, hik, hjk, mul_add]

/-- In the coordinates `F = update (c • w) k c`, a unit translation of `w` off `k` is the
elementary move adding `F k = c`. -/
private theorem update_smul_translate {i k : Fin H} (hik : i ≠ k) (c : ZMod P)
    (w : Fin H → ZMod P) :
    update (c • update w i (w i + 1)) k c = elementaryMove i k (update (c • w) k c) := by
  funext t
  simp only [elementaryMove, update_apply, Pi.smul_apply, smul_eq_mul]
  by_cases htk : t = k
  · simp [htk, hik.symm]
  · by_cases hti : t = i <;> simp [hti, htk, hik, mul_add]

/-- **The fibers**: on `{F k ≠ 0}`, `g` is close to its averages over the fibers `{F k = c}`. -/
private theorem fiber_bound (hH : 3 ≤ H) (k : Fin H) (g : (Fin H → ZMod P) → ℝ) :
    𝔼 F, nz (F k) * (g F - fib g k (F k)) ^ 2 ≤ 2048 * H * dir g := by
  -- A partner `σ i ∉ {i, k}` for every coordinate `i`.
  have hσ (i : Fin H) : ∃ j, j ≠ i ∧ j ≠ k := by
    by_contra h
    push Not at h
    have hsub : (univ : Finset (Fin H)) ⊆ {i, k} := fun j _ ↦ by
      by_cases hj : j = i
      · simp [hj]
      · simp [h j hj]
    have := (card_le_card hsub).trans (card_insert_le _ _)
    simp only [card_univ, Fintype.card_fin, card_singleton] at this
    omega
  choose σ hσ using hσ
  -- Coordinates on the fiber `{F k = c}`: `F = update (c • w) k c`.
  set Ψ : ZMod P → (Fin H → ZMod P) → (Fin H → ZMod P) := fun c w ↦ update (c • w) k c with hΨ
  set G : ZMod P × (Fin H → ZMod P) → ℝ := fun q ↦ nz q.1 * g (Ψ q.1 q.2) with hG
  have hfib {c : ZMod P} (hc : c ≠ 0) (φ : (Fin H → ZMod P) → ℝ) :
      𝔼 w, φ (Ψ c w) = 𝔼 F, φ (update F k c) :=
    expect_comp_smul hc fun F ↦ φ (update F k c)
  -- The left side is the Efron–Stein left side for `G`.
  have hL : 𝔼 q, (G q - 𝔼 w, G (q.1, w)) ^ 2 =
      𝔼 F, nz (F k) * (g F - fib g k (F k)) ^ 2 := by
    rw [Fintype.expect_prod_type,
      ← Fintype.expect_expect_update (fun F ↦ nz (F k) * (g F - fib g k (F k)) ^ 2) k]
    simp only [update_self]
    conv_rhs => rw [expect_comm]
    refine expect_congr rfl fun c _ ↦ ?_
    by_cases hc : c = 0
    · simp [hG, nz, hc]
    · have h1 : nz c = 1 := by simp [nz, hc]
      simp only [hG, h1, one_mul]
      rw [hfib hc g]
      exact hfib hc fun F ↦ (g F - 𝔼 F', g (update F' k c)) ^ 2
  -- The coordinate `k` of `w` is not seen.
  have hk : 𝔼 q, (G q - 𝔼 a, G (q.1, update q.2 k a)) ^ 2 = 0 := by
    have h (q : ZMod P × (Fin H → ZMod P)) (a : ZMod P) : G (q.1, update q.2 k a) = G q := by
      have : update (q.1 • update q.2 k a) k q.1 = update (q.1 • q.2) k q.1 := by
        funext t
        by_cases ht : t = k <;> simp [ht]
      simp only [hG, hΨ, this]
    simp [h]
  -- A move of `w` that is an elementary move of `F` costs at most `dir g`.
  have hterm {a b : Fin H} (hab : b ≠ a)
      (M : ZMod P × (Fin H → ZMod P) → ZMod P × (Fin H → ZMod P)) (hM₁ : ∀ q, (M q).1 = q.1)
      (hM : ∀ c w, Ψ c (M (c, w)).2 = elementaryMove a b (Ψ c w)) :
      𝔼 q, (G (M q) - G q) ^ 2 ≤ dir g := by
    refine le_trans ?_ (le_dir g hab)
    rw [Fintype.expect_prod_type,
      ← Fintype.expect_expect_update (fun F ↦ (g (elementaryMove a b F) - g F) ^ 2) k]
    conv_rhs => rw [expect_comm]
    refine expect_le_expect fun c _ ↦ ?_
    by_cases hc : c = 0
    · have h0 : nz c = 0 := by simp [nz, hc]
      have hz (w : Fin H → ZMod P) : G (M (c, w)) - G (c, w) = 0 := by
        simp only [hG, hM₁, h0, zero_mul, sub_self]
      simp only [hz]
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, expect_const_zero]
      exact expect_nonneg fun _ _ ↦ sq_nonneg _
    · have h1 : nz c = 1 := by simp [nz, hc]
      have : ∀ w, G (M (c, w)) - G (c, w) = g (elementaryMove a b (Ψ c w)) - g (Ψ c w) := by
        intro w
        simp only [hG, hM₁, h1, one_mul, hM]
      simp only [this]
      exact (hfib hc fun F ↦ (g (elementaryMove a b F) - g F) ^ 2).le
  -- The four moves of the pair `(i, σ i)`, for `i ≠ k`.
  have hi (i : Fin H) (hik : i ≠ k) :
      𝔼 q, (G q - 𝔼 a, G (q.1, update q.2 i a)) ^ 2 ≤ 2048 * dir g := by
    set j := σ i
    have hji : j ≠ i := (hσ i).1
    have hjk : j ≠ k := (hσ i).2
    refine (expect_sq_sub_expect_update_le_pairShearTranslation (Equiv.refl _) (Equiv.refl _)
      hji.symm G).trans ?_
    rw [Fin.sum_univ_four]
    have hmv (m : Fin 4) {a b : Fin H} (hab : b ≠ a)
        (hM : ∀ c w, Ψ c (pairShearTranslationMove (Equiv.refl _) (Equiv.refl _) i j m (c, w)).2 =
          elementaryMove a b (Ψ c w)) :
        𝔼 q, (G (pairShearTranslationMove (Equiv.refl _) (Equiv.refl _) i j m q) - G q) ^ 2 ≤
          dir g :=
      hterm hab _ (fun q ↦ by fin_cases m <;> rfl) hM
    have e0 := hmv 0 (a := i) (b := j) hji fun c w ↦ update_smul_shear hik hjk c w
    have e1 := hmv 1 (a := j) (b := i) hji.symm fun c w ↦ update_smul_shear hjk hik c w
    have e2 := hmv 2 (a := i) (b := k) hik.symm fun c w ↦ update_smul_translate hik c w
    have e3 := hmv 3 (a := j) (b := k) hjk.symm fun c w ↦ update_smul_translate hjk c w
    linarith
  -- Efron–Stein, with the coordinate `k` free and the others paired.
  have hD : 0 ≤ dir g :=
    sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ expect_nonneg fun _ _ ↦ sq_nonneg _
  rw [← hL]
  refine (Fintype.expect_sq_sub_expect_le_sum_expect_sq_sub_update G).trans ?_
  calc ∑ i, 𝔼 q, (G q - 𝔼 a, G (q.1, update q.2 i a)) ^ 2 ≤ ∑ _i : Fin H, 2048 * dir g := by
        refine sum_le_sum fun i _ ↦ ?_
        by_cases hik : i = k
        · subst hik
          rw [hk]
          positivity
        · exact hi i hik
    _ = 2048 * H * dir g := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring



/-- **Gluing two fibrations**: for `k ≠ l`, the fiber averages over `{F k = c}` and `{F l = d}`
differ little on independent nonzero values `c` and `d`. -/
private theorem expect_nz_nz_sq_le {k l : Fin H} (hkl : k ≠ l) (g : (Fin H → ZMod P) → ℝ) :
    𝔼 c, 𝔼 d, nz c * nz d * (fib g k c - fib g l d) ^ 2 ≤
      2 * 𝔼 F, nz (F k) * (g F - fib g k (F k)) ^ 2 +
        2 * 𝔼 F, nz (F l) * (g F - fib g l (F l)) ^ 2 := by
  rw [← expect_comp_eval_eval hkl fun c d ↦ nz c * nz d * (fib g k c - fib g l d) ^ 2,
    mul_expect, mul_expect, ← expect_add_distrib]
  refine expect_le_expect fun F _ ↦ ?_
  have h1 := nz_nonneg (F k)
  have h2 := nz_nonneg (F l)
  have h3 := nz_le_one (F k)
  have h4 := nz_le_one (F l)
  have hsq : (fib g k (F k) - fib g l (F l)) ^ 2 ≤
      2 * (g F - fib g k (F k)) ^ 2 + 2 * (g F - fib g l (F l)) ^ 2 := by
    nlinarith [sq_nonneg (2 * g F - fib g k (F k) - fib g l (F l))]
  have hA := sq_nonneg (g F - fib g k (F k))
  have hB := sq_nonneg (g F - fib g l (F l))
  have hkk : nz (F k) * nz (F l) ≤ nz (F k) := by nlinarith
  have hll : nz (F k) * nz (F l) ≤ nz (F l) := by nlinarith
  calc nz (F k) * nz (F l) * (fib g k (F k) - fib g l (F l)) ^ 2
      ≤ nz (F k) * nz (F l) * (2 * (g F - fib g k (F k)) ^ 2 + 2 * (g F - fib g l (F l)) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg h1 h2)
    _ ≤ 2 * (nz (F k) * (g F - fib g k (F k)) ^ 2) +
          2 * (nz (F l) * (g F - fib g l (F l)) ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_right hkk hA, mul_le_mul_of_nonneg_right hll hB]

/-- The second moments of the fiber averages about the weighted mean `ȳ` of `fib g l`, on the
nonzero values, are controlled by the gluing term. -/
private theorem expect_nz_sq_sub_le {k l : Fin H} (g : (Fin H → ZMod P) → ℝ) :
    (1 / 2) * 𝔼 c, nz c * (fib g k c - (𝔼 d, nz d * fib g l d) / 𝔼 d : ZMod P, nz d) ^ 2 ≤
        𝔼 c, 𝔼 d, nz c * nz d * (fib g k c - fib g l d) ^ 2 ∧
      (1 / 2) * 𝔼 d, nz d * (fib g l d - (𝔼 d, nz d * fib g l d) / 𝔼 d : ZMod P, nz d) ^ 2 ≤
        𝔼 c, 𝔼 d, nz c * nz d * (fib g k c - fib g l d) ^ 2 := by
  have hW := half_le_expect_nz (P := P)
  have hW0 : 𝔼 d : ZMod P, nz d ≠ 0 := by linarith
  set ybar := (𝔼 d, nz d * fib g l d) / 𝔼 d : ZMod P, nz d
  set xbar := (𝔼 c, nz c * fib g k c) / 𝔼 c : ZMod P, nz c
  constructor
  · -- For each `c`, average over `d`.
    have hc (c : ZMod P) :
        (1 / 2) * (fib g k c - ybar) ^ 2 ≤ 𝔼 d, nz d * (fib g l d - fib g k c) ^ 2 := by
      have := (expect_mul_sq_sub_ge nz (fib g l) (fib g k c) nz_nonneg hW0).1
      have h0 := sq_nonneg (fib g k c - ybar)
      calc (1 / 2) * (fib g k c - ybar) ^ 2 ≤ (𝔼 d, nz d) * (ybar - fib g k c) ^ 2 := by
            rw [show (ybar - fib g k c) ^ 2 = (fib g k c - ybar) ^ 2 by ring]
            exact mul_le_mul_of_nonneg_right hW h0
        _ ≤ _ := this
    rw [mul_expect]
    refine expect_le_expect fun c _ ↦ ?_
    calc 1 / 2 * (nz c * (fib g k c - ybar) ^ 2) = nz c * ((1 / 2) * (fib g k c - ybar) ^ 2) := by
          ring
      _ ≤ nz c * 𝔼 d, nz d * (fib g l d - fib g k c) ^ 2 :=
          mul_le_mul_of_nonneg_left (hc c) (nz_nonneg c)
      _ = _ := by
          rw [mul_expect]
          exact expect_congr rfl fun d _ ↦ by ring
  · -- For each `d`, average over `c`; then `ybar` beats `xbar`.
    have hd (d : ZMod P) :
        (1 / 2) * (fib g l d - xbar) ^ 2 ≤ 𝔼 c, nz c * (fib g k c - fib g l d) ^ 2 := by
      have := (expect_mul_sq_sub_ge nz (fib g k) (fib g l d) nz_nonneg hW0).1
      have h0 := sq_nonneg (fib g l d - xbar)
      calc (1 / 2) * (fib g l d - xbar) ^ 2 ≤ (𝔼 c, nz c) * (xbar - fib g l d) ^ 2 := by
            rw [show (xbar - fib g l d) ^ 2 = (fib g l d - xbar) ^ 2 by ring]
            exact mul_le_mul_of_nonneg_right hW h0
        _ ≤ _ := this
    have hmin := (expect_mul_sq_sub_ge nz (fib g l) xbar nz_nonneg hW0).2
    calc (1 / 2) * 𝔼 d, nz d * (fib g l d - ybar) ^ 2
        ≤ (1 / 2) * 𝔼 d, nz d * (fib g l d - xbar) ^ 2 :=
          mul_le_mul_of_nonneg_left hmin (by norm_num)
      _ ≤ 𝔼 d, 𝔼 c, nz c * nz d * (fib g k c - fib g l d) ^ 2 := by
          rw [mul_expect]
          refine expect_le_expect fun d _ ↦ ?_
          calc 1 / 2 * (nz d * (fib g l d - xbar) ^ 2)
              = nz d * ((1 / 2) * (fib g l d - xbar) ^ 2) := by
                ring
            _ ≤ nz d * 𝔼 c, nz c * (fib g k c - fib g l d) ^ 2 :=
                mul_le_mul_of_nonneg_left (hd d) (nz_nonneg d)
            _ = _ := by
                rw [mul_expect]
                exact expect_congr rfl fun c _ ↦ by ring
      _ = _ := expect_comm _ _ _

/-- **The Poincaré inequality for the elementary moves on the nonzero vectors** of `(ZMod P) ^ H`,
for a prime `P` and `H ≥ 3`, uniformly in `P`: every real function `g` has, about some constant, a
second moment on the nonzero vectors at most `36864 H²` times its total squared change along the
elementary moves `F ↦ F + F b • e a`, `a ≠ b`. -/
theorem exists_expect_sq_sub_le_elementaryMove (hH : 3 ≤ H) (g : (Fin H → ZMod P) → ℝ) :
    ∃ m : ℝ, 𝔼 F, (if F = 0 then 0 else (g F - m) ^ 2) ≤
      36864 * H ^ 2 * ∑ a, ∑ b ∈ univ.erase a, 𝔼 F, (g (elementaryMove a b F) - g F) ^ 2 := by
  have h0 : 0 < H := by omega
  set k₀ : Fin H := ⟨0, h0⟩
  set k₁ : Fin H := ⟨1, by omega⟩
  have h01 : k₀ ≠ k₁ := by simp [k₀, k₁, Fin.ext_iff]
  set B := 2048 * (H : ℝ) * dir g
  have hS (k : Fin H) : 𝔼 F, nz (F k) * (g F - fib g k (F k)) ^ 2 ≤ B := fiber_bound hH k g
  have hS0 (k : Fin H) : 0 ≤ 𝔼 F, nz (F k) * (g F - fib g k (F k)) ^ 2 :=
    expect_nonneg fun F _ ↦ mul_nonneg (nz_nonneg _) (sq_nonneg _)
  set ybar := (𝔼 d, nz d * fib g k₀ d) / 𝔼 d : ZMod P, nz d
  refine ⟨ybar, ?_⟩
  -- On `{F k ≠ 0}`, `g` is close to `ybar`.
  have hT (k : Fin H) : 𝔼 F, nz (F k) * (g F - ybar) ^ 2 ≤ 18 * B := by
    have hsplit : 𝔼 F, nz (F k) * (g F - ybar) ^ 2 ≤
        2 * 𝔼 F, nz (F k) * (g F - fib g k (F k)) ^ 2 +
          2 * 𝔼 c, nz c * (fib g k c - ybar) ^ 2 := by
      rw [← expect_comp_eval k fun c ↦ nz c * (fib g k c - ybar) ^ 2, mul_expect, mul_expect,
        ← expect_add_distrib]
      refine expect_le_expect fun F _ ↦ ?_
      have := nz_nonneg (F k)
      nlinarith [sq_nonneg (g F - 2 * fib g k (F k) + ybar),
        mul_nonneg this (sq_nonneg (g F - 2 * fib g k (F k) + ybar))]
    by_cases hk : k = k₀
    · subst hk
      have hQ := expect_nz_nz_sq_le h01.symm g
      have hb := (expect_nz_sq_sub_le (k := k₁) (l := k₀) g).2
      have := hS k₀
      have := hS k₁
      have := hS0 k₁
      have := hS0 k₀
      nlinarith
    · have hQ := expect_nz_nz_sq_le hk g
      have hb := (expect_nz_sq_sub_le (k := k) (l := k₀) g).1
      have := hS k
      have := hS k₀
      have := hS0 k
      have := hS0 k₀
      nlinarith
  -- Every nonzero vector has a nonzero coordinate.
  have hpt (F : Fin H → ZMod P) :
      (if F = 0 then 0 else (g F - ybar) ^ 2) ≤ ∑ k, nz (F k) * (g F - ybar) ^ 2 := by
    split_ifs with hF
    · exact sum_nonneg fun k _ ↦ mul_nonneg (nz_nonneg _) (sq_nonneg _)
    · obtain ⟨k, hk⟩ : ∃ k, F k ≠ 0 := by
        by_contra h
        push Not at h
        exact hF (funext h)
      have h1 : nz (F k) = 1 := by simp [nz, hk]
      calc (g F - ybar) ^ 2 = nz (F k) * (g F - ybar) ^ 2 := by rw [h1, one_mul]
        _ ≤ _ := single_le_sum (f := fun k ↦ nz (F k) * (g F - ybar) ^ 2)
            (fun k _ ↦ mul_nonneg (nz_nonneg _) (sq_nonneg _)) (mem_univ k)
  calc 𝔼 F, (if F = 0 then 0 else (g F - ybar) ^ 2) ≤ 𝔼 F, ∑ k, nz (F k) * (g F - ybar) ^ 2 :=
        expect_le_expect fun F _ ↦ hpt F
    _ = ∑ k, 𝔼 F, nz (F k) * (g F - ybar) ^ 2 := expect_sum_comm _ _ _
    _ ≤ ∑ _k : Fin H, 18 * B := sum_le_sum fun k _ ↦ hT k
    _ = 36864 * H ^ 2 * dir g := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp only [B]
        ring

end Cslib.RotationMap
