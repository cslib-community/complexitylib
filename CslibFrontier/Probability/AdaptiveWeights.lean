/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer weights for adaptive Boolean computations

A finite computation chooses a Boolean answer at each step. The two answer weights sum to a
common denominator `D`, but may depend on the complete current state. Thus later answer weights
may depend on earlier answers. Products of these weights give unnormalized transcript weights.

This finite weighted-tree calculation is used in approximate oracle simulation
[Fenner2003]. It makes no computability or machine-resource assumption.

## Main definitions

* `AdaptiveWeights.branchWeight`: the weight of one answer, `p s` for `true` and `D - p s` for
  `false`.
* `AdaptiveWeights.pathWeight`: the product of weights along an explicit answer list.
* `AdaptiveWeights.acceptWeight`: the total weight of accepting answer sequences.

## Main results

* `AdaptiveWeights.pathWeight_eq_prod`: express a transcript weight as a product over prefixes.
* `AdaptiveWeights.acceptWeight_eq_sum`: express the accepting weight as a finite Boolean sum.
* `AdaptiveWeights.acceptWeight_bounds`: accepting weight lies between zero and `D ^ n`.
* `AdaptiveWeights.acceptWeight_error`: per-step wrong-answer bounds give an adaptive error bound.
* `AdaptiveWeights.sum_error`: amplified error remains small after summing a Boolean batch.

## References

* [S. Fenner, *PP-Lowness and a Simple Definition of AWPP*][Fenner2003]
-/

@[expose] public section

namespace Cslib.Probability.AdaptiveWeights

open Finset

variable {σ : Type*}

/-- Branch weights with a common total `D`; the true-answer numerator may depend on the state. -/
def branchWeight (D : ℤ) (p : σ → ℤ) (s : σ) (b : Bool) : ℤ :=
  if b then p s else D - p s

/-- The product of branch weights along a transcript. The transition may depend on each answer. -/
def pathWeight (D : ℤ) (p : σ → ℤ) (step : σ → Bool → σ) : σ → List Bool → ℤ
  | _, [] => 1
  | s, b :: bs => branchWeight D p s b * pathWeight D p step (step s b) bs

/-- A product over the successive replay prefixes, suitable for uniform counting products. -/
theorem pathWeight_eq_prod (D : ℤ) (p : σ → ℤ) (step : σ → Bool → σ)
    (s : σ) (bs : List Bool) :
    pathWeight D p step s bs = ∏ i ∈ range bs.length,
      branchWeight D p (bs.take i |>.foldl step s) (bs.getD i false) := by
  induction bs generalizing s with
  | nil => simp [pathWeight]
  | cons b bs ih =>
    simp only [pathWeight, List.length_cons, prod_range_succ', List.take_succ_cons,
      List.foldl_cons, List.getD_cons_succ, List.take_zero, List.foldl_nil,
      List.getD_cons_zero, ih]
    ring

/-- Total accepting weight after a fixed number of adaptive steps. -/
def acceptWeight (D : ℤ) (p : σ → ℤ) (step : σ → Bool → σ) (accept : σ → Bool) :
    ℕ → σ → ℤ
  | 0, s => if accept s then 1 else 0
  | n + 1, s =>
      (D - p s) * acceptWeight D p step accept n (step s false) +
        p s * acceptWeight D p step accept n (step s true)

/-- The recursive weighted computation sums precisely the accepting transcript weights. -/
theorem acceptWeight_eq_sum (D : ℤ) (p : σ → ℤ) (step : σ → Bool → σ)
    (accept : σ → Bool) (n : ℕ) (s : σ) :
    acceptWeight D p step accept n s = ∑ w : Fin n → Bool,
      pathWeight D p step s (List.ofFn w) *
        if accept ((List.ofFn w).foldl step s) then 1 else 0 := by
  induction n generalizing s with
  | zero => simp [acceptWeight, pathWeight]
  | succ n ih =>
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Bool).sum_comp,
      Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ, Fin.cons_zero,
      Fin.cons_succ, pathWeight, List.foldl_cons, branchWeight, Bool.false_eq_true,
      ite_false, ite_true, mul_assoc, ← mul_sum, ← ih, acceptWeight]
    ring

/-- Nonnegative branch weights give an accepting weight between zero and the total mass. -/
theorem acceptWeight_bounds {D : ℤ} {p : σ → ℤ} (step : σ → Bool → σ)
    (accept : σ → Bool) (hp : ∀ s, 0 ≤ p s ∧ p s ≤ D)
    (n : ℕ) (s : σ) :
    0 ≤ acceptWeight D p step accept n s ∧ acceptWeight D p step accept n s ≤ D ^ n := by
  induction n generalizing s with
  | zero => simp only [acceptWeight, pow_zero]; split <;> norm_num
  | succ n ih =>
    obtain ⟨hf₀, hf₁⟩ := ih (step s false)
    obtain ⟨ht₀, ht₁⟩ := ih (step s true)
    obtain ⟨hp₀, hp₁⟩ := hp s
    rw [acceptWeight, pow_succ]
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hp₁) hf₀) (mul_nonneg hp₀ ht₀)
    · calc
        (D - p s) * acceptWeight D p step accept n (step s false) +
            p s * acceptWeight D p step accept n (step s true) ≤
            (D - p s) * D ^ n + p s * D ^ n :=
          add_le_add (mul_le_mul_of_nonneg_left hf₁ (sub_nonneg.mpr hp₁))
            (mul_le_mul_of_nonneg_left ht₁ hp₀)
        _ = D ^ n * D := by ring

private theorem abs_sub_indicator_le {v E : ℤ} (hv : 0 ≤ v ∧ v ≤ E) (b : Bool) :
    |v - E * (if b then 1 else 0)| ≤ E := by
  cases b
  · simpa only [Bool.false_eq_true, ite_false, mul_zero, sub_zero, abs_of_nonneg hv.1] using hv.2
  · simp only [ite_true, mul_one, abs_of_nonpos (sub_nonpos.mpr hv.2)]
    omega

private theorem error_step {D E M wg wo vg vo n : ℤ} (c : Bool)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hM : 0 ≤ M) (hn : 0 ≤ n)
    (hg : 0 ≤ wg) (ho : 0 ≤ wo) (hsum : wg + wo = D)
    (herr : M * wo ≤ D) (hvo : 0 ≤ vo ∧ vo ≤ E)
    (hvg : M * |vg - E * (if c then 1 else 0)| ≤ n * E) :
    M * |wg * vg + wo * vo - (D * E) * (if c then 1 else 0)| ≤
      (n + 1) * (D * E) := by
  have hbad := abs_sub_indicator_le hvo c
  have hdecomp : wg * vg + wo * vo - (D * E) * (if c then 1 else 0) =
      wg * (vg - E * (if c then 1 else 0)) + wo * (vo - E * (if c then 1 else 0)) := by
    rw [← hsum]
    ring
  rw [hdecomp]
  calc
    M * |wg * (vg - E * (if c then 1 else 0)) +
        wo * (vo - E * (if c then 1 else 0))| ≤
        M * (wg * |vg - E * (if c then 1 else 0)| +
          wo * |vo - E * (if c then 1 else 0)|) := by
      apply mul_le_mul_of_nonneg_left _ hM
      simpa only [abs_mul, abs_of_nonneg hg, abs_of_nonneg ho] using abs_add_le
        (wg * (vg - E * (if c then 1 else 0))) (wo * (vo - E * (if c then 1 else 0)))
    _ = wg * (M * |vg - E * (if c then 1 else 0)|) +
        (M * wo) * |vo - E * (if c then 1 else 0)| := by ring
    _ ≤ wg * (n * E) + D * E := by gcongr
    _ ≤ D * (n * E) + D * E :=
      add_le_add (mul_le_mul_of_nonneg_right (show wg ≤ D by omega) (mul_nonneg hn hE)) le_rfl
    _ = (n + 1) * (D * E) := by ring

/-- If every step gives weight at most `D / M` to the wrong answer, the total acceptance weight
differs from the ideal deterministic answer by at most `n / M` of the total mass. Answers and
future weights may depend on the state, so the estimate includes adaptive computations. -/
theorem acceptWeight_error {D M : ℤ} {p : σ → ℤ} (step : σ → Bool → σ)
    (accept answer : σ → Bool) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hp : ∀ s, 0 ≤ p s ∧ p s ≤ D)
    (herr : ∀ s, M * branchWeight D p s (!(answer s)) ≤ D) (n : ℕ) (s : σ) :
    M * |acceptWeight D p step accept n s - D ^ n *
      (if accept ((fun s => step s (answer s))^[n] s) then 1 else 0)| ≤ (n : ℤ) * D ^ n := by
  induction n generalizing s with
  | zero => cases hs : accept s <;> simp [acceptWeight, hs]
  | succ n ih =>
    have h := ih (step s (answer s))
    have he := herr s
    have hb₀ := acceptWeight_bounds step accept hp n (step s false)
    have hb₁ := acceptWeight_bounds step accept hp n (step s true)
    obtain ⟨hp₀, hp₁⟩ := hp s
    rw [acceptWeight, pow_succ, mul_comm (D ^ n) D, Function.iterate_succ_apply]
    cases ha : answer s
    · simp only [ha, Bool.not_false, branchWeight, ite_true] at he h ⊢
      simpa only [Nat.cast_add, Nat.cast_one] using error_step
        (accept ((fun s => step s (answer s))^[n] (step s false))) hD (pow_nonneg hD n) hM
        (Nat.cast_nonneg n) (sub_nonneg.mpr hp₁) hp₀ (by ring) he hb₁ h
    · simp only [ha, Bool.not_true, branchWeight, Bool.false_eq_true, ite_false] at he h ⊢
      have he' := error_step
        (accept ((fun s => step s (answer s))^[n] (step s true))) hD (pow_nonneg hD n) hM
        (Nat.cast_nonneg n) hp₀ (sub_nonneg.mpr hp₁) (by ring) he hb₀ h
      simpa only [Nat.cast_add, Nat.cast_one, add_comm] using he'

/-- Summing over `m` witness bits preserves a one-sixteenth total error when each of `n` steps
has error at most `2 ^ -(m + n + 4)`. All quantities are unnormalized integers. -/
theorem sum_error {m n : ℕ} {E : ℤ} (hE : 0 ≤ E)
    (f : (Fin m → Bool) → ℤ) (ideal : (Fin m → Bool) → Bool)
    (herr : ∀ w, (2 : ℤ) ^ (m + n + 4) *
      |f w - E * (if ideal w then 1 else 0)| ≤ (n : ℤ) * E) :
    16 * |(∑ w, f w) - E * ∑ w, (if ideal w then (1 : ℤ) else 0)| ≤ E := by
  let M : ℤ := 2 ^ (m + n + 4)
  have hM : 0 < M := by dsimp [M]; positivity
  have hdiff : (∑ w, f w) - E * ∑ w, (if ideal w then (1 : ℤ) else 0) =
      ∑ w, (f w - E * (if ideal w then 1 else 0)) := by
    rw [sum_sub_distrib, mul_sum]
  have hsum : M * |∑ w, (f w - E * (if ideal w then (1 : ℤ) else 0))| ≤
      (2 : ℤ) ^ m * ((n : ℤ) * E) := by
    calc
      M * |∑ w, (f w - E * (if ideal w then (1 : ℤ) else 0))| ≤
          M * ∑ w, |f w - E * (if ideal w then (1 : ℤ) else 0)| :=
        mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hM.le
      _ = ∑ w, M * |f w - E * (if ideal w then (1 : ℤ) else 0)| := by rw [mul_sum]
      _ ≤ ∑ _w : Fin m → Bool, (n : ℤ) * E := sum_le_sum fun w _ => herr w
      _ = (2 : ℤ) ^ m * ((n : ℤ) * E) := by
        simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hn : (n : ℤ) ≤ (2 : ℤ) ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hscale : 16 * ((2 : ℤ) ^ m * n) ≤ M := by
    dsimp [M]
    rw [pow_add, pow_add, show (2 : ℤ) ^ 4 = 16 by norm_num]
    nlinarith [mul_le_mul_of_nonneg_left hn (show 0 ≤ (2 : ℤ) ^ m by positivity)]
  rw [hdiff]
  apply (mul_le_mul_iff_right₀ hM).mp
  calc
    M * (16 * |∑ w, (f w - E * (if ideal w then (1 : ℤ) else 0))|) =
        16 * (M * |∑ w, (f w - E * (if ideal w then (1 : ℤ) else 0))|) := by ring
    _ ≤ 16 * ((2 : ℤ) ^ m * ((n : ℤ) * E)) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ M * E := by nlinarith [mul_le_mul_of_nonneg_right hscale hE]

end Cslib.Probability.AdaptiveWeights
