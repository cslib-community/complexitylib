/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Hitting
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.Combinatorics.Expander.Mixing
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.Finset.Variance

/-!
# Varying-density hitting bounds for expander walks

Equation (8.24) and the constant-set corollary of [Goldreich2007DraftR4], Exercise 8.43
(printed p. 381, PDF p. 117). A uniform initial vertex and independent uniform incident
slots generate the walk. Here `t` counts edges, so the source length is `t + 1`.
The native parameter is `spectralExpansion`; the transport theorem accepts any upper
bound, in particular the source normalized eigenvalue bound `lambda / d`.
No uniform machine or running-time claim is made. Exercise 8.44 is separate.

The supported-function second-moment estimate is dualized using self-adjointness to
bound a masked output; iterating it retains each individual density.

## Main results

* `Cslib.RotationMap.expect_mask_walk_sq_le`: the masked-output second-moment estimate.
* `Cslib.RotationMap.dens_filter_forall_walkAt_mem_le_product`: the varying-density product.
* `Cslib.RotationMap.dens_filter_forall_walkAt_mem_le_rpow_of_spectralExpansion_le`:
  the constant-set corollary with explicit source parameters.
-/

public section

namespace Cslib.RotationMap
open Finset
open scoped BigOperators
variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [DecidableEq V] (G : RotationMap V D)

omit [DecidableEq V] [Nonempty V] in
/-- A supported function has small second moment after a walk step. -/
theorem expect_walk_sq_le_dens_add_spectralExpansion_sq {B : Finset V}
    {f : V → ℝ} (hf : ∀ v ∉ B, f v = 0) :
    𝔼 v, G.walk f v ^ 2 ≤
      ((dens B : ℝ) + G.spectralExpansion ^ 2) * 𝔼 v, f v ^ 2 := by
  have h := G.expect_walk_pow_sub_expect_sq_le 1 f
  simp only [pow_one, Nat.mul_one] at h
  have hw := G.expect_walk f
  rw [← hw, Fintype.expect_sub_expect_sq, hw, Fintype.expect_sub_expect_sq] at h
  have hs := Fintype.sq_expect_le_dens_mul_expect_sq_of_eq_zero hf
  have hn := mul_nonneg (sq_nonneg G.spectralExpansion) (sq_nonneg (𝔼 v, f v))
  nlinarith

omit [Nonempty V] in
/-- Restricting the output of a walk to a set of density `ρ` has squared norm at
most `ρ + η²` times the input squared norm. This is the adjoint of the supported bound. -/
theorem expect_mask_walk_sq_le (B : Finset V) (f : V → ℝ) :
    𝔼 v, (if v ∈ B then G.walk f v else 0) ^ 2 ≤
      ((dens B : ℝ) + G.spectralExpansion ^ 2) * 𝔼 v, f v ^ 2 := by
  let g : V → ℝ := fun v => if v ∈ B then G.walk f v else 0
  have hg : ∀ v ∉ B, g v = 0 := by intro v hv; simp [g, hv]
  have heq : (𝔼 v, g v ^ 2) = 𝔼 v, g v * G.walk f v := by
    apply expect_congr rfl
    intro v _
    by_cases hv : v ∈ B <;> simp [g, hv, pow_two]
  have hc := expect_mul_sq_le_sq_mul_sq univ (G.walk g) f
  rw [← G.expect_mul_walk_comm g f, ← heq] at hc
  have hb := G.expect_walk_sq_le_dens_add_spectralExpansion_sq hg
  have hn : 0 ≤ 𝔼 v, f v ^ 2 := expect_nonneg fun _ _ => sq_nonneg _
  have hgn : 0 ≤ 𝔼 v, g v ^ 2 := expect_nonneg fun _ _ => sq_nonneg _
  have hm := mul_le_mul_of_nonneg_right hb hn
  change (𝔼 v, g v ^ 2) ≤ _
  by_cases hz : (𝔼 v, g v ^ 2) = 0
  · rw [hz]
    positivity
  · have hp : 0 < 𝔼 v, g v ^ 2 := lt_of_le_of_ne hgn (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hp).mp
    calc (𝔼 v, g v ^ 2) * (𝔼 v, g v ^ 2) ≤
        ((dens B : ℝ) + G.spectralExpansion ^ 2) * (𝔼 v, g v ^ 2) * (𝔼 v, f v ^ 2) := by
          simpa only [pow_two] using hc.trans hm
      _ = _ := by ring

/-- Propagate an input through the successive set masks. -/
private noncomputable def maskedSteps : ℕ → (ℕ → Finset V) → (V → ℝ) → V → ℝ
  | 0, _, f => f
  | t + 1, B, f => maskedSteps t (fun i => B (i + 1))
      (fun v => if v ∈ B 0 then G.walk f v else 0)

omit [Nonempty V] in
private theorem expect_maskedSteps_sq_le (t : ℕ) (B : ℕ → Finset V) (f : V → ℝ) :
    (𝔼 v, G.maskedSteps t B f v ^ 2) ≤
      (∏ i ∈ range t, ((dens (B i) : ℝ) + G.spectralExpansion ^ 2)) *
        (𝔼 v, f v ^ 2) := by
  induction t generalizing B f with
  | zero => simp [maskedSteps]
  | succ t ih =>
    calc _ ≤ (∏ i ∈ range t, ((dens (B (i + 1)) : ℝ) + G.spectralExpansion ^ 2)) *
        (𝔼 v, (if v ∈ B 0 then G.walk f v else 0) ^ 2) := ih _ _
      _ ≤ (∏ i ∈ range t, ((dens (B (i + 1)) : ℝ) + G.spectralExpansion ^ 2)) *
        (((dens (B 0) : ℝ) + G.spectralExpansion ^ 2) * (𝔼 v, f v ^ 2)) := by
          gcongr
          exact G.expect_mask_walk_sq_le _ _
      _ = _ := by rw [prod_range_succ']; ring

omit [Nonempty V] [Nonempty D] in
private theorem expect_mul_walk_weightedWalk (t : ℕ) (B : ℕ → Finset V) (f : V → ℝ) :
    (𝔼 v, f v * G.walk (G.weightedWalk t
      (fun i v => if v ∈ B i then (1 : ℝ) else 0)) v) =
      𝔼 v, G.maskedSteps (t + 1) B f v := by
  induction t generalizing B f with
  | zero =>
    rw [G.expect_mul_walk_comm]
    apply expect_congr rfl
    intro v _
    simp only [weightedWalk_zero, maskedSteps]
    split_ifs <;> simp
  | succ t ih =>
    rw [G.expect_mul_walk_comm]
    have heq (v : V) : G.walk f v * G.weightedWalk (t + 1)
        (fun i v => if v ∈ B i then (1 : ℝ) else 0) v =
        (if v ∈ B 0 then G.walk f v else 0) *
          G.walk (G.weightedWalk t (fun i v => if v ∈ B (i + 1) then (1 : ℝ) else 0)) v := by
      simp only [weightedWalk_succ, Pi.mul_apply]
      split_ifs <;> simp
    simp only [heq]
    exact ih _ _

/-- The squared varying-density hitting bound; `t` counts edges, hence `t + 1` vertices. -/
theorem sq_dens_filter_forall_walkAt_mem_le_product (B : ℕ → Finset V) (t : ℕ) :
    (dens {p : V × (Fin t → D) | ∀ i ≤ t, G.walkAt p i ∈ B i} : ℝ) ^ 2 ≤
      (dens (B 0) : ℝ) *
        ∏ i ∈ range t, ((dens (B (i + 1)) : ℝ) + G.spectralExpansion ^ 2) := by
  let f : V → ℝ := fun v => if v ∈ B 0 then 1 else 0
  have hprob : (dens {p : V × (Fin t → D) | ∀ i ≤ t, G.walkAt p i ∈ B i} : ℝ) =
      𝔼 v, G.maskedSteps t (fun i => B (i + 1)) f v := by
    rw [← Fintype.expect_boole]
    have hprod := G.expect_weightedWalk t (fun i v => if v ∈ B i then (1 : ℝ) else 0)
    have heq : (𝔼 p : V × (Fin t → D),
        if ∀ i ≤ t, G.walkAt p i ∈ B i then (1 : ℝ) else 0) =
        𝔼 v, G.weightedWalk t (fun i v => if v ∈ B i then (1 : ℝ) else 0) v := by
      rw [hprod]
      apply expect_congr rfl
      intro p _
      simp only [prod_ite_zero, prod_const_one, mem_range, Nat.lt_succ_iff]
    rw [heq]
    cases t with
    | zero => rfl
    | succ t =>
      simp only [weightedWalk_succ, Pi.mul_apply]
      exact G.expect_mul_walk_weightedWalk t (fun i => B (i + 1)) f
  rw [hprob]
  have hc := expect_mul_sq_le_sq_mul_sq univ
    (G.maskedSteps t (fun i => B (i + 1)) f) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Fintype.expect_const] at hc
  have hb := G.expect_maskedSteps_sq_le t (fun i => B (i + 1)) f
  have hf : (𝔼 v, f v ^ 2) = (dens (B 0) : ℝ) := Fintype.expect_boole_mem_sq _
  rw [hf] at hb
  exact hc.trans (hb.trans_eq (mul_comm _ _))

/-- Goldreich Exercise 8.43, equation (8.24), for `t + 1` vertices. -/
theorem dens_filter_forall_walkAt_mem_le_product (B : ℕ → Finset V) (t : ℕ) :
    (dens {p : V × (Fin t → D) | ∀ i ≤ t, G.walkAt p i ∈ B i} : ℝ) ≤
      Real.sqrt (dens (B 0) : ℝ) *
        ∏ i ∈ range t, Real.sqrt ((dens (B (i + 1)) : ℝ) + G.spectralExpansion ^ 2) := by
  apply (abs_le_of_sq_le_sq' ?_ (by positivity)).2
  rw [mul_pow, Real.sq_sqrt (by positivity), ← prod_pow]
  have hs (i : ℕ) : (Real.sqrt ((dens (B (i + 1)) : ℝ) + G.spectralExpansion ^ 2)) ^ 2 =
      (dens (B (i + 1)) : ℝ) + G.spectralExpansion ^ 2 := Real.sq_sqrt (by positivity)
  simp only [hs]
  exact G.sq_dens_filter_forall_walkAt_mem_le_product B t

/-- Transport of equation (8.24) to an upper bound on the normalized spectral parameter. -/
theorem dens_filter_forall_walkAt_mem_le_product_of_spectralExpansion_le
    (B : ℕ → Finset V) (t : ℕ) {η : ℝ} (hη : G.spectralExpansion ≤ η) :
    (dens {p : V × (Fin t → D) | ∀ i ≤ t, G.walkAt p i ∈ B i} : ℝ) ≤
      Real.sqrt (dens (B 0) : ℝ) *
        ∏ i ∈ range t, Real.sqrt ((dens (B (i + 1)) : ℝ) + η ^ 2) := by
  refine (G.dens_filter_forall_walkAt_mem_le_product B t).trans ?_
  have hn := G.spectralExpansion_nonneg
  gcongr

/-- The constant-set corollary for `t + 1` vertices, in square-root power form:
`(sqrt (ρ + η²))^(t+1) = (ρ + η²)^((t+1)/2)`. -/
theorem dens_filter_forall_walkAt_mem_le_sqrt_pow (B : Finset V) (t : ℕ)
    {η : ℝ} (hη : G.spectralExpansion ≤ η) :
    (dens {p : V × (Fin t → D) | ∀ i ≤ t, G.walkAt p i ∈ B} : ℝ) ≤
      Real.sqrt ((dens B : ℝ) + η ^ 2) ^ (t + 1) := by
  have h := G.dens_filter_forall_walkAt_mem_le_product_of_spectralExpansion_le
    (fun _ => B) t hη
  simp only [prod_const, card_range] at h
  refine h.trans ?_
  rw [pow_succ' (Real.sqrt ((dens B : ℝ) + η ^ 2)) t]
  gcongr
  exact le_add_of_nonneg_right (sq_nonneg η)

/-- Goldreich's constant-set bound, with the source's unnormalized eigenvalue
bound `λ` and degree `d` kept explicit. The walk visits `t + 1` vertices. -/
theorem dens_filter_forall_walkAt_mem_le_rpow_of_spectralExpansion_le
    (B : Finset V) (t : ℕ) (lambda d : ℝ) (h : G.spectralExpansion ≤ lambda / d) :
    (dens {p : V × (Fin t → D) | ∀ i ≤ t, G.walkAt p i ∈ B} : ℝ) ≤
      ((dens B : ℝ) + (lambda / d) ^ 2) ^ (((t + 1 : ℕ) : ℝ) / 2) := by
  refine (G.dens_filter_forall_walkAt_mem_le_sqrt_pow B t h).trans_eq ?_
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

end Cslib.RotationMap
