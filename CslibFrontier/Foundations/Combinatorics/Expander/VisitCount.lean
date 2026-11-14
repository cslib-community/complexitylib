/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.HittingProduct
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Bounds
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Visit counts of expander walks

Selected-time hitting, factorial moments and integer tails for the uniform-start walk.
The walk has `t + 1` vertices and `t` independently uniform ports. Loops and parallel
edges are allowed. This is the analytic step in [Goldreich2007DraftR4], Exercise 8.44
(PDF p. 117, printed p. 381).

For `L = t + 1`, `ρ = dens W`, `η = spectralExpansion`, and `q = ρ + η²`,
the selected-time probability is at most `q^(|S|/2)`, and
`E choose(visitCount,m) ≤ choose(L,m) q^(m/2)`. The strict integer tail gains
`1/(m+1)`. The source's strict inequality therefore requires `1 ≤ m ≤ L` and
`q > 0`; without these hypotheses an empty set and `η = 0` would demand `0 < 0`.
The printed `αL` binomial parameter needs an integer convention. The half-visits
corollary uses integer division for `N > L/2`, including odd `L`.

The guideline's full-set masks in (8.24) introduce factors `sqrt(1+η²)`;
these cannot be dropped. Unrestricted norm contraction supplies factor one instead.
See source qualifications in issue #4781. No sampler or runtime claim is made.

## Main results

* `Cslib.RotationMap.dens_filter_selected_walkAt_mem_le`
* `Cslib.RotationMap.expect_choose_visitCount_le`
* `Cslib.RotationMap.dens_filter_visitCount_ge_le`
* `Cslib.RotationMap.dens_filter_visitCount_gt_le`
* `Cslib.RotationMap.dens_filter_visitCount_half_lt`
-/

public section
namespace Cslib.RotationMap
open Finset
open scoped BigOperators
variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [DecidableEq V] (G : RotationMap V D)

/-- Number of visits to `W`, including the initial vertex. -/
@[expose] def visitCount (W : Finset V) {t : ℕ} (p : V × (Fin t → D)) : ℕ :=
  ((range (t + 1)).filter fun i => G.walkAt p i ∈ W).card

omit [Fintype V] [Fintype D] [Nonempty V] [Nonempty D] in
/-- A walk cannot have more visits than vertex times. -/
theorem visitCount_le (W : Finset V) {t : ℕ} (p : V × (Fin t → D)) :
    G.visitCount W p ≤ t + 1 := by
  exact (card_filter_le _ _).trans_eq (card_range _)

omit [Fintype V] [Fintype D] [Nonempty V] [Nonempty D] in
/-- No vertex time visits the empty set. -/
@[simp] theorem visitCount_empty {t : ℕ} (p : V × (Fin t → D)) :
    G.visitCount ∅ p = 0 := by simp [visitCount]

omit [Fintype D] [Nonempty V] [Nonempty D] in
/-- Every vertex time visits the full vertex set. -/
@[simp] theorem visitCount_univ {t : ℕ} (p : V × (Fin t → D)) :
    G.visitCount univ p = t + 1 := by simp [visitCount]

omit [Fintype V] [Fintype D] [Nonempty V] [Nonempty D] in
/-- A zero-edge walk counts only its initial vertex. -/
theorem visitCount_zero (W : Finset V) (p : V × (Fin 0 → D)) :
    G.visitCount W p = if p.1 ∈ W then 1 else 0 := by
  classical
  by_cases hp : p.1 ∈ W <;> simp [visitCount, filter_singleton, walkAt_zero, hp]

/-- The selected-time hitting estimate in squared form. Unselected steps use
norm contraction, rather than the weaker full-set mask estimate from Exercise 8.43. -/
theorem sq_dens_filter_selected_walkAt_mem_le (W : Finset V) (t : ℕ)
    (S : Finset ℕ) (hS : S ⊆ range (t + 1)) :
    (dens {p : V × (Fin t → D) | ∀ i ∈ S, G.walkAt p i ∈ W} : ℝ) ^ 2 ≤
      ((dens W : ℝ) + G.spectralExpansion ^ 2) ^ S.card := by
  let B : ℕ → Finset V := fun i => if i ∈ S then W else univ
  let q : ℝ := (dens W : ℝ) + G.spectralExpansion ^ 2
  let c : ℕ → ℝ := fun i => if i ∈ S then q else 1
  have hc (i : ℕ) : 0 ≤ c i := by dsimp [c, q]; split_ifs <;> positivity
  have hstep (i : ℕ) (f : V → ℝ) :
      (𝔼 v, (if v ∈ B (i + 1) then G.walk f v else 0) ^ 2) ≤
        c (i + 1) * (𝔼 v, f v ^ 2) := by
    by_cases hi : i + 1 ∈ S
    · simpa [B, c, q, hi] using G.expect_mask_walk_sq_le W f
    · simpa [B, c, hi] using G.expect_walk_sq_le f
  have h := G.sq_dens_filter_forall_walkAt_mem_le_of_step_bounds B t
    (fun i => c (i + 1)) (fun i => hc (i + 1)) hstep
  have hevent (p : V × (Fin t → D)) :
      (∀ i ≤ t, G.walkAt p i ∈ B i) ↔ ∀ i ∈ S, G.walkAt p i ∈ W := by
    constructor
    · intro hp i hi
      have hir := mem_range.mp (hS hi)
      simpa [B, hi] using hp i (by omega)
    · intro hp i _
      by_cases hi : i ∈ S <;> simp [B, hi, hp i]
  simp only [hevent] at h
  have h0 : (dens (B 0) : ℝ) ≤ c 0 := by
    by_cases hi : 0 ∈ S
    · simp only [B, c, ite_eq_left hi]
      exact le_add_of_nonneg_right (sq_nonneg _)
    · simp [B, c, hi]
  refine h.trans ((mul_le_mul_of_nonneg_right h0
    (prod_nonneg fun i _ => hc (i + 1))).trans_eq ?_)
  rw [mul_comm, ← prod_range_succ']
  dsimp [c]
  rw [← prod_filter]
  have heq : (range (t + 1)).filter (fun i => i ∈ S) = S := by
    ext i
    exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨hS h, h⟩⟩
  rw [heq, prod_const]

/-- Selected-time hitting for any subset of the `t + 1` vertex times. -/
theorem dens_filter_selected_walkAt_mem_le (W : Finset V) (t : ℕ)
    (S : Finset ℕ) (hS : S ⊆ range (t + 1)) :
    (dens {p : V × (Fin t → D) | ∀ i ∈ S, G.walkAt p i ∈ W} : ℝ) ≤
      ((dens W : ℝ) + G.spectralExpansion ^ 2) ^ ((S.card : ℝ) / 2) := by
  have h := G.sq_dens_filter_selected_walkAt_mem_le W t S hS
  apply (abs_le_of_sq_le_sq' ?_ (by positivity)).2
  have heq : (((dens W : ℝ) + G.spectralExpansion ^ 2) ^ ((S.card : ℝ) / 2)) ^ 2 =
      ((dens W : ℝ) + G.spectralExpansion ^ 2) ^ S.card := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
    rw [Nat.cast_ofNat, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_natCast]
  rw [heq]
  exact h

/-- The binomial factorial moment of the number of visits. -/
theorem expect_choose_visitCount_le (W : Finset V) (t m : ℕ) :
    (𝔼 p : V × (Fin t → D), (Nat.choose (G.visitCount W p) m : ℝ)) ≤
      Nat.choose (t + 1) m *
        ((dens W : ℝ) + G.spectralExpansion ^ 2) ^ ((m : ℝ) / 2) := by
  let T := (range (t + 1)).powersetCard m
  have hcount (p : V × (Fin t → D)) :
      (Nat.choose (G.visitCount W p) m : ℝ) =
        ∑ S ∈ T, if ∀ i ∈ S, G.walkAt p i ∈ W then (1 : ℝ) else 0 := by
    have heq : T.filter (fun S => ∀ i ∈ S, G.walkAt p i ∈ W) =
        ((range (t + 1)).filter fun i => G.walkAt p i ∈ W).powersetCard m := by
      ext S
      simp only [T, mem_filter, mem_powersetCard, subset_iff]
      aesop
    rw [sum_boole, heq, card_powersetCard]
    rfl
  simp only [hcount]
  rw [expect_sum_comm]
  have hb : ∀ S ∈ T, (𝔼 p : V × (Fin t → D),
      if ∀ i ∈ S, G.walkAt p i ∈ W then (1 : ℝ) else 0) ≤
      ((dens W : ℝ) + G.spectralExpansion ^ 2) ^ ((m : ℝ) / 2) := by
    intro S hS
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hS
    rw [Fintype.expect_boole]
    simpa only [hcard] using G.dens_filter_selected_walkAt_mem_le W t S hsub
  calc _ ≤ ∑ _S ∈ T,
        ((dens W : ℝ) + G.spectralExpansion ^ 2) ^ ((m : ℝ) / 2) := sum_le_sum hb
    _ = _ := by rw [sum_const, nsmul_eq_mul]; simp only [T, card_powersetCard, card_range]

/-- Integer upper tail, including threshold zero and impossible thresholds. -/
theorem dens_filter_visitCount_ge_le (W : Finset V) (t m : ℕ) :
    (dens {p : V × (Fin t → D) | m ≤ G.visitCount W p} : ℝ) ≤
      Nat.choose (t + 1) m *
        ((dens W : ℝ) + G.spectralExpansion ^ 2) ^ ((m : ℝ) / 2) := by
  refine le_trans ?_ (G.expect_choose_visitCount_le W t m)
  rw [← Fintype.expect_boole]
  apply expect_le_expect
  intro p _
  split_ifs with hp
  · exact_mod_cast Nat.choose_pos hp
  · positivity

/-- Strict integer upper tail with the factorial-moment improvement `1 / (m + 1)`. -/
theorem dens_filter_visitCount_gt_le (W : Finset V) (t m : ℕ) :
    (dens {p : V × (Fin t → D) | m < G.visitCount W p} : ℝ) ≤
      (Nat.choose (t + 1) m *
        ((dens W : ℝ) + G.spectralExpansion ^ 2) ^ ((m : ℝ) / 2)) / (m + 1) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < m + 1)).mpr
  refine le_trans ?_ (G.expect_choose_visitCount_le W t m)
  rw [← Fintype.expect_boole, expect_mul]
  apply expect_le_expect
  intro p _
  split_ifs with hp
  · simp only [one_mul]
    have h := Nat.choose_le_choose m (Nat.succ_le_of_lt hp)
    rw [Nat.choose_succ_self_right] at h
    exact_mod_cast h
  · simp

/-- The source's strictly-smaller bound, with the required nondegenerate hypotheses. -/
theorem dens_filter_visitCount_gt_lt (W : Finset V) (t m : ℕ)
    (hm : 1 ≤ m) (hmL : m ≤ t + 1)
    (hq : 0 < (dens W : ℝ) + G.spectralExpansion ^ 2) :
    (dens {p : V × (Fin t → D) | m < G.visitCount W p} : ℝ) <
      Nat.choose (t + 1) m *
        ((dens W : ℝ) + G.spectralExpansion ^ 2) ^ ((m : ℝ) / 2) := by
  refine (G.dens_filter_visitCount_gt_le W t m).trans_lt ?_
  apply div_lt_self
  · exact mul_pos (by exact_mod_cast Nat.choose_pos hmL) (Real.rpow_pos_of_pos hq _)
  · exact_mod_cast (show 1 < m + 1 by omega)

/-- Goldreich's half-visits example for every positive vertex length `t + 1`.
The event uses integer division, so odd lengths have their usual strict-majority meaning. -/
theorem dens_filter_visitCount_half_lt (W : Finset V) (t : ℕ)
    (hη : G.spectralExpansion < Real.sqrt (dens W : ℝ)) :
    (dens {p : V × (Fin t → D) | (t + 1) / 2 < G.visitCount W p} : ℝ) <
      (32 * (dens W : ℝ)) ^ (((t + 1 : ℕ) : ℝ) / 4) := by
  let ρ : ℝ := dens W
  have hρ : 0 < ρ := by
    have : 0 < Real.sqrt ρ := lt_of_le_of_lt G.spectralExpansion_nonneg hη
    exact Real.sqrt_pos.mp this
  have hq : ρ + G.spectralExpansion ^ 2 < 2 * ρ := by
    have hs := Real.sq_sqrt hρ.le
    have hn := G.spectralExpansion_nonneg
    nlinarith
  by_cases hsmall : ρ ≤ 1 / 32
  · let k := (t + 2) / 2
    have hk : 0 < k := by dsimp [k]; omega
    have hkr : ((t + 1 : ℕ) : ℝ) / 4 ≤ (k : ℝ) / 2 := by
      have hi : t + 1 ≤ 2 * k := by dsimp [k]; omega
      have hi' : ((t + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hi
      linarith
    have hevent : (dens {p : V × (Fin t → D) |
        (t + 1) / 2 < G.visitCount W p} : ℝ) ≤
        dens ({p : V × (Fin t → D) | k ≤ G.visitCount W p} : Finset _) := by
      have hsub : ({p : V × (Fin t → D) | (t + 1) / 2 < G.visitCount W p} : Finset _) ⊆
          ({p : V × (Fin t → D) | k ≤ G.visitCount W p} : Finset _) := by
        intro p hp
        simp only [mem_filter, mem_univ, true_and] at hp ⊢
        dsimp [k]
        omega
      exact_mod_cast dens_mono hsub
    have hc : (0 : ℝ) < Nat.choose (t + 1) k := by
      exact_mod_cast Nat.choose_pos (show k ≤ t + 1 by dsimp [k]; omega)
    calc _ ≤ _ := hevent.trans (G.dens_filter_visitCount_ge_le W t k)
      _ < (Nat.choose (t + 1) k : ℝ) * (2 * ρ) ^ ((k : ℝ) / 2) := by
        apply mul_lt_mul_of_pos_left _ hc
        exact Real.rpow_lt_rpow (by positivity) hq (div_pos (by exact_mod_cast hk) (by norm_num))
      _ ≤ (2 : ℝ) ^ (t + 1) * (2 * ρ) ^ (((t + 1 : ℕ) : ℝ) / 4) := by
        apply mul_le_mul
        · exact_mod_cast Nat.choose_le_two_pow (t + 1) k
        · exact Real.rpow_le_rpow_of_exponent_ge (by positivity) (by linarith) hkr
        · positivity
        · positivity
      _ = _ := by
        have heq : ((2 : ℝ) ^ 4) ^ (((t + 1 : ℕ) : ℝ) / 4) = (2 : ℝ) ^ (t + 1) := by
          rw [← Real.rpow_natCast (2 : ℝ) 4, ← Real.rpow_mul (by positivity)]
          norm_num only [Nat.cast_ofNat]
          rw [show (4 : ℝ) * (((t + 1 : ℕ) : ℝ) / 4) = ((t + 1 : ℕ) : ℝ) by ring,
            Real.rpow_natCast]
        calc _ = ((2 : ℝ) ^ 4) ^ (((t + 1 : ℕ) : ℝ) / 4) *
            (2 * ρ) ^ (((t + 1 : ℕ) : ℝ) / 4) := by rw [heq]
          _ = _ := by rw [← Real.mul_rpow (by positivity) (by positivity)]; congr 1; ring
  · have hd : (dens {p : V × (Fin t → D) | (t + 1) / 2 < G.visitCount W p} : ℝ) ≤ 1 := by
      exact_mod_cast (dens_le_one (s := {p : V × (Fin t → D) | (t + 1) / 2 < G.visitCount W p}))
    exact hd.trans_lt (Real.one_lt_rpow (by change 1 < 32 * ρ; linarith) (by positivity))

/-- Selected-time hitting with an explicit upper bound on the normalized eigenvalue. -/
theorem dens_filter_selected_walkAt_mem_le_of_spectralExpansion_le
    (W : Finset V) (t : ℕ) (S : Finset ℕ) (hS : S ⊆ range (t + 1))
    (lambda d : ℝ) (h : G.spectralExpansion ≤ lambda / d) :
    (dens {p : V × (Fin t → D) | ∀ i ∈ S, G.walkAt p i ∈ W} : ℝ) ≤
      ((dens W : ℝ) + (lambda / d) ^ 2) ^ ((S.card : ℝ) / 2) := by
  refine (G.dens_filter_selected_walkAt_mem_le W t S hS).trans ?_
  have hn := G.spectralExpansion_nonneg
  gcongr

end Cslib.RotationMap
