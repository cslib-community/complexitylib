/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyParams
public import Complexity.Foundations.Analysis.SpecialFunctions.PolynomialSwitch
public import Complexity.Foundations.Analysis.SpecialFunctions.RationalRamp
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concrete hierarchy parameters with Lipschitz fourth roots

This module supplies an actual regular witness extending `Matrix.HierarchyParams`. Its correction
ramp is rational, its five bounded cutoffs are polynomial switches, and all required fourth roots
and complementary fourth roots are globally Lipschitz. The strict threshold ladder is
`0 < θ < θ₂ < 1/(32q)`, `0 < δ₀ < δ₁ < θ/100`, and
`0 < η < η₂ < δ₀/3`, with copy thresholds `1/(8q)` and `1/(4q)`.

The construction fixes `θ = 1/(128q)` and width `a = 1/(384q)`, giving
`θ₂ = θ + 3a = 1/(64q)` for the rational ramp. It then chooses a positive iteration count from
the factorial tail, the number of copies, and the detector ranks, in that order. Thus the
existence theorem proves the new conditions; they are not extra premises on an unspecified stage.
The underlying `HierarchyParams` can be passed directly to all existing stage theorems.

This is the fourth-moment adaptation in complexitylib issue #1721 of the core hierarchy
conditions in [OpenAI2026LogSpace, Sections 4.1--4.4]. The pinned preprint uses eighth roots.
The witness does not establish eighth-root regularity, every later atom/access-score margin,
the recursive estimator, or rational-machine resource bounds. When `q` is rational, the displayed
scalar functions use only rational arithmetic and min/max; selecting the iteration count and
integer ranks here is an existence argument.

## Main definitions

* `Matrix.FourthRootHierarchyParams`: reduced algebraic-stage data together with the strict
  core threshold ladder, monotone cutoffs, and fourth-root regularity.

## Main results

* `Matrix.FourthRootHierarchyParams.nonempty`: a concrete regular witness exists for `q > 0`
  and `cπ > 0`.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 4.1--4.4 and Remark 4.6 (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Matrix

open Cslib

/-- Concrete regularity requirements for the fourth-moment hierarchy, extending the existing
algebraic-stage interface. The core threshold ladder is included, but later access-score margins
are not asserted by this structure. -/
structure FourthRootHierarchyParams (q cπ Cπ Cpair Cvar : ℝ)
    extends HierarchyParams q cπ Cπ Cpair Cvar where
  /-- Upper support threshold of the row gate. -/
  η₂ : ℝ
  θ_lt_θ₂ : θ < θ₂
  θ₂_lt : θ₂ < 1 / (32 * q)
  k_pos : 0 < k
  tail_small : Real.exp (1 / θ) * (L / θ) ^ k / k.factorial ≤ 1 / (32 * q)
  copies_strict : q * ((k : ℝ) + 1) < m + 1
  τ₀_eq : τ₀ = 1 / (8 * q)
  τ₁_eq : τ₁ = 1 / (4 * q)
  δ₀_lt_δ₁ : δ₀ < δ₁
  δ₁_lt : δ₁ < θ / 100
  η_lt_η₂ : η < η₂
  η₂_lt : η₂ < δ₀ / 3
  χ_mono : Monotone χ
  ϕ_mono : Monotone ϕ
  ρ_nonneg : ∀ t, 0 ≤ ρ t
  ρ_antitone : Antitone ρ
  ρ_zero : ∀ t, η₂ ≤ t → ρ t = 0
  κ_mono : Monotone κ
  κ_one_ge : ∀ t, 1 / 2 ≤ t → κ t = 1
  Q_root : ∃ K, LipschitzWith K fun t => Q t ^ (4⁻¹ : ℝ)
  cutoff_roots : ∀ F ∈ [χ, ϕ, ρ, γ, κ],
    (∃ K, LipschitzWith K fun t => F t ^ (4⁻¹ : ℝ)) ∧
      (∃ K, LipschitzWith K fun t => (1 - F t) ^ (4⁻¹ : ℝ))

namespace FourthRootHierarchyParams

variable {q cπ Cπ Cpair Cvar : ℝ}

/-- A concrete hierarchy witness with a rational ramp, polynomial cutoffs, the strict core
threshold ladder, and global fourth-root regularity. -/
theorem nonempty (hq : 0 < q) (hcπ : 0 < cπ) :
    Nonempty (FourthRootHierarchyParams q cπ Cπ Cpair Cvar) := by
  set θ : ℝ := 1 / (128 * q)
  set a : ℝ := 1 / (384 * q)
  set θ₂ : ℝ := θ + 3 * a
  have hθ : 0 < θ := by positivity
  have ha : 0 < a := by positivity
  have hθ₂ : θ₂ = 1 / (64 * q) := by
    dsimp [θ₂, θ, a]
    field_simp
    ring
  have hθ₂small : θ₂ < 1 / (32 * q) := by
    rw [hθ₂, div_lt_div_iff_of_pos_left one_pos (by positivity) (by positivity)]
    linarith
  have hτ : 1 / (8 * q) < 1 / (4 * q) := by
    rw [div_lt_div_iff_of_pos_left one_pos (by positivity) (by positivity)]
    linarith
  have hτ₁ : 1 / (4 * q) ≤ 1 / q := by
    rw [div_le_div_iff_of_pos_left one_pos (by positivity) hq]
    linarith
  set δ₀ : ℝ := θ / 400
  set δ₁ : ℝ := θ / 200
  set η : ℝ := δ₀ / 1000
  set η₂ : ℝ := δ₀ / 500
  have hδ₀ : 0 < δ₀ := by positivity
  have hδ : δ₀ < δ₁ := by dsimp [δ₀, δ₁]; linarith
  have hη : 0 < η := by positivity
  have hη₂ : η < η₂ := by dsimp [η, η₂]; linarith
  obtain ⟨k, hk⟩ := exists_factorial_bound_le θ 1
    (δ := min (1 / (32 * q)) (Real.exp (1 / θ) / 2)) (by positivity)
  have htail : Real.exp (1 / θ) * (1 / θ) ^ k / k.factorial ≤ 1 / (32 * q) :=
    hk.trans (min_le_left _ _)
  have hkpos : 0 < k := by
    by_contra h
    have hzero : k = 0 := Nat.eq_zero_of_not_pos h
    have hb := hk.trans (min_le_right _ _)
    simp only [hzero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one] at hb
    linarith [Real.exp_pos (1 / θ)]
  set m : ℕ := ⌈q⌉₊ * (k + 1)
  have hcopies : q * ((k : ℝ) + 1) < (m : ℝ) + 1 := by
    have hqc : q ≤ ⌈q⌉₊ := Nat.le_ceil q
    have hm : (m : ℝ) = ⌈q⌉₊ * ((k : ℝ) + 1) := by simp [m]
    rw [hm]
    nlinarith [(Nat.cast_nonneg (α := ℝ) k)]
  set J : ℕ := ⌈(2 * Cπ * m * k * (k + 1)) / δ₀⌉₊ + 1
  set K : ℕ := ⌈160 * (1 + Cpair * k / η)⌉₊
  set R : ℝ := (4 * J + 40 * |Cvar|) / cπ
  have hR : 4 * (J : ℝ) + 40 * |Cvar| ≤ cπ * R := by
    dsimp [R]
    rw [mul_div_cancel₀ _ hcπ.ne']
  have hγ : (1 / 2 : ℝ) < 4 / 5 := by norm_num
  have hκ : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  refine ⟨{
    Q := rationalRamp4 θ a
    θ := θ
    θ₂ := θ₂
    L := 1
    k := k
    m := m
    τ₀ := 1 / (8 * q)
    τ₁ := 1 / (4 * q)
    χ := polynomialSwitch4 (1 / (8 * q)) (1 / (4 * q))
    δ₀ := δ₀
    δ₁ := δ₁
    ϕ := polynomialSwitch4 δ₀ δ₁
    η := η
    ρ := fun t => 1 - polynomialSwitch4 η η₂ t
    γ := fun t => 1 - polynomialSwitch4 (1 / 2) (4 / 5) t
    κ := polynomialSwitch4 (1 / 4) (1 / 2)
    J := J
    K := K
    R := R
    Q_nonneg := rationalRamp4_nonneg ha.le θ
    Q_le := rationalRamp4_le ha θ
    le_Q := le_rationalRamp4 ha θ
    Q_mono := monotone_rationalRamp4 ha θ
    Q_lipschitz := fun s t hst => ?_
    θ_pos := hθ
    L_nonneg := zero_le_one
    truncation := ?_
    χ_nonneg := polynomialSwitch4_nonneg _ _
    χ_le_one := polynomialSwitch4_le_one _ _
    χ_zero := fun _ h => polynomialSwitch4_of_le hτ h
    χ_one := fun _ h => polynomialSwitch4_of_ge hτ h
    τ₁_le := hτ₁
    copies := ?_
    δ₀_pos := hδ₀
    ϕ_nonneg := polynomialSwitch4_nonneg _ _
    ϕ_le_one := polynomialSwitch4_le_one _ _
    ϕ_zero := fun _ h => polynomialSwitch4_of_le hδ h
    ϕ_one := fun _ h => polynomialSwitch4_of_ge hδ h
    η_pos := hη
    ρ_le_one := fun t => sub_le_self _ (polynomialSwitch4_nonneg _ _ t)
    ρ_one := fun t h => by rw [polynomialSwitch4_of_le hη₂ h, sub_zero]
    γ_nonneg := fun t => sub_nonneg.mpr (polynomialSwitch4_le_one _ _ t)
    γ_le_one := fun t => sub_le_self _ (polynomialSwitch4_nonneg _ _ t)
    γ_antitone := fun _ _ h => sub_le_sub_left (monotone_polynomialSwitch4 hγ.le h) 1
    γ_one := fun t h => by rw [polynomialSwitch4_of_le hγ h, sub_zero]
    γ_zero := fun t h => by rw [polynomialSwitch4_of_ge hγ h, sub_self]
    κ_nonneg := polynomialSwitch4_nonneg _ _
    κ_le_one := polynomialSwitch4_le_one _ _
    κ_zero := fun _ h => polynomialSwitch4_of_le hκ h
    κ_one := fun _ h => polynomialSwitch4_of_ge hκ h.le
    J_pos := Nat.succ_pos _
    rank := ?_
    gate := Nat.le_ceil _
    R_rank := by linarith [abs_nonneg Cvar]
    R_var := by linarith [le_abs_self Cvar]
    η₂ := η₂
    θ_lt_θ₂ := by dsimp [θ₂]; linarith
    θ₂_lt := hθ₂small
    k_pos := hkpos
    tail_small := htail
    copies_strict := hcopies
    τ₀_eq := rfl
    τ₁_eq := rfl
    δ₀_lt_δ₁ := hδ
    δ₁_lt := by dsimp [δ₁]; linarith
    η_lt_η₂ := hη₂
    η₂_lt := by dsimp [η₂]; linarith
    χ_mono := monotone_polynomialSwitch4 hτ.le
    ϕ_mono := monotone_polynomialSwitch4 hδ.le
    ρ_nonneg := fun t => sub_nonneg.mpr (polynomialSwitch4_le_one _ _ t)
    ρ_antitone := fun _ _ h => sub_le_sub_left (monotone_polynomialSwitch4 hη₂.le h) 1
    ρ_zero := fun t h => by rw [polynomialSwitch4_of_ge hη₂ h, sub_self]
    κ_mono := monotone_polynomialSwitch4 hκ.le
    κ_one_ge := fun _ h => polynomialSwitch4_of_ge hκ h
    Q_root := ⟨_, lipschitzWith_rationalRamp4_root ha θ⟩
    cutoff_roots := ?_ }⟩
  · have h := (lipschitzWith_rationalRamp4 ha θ).dist_le_mul t s
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hst)] at h
    exact (le_abs_self _).trans h
  · calc θ₂ + Real.exp (1 / θ) * (1 / θ) ^ k / k.factorial ≤ θ₂ + 1 / (32 * q) := by
          linarith
      _ = (3 / 64) / q := by rw [hθ₂]; field_simp; ring
      _ ≤ (1 / 8) / q := div_le_div_of_nonneg_right (by norm_num) hq.le
      _ = 1 / (8 * q) := by ring
  · rw [div_le_div_iff₀ (by positivity) hq, one_mul]
    simpa only [mul_comm] using hcopies.le
  · have hJ : (2 * Cπ * m * k * (k + 1)) / δ₀ ≤ (J : ℝ) := by
      dsimp [J]
      push_cast
      exact (Nat.le_ceil _).trans (by linarith)
    have hb := (div_le_iff₀ hδ₀).mp hJ
    linarith
  · intro F hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl | rfl | rfl
    · exact ⟨exists_lipschitzWith_polynomialSwitch4_root _ _,
        exists_lipschitzWith_one_sub_polynomialSwitch4_root _ _⟩
    · exact ⟨exists_lipschitzWith_polynomialSwitch4_root _ _,
        exists_lipschitzWith_one_sub_polynomialSwitch4_root _ _⟩
    · refine ⟨exists_lipschitzWith_one_sub_polynomialSwitch4_root _ _, ?_⟩
      simpa only [sub_sub_cancel] using exists_lipschitzWith_polynomialSwitch4_root η η₂
    · refine ⟨exists_lipschitzWith_one_sub_polynomialSwitch4_root _ _, ?_⟩
      simpa only [sub_sub_cancel] using
        exists_lipschitzWith_polynomialSwitch4_root (1 / 2) (4 / 5)
    · exact ⟨exists_lipschitzWith_polynomialSwitch4_root _ _,
        exists_lipschitzWith_one_sub_polynomialSwitch4_root _ _⟩

end FourthRootHierarchyParams

end Matrix
