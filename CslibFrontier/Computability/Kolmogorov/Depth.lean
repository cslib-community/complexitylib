/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.Basic

/-!
# Computational depth

The *computational depth* of an object `x` at time `t` is `C_M^t(x) - C_M(x)`: how much longer
the shortest descriptions of `x` become when they must run within `t` steps. This is the basic
computational depth of
[Antunes, Fortnow, van Melkebeek and Vinodchandran, Section 3][AFvMV2006], there defined with
prefix-free complexity, here with the plain complexity of any description method. It is computed
in `ℕ∞` with truncated subtraction, and since `C_M(x) ≤ C_M^t(x)`, depth plus plain complexity is
exactly the time-bounded complexity. The depth between two time bounds `t₁ ≤ t₂` is
`C_M^{t₁}(x) - C_M^{t₂}(x)`, and depths between consecutive time bounds add up.

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.depth`: the depth `C_M^t(x) - C_M(x)`.
* `Cslib.Kolmogorov.DescriptionMethod.depthBetween`: the depth `C_M^{t₁}(x) - C_M^{t₂}(x)`
  between two time bounds.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.depth_add_ecomplexity`: `depth + C_M(x) = C_M^t(x)`.
* `Cslib.Kolmogorov.DescriptionMethod.depth_antitone`: more time cannot increase the depth.
* `Cslib.Kolmogorov.DescriptionMethod.depth_eq_zero_iff`: the depth vanishes exactly when the time
  bound attains the plain complexity, which some time bound does
  (`exists_forall_le_depth_eq_zero`).
* `Cslib.Kolmogorov.DescriptionMethod.depthBetween_add`: depths between consecutive time bounds
  add up.
* `Cslib.Kolmogorov.DescriptionMethod.depthBetween_add_depth`: depth between two bounds plus depth
  at the upper bound equals depth at the lower bound.

## References

* [L. Antunes, L. Fortnow, D. van Melkebeek, N. V. Vinodchandran, *Computational
  depth*][AFvMV2006]
-/

@[expose] public section

namespace Cslib.Kolmogorov.DescriptionMethod

variable {α : Type*} (M : DescriptionMethod α)

/-- The *computational depth* `C_M^t(x) - C_M(x)` of `x` at time `t`. -/
noncomputable def depth (t : ℕ) (x : α) : ℕ∞ :=
  M.etimeBoundedComplexity t x - M.ecomplexity x

/-- The depth `C_M^{t₁}(x) - C_M^{t₂}(x)` of `x` between the time bounds `t₁` and `t₂`. -/
noncomputable def depthBetween (t₁ t₂ : ℕ) (x : α) : ℕ∞ :=
  M.etimeBoundedComplexity t₁ x - M.etimeBoundedComplexity t₂ x

variable {M} {t t₁ t₂ t₃ : ℕ} {x : α}

/-- Depth plus plain complexity is exactly the time-bounded complexity. -/
theorem depth_add_ecomplexity (M : DescriptionMethod α) (t : ℕ) (x : α) :
    M.depth t x + M.ecomplexity x = M.etimeBoundedComplexity t x :=
  tsub_add_cancel_of_le (M.ecomplexity_le_etimeBoundedComplexity t x)

theorem depth_le_etimeBoundedComplexity (M : DescriptionMethod α) (t : ℕ) (x : α) :
    M.depth t x ≤ M.etimeBoundedComplexity t x :=
  tsub_le_self

/-- **Monotonicity in the time bound.** More time cannot increase the depth. -/
theorem depth_antitone (M : DescriptionMethod α) (x : α) : Antitone (M.depth · x) :=
  fun _ _ h => tsub_le_tsub_right (M.etimeBoundedComplexity_mono h) _

/-- The depth vanishes exactly when the time bound attains the plain complexity. -/
theorem depth_eq_zero_iff : M.depth t x = 0 ↔ M.etimeBoundedComplexity t x = M.ecomplexity x :=
  tsub_eq_zero_iff_le.trans
    ⟨fun h => le_antisymm h (M.ecomplexity_le_etimeBoundedComplexity t x), le_of_eq⟩

/-- The depth is infinite exactly when `x` has a description but none within the time bound. -/
theorem depth_eq_top_iff :
    M.depth t x = ⊤ ↔ M.etimeBoundedComplexity t x = ⊤ ∧ M.ecomplexity x ≠ ⊤ :=
  ENat.sub_eq_top_iff

/-- Every object has depth zero from some time bound on. -/
theorem exists_forall_le_depth_eq_zero (M : DescriptionMethod α) (x : α) :
    ∃ t, ∀ t' ≥ t, M.depth t' x = 0 := by
  obtain ⟨t, ht⟩ := M.exists_etimeBoundedComplexity_eq_ecomplexity x
  exact ⟨t, fun t' h => nonpos_iff_eq_zero.mp
    ((M.depth_antitone x h).trans_eq (depth_eq_zero_iff.mpr ht))⟩

/-- The depth between `t` and a time bound attaining the plain complexity is the depth at `t`. -/
theorem depthBetween_eq_depth (h : M.etimeBoundedComplexity t₂ x = M.ecomplexity x) :
    M.depthBetween t₁ t₂ x = M.depth t₁ x := by
  rw [depthBetween, depth, h]

/-- Depth between two time bounds plus the complexity at the later one is the complexity at the
earlier one. -/
theorem depthBetween_add_etimeBoundedComplexity (h : t₁ ≤ t₂) :
    M.depthBetween t₁ t₂ x + M.etimeBoundedComplexity t₂ x = M.etimeBoundedComplexity t₁ x :=
  tsub_add_cancel_of_le (M.etimeBoundedComplexity_mono h)

/-- Depths between consecutive time bounds add up. -/
theorem depthBetween_add (h₁₂ : t₁ ≤ t₂) (h₂₃ : t₂ ≤ t₃) :
    M.depthBetween t₁ t₂ x + M.depthBetween t₂ t₃ x = M.depthBetween t₁ t₃ x :=
  tsub_add_tsub_cancel (M.etimeBoundedComplexity_mono h₁₂) (M.etimeBoundedComplexity_mono h₂₃)

/-- The depth at `t₁` is the depth between `t₁` and `t₂` plus the depth at `t₂`. -/
theorem depthBetween_add_depth (h : t₁ ≤ t₂) :
    M.depthBetween t₁ t₂ x + M.depth t₂ x = M.depth t₁ x :=
  tsub_add_tsub_cancel (M.etimeBoundedComplexity_mono h)
    (M.ecomplexity_le_etimeBoundedComplexity t₂ x)

end Cslib.Kolmogorov.DescriptionMethod
