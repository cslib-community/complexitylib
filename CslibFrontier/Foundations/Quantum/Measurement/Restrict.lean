/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Measurement

/-!
# Restricting a state to a set of outcomes

The restriction `Cslib.Quantum.restrictOutcomes S` keeps the amplitudes of a state on the outcomes
in `S`. It is a linear map whose squared norm is the probability of measuring an outcome in `S`
(`Cslib.Quantum.norm_restrictOutcomes_sq`), so a measurement probability is a quadratic form
`‖R ψ‖²` with `R` linear. The inner product of two restrictions is the overlap of the states on
`S` (`Cslib.Quantum.inner_restrictOutcomes`).

The projection `Cslib.Quantum.projOutcomes p` instead stays in the same space: it keeps the
amplitudes on the outcomes satisfying `p` and zeroes the others. A state is the sum of its
projections on `p` and on `¬p` (`Cslib.Quantum.projOutcomes_add_projOutcomes_not`).

## Main definitions

* `Cslib.Quantum.restrictOutcomes`: the amplitudes on a set of outcomes.
* `Cslib.Quantum.projOutcomes`: the projection onto the outcomes satisfying a predicate.

## Main results

* `Cslib.Quantum.norm_restrictOutcomes_sq`: `‖R_S ψ‖² = measureProb ψ S`.
* `Cslib.Quantum.inner_restrictOutcomes`: `⟪R_S φ, R_S ψ⟫ = ∑_{y ∈ S} conj(φ_y) ψ_y`.
* `Cslib.Quantum.projOutcomes_add_projOutcomes_not`: `P_p ψ + P_{¬p} ψ = ψ`.
* `Cslib.Quantum.norm_projOutcomes_sq`, `Cslib.Quantum.norm_projOutcomes_sq_mem`: squared norm of
  `projOutcomes` as `measureProb`.
* `Cslib.Quantum.inner_projOutcomes_eq_zero`: orthogonality of `projOutcomes` for disjoint
  predicates.
-/

public section

namespace Cslib.Quantum

open Finset

variable {ι : Type*}

/-- The **restriction to the outcomes in `S`**: the vector of amplitudes of a state on `S`. -/
@[expose] noncomputable def restrictOutcomes (S : Finset ι) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ S where
  toFun ψ := WithLp.toLp 2 fun y => ψ.ofLp y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrictOutcomes_apply (S : Finset ι) (ψ : EuclideanSpace ℂ ι) (y : S) :
    (restrictOutcomes S ψ).ofLp y = ψ.ofLp y :=
  rfl

/-- The squared norm of the restriction to `S` is the probability of an outcome in `S`. -/
theorem norm_restrictOutcomes_sq (S : Finset ι) (ψ : EuclideanSpace ℂ ι) :
    ‖restrictOutcomes S ψ‖ ^ 2 = measureProb ψ S := by
  rw [EuclideanSpace.norm_sq_eq, measureProb]
  exact sum_coe_sort S fun y => ‖ψ.ofLp y‖ ^ 2

/-- The inner product of two restrictions to `S` is the overlap of the states on `S`. -/
theorem inner_restrictOutcomes (S : Finset ι) (φ ψ : EuclideanSpace ℂ ι) :
    inner ℂ (restrictOutcomes S φ) (restrictOutcomes S ψ) =
      ∑ y ∈ S, star (φ.ofLp y) * ψ.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine (sum_coe_sort S fun y => ψ.ofLp y * star (φ.ofLp y)).trans ?_
  exact sum_congr rfl fun y _ => mul_comm _ _

/-- The **projection onto the outcomes satisfying `p`**: it keeps the amplitudes on those outcomes
and zeroes the others. -/
@[expose] noncomputable def projOutcomes (p : ι → Prop) [DecidablePred p] :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun ψ := WithLp.toLp 2 fun y => if p y then ψ.ofLp y else 0
  map_add' ψ φ := by
    ext y
    simp only [WithLp.ofLp_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c ψ := by
    ext y
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

@[simp] theorem projOutcomes_apply (p : ι → Prop) [DecidablePred p] (ψ : EuclideanSpace ℂ ι)
    (y : ι) : (projOutcomes p ψ).ofLp y = if p y then ψ.ofLp y else 0 :=
  rfl

/-- A state is the sum of its projections onto the outcomes satisfying `p` and the others. -/
theorem projOutcomes_add_projOutcomes_not (p : ι → Prop) [DecidablePred p]
    (ψ : EuclideanSpace ℂ ι) : projOutcomes p ψ + projOutcomes (fun y => ¬p y) ψ = ψ := by
  ext y
  simp only [WithLp.ofLp_add, Pi.add_apply, projOutcomes_apply]
  split_ifs <;> simp_all

/-- Projecting twice projects onto the outcomes satisfying both predicates. -/
theorem projOutcomes_projOutcomes (p q : ι → Prop) [DecidablePred p] [DecidablePred q]
    (ψ : EuclideanSpace ℂ ι) :
    projOutcomes p (projOutcomes q ψ) = projOutcomes (fun y => p y ∧ q y) ψ := by
  ext y
  simp only [projOutcomes_apply]
  split_ifs <;> simp_all

/-- The squared norm of `projOutcomes p ψ` is the probability of outcomes satisfying `p`. -/
theorem norm_projOutcomes_sq [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (ψ : EuclideanSpace ℂ ι) : ‖projOutcomes p ψ‖ ^ 2 = measureProb ψ (univ.filter p) := by
  rw [EuclideanSpace.norm_sq_eq, measureProb, ← sum_filter_add_sum_filter_not univ p]
  have hzero : ∑ y ∈ univ.filter (fun y => ¬p y), ‖(projOutcomes p ψ).ofLp y‖ ^ 2 = 0 := by
    refine sum_eq_zero fun y hy => ?_
    simp only [projOutcomes_apply, (mem_filter.1 hy).2, ↓reduceIte, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [hzero, add_zero]
  refine sum_congr rfl fun y hy => ?_
  simp only [projOutcomes_apply, (mem_filter.1 hy).2, ↓reduceIte]

/-- The squared norm of `projOutcomes (· ∈ S) ψ` is `measureProb ψ S`. -/
theorem norm_projOutcomes_sq_mem [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (ψ : EuclideanSpace ℂ ι) : ‖projOutcomes (· ∈ S) ψ‖ ^ 2 = measureProb ψ S := by
  have hS : univ.filter (· ∈ S) = S := by ext y; simp only [mem_filter, mem_univ, true_and]
  simpa only [hS] using norm_projOutcomes_sq (· ∈ S) ψ

/-- Projections onto disjoint outcome predicates are orthogonal. -/
theorem inner_projOutcomes_eq_zero [Fintype ι] (p q : ι → Prop)
    [DecidablePred p] [DecidablePred q] (hpq : ∀ y, ¬(p y ∧ q y))
    (φ ψ : EuclideanSpace ℂ ι) :
    inner ℂ (projOutcomes p φ) (projOutcomes q ψ) = 0 := by
  rw [PiLp.inner_apply]
  refine sum_eq_zero fun y _ => ?_
  by_cases hp : p y
  · have hq : ¬q y := fun hq => hpq y ⟨hp, hq⟩
    simp only [projOutcomes_apply, hp, ↓reduceIte, hq, inner_zero_right]
  · simp only [projOutcomes_apply, hp, ↓reduceIte, inner_zero_left]

end Cslib.Quantum
