/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Spread.Basic

/-!
# Talagrand's thinning conjectures and their elementary implication

The named conjectures are propositions, not axioms or asserted solutions. A universal alpha is
chosen before the finite dimension, product density, event and parent law. The definitions use
Talagrand's actual factor-two weak-cover normalization and the h(empty,J)=1 convention.

## Main definitions

* `Conjecture73At`, `Conjecture78At`, `Conjecture711At`: the source assertions at fixed alpha.
* `Conjecture73`, `Conjecture78`, `Conjecture711`: the universal-constant assertions.

## Main results

* `conjecture78At_of_conjecture711At`, `conjecture78_of_conjecture711`: the source's
  normalized-moment/Fubini implication, with the same constant.

## References

[Talagrand2010Small], Conjecture 7.3 (author PDF p.9), Conjectures 7.8 and 7.11,
(7.8)–(7.11) and the proof that 7.11 implies 7.8 (p.10). The reverse implication uses
finite convex separation, formalized in `conjecture711At_of_conjecture78At` in the
`Spread.Duality` module. The factor-two 7.8-to-7.3 reduction is formalized in
`conjecture73At_of_conjecture78At` in `Spread.Exceptional`.
-/

public section
namespace Cslib.Probability.Spread
open Finset
open scoped BigOperators

/-- Conjecture 7.3: the exceptional family is weakly alpha*p-small, uniformly in dimension. -/
@[expose] def Conjecture73At (α : ℝ) : Prop :=
  ∀ n : ℕ, ∀ p : ℝ, 0 < p → p < 1 → ∀ A : Set (Finset (Fin n)), IsUpperSet A →
    IsWeaklySmall (α * p) {J | productProb p A < theta α A J}

/-- Conjecture 7.8: alpha-thinning of every alpha*p-spread law is dominated on all up-classes. -/
@[expose] def Conjecture78At (α : ℝ) : Prop :=
  ∀ n : ℕ, ∀ p : ℝ, 0 < p → p < 1 → ∀ ν : PMF (Finset (Fin n)),
    IsSpreadLaw (α * p) ν → ∀ A : Set (Finset (Fin n)), IsUpperSet A →
      (∑ J, (ν J).toReal * theta α A J) ≤ productProb p A

/-- Conjecture 7.11: one probability witness majorizes the entire thinning profile of an event. -/
@[expose] def Conjecture711At (α : ℝ) : Prop :=
  ∀ n : ℕ, ∀ p : ℝ, 0 < p → p < 1 → ∀ A : Set (Finset (Fin n)), IsUpperSet A →
    ∃ η : PMF (Finset (Fin n)), ∀ J,
      theta α A J ≤ productProb p A * coverScore (α * p) η J

/-- Talagrand 2010 Conjecture 7.3, with one constant for all finite universes and densities. -/
@[expose] def Conjecture73 : Prop := ∃ α : ℝ, 0 < α ∧ α < 1 ∧ Conjecture73At α
/-- Talagrand 2010 Conjecture 7.8, in its source upper-event domination formulation. -/
@[expose] def Conjecture78 : Prop := ∃ α : ℝ, 0 < α ∧ α < 1 ∧ Conjecture78At α
/-- Talagrand 2010 Conjecture 7.11, including the full event-dependent probability witness. -/
@[expose] def Conjecture711 : Prop := ∃ α : ℝ, 0 < α ∧ α < 1 ∧ Conjecture711At α

/-- The source's easy dual-to-domination implication keeps the same alpha. Both the averaging
law and the majorizing witness are actual PMFs; no domination or normalization oracle is used. -/
theorem conjecture78At_of_conjecture711At {α : ℝ} (hα : 0 < α)
    (h : Conjecture711At α) : Conjecture78At α := by
  intro n p hp hp' ν hν A hA
  obtain ⟨η, hη⟩ := h n p hp hp' A hA
  have hb := productProb_nonneg hp.le hp'.le A
  calc _ ≤ ∑ J, (ν J).toReal * (productProb p A * coverScore (α * p) η J) :=
          sum_le_sum fun J _ => mul_le_mul_of_nonneg_left (hη J) ENNReal.toReal_nonneg
    _ = productProb p A * (∑ J, (ν J).toReal * coverScore (α * p) η J) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro J _
          ring
    _ ≤ productProb p A * 1 := mul_le_mul_of_nonneg_left
      (average_coverScore_le_one (mul_pos hα hp) hν η) hb
    _ = _ := mul_one _

/-- Resolution of 7.11 implies resolution of 7.8 with the original quantifiers. -/
theorem conjecture78_of_conjecture711 (h : Conjecture711) : Conjecture78 := by
  obtain ⟨α, hα, hα', h⟩ := h
  exact ⟨α, hα, hα', conjecture78At_of_conjecture711At hα h⟩

end Cslib.Probability.Spread
