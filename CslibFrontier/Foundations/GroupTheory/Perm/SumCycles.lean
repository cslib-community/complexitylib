/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate (Mathlib GroupTheory/Perm/Cycle)

public import CslibFrontier.Foundations.GroupTheory.Perm.Doubled

/-!
# Complete cycle membership in a disjoint sum

The existing complete orbit equivalence of a disjoint-sum permutation gives its literal
cycle relation. Fixed points remain singleton orbits; points in different summands never
share an orbit. These are consequences of `sumOrbitEquiv`, without a second orbit argument.
-/

public section

namespace Equiv.Perm

variable {α β : Type*} [Finite α] [Finite β]

/-- The full orbit relation of a disjoint-sum permutation is the original relation in each
summand, with no orbit joining the two sides. -/
theorem sameCycle_sumCongr_iff (f : Perm α) (g : Perm β) (x y : α ⊕ β) :
    SameCycle (Equiv.sumCongr f g) x y ↔ match x, y with
      | Sum.inl a, Sum.inl b => f.SameCycle a b
      | Sum.inr a, Sum.inr b => g.SameCycle a b
      | _, _ => False := by
  have he : SameCycle (Equiv.sumCongr f g) x y ↔
      sumOrbitEquiv f g (Quotient.mk _ x) = sumOrbitEquiv f g (Quotient.mk _ y) :=
    ⟨fun h => congrArg (sumOrbitEquiv f g) (Quotient.sound h),
      fun h => Quotient.exact ((sumOrbitEquiv f g).injective h)⟩
  rw [he]
  cases x <;> cases y <;>
    simp only [sumOrbitEquiv, Equiv.coe_fn_mk, Quotient.lift_mk, Sum.map_inl, Sum.map_inr]
  · simp only [Sum.inl.injEq]
    exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
  · simp
  · simp
  · simp only [Sum.inr.injEq]
    exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

end Equiv.Perm
