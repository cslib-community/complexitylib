/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate (Mathlib GroupTheory/Perm/Cycle)

public import CslibFrontier.Init
public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Doubling the points of a finite permutation

`Equiv.Perm.doubled` replaces every point of a cycle by two successive points. Its orbit
quotient includes singleton cycles of the original permutation. These finite permutation
identities are original and do not assert a geometric realization.

## Main definitions

* `Equiv.Perm.doubled`: replaces each point by two consecutive points.
* `Equiv.Perm.doubledOrbitEquiv`: complete doubled/original orbit correspondence.
* `Equiv.Perm.sumOrbitEquiv`: complete disjoint-sum orbit decomposition.

## Main results

* `Equiv.Perm.SameCycle.map_of_semiconj`: maps finite permutation orbits.
* `Equiv.Perm.sameCycle_equiv_iff`: changes orbit coordinates by an equivalence.
* `Equiv.Perm.sameCycle_doubled`: doubling preserves the original orbit partition.
-/

public section

namespace Equiv.Perm

variable {α β : Type*} [Finite α] [Finite β]

omit [Finite β] in
/-- A semiconjugacy maps an entire finite permutation orbit into one orbit. -/
theorem SameCycle.map_of_semiconj {f : Perm α} {g : Perm β} {u : α → β}
    (h : Function.Semiconj u f g) {x y : α} (hxy : f.SameCycle x y) :
    g.SameCycle (u x) (u y) := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast, ← iterate_eq_pow, ← h.iterate_right n, iterate_eq_pow, hn]

/-- An explicit change of coordinates preserves all permutation orbits. -/
theorem sameCycle_equiv_iff (e : α ≃ β) (f : Perm α) (g : Perm β)
    (h : ∀ x, e (f x) = g (e x)) (x y : α) :
    g.SameCycle (e x) (e y) ↔ f.SameCycle x y := by
  constructor
  · intro hxy
    have hi : Function.Semiconj e.symm g f := by
      intro z
      obtain ⟨a, rfl⟩ := e.surjective z
      rw [← h, e.symm_apply_apply, e.symm_apply_apply]
    simpa only [e.symm_apply_apply] using hxy.map_of_semiconj hi
  · exact fun hxy => hxy.map_of_semiconj h

/-- Replace each point `x` by the consecutive block `(x,false), (x,true)`. -/
@[expose] def doubled (f : Perm α) : Perm (α × Bool) where
  toFun x := if x.2 then (f x.1, false) else (x.1, true)
  invFun x := if x.2 then (x.1, false) else (f.symm x.1, true)
  left_inv := by rintro ⟨x, b⟩; cases b <;> simp
  right_inv := by rintro ⟨x, b⟩; cases b <;> simp

omit [Finite α] in
/-- The square on the first point of each block is the original permutation. -/
@[simp] theorem doubled_squared (f : Perm α) (x : α) :
    doubled f (doubled f (x, false)) = (f x, false) := rfl

/-- Doubling changes cycle lengths but leaves the full orbit partition unchanged. -/
theorem sameCycle_doubled (f : Perm α) (x y : α × Bool) :
    (doubled f).SameCycle x y ↔ f.SameCycle x.1 y.1 := by
  let q : α → Quotient (SameCycle.setoid f) := Quotient.mk _
  have hq : Function.Semiconj (fun z : α × Bool => q z.1) (doubled f)
      (1 : Perm (Quotient (SameCycle.setoid f))) := by
    rintro ⟨a, b⟩
    cases b
    · rfl
    · exact Quotient.sound (sameCycle_apply_left.mpr (SameCycle.rfl (f := f)))
  constructor
  · intro hxy
    exact Quotient.exact (sameCycle_one.mp (hxy.map_of_semiconj hq))
  · intro hxy
    have hfirst : (doubled f).SameCycle (x.1, false) (y.1, false) := by
      have hs : Function.Semiconj (fun a => (a, false)) f (⇑(doubled f ^ 2)) := by
        intro a
        rfl
      exact (hxy.map_of_semiconj hs).of_pow
    have hx (z : α × Bool) : (doubled f).SameCycle z (z.1, false) := by
      rcases z with ⟨a, b⟩
      cases b
      · exact .rfl
      · exact (SameCycle.rfl (f := doubled f) (x := (a, false))).apply_left
    exact (hx x).trans (hfirst.trans (hx y).symm)

/-- All doubled orbits, with no omission of fixed points, correspond to original orbits. -/
@[expose] def doubledOrbitEquiv (f : Perm α) :
    Quotient (SameCycle.setoid (doubled f)) ≃ Quotient (SameCycle.setoid f) where
  toFun := Quotient.map Prod.fst (fun _ _ h => (sameCycle_doubled f _ _).mp h)
  invFun := Quotient.map (fun x => (x, false))
    (fun _ _ h => (sameCycle_doubled f _ _).mpr h)
  left_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | h z => exact Quotient.sound ((sameCycle_doubled f _ _).mpr .rfl)
  right_inv := by intro z; induction z using Quotient.inductionOn; rfl

end Equiv.Perm

namespace Equiv.Perm

variable {α β : Type*} [Finite α] [Finite β]

/-- All orbits of a permutation on a disjoint sum split into the two orbit quotients. -/
@[expose] def sumOrbitEquiv (f : Perm α) (g : Perm β) :
    Quotient (SameCycle.setoid (Equiv.sumCongr f g)) ≃
      Quotient (SameCycle.setoid f) ⊕ Quotient (SameCycle.setoid g) where
  toFun := Quotient.lift
    (Sum.map (Quotient.mk (SameCycle.setoid f)) (Quotient.mk (SameCycle.setoid g)))
    (by
      intro x y h
      have hc : Function.Semiconj
          (Sum.map (Quotient.mk (SameCycle.setoid f)) (Quotient.mk (SameCycle.setoid g)))
          (Equiv.sumCongr f g) (1 : Perm (Quotient (SameCycle.setoid f) ⊕
            Quotient (SameCycle.setoid g))) := by
        intro z
        cases z with
        | inl a =>
          exact congrArg Sum.inl
            (Quotient.sound (sameCycle_apply_left.mpr (SameCycle.rfl (f := f))))
        | inr b =>
          exact congrArg Sum.inr
            (Quotient.sound (sameCycle_apply_left.mpr (SameCycle.rfl (f := g))))
      exact sameCycle_one.mp (h.map_of_semiconj hc))
  invFun := Sum.elim
    (Quotient.map Sum.inl (fun _ _ h => h.map_of_semiconj (by intro a; rfl)))
    (Quotient.map Sum.inr (fun _ _ h => h.map_of_semiconj (by intro a; rfl)))
  left_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | h z => cases z <;> rfl
  right_inv := by
    intro z
    cases z with
    | inl z => induction z using Quotient.inductionOn; rfl
    | inr z => induction z using Quotient.inductionOn; rfl

end Equiv.Perm
