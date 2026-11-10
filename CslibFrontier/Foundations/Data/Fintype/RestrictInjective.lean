/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `Mathlib/SetTheory/Cardinal/Finite.lean`)

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Set

/-!
# Counting functions by a property of their restriction

For an injection `ι : A → D`, a function `g : D → β` is determined by its restriction `g ∘ ι` and
its values off the range of `ι`. So the functions whose restriction has a property `Q` are, in
proportion, exactly as many as the functions `A → β` with `Q`: the restriction of a uniformly random
function along an injection is uniformly random.

## Main results

* `Nat.card_subtype_comp_injective_mul`: the multiplicative form, with no finiteness hypotheses.
* `Nat.card_subtype_comp_injective_div`: the proportion form, for finite `D` and `β`.
-/

public section

open Function

namespace Nat

/-- For an injection `ι : A → D`, the functions `D → β` whose restriction along `ι` has the property
`Q`, counted against all functions `A → β`, are as many as the functions `A → β` with `Q` counted
against all functions `D → β`. -/
theorem card_subtype_comp_injective_mul {A D β : Type*} (ι : A → D) (hι : Injective ι)
    (Q : (A → β) → Prop) :
    Nat.card {g : D → β // Q (g ∘ ι)} * Nat.card (A → β) =
      Nat.card {h : A → β // Q h} * Nat.card (D → β) := by
  classical
  let S := (Set.range ι)ᶜ
  let e : (D → β) ≃ (A → β) × (S → β) :=
    ((Equiv.Set.sumCompl (Set.range ι)).arrowCongr (Equiv.refl β)).symm.trans
      ((Equiv.sumArrowEquivProdArrow _ _ _).trans
        (Equiv.prodCongr ((Equiv.ofInjective ι hι).arrowCongr (Equiv.refl β)).symm
          (Equiv.refl _)))
  have he : ∀ g, (e g).1 = g ∘ ι := fun g => rfl
  have e1 : {g : D → β // Q (g ∘ ι)} ≃ {h : A → β // Q h} × (S → β) :=
    (e.subtypeEquiv fun g => by rw [he]).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd (p := Q))
  rw [Nat.card_congr e1, Nat.card_congr e, Nat.card_prod, Nat.card_prod, mul_assoc,
    mul_comm (Nat.card (S → β))]

/-- **Restrictions of uniform functions are uniform.** For an injection `ι : A → D`, the fraction
of the functions `g : D → β` whose restriction `g ∘ ι` has the property `Q` equals the fraction of
the functions `A → β` with `Q`. -/
theorem card_subtype_comp_injective_div {A D β : Type*} [Finite D] [Finite β] [Nonempty β]
    (ι : A → D) (hι : Injective ι) (Q : (A → β) → Prop) :
    (Nat.card {g : D → β // Q (g ∘ ι)} : ℝ) / Nat.card (D → β) =
      Nat.card {h : A → β // Q h} / Nat.card (A → β) := by
  have : Finite A := Finite.of_injective ι hι
  have hD : (Nat.card (D → β) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hA : (Nat.card (A → β) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [div_eq_div_iff hD hA]
  exact_mod_cast card_subtype_comp_injective_mul ι hι Q

end Nat
