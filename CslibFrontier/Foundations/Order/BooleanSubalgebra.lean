/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib/Order/BooleanSubalgebra.lean)

public import CslibFrontier.Init
public import Mathlib.Data.Set.SymmDiff
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.BooleanSubalgebra

/-!
# Boolean subalgebras from complement and meet closure

A subset `s : Set α` of a Boolean algebra containing `⊥` and closed under complement (`ᶜ`) and
meet (`⊓`) is also closed under join (`⊔`) by De Morgan's law (`x ⊔ y = (xᶜ ⊓ yᶜ)ᶜ`), and
therefore forms a `BooleanSubalgebra α` (`BooleanSubalgebra.ofComplInf`). Every
`BooleanSubalgebra` is also closed under symmetric difference (`BooleanSubalgebra.symmDiff_mem`).

## Main definitions

* `BooleanSubalgebra.ofComplInf`: construct a `BooleanSubalgebra` from `⊥`, complement, and meet
  closure.

## Main results

* `BooleanSubalgebra.coe_ofComplInf`, `BooleanSubalgebra.mem_ofComplInf`: `@[simp]` carrier and
  membership lemmas for `BooleanSubalgebra.ofComplInf`.
* `BooleanSubalgebra.symmDiff_mem`: closure of any `BooleanSubalgebra` under symmetric difference.
-/

@[expose] public section

namespace BooleanSubalgebra

/-- Construct a `BooleanSubalgebra` from closure under `⊥`, complement, and meet (`⊓`), deriving
join (`⊔`) closure by De Morgan's law (`x ⊔ y = (xᶜ ⊓ yᶜ)ᶜ`). -/
def ofComplInf {α : Type*} [BooleanAlgebra α] (s : Set α)
    (hbot : ⊥ ∈ s)
    (hcompl : ∀ ⦃x⦄, x ∈ s → xᶜ ∈ s)
    (hinf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → x ⊓ y ∈ s) : BooleanSubalgebra α where
  carrier := s
  bot_mem' := hbot
  compl_mem' hx := hcompl hx
  infClosed' _ hx _ hy := hinf hx hy
  supClosed' _ hx _ hy := by
    simpa only [compl_inf, compl_compl] using hcompl (hinf (hcompl hx) (hcompl hy))

/-- The underlying set of `ofComplInf s hbot hcompl hinf` is `s`. -/
@[simp]
theorem coe_ofComplInf {α : Type*} [BooleanAlgebra α] (s : Set α)
    (hbot : ⊥ ∈ s) (hcompl : ∀ ⦃x⦄, x ∈ s → xᶜ ∈ s)
    (hinf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → x ⊓ y ∈ s) :
    (ofComplInf s hbot hcompl hinf : Set α) = s := rfl

/-- Membership in `ofComplInf s hbot hcompl hinf` is membership in `s`. -/
@[simp]
theorem mem_ofComplInf {α : Type*} [BooleanAlgebra α] {s : Set α}
    {hbot : ⊥ ∈ s} {hcompl : ∀ ⦃x⦄, x ∈ s → xᶜ ∈ s}
    {hinf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → x ⊓ y ∈ s} {x : α} :
    x ∈ ofComplInf s hbot hcompl hinf ↔ x ∈ s := Iff.rfl

/-- Every `BooleanSubalgebra` is closed under symmetric difference `x ∆ y = (x \ y) ⊔ (y \ x)`. -/
theorem symmDiff_mem {α : Type*} [BooleanAlgebra α] (S : BooleanSubalgebra α) {x y : α}
    (hx : x ∈ S) (hy : y ∈ S) : symmDiff x y ∈ S := by
  rw [symmDiff_def]
  exact S.sup_mem (S.sdiff_mem hx hy) (S.sdiff_mem hy hx)

end BooleanSubalgebra
