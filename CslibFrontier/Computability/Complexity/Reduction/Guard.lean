/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction

/-!
# Guarded polynomial-time reductions

Many reductions are faithful only on instances with some syntactic shape, such as a clause-width
bound or well-formed arities, and send every other instance to a fixed rejected instance. This
module states that pattern once.

## Main results

* `Cslib.Complexity.PolyTimeReducible.of_guard`: a polynomial-time test `g` and a polynomial-time
  map `f` with `a ∈ A ↔ g a = true ∧ f a ∈ B` give a reduction from `A` to `B`, sending the
  instances that fail the test to a fixed instance outside `B`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}

/-- **Guarded reduction.** If membership in `A` is a polynomial-time test `g` together with
membership of `f a` in `B`, for a polynomial-time map `f`, then `a ↦ if g a then f a else b₀`
reduces `A` to `B` for any fixed `b₀ ∉ B`. -/
theorem PolyTimeReducible.of_guard {g : α → Bool} {f : α → β} (b₀ : β)
    (hg : ComputableInPolyTime g encA encBool) (hf : ComputableInPolyTime f encA encB)
    (hb₀ : b₀ ∉ B) (h : ∀ a, a ∈ A ↔ g a = true ∧ f a ∈ B) :
    PolyTimeReducible encA encB A B := by
  refine ⟨fun a => if g a then f a else b₀, hg.ite hf (.const b₀), fun a => ?_⟩
  rw [h a]
  by_cases hga : g a = true <;> simp [hga, hb₀]

end Cslib.Complexity
