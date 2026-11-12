/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction

/-!
# Reductions from `P` to nontrivial problems

Every problem in `P` polynomial-time reduces to every problem with a member and a nonmember:
decide membership, then output the member or the nonmember. So `P` lies below every nontrivial
problem in the polynomial-time many-one order, and under `P = NP` every nontrivial problem is
`NP`-hard.

## Main results

* `Cslib.Complexity.polyTimeReducible_of_mem_P`: every problem in `P` reduces to every problem
  with a member and a nonmember.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Every problem in `P` reduces to every problem with a member `b₁` and a nonmember `b₀`:
decide membership and output `b₁` or `b₀`. -/
theorem polyTimeReducible_of_mem_P {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (hA : A ∈ P encA) {b₁ b₀ : β} (h₁ : b₁ ∈ B) (h₀ : b₀ ∉ B) :
    PolyTimeReducible encA encB A B := by
  obtain ⟨f, hf, hfA⟩ := hA
  refine ⟨fun a => if f a then b₁ else b₀, hf.ite (.const b₁) (.const b₀), fun a => ?_⟩
  rw [hfA a]
  cases hfa : f a
  · simp only [hfa, Bool.false_eq_true, ↓reduceIte, h₀]
  · simp only [hfa, ↓reduceIte, h₁]

end Cslib.Complexity
