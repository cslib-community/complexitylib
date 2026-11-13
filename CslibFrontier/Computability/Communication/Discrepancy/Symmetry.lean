/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Discrepancy

/-!
# Discrepancy under exchange of the players

Transposing the input distribution and Boolean gadget preserves discrepancy, since the same
rectangles are available after swapping their two factors. In particular, uniform discrepancy
is unchanged when the players exchange roles in a lifting simulation.
-/

public section

namespace Cslib.Communication

open Finset BitString Probability

variable {X Y : Type*} [Finite X] [Finite Y]

private theorem discrepancy_flip_le_of_swap (ν : PMF (X × Y)) (μ : PMF (Y × X))
    (f : X → Y → Bool) (hswap : ∀ x y, μ (y, x) = ν (x, y)) :
    discrepancy μ (fun y x => f x y) ≤ discrepancy ν f := by
  obtain ⟨A, B, h⟩ := exists_abs_sum_eq_discrepancy μ (fun y x => f x y)
  rw [← h, sum_comm]
  simpa only [hswap] using abs_sum_le_discrepancy ν f B A

/-- Swapping the two players and the two coordinates of the input distribution preserves
rectangle discrepancy. -/
theorem discrepancy_flip_of_swap (ν : PMF (X × Y)) (μ : PMF (Y × X))
    (f : X → Y → Bool) (hswap : ∀ x y, μ (y, x) = ν (x, y)) :
    discrepancy μ (fun y x => f x y) = discrepancy ν f := by
  apply le_antisymm (discrepancy_flip_le_of_swap ν μ f hswap)
  simpa only using
    discrepancy_flip_le_of_swap μ ν (fun y x => f x y) (fun y x => (hswap x y).symm)

omit [Finite X] [Finite Y] in
/-- Uniform discrepancy is invariant under exchanging the players. -/
theorem discrepancy_uniform_flip [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → Bool) :
    discrepancy (PMF.uniformOfFintype (Y × X)) (fun y x => f x y) =
      discrepancy (PMF.uniformOfFintype (X × Y)) f := by
  apply discrepancy_flip_of_swap
  intro x y
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.mul_comm]

end Cslib.Communication
