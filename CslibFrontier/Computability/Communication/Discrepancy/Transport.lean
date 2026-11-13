/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Discrepancy

/-!
# Discrepancy under alphabet equivalences

Separate equivalences of the players' alphabets map rectangles bijectively to rectangles.
Thus transporting a gadget and its distribution preserves discrepancy. In particular, changing
between finite indices and bit strings does not change uniform discrepancy.
-/

public section

namespace Cslib.Communication

open Finset Probability

variable {X Y X' Y' : Type*} [Finite X] [Finite Y] [Finite X'] [Finite Y']

private theorem discrepancy_comap_equiv_le (e : X' ≃ X) (f : Y' ≃ Y)
    (ν : PMF (X × Y)) (μ : PMF (X' × Y')) (g : X → Y → Bool)
    (hμ : ∀ x y, μ (x, y) = ν (e x, f y)) :
    discrepancy μ (fun x y => g (e x) (f y)) ≤ discrepancy ν g := by
  obtain ⟨A, B, h⟩ := exists_abs_sum_eq_discrepancy μ (fun x y => g (e x) (f y))
  rw [← h]
  simpa only [sum_map, Equiv.toEmbedding_apply, hμ] using
    abs_sum_le_discrepancy ν g (A.map e.toEmbedding) (B.map f.toEmbedding)

/-- Transporting both alphabet coordinates and their point masses preserves discrepancy. -/
theorem discrepancy_comap_equiv (e : X' ≃ X) (f : Y' ≃ Y)
    (ν : PMF (X × Y)) (μ : PMF (X' × Y')) (g : X → Y → Bool)
    (hμ : ∀ x y, μ (x, y) = ν (e x, f y)) :
    discrepancy μ (fun x y => g (e x) (f y)) = discrepancy ν g := by
  apply le_antisymm (discrepancy_comap_equiv_le e f ν μ g hμ)
  have hrev := discrepancy_comap_equiv_le e.symm f.symm μ ν
    (fun x y => g (e x) (f y)) (fun x y => by simpa using (hμ (e.symm x) (f.symm y)).symm)
  simpa only [Equiv.apply_symm_apply] using hrev

omit [Finite X] [Finite Y] [Finite X'] [Finite Y'] in
/-- Uniform discrepancy is invariant under separate equivalences of the input alphabets. -/
theorem discrepancy_uniform_comap_equiv
    [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    [Nonempty X] [Nonempty Y] [Nonempty X'] [Nonempty Y']
    (e : X' ≃ X) (f : Y' ≃ Y) (g : X → Y → Bool) :
    discrepancy (PMF.uniformOfFintype (X' × Y')) (fun x y => g (e x) (f y)) =
      discrepancy (PMF.uniformOfFintype (X × Y)) g := by
  apply discrepancy_comap_equiv
  intro x y
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod,
    Fintype.card_congr e, Fintype.card_congr f]

end Cslib.Communication
