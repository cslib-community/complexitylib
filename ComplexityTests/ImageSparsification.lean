/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.LinearAlgebra.ImageSparsification

/-!
# Image sparsification examples

The tests exercise an exact cover of a nonsurjective product map, the exceptional-output
budget when the output space is zero, and failure of the decomposition condition when both
input spaces are zero but the output space contains constants.
-/

open Cslib.ImageSparsification Module Finset

namespace ComplexityTests.ImageSparsification

private def constantMap (_ : Unit) (_ : Fin 3) : Fin 3 := 0

private theorem constant_decomposition :
    HasSliceDecomposition constantMap
      (⊤ : Submodule ℚ (Unit → ℚ)) (⊥ : Submodule ℚ (Fin 3 → ℚ)) ⊤ := by
  intro v _
  exact ⟨fun _ _ ↦ v 0, 0, fun _ ↦ Submodule.mem_top,
    fun _ ↦ Submodule.zero_mem _, fun _ _ ↦ (add_zero _).symm⟩

-- The output type has three elements, but this map attains only one. The theorem still
-- gives an exact cover using one selected input, with no surjectivity assumption.
example : ∃ (s : Finset Unit) (t : Finset (Fin 3)), s.card + t.card = 1 ∧
    ∀ (a : Unit) (b : Fin 3),
      (∃ a' ∈ s, ∃ b' : Fin 3, constantMap a' b' = constantMap a b) ∨
      (∃ b' ∈ t, ∃ a' : Unit, constantMap a' b' = constantMap a b) := by
  obtain ⟨s, t, hcard, hcover⟩ := exists_image_cover constant_decomposition
  have hbound : s.card + t.card ≤ 1 := by simpa using hcard
  have hpos : 0 < s.card + t.card := by
    rcases hcover () 0 with ⟨a, ha, _, _⟩ | ⟨b, hb, _, _⟩
    · have := Finset.card_pos.mpr ⟨a, ha⟩
      omega
    · have := Finset.card_pos.mpr ⟨b, hb⟩
      omega
  exact ⟨s, t, by omega, hcover⟩

-- With the zero output space, every output can be exceptional. For the pairing map all
-- four outputs are attained, and the exceptional-output bound is achieved exactly.
example : ∃ e : Finset (Bool × Bool), e.card = 4 ∧ ∀ a b, (a, b) ∈ e := by
  have h : HasSliceDecomposition Prod.mk (⊥ : Submodule ℚ (Bool → ℚ))
      (⊥ : Submodule ℚ (Bool → ℚ)) (⊥ : Submodule ℚ ((Bool × Bool) → ℚ)) := by
    intro v hv
    rw [Submodule.mem_bot] at hv
    subst v
    exact (sliceSpace _ _).zero_mem
  obtain ⟨s, t, e, hs, ht, _, _, hcover⟩ := exists_image_cover_with_exceptions h
  have hs' : s = ∅ := Finset.card_eq_zero.mp (by simpa using hs)
  have ht' : t = ∅ := Finset.card_eq_zero.mp (by simpa using ht)
  have he (a b : Bool) : (a, b) ∈ e := by simpa [hs', ht'] using hcover a b
  have heq : e = univ := Finset.eq_univ_iff_forall.mpr fun x ↦ he x.1 x.2
  exact ⟨e, by simp [heq], he⟩

-- The slice hypothesis is substantive: zero input spaces cannot represent the constant-one
-- pullback on a nonempty product.
example : ¬ HasSliceDecomposition (fun (_ : Unit) (_ : Unit) ↦ ())
    (⊥ : Submodule ℚ (Unit → ℚ)) (⊥ : Submodule ℚ (Unit → ℚ))
    (⊤ : Submodule ℚ (Unit → ℚ)) := by
  intro h
  have hmem := h (fun _ ↦ 1) Submodule.mem_top
  rw [sliceSpace_bot_bot, Submodule.mem_bot] at hmem
  have := congrFun (congrFun hmem ()) ()
  norm_num at this

end ComplexityTests.ImageSparsification
