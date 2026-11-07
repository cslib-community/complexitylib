/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.NumberTheory.Padics.AdjoinRootValuation
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases

/-! Tests for the 2-adic valuation of `K = ℚ[U] / (U ^ 2 + U + 1)`, the case `e = 2` of the
coefficient field of [OpenAI2026ETH], §D.4.1. -/

namespace ComplexityTests.AdjoinRootValuation

open Polynomial
open scoped WithZero

/-- `U ^ 2 + U + 1`, irreducible modulo 2. -/
noncomputable def f : ℤ[X] := X ^ 2 + X + 1

theorem f_monic : f.Monic := by unfold f; monicity!

theorem f_irreducible : Irreducible (f.map (Int.castRingHom (ZMod 2))) := by
  unfold f
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
    simp [this]
  · intro x hx
    rw [IsRoot.def, eval_add, eval_add, eval_pow, eval_X, eval_one] at hx
    fin_cases x <;> revert hx <;> decide

/-- The field `K = ℚ[U] / (U ^ 2 + U + 1)`. -/
abbrev K : Type := AdjoinRoot (f.map (Int.castRingHom ℚ))

/-- The 2-adic valuation of `K`. -/
noncomputable abbrev v : Valuation K ℤᵐ⁰ := AdjoinRoot.padicValuation 2 f_monic f_irreducible

/-- The map `ℤ[U] / (f) → K`. -/
noncomputable abbrev ι : AdjoinRoot f →+* K := AdjoinRoot.map (Int.castRingHom ℚ) f _ dvd_rfl

instance : Fact (Irreducible (f.map (Int.castRingHom (ZMod 2)))) := ⟨f_irreducible⟩

/-- `U ^ 2 + U + 1 = 0` modulo `2`. -/
theorem root_sq_add_root_add_one :
    (AdjoinRoot.root (f.map (Int.castRingHom (ZMod 2)))) ^ 2 + AdjoinRoot.root _ + 1 = 0 := by
  rw [← AdjoinRoot.mk_X, ← map_pow, ← map_add, ← map_one (AdjoinRoot.mk _), ← map_add,
    AdjoinRoot.mk_eq_zero]
  exact dvd_of_eq (by simp [f])

/-- `U` is nonzero modulo `2`: otherwise `f(0) = 1` would vanish. -/
theorem root_ne_zero_mod_two :
    AdjoinRoot.map (Int.castRingHom (ZMod 2)) f _ dvd_rfl (AdjoinRoot.root f) ≠ 0 := by
  rw [AdjoinRoot.map_root]
  intro h
  have := root_sq_add_root_add_one
  rw [h] at this
  simp at this

/-- `1 + U` is nonzero modulo `2`: it is `U²`, the square of a nonzero element of a field. -/
theorem one_add_root_ne_zero_mod_two :
    AdjoinRoot.map (Int.castRingHom (ZMod 2)) f _ dvd_rfl (1 + AdjoinRoot.root f) ≠ 0 := by
  have hroot := root_ne_zero_mod_two
  rw [AdjoinRoot.map_root] at hroot
  rw [map_add, map_one, AdjoinRoot.map_root]
  intro h1
  have h := root_sq_add_root_add_one
  rw [add_assoc, add_comm (AdjoinRoot.root _), h1, add_zero] at h
  exact pow_ne_zero 2 hroot h

/-! ### The valuation on concrete elements -/

theorem padicValRat_two : padicValRat 2 (2 : ℚ) = 1 := by
  exact_mod_cast padicValRat.self (p := 2) one_lt_two

/-- `v (1 / 2) = exp 1`: the valuation extends that of `ℚ`. -/
example : v (algebraMap ℚ K (1 / 2)) = WithZero.exp 1 := by
  rw [AdjoinRoot.padicValuation_algebraMap]
  simp [Rat.padicValuation, padicValRat_two]

/-- `v (2 U) = v 2 * v U = exp (-1)`, by multiplicativity: `U` is nonzero modulo `2`. -/
example : v (algebraMap ℚ K 2 * ι (AdjoinRoot.root f)) = WithZero.exp (-1) := by
  rw [map_mul, AdjoinRoot.padicValuation_algebraMap,
    (AdjoinRoot.padicValuation_map_eq_one_iff f_monic f_irreducible _).mpr root_ne_zero_mod_two,
    mul_one]
  simp [Rat.padicValuation, padicValRat_two]

/-- `1 + U` is integral and nonzero modulo `2`, hence a unit of the valuation ring. -/
example : ∃ h : ι (1 + AdjoinRoot.root f) ∈ v.integer, IsUnit (⟨_, h⟩ : v.integer) :=
  have h := AdjoinRoot.padicValuation_map_le_one f_monic f_irreducible (1 + AdjoinRoot.root f)
  ⟨h, AdjoinRoot.isUnit_of_padicValuation_eq_one f_monic f_irreducible h
    ((AdjoinRoot.padicValuation_map_eq_one_iff f_monic f_irreducible _).mpr
      one_add_root_ne_zero_mod_two)⟩

end ComplexityTests.AdjoinRootValuation
