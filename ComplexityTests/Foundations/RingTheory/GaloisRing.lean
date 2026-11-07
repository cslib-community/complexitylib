/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.RingTheory.GaloisRing
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases

/-! Tests for Galois rings, on `(ℤ / 8)[U] / (U ^ 2 + U + 1)`: the case `p = 2`, `e = 2` and
precision `3` of the base coefficient ring `O / (2 ^ 3)` of [OpenAI2026ETH], §D.4.1, which is the
manuscript's `A_3` when `ℓ = 1`. -/

namespace ComplexityTests.GaloisRing

open Polynomial IsLocalRing

/-- `U ^ 2 + U + 1`, irreducible modulo 2. -/
noncomputable def f : ℤ[X] := X ^ 2 + X + 1

theorem f_monic : f.Monic := by unfold f; monicity!

theorem f_natDegree : f.natDegree = 2 := by unfold f; compute_degree!

theorem f_irreducible : Irreducible (f.map (Int.castRingHom (ZMod 2))) := by
  unfold f
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
    simp [this]
  · intro x hx
    rw [IsRoot.def, eval_add, eval_add, eval_pow, eval_X, eval_one] at hx
    fin_cases x <;> revert hx <;> decide

instance : Fact f.Monic := ⟨f_monic⟩

instance : Fact (Irreducible (f.map (Int.castRingHom (ZMod 2)))) := ⟨f_irreducible⟩

/-- The ring `(ℤ / 8)[U] / (U ^ 2 + U + 1)`. -/
abbrev A : Type := GaloisRing 2 3 f

/-- The root `U`. -/
noncomputable abbrev U : A := AdjoinRoot.root _

/-! ### Locality and units -/

/-- The residue field has characteristic two. -/
theorem two_eq_zero : (2 : AdjoinRoot (f.map (Int.castRingHom (ZMod 2)))) = 0 := by
  rw [← map_ofNat (AdjoinRoot.of _), show (OfNat.ofNat 2 : ZMod 2) = 0 by decide, map_zero]

/-- The ring is local. -/
example : IsLocalRing A := inferInstance

/-- `2` is not a unit: it vanishes modulo `2`. -/
example : ¬IsUnit (2 : A) := by
  rw [GaloisRing.isUnit_iff f_monic f_irreducible, map_ofNat, not_not]
  exact two_eq_zero

/-- `1 + 2 U` is a unit: it is one modulo `2`. -/
example : IsUnit (1 + 2 * U) := by
  rw [GaloisRing.isUnit_iff f_monic f_irreducible]
  simp only [map_add, map_mul, map_one, map_ofNat, two_eq_zero, zero_mul, add_zero]
  exact one_ne_zero

/-- `2` generates the maximal ideal. -/
example : (2 : A) ∈ maximalIdeal A := by
  rw [GaloisRing.maximalIdeal_eq]
  exact_mod_cast Ideal.mem_span_singleton_self (2 : A)

/-- The residue field has `2 ^ 2 = 4` elements. -/
example : Nat.card (AdjoinRoot (f.map (Int.castRingHom (ZMod 2)))) = 4 := by
  rw [GaloisRing.natCard_adjoinRoot f_monic, f_natDegree]
  norm_num

/-! ### Digit lifts and interpolation -/

/-- The digit vector `(0, 1)`. -/
def c₀₁ : Fin f.natDegree → ZMod 2 := fun i => if (i : ℕ) = 1 then 1 else 0

/-- The digit vector `(1, 0)`. -/
def c₁₀ : Fin f.natDegree → ZMod 2 := fun i => if (i : ℕ) = 0 then 1 else 0

/-- The lift of `(0, 1)` is `U`, and the lift of `(1, 0)` is `1`. -/
theorem digitLift_c₀₁ :
    GaloisRing.digitLift 2 3 f c₀₁ = U ∧ GaloisRing.digitLift 2 3 f c₁₀ = 1 := by
  simp only [GaloisRing.digitLift, Fin.sum_univ_eq_sum_range
    (fun i => (((if i = 1 then 1 else 0 : ZMod 2)).val : A) * AdjoinRoot.root _ ^ i),
    Fin.sum_univ_eq_sum_range
    (fun i => (((if i = 0 then 1 else 0 : ZMod 2)).val : A) * AdjoinRoot.root _ ^ i),
    c₀₁, c₁₀, f_natDegree, Finset.sum_range_succ, Finset.sum_range_zero]
  exact ⟨by simp [ZMod.val_one]; rfl, by simp [ZMod.val_one]⟩

/-- `U - 1` is a unit, as the difference of two distinct digit lifts. -/
example : IsUnit (U - 1) := by
  rw [← digitLift_c₀₁.1, ← digitLift_c₀₁.2]
  refine GaloisRing.isUnit_digitLift_sub f_monic f_irreducible fun h => ?_
  have := congrFun h ⟨1, by rw [f_natDegree]; norm_num⟩
  simp [c₀₁, c₁₀] at this

/-- There are `4` digit vectors, so a cubic over the ring is the interpolant of its values at the
four digit lifts. -/
example (P : A[X]) (hP : P.natDegree ≤ 3) :
    P = Lagrange.ringInterpolate Finset.univ (GaloisRing.digitLift 2 3 f)
      (fun c => P.eval (GaloisRing.digitLift 2 3 f c)) := by
  refine GaloisRing.eq_ringInterpolate_digitLift f_monic f_irreducible
    ((degree_le_natDegree).trans_lt ?_)
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, f_natDegree]
  exact_mod_cast (show P.natDegree < 2 ^ 2 by omega)

end ComplexityTests.GaloisRing
