/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.NumberTheory.Padics.AdjoinRootReduction
import ComplexityTests.Foundations.NumberTheory.Padics.AdjoinRootValuation

/-! Tests for the reductions `O → (ℤ / 2 ^ n)[U] / (U ^ 2 + U + 1)` of the valuation ring of
`K = ℚ[U] / (U ^ 2 + U + 1)`. -/

namespace ComplexityTests.AdjoinRootReduction

open Polynomial ComplexityTests.AdjoinRootValuation

/-- The valuation ring `O` of `K`. -/
noncomputable abbrev O : Subring K := v.integer

/-- Reduction of `O` modulo `2 ^ n`. -/
noncomputable abbrev π (n : ℕ) : O →+* GaloisRing 2 n f :=
  AdjoinRoot.reduction f_monic f_irreducible n

/-- `U ∈ O` reduces to `U`. -/
example (n : ℕ) : π n ⟨ι (AdjoinRoot.root f), (Valuation.mem_integer_iff _ _).mpr
    (AdjoinRoot.padicValuation_map_le_one f_monic f_irreducible _)⟩ = AdjoinRoot.root _ := by
  rw [AdjoinRoot.reduction_toRat, AdjoinRoot.map_root]

/-- `1 + U ∈ O` reduces to `1 + U`. -/
example (n : ℕ) : π n ⟨ι (1 + AdjoinRoot.root f), (Valuation.mem_integer_iff _ _).mpr
    (AdjoinRoot.padicValuation_map_le_one f_monic f_irreducible _)⟩ = 1 + AdjoinRoot.root _ := by
  rw [AdjoinRoot.reduction_toRat, map_add, map_one, AdjoinRoot.map_root]

/-- On `ℤ_(2)`, the reduction is reduction modulo `2 ^ n`. -/
example (n : ℕ) (q : (Rat.padicValuation 2).integer) (hq : algebraMap ℚ K q ∈ O) :
    π n ⟨_, hq⟩ = algebraMap (ZMod (2 ^ n)) _ (Rat.padicIntegerToZModPow 2 n q) :=
  AdjoinRoot.reduction_algebraMap f_monic f_irreducible n q hq

/-- The reductions modulo `8` and then `2` agree with the reduction modulo `2`. -/
example : (AdjoinRoot.map (ZMod.castHom (pow_dvd_pow 2 (by norm_num : 1 ≤ 3)) (ZMod (2 ^ 1))) _ _
    (GaloisRing.map_castHom_map f (pow_dvd_pow 2 (by norm_num : 1 ≤ 3))).symm.dvd).comp (π 3) =
      π 1 :=
  AdjoinRoot.castHom_comp_reduction f_monic f_irreducible (by norm_num : 1 ≤ 3)

end ComplexityTests.AdjoinRootReduction
