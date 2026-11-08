/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.HashFamily.Matrix
import CslibFrontier.Probability.UniversalHash
import Mathlib.Algebra.Field.ZMod

/-!
# Finite-field matrix hashing clients

A nonzero input to a uniform `2 × 3` matrix over `ZMod 17` has uniform output. Zero input
instead has deterministic output, so the nonzero premise cannot be dropped. Matrix universality
also feeds the existing leftover-hash theorem without a new family or entropy definition.
-/

namespace CslibFrontierTests.MatrixHash

open Cslib.Probability Cslib.Probability.PMF
open scoped Matrix ENNReal Cslib.Probability.PMF

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

example :
    (PMF.uniformOfFintype (Matrix (Fin 2) (Fin 3) (ZMod 17))).map
      (fun A => A *ᵥ ![2, 3, 4]) = PMF.uniformOfFintype (Fin 2 → ZMod 17) :=
  uniformOfFintype_map_mulVec _ (by decide)

theorem zero_input :
    (PMF.uniformOfFintype (Matrix (Fin 2) (Fin 3) (ZMod 17))).map
      (fun A => A *ᵥ (0 : Fin 3 → ZMod 17)) = PMF.pure 0 := by
  simp only [Matrix.mulVec_zero]
  exact PMF.map_const _ _

example :
    (PMF.uniformOfFintype (Matrix (Fin 2) (Fin 3) (ZMod 17))).map
      (fun A => A *ᵥ (0 : Fin 3 → ZMod 17)) ≠
        PMF.uniformOfFintype (Fin 2 → ZMod 17) := by
  rw [zero_input]
  intro h
  have hzero := congrArg (fun p => (p 0).toReal) h
  norm_num [PMF.uniformOfFintype_apply, Fintype.card_fun] at hzero

example :
    IsDeltaUniversalHash (PMF.uniformOfFintype (Matrix (Fin 2) (Fin 3) (ZMod 17)))
      (fun A x => A *ᵥ x) (289 : ℝ≥0∞)⁻¹ := by
  simpa using (isDeltaUniversalHash_mulVec (ι := Fin 2) (κ := Fin 3) (F := ZMod 17))

example :
    IsDeltaUniversalHash (PMF.uniformOfFintype (Matrix (Fin 0) (Fin 0) (ZMod 17)))
      (fun A x => A *ᵥ x) 1 := by
  simpa using (isDeltaUniversalHash_mulVec (ι := Fin 0) (κ := Fin 0) (F := ZMod 17))

example :
    dist
      (seededHash (PMF.uniformOfFintype (Matrix (Fin 2) (Fin 3) (ZMod 17)))
        (PMF.uniformOfFintype (Fin 3 → ZMod 17)) (fun A x => A *ᵥ x))
      ((PMF.uniformOfFintype (Matrix (Fin 2) (Fin 3) (ZMod 17))).bind fun A =>
        (PMF.uniformOfFintype (Fin 2 → ZMod 17)).map (A, ·)) ≤
      Real.sqrt ((17 : ℝ)⁻¹) / 2 := by
  have h := (isDeltaUniversalHash_mulVec (ι := Fin 2) (κ := Fin 3)
    (F := ZMod 17)).isTwoUniversal.leftover_hash_of_mass_le
      (PMF.uniformOfFintype (Fin 3 → ZMod 17))
      (mass := (17 : ℝ)⁻¹ ^ 3) (by intro x; norm_num [PMF.uniformOfFintype_apply])
  norm_num at h ⊢
  exact h

end CslibFrontierTests.MatrixHash
