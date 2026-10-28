/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.HashFamily
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.Product
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Uniform random functions as Δ-universal hash families

A uniformly random function into a finite additive group has uniform differences at distinct
inputs. Negating the complete function preserves its uniform law, and hence the same bound.
These are information-theoretic laws; they make no efficient-sampling claim.

## Main results

* `Cslib.Probability.isDeltaUniversalHash_uniformOfFintype`: uniform functions are Δ-universal.
* `Cslib.Probability.isDeltaUniversalHash_neg_uniformOfFintype`: negated uniform functions satisfy
  the same bound.
-/

@[expose] public section

namespace Cslib.Probability

open scoped ENNReal

/-- A uniformly random function from a finite domain `X` into a finite additive group `G` is
`|G|⁻¹`-almost-Δ-universal. -/
theorem isDeltaUniversalHash_uniformOfFintype {X G : Type*} [Fintype X] [DecidableEq X]
    [AddGroup G] [Fintype G] [Nonempty G] :
    IsDeltaUniversalHash (PMF.uniformOfFintype (X → G)) id (Fintype.card G : ℝ≥0∞)⁻¹ := by
  refine IsDeltaUniversalHash.of_map_sub_eq_uniform fun x x' hx => ?_
  rw [← Probability.PMF.uniformOfFintype_update x, PMF.map_bind]
  simp only [id_eq, PMF.map_comp, Function.comp_def, Function.update_self,
    Function.update_of_ne hx.symm]
  simp only [PMF.map, Function.comp_def]
  rw [PMF.bind_comm]
  have hsub (f : X → G) :
      ((PMF.uniformOfFintype G).bind fun a => PMF.pure (a - f x')) =
        PMF.uniformOfFintype G :=
    Probability.PMF.uniformOfFintype_map_equiv (Equiv.subRight (f x'))
  simp only [hsub, PMF.bind_const]

/-- The negated uniform random function `f ↦ (fun x => -f x)` from a finite domain `X` into a
finite additive group `G` is `|G|⁻¹`-almost-Δ-universal. -/
theorem isDeltaUniversalHash_neg_uniformOfFintype {X G : Type*} [Fintype X] [DecidableEq X]
    [AddGroup G] [Fintype G] [Nonempty G] :
    IsDeltaUniversalHash (PMF.uniformOfFintype (X → G)) (fun f x => -f x)
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  intro x x' hx δ
  have hmap := Probability.PMF.uniformOfFintype_map_equiv
    (Equiv.piCongrRight fun _ : X => Equiv.neg G)
  have h := isDeltaUniversalHash_uniformOfFintype x x' hx δ
  rw [← hmap, PMF.toOuterMeasure_map_apply] at h
  exact h

end Cslib.Probability
