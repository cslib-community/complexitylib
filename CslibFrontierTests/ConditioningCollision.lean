/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.OneWay.Collision
import CslibFrontier.Probability.Product

/-! Conditioning tests cover null observations, unequal fibers and joint reconstruction. -/

namespace ComplexityTests.ConditioningCollision

open Cslib Cslib.Probability Cslib.Probability.PMF Cslib.Crypto

-- Impossible observations use the second marginal; they do not erase its retained value.
example : conditionalSnd (PMF.pure (false, true)) true = PMF.pure true := by
  simp [conditionalSnd]

-- Possible observations recover their kernel exactly, including deterministic correlations.
example : conditionalSnd (PMF.pure (false, true)) false = PMF.pure true := by
  simpa using conditionalSnd_bind_pair (PMF.pure false) (fun _ => PMF.pure true) false (by simp)

-- Unequal fibers must get different conditional laws: one source point versus two.
private def observation (i : Fin 3) : Bool := i == 0

example : collisionProbability
    (conditionalSnd ((uniformOfFintype (Fin 3)).map (fun i => (observation i, i))) true) = 1 := by
  let : Nonempty {i // observation i = true} := ⟨⟨0, by decide⟩⟩
  rw [collisionProbability_conditionalSnd_uniform_map]
  have hcard : Nat.card {i // observation i = true} = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hcard]
  norm_num

example : collisionProbability
    (conditionalSnd ((uniformOfFintype (Fin 3)).map (fun i => (observation i, i))) false) =
      1 / 2 := by
  let : Nonempty {i // observation i = false} := ⟨⟨1, by decide⟩⟩
  rw [collisionProbability_conditionalSnd_uniform_map]
  have hcard : Nat.card {i // observation i = false} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hcard]
  norm_num

-- The full joint law, not just separate marginals, survives revealing and resampling.
example :
    (((uniformOfFintype Bool).bind (fun b => PMF.pure (b, !b))).map Prod.fst).bind
        (fun b => (conditionalSnd
          ((uniformOfFintype Bool).bind (fun b => PMF.pure (b, !b))) b).map (b, ·)) =
      (uniformOfFintype Bool).bind (fun b => PMF.pure (b, !b)) := bind_conditionalSnd _

-- Collisions still make sense on infinite ambient types.
example (p : PMF (List Bool)) :
    collisionProbability (p.map (List.cons true)) = collisionProbability p :=
  collisionProbability_map_of_injective p _ (fun _ _ h => List.cons.inj h |>.2)

example (n : ℕ) : collisionProbability (BitString.uniformList n) = ((2 : ℝ) ^ n)⁻¹ := by
  rw [BitString.uniformList, collisionProbability_map_of_injective _ _ List.ofFn_injective,
    collisionProbability_uniform]
  simp

example : collisionProbability (PMF.pure ([] : List Bool)) = 1 := by
  rw [collisionProbability_eq_probability]
  simp

-- No regularity or injectivity is hidden in the elementary inversion equality.
example (n : ℕ) :
    collisionProbability ((BitString.uniformList n).map (fun _ => ([] : List Bool))) = 1 := by
  rw [output_collision_eq_inversion]
  simp [inversionGame, Game.succProbability]

example {f : List Bool → List Bool} (hf : OneWay f) :
    Negligible (fun n =>
      Real.toNNReal (collisionProbability ((BitString.uniformList n).map f))) :=
  hf.output_collision_negligible

end ComplexityTests.ConditioningCollision
