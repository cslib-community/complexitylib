/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Probability.Extractor.Basic
import CslibFrontier.Probability.Product
import CslibFrontier.Probability.StatisticalDistance

/-! Ordinary-import clients for seedless extraction, including the smallest lengths. -/

set_option linter.privateModule false

open Cslib Cslib.Probability Cslib.Probability.PMF

-- The zero-entropy boundary is inhabited by a point mass, and its first bit is fixed.
example : minEntropy (PMF.pure (fun _ : Fin 1 => false)) = 0 := by
  simp

example : (PMF.pure (fun _ : Fin 1 => false)).map (fun x => x 0) = PMF.pure false := by
  simp

example : ¬ IsExtractor (fun (x : BitString 1) (_ : Unit) => x) 0 (1 / 4) := by
  simpa only [id, Nat.cast_one, Nat.cast_ofNat, sub_self,
    show (2 : ℝ) - 1 = 1 by norm_num, show (3 : ℝ) - 1 = 2 by norm_num] using
    not_isExtractor_bitString (n := 1) (m := 1) (by decide) (by decide)
    id (ε := 1 / 4) (by norm_num)

-- The witness specializes to identity on two bits without losing the first-coordinate law.
example : ∃ (source : PMF (BitString 2)) (b : Bool),
    1 ≤ minEntropy source ∧ (source.map id).map (fun x => x ⟨0, by decide⟩) = PMF.pure b ∧
    1 / 2 ≤ dist (source.map id) (PMF.uniformOfFintype (BitString 2)) := by
  simpa only [id, Nat.cast_one, Nat.cast_ofNat, sub_self,
    show (2 : ℝ) - 1 = 1 by norm_num, show (3 : ℝ) - 1 = 2 by norm_num] using
    exists_minEntropy_map_first_eq_pure (n := 2) (m := 2)
    (by decide) (by decide) id

-- Constant multibit output also fails with a singleton seed.
example : ¬ IsExtractor (fun (_ : BitString 3) (_ : Unit) =>
    (fun _ : Fin 2 => true)) 2 (1 / 4) := by
  simpa only [id, Nat.cast_one, Nat.cast_ofNat, sub_self,
    show (2 : ℝ) - 1 = 1 by norm_num, show (3 : ℝ) - 1 = 2 by norm_num] using
    not_isExtractor_bitString (n := 3) (m := 2) (by decide) (by decide)
    (fun _ _ => true) (ε := 1 / 4) (by norm_num)

-- The lower bound is sharp for identity on two bits.
example : ∃ source : PMF (BitString 2),
    dist (source.map id) (PMF.uniformOfFintype (BitString 2)) = 1 / 2 := by
  let p := PMF.uniformOfFintype (BitString 2)
  let event : Set (BitString 2) := {x | x 0 = false}
  have hevent : ∃ x ∈ event, x ∈ p.support := by
    exact ⟨fun _ => false, rfl, by simp [p]⟩
  refine ⟨p.filter event hevent, ?_⟩
  rw [PMF.map_id, dist_comm, dist_filter]
  have hmarginal : p.map (fun x => x 0) = PMF.uniformOfFintype Bool := by
    dsimp only [p]
    rw [← pi_uniformOfFintype, pi_map_eval]
  have hprob := congrArg (fun q : PMF Bool => q.toOuterMeasure {true}) hmarginal
  rw [PMF.toOuterMeasure_map_apply] at hprob
  have heq : (fun x : BitString 2 => x 0) ⁻¹' ({true} : Set Bool) = eventᶜ := by
    ext x
    simp [event]
  rw [heq] at hprob
  rw [hprob]
  norm_num [PMF.toOuterMeasure_apply, PMF.uniformOfFintype_apply]
