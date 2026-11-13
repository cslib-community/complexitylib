/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import CslibFrontier.Probability.PMF.Independence
import CslibFrontier.Probability.PMF.Uniform

/-! # Independent observables of a finite PMF -/

namespace CslibFrontierTests.PMFIndependence

open Cslib.Probability Cslib.Probability.PMF ProbabilityTheory

/-- The two coordinates of a uniform pair: the second is uniform and independent of the first. -/
example : IndepUniform (PMF.uniformOfFintype (Bool × Bool)) Prod.fst Prod.snd := by
  refine ⟨?_⟩
  rw [uniformOfFintype_prod_map_fst, PMF.uniformOfFintype_prod]
  exact PMF.map_id _

/-- Its characterization gives Mathlib's independence and the uniform marginal. -/
example : IndepFun Prod.fst Prod.snd (PMF.uniformOfFintype (Bool × Bool)).toMeasure ∧
    (PMF.uniformOfFintype (Bool × Bool)).map Prod.snd = PMF.uniformOfFintype Bool :=
  (indepUniform_iff measurable_fst measurable_snd).1
    ⟨by rw [uniformOfFintype_prod_map_fst, PMF.uniformOfFintype_prod]; exact PMF.map_id _⟩

/-- A constant first observable is independent of everything, so `IndepUniform` reduces to the
second observable being uniform. -/
example (Y : Bool → Bool) (hY : (PMF.uniformOfFintype Bool).map Y = PMF.uniformOfFintype Bool) :
    IndepUniform (PMF.uniformOfFintype Bool) (fun _ => ()) Y := by
  refine ⟨?_⟩
  rw [show (PMF.uniformOfFintype Bool).map (fun _ => ()) = PMF.pure () from PMF.map_const _ _,
    PMF.pure_bind]
  conv_rhs => rw [← hY]
  rw [PMF.map_comp]
  rfl

end CslibFrontierTests.PMFIndependence
