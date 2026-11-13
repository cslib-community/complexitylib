/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Communication.OneOutRectangle
import CslibFrontier.Probability.IID.Distinct
import Mathlib.Tactic

/-! The actual projected rectangle solver on a nonconstant two-input equality relation,
and nonuniform sampling/empty-tuple clients for the distinctness estimate. -/

namespace CslibFrontierTests.CommunicationOneOutRectangle
open Cslib.Communication Protocol OneOut
open Cslib.Probability

/-- A protocol computing equality, with both players sending one bit. -/
def eqProtocol : Protocol Bool Bool Bool :=
  .alice id
    (.bob id (.output true) (.output false))
    (.bob id (.output false) (.output true))

/-- The one-element injective tuple for a supplied input bit. -/
def singleton (a : Bool) : Fin 1 ↪ Bool := ⟨fun _ => a, fun _ _ _ => Subsingleton.elim _ _⟩

/-- Original protocol on legal injective tuples. -/
def original := atCoordinate eqProtocol (0 : Fin 1)

private theorem original_correct : original.Solves (Relation (fun a b z => z = decide (a = b)))
    Set.univ Set.univ := by
  apply solves_atCoordinate
  intro a _ b _
  cases a <;> cases b <;> rfl

private theorem alice_mem (a : Bool) : a ∈ aliceSide original 0 ∅ := by
  have h := canForce_aliceProjection original (singleton a)
  apply (original.labelLeaves.canForce_mono true ?_) h
  intro w hw
  change a ∈ aliceProjection original w at hw
  simpa [aliceGoal, Fin.eq_zero] using hw

private theorem bob_mem (b : Bool) : b ∈ bobSide original 0 ∅ := by
  have h := canForce_bobProjection original (singleton b)
  apply (original.labelLeaves.canForce_mono false ?_) h
  intro w hw
  change b ∈ bobProjection original w at hw
  simpa [bobGoal, Fin.eq_zero] using hw

/-- The newly compiled single-input protocol solves equality on every original input pair. -/
example (a b : Bool) : (rectangleProtocol original 0 ∅).run a b = decide (a = b) :=
  rectangleProtocol_solves original_correct 0 ∅ a (alice_mem a) b (bob_mem b)

example : (rectangleProtocol original 0 ∅).depth = 2 := by
  simp [original, eqProtocol]

/-- No repetition is possible for a single draw, even from a point mass. -/
example : ((Cslib.Probability.PMF.iid (PMF.pure true) 1).toOuterMeasure
    {x | ¬ Function.Injective x}).toReal = 0 := by
  have h := Cslib.Probability.PMF.iid_not_injective_le (PMF.pure true) 1
  have hz : ((Cslib.Probability.PMF.iid (PMF.pure true) 1).toOuterMeasure
      {x | ¬ Function.Injective x}).toReal ≤ 0 := by
    simpa only [show (1 : ℕ).choose 2 = 0 from rfl, Nat.cast_zero, zero_mul] using h
  exact le_antisymm hz ENNReal.toReal_nonneg

/-- A nonuniform source still satisfies the atom-mass estimate; no uniformity hypothesis. -/
example (μ : PMF Bool) (h : ∀ a, (μ a).toReal ≤ (3 / 4 : ℝ)) :
    ((Cslib.Probability.PMF.iid μ 2).toOuterMeasure
      {x | ¬ Function.Injective x}).toReal ≤ 3 / 4 := by
  simpa only [show (2 : ℕ).choose 2 = 1 from rfl, Nat.cast_one, one_mul] using
    Cslib.Probability.PMF.iid_not_injective_le_of_mass_le μ 2 h

example :
    Function.Injective (Fin.elim0 : Fin 0 → Bool) := Function.injective_of_subsingleton _

/-- The light-atom hypotheses have a nonempty instance, including the exact two-draw boundary. -/
example :
    (3 / 2 : ℝ) ≤
      ((Cslib.Probability.PMF.iid (PMF.uniformOfFintype (Fin 4)) 2).toOuterMeasure
        {x | Function.Injective x}).toReal +
      ((Cslib.Probability.PMF.iid (PMF.uniformOfFintype (Fin 4)) 2).toOuterMeasure
        {x | Function.Injective x}).toReal := by
  have hmass (a : Fin 4) :
      ((PMF.uniformOfFintype (Fin 4)) a).toReal ≤ (((2 : ℕ) : ℝ) ^ 2)⁻¹ := by
    norm_num [PMF.uniformOfFintype_apply]
  convert Cslib.Probability.PMF.iid_injective_pair_ge
    (PMF.uniformOfFintype (Fin 4)) (PMF.uniformOfFintype (Fin 4)) 2 (by omega)
    hmass hmass using 1; norm_num

end CslibFrontierTests.CommunicationOneOutRectangle
