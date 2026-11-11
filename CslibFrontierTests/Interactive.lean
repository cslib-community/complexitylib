/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Interactive.Sequential
import CslibFrontier.Probability.PMF.Uniform

/-!
# Tests for interactive reductions

A one-challenge reduction `coinStep` on Boolean claims: the verifier sends a fair coin `c` and
outputs the claim `x || c`. It reduces the claim "`x` is `true`" to itself, is perfectly complete,
and is round-by-round sound with error `1 / 2`, since a false claim survives only when `c` is
`true`. Its iterations exercise sequential composition with nonzero errors, so the composition
and iteration theorems are applied to satisfiable hypotheses.
-/

namespace CslibFrontierTests.Interactive

open Cslib Cslib.Interactive Spec
open scoped ENNReal

/-- One round: a public fair coin. -/
abbrev coinSpec : Spec := [.verifier Bool]

/-- The claim that the Boolean statement is `true`; there is no witness. -/
def rel : Bool → Unit → Prop := fun x _ => x = true

/-- The verifier sends a fair coin `c` and both parties continue with the claim `x || c`. -/
noncomputable def coinStep :
    Reduction OracleSpec.empty OracleSpec.empty coinSpec Bool Unit Bool Unit where
  prover x _ := pure (show Bool → ProbOracleComp OracleSpec.empty (Bool × Unit) from
    fun c => pure (x || c, ()))
  verifier :=
    { samplers := (ProbComp.uniform Bool, ())
      decide := fun x c => pure (some (x || c.1)) }

/-- The coin round is perfectly complete. -/
theorem coinStep_complete : coinStep.Complete World.plain rel rel 0 := by
  rintro x ⟨⟩ (rfl : x = true)
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  simp [coinStep, runStrategy, Verifier.outputOn, rel]
  rfl

/-- The coin round is round-by-round sound with error `1 / 2`. -/
theorem coinStep_rbrSound :
    coinStep.verifier.RbrSound (language rel) (language rel) ((1 / 2 : ℝ≥0∞), ()) := by
  refine ⟨fun x p => match p with
      | none => x = true
      | some (c, ()) => (x || c) = true,
    fun x hx hS => hx ⟨(), hS⟩, fun x => ⟨fun hx => ?_, fun c hS ⟨x', ⟨⟨⟩, hx'⟩, hout⟩ => ?_⟩⟩
  · have hset : {c : Bool | (x || c) = true} = {true} := by
      ext c
      cases x <;> cases c <;> simp_all
    change (ProbComp.eval (ProbComp.uniform Bool)).toOuterMeasure {c | (x || c) = true} ≤ 1 / 2
    rw [hset, ProbComp.eval_uniform, Probability.PMF.toOuterMeasure_uniformOfFintype]
    have hcard : (Finset.univ.filter (· ∈ ({true} : Set Bool))).card = 1 := by decide
    rw [hcard, Fintype.card_bool]
    simp
  · simp only [Verifier.outputOn, coinStep] at hout
    exact hS ((Option.some.inj hout).trans hx')

/-- The coin round is sound with error `1 / 2`, by round-by-round soundness. -/
theorem coinStep_sound :
    coinStep.verifier.Sound (oP := OracleSpec.empty) World.plain (language rel) (language rel)
      (1 / 2) := by
  simpa [PerChallenge.sum] using coinStep_rbrSound.sound

/-- Two coin rounds in sequence are complete, by composition. -/
example : (coinStep.append coinStep).Complete World.plain rel rel 0 := by
  simpa using coinStep_complete.append coinStep_complete

/-- Two coin rounds in sequence are sound with error `1`, by composition of round-by-round
soundness; the composed errors are concatenated. -/
example :
    (coinStep.append coinStep).verifier.Sound (oP := OracleSpec.empty) World.plain (language rel)
      (language rel) (1 / 2 + 1 / 2) := by
  have h := (coinStep_rbrSound.append coinStep_rbrSound).sound
  simp only [PerChallenge.sum_append, PerChallenge.sum, add_zero] at h
  exact h

/-- Iterated coin rounds are complete, by iterated composition. -/
example (k : ℕ) :
    (Reduction.iterate (s := fun _ => coinSpec) (S := fun _ => Bool) (W := fun _ => Unit)
      (fun _ => coinStep) k).Complete World.plain rel rel 0 := by
  simpa using Reduction.Complete.iterate (rel := fun _ => rel) (ε := fun _ => 0) k
    fun _ _ => coinStep_complete

end CslibFrontierTests.Interactive
