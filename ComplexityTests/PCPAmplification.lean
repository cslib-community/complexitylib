/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Amplification
import Complexity.Computability.PCP.Amplification.Arithmetic
import Mathlib.Tactic.NormNum.Prime

/-! Regression clients for amplification with actual rotations and arbitrary degree. -/

namespace ComplexityTests.PCPAmplification

open Cslib.PCP Cslib.RotationMap
open ConstraintGraph HadamardTester

private abbrev Label := AffinePlaneFamilyLabel (ZMod 257) 257

private noncomputable def spectralBound : ℝ :=
  1 - 9 / (400 * (257 : ℝ) ^ 16)

private noncomputable def arithmeticInputs
    (G : FinConstraintGraph.{0} (Bool × (Fin 6 → Bool))) :
    letI := Classical.decEq G.V
    G.graph.PreprocessExpanders Label spectralBound :=
  letI := Classical.decEq G.V
  .ofFamily G.graph arithmeticExpanderFamily

private def singleGraph : ConstraintGraph Unit Unit (Bool × (Fin 6 → Bool)) :=
  ⟨fun _ => (), fun _ => (), fun _ _ _ => False⟩

private def singleLoop : FinConstraintGraph.{0} (Bool × (Fin 6 → Bool)) :=
  ⟨Unit, Unit, singleGraph⟩

-- The supplied contract is inhabited by the concrete arithmetic expander family.
example :
    letI := Classical.decEq singleLoop.V
    (arithmeticInputs singleLoop).whole.spectralExpansion ≤ spectralBound :=
  letI := Classical.decEq singleLoop.V
  (arithmeticInputs singleLoop).spectralExpansion_whole_le

-- The new interface recovers the old family-based pipeline exactly.
example {V E α : Type} [Fintype E] [DecidableEq V] (G : ConstraintGraph V E α) :
    G.preprocessWith (.ofFamily G arithmeticExpanderFamily) =
      G.preprocess arithmeticExpanderFamily :=
  rfl

example {V E α : Type} [Fintype E] [DecidableEq V] [Fintype α] [DecidableEq α]
    (G : ConstraintGraph V E α) (T q : ℕ) [NeZero q] :
    G.amplifyWith (.ofFamily G expanderFamily) T q = G.amplify T q :=
  rfl

-- Real arithmetic parameters are obtained without evaluating the enormous fixed degree.
example : ∃ q : ℕ, 2 ≤ q ∧
    2 / Amplification.retention (Fintype.card Label) spectralBound ≤
      ((q : ℝ) - 1) /
        Amplification.denominator 840 (Fintype.card (Bool × (Fin 6 → Bool)))
          (Fintype.card Label) spectralBound :=
  Amplification.exists_killRate (loss := 840) (by norm_num)
    Fintype.card_pos Fintype.card_pos (by norm_num [spectralBound])

-- These parameters actually instantiate the full amplifier, including all its size, value and
-- satisfiability fields. This is a mathematical client, not an efficiency certificate for a round.
open Amplification.Arithmetic in
example : Nonempty (Amplifier.{0} (Bool × (Fin 6 → Bool))) :=
  ⟨Amplification.amplifier arithmeticInputs walkLength killRate
    (by norm_num [spectralBound]) two_le_killRate walkLength_eq gap_pos gap_le_one gain⟩

-- A concrete normalization check for the generic coefficients, separate from family existence.
example : Amplification.retention 120 (1 - 1 / 360000) = 1 / 1452000 := by
  norm_num [Amplification.retention]

example (K : ℕ) : Amplification.denominator 476 K 120 (1 - 1 / 360000) =
    476 * (4 * (K : ℝ) ^ 2 + 16 * (K : ℝ) ^ 4 + 92928000 * (K : ℝ) ^ 5) := by
  norm_num [Amplification.denominator]
  ring

example (K : ℕ) : Amplification.denominator 840 K 120 (1 - 1 / 360000) =
    840 * (4 * (K : ℝ) ^ 2 + 16 * (K : ℝ) ^ 4 + 92928000 * (K : ℝ) ^ 5) := by
  norm_num [Amplification.denominator]
  ring

end ComplexityTests.PCPAmplification
