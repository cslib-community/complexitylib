/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexity.Foundations.Combinatorics.PartialLabelScores
import Mathlib.Tactic.NormNum

public section

open Cslib.BalancedSchedules
open scoped BigOperators

namespace Cslib.Tests.PartialLabelScores

-- An unknown index is not resampled when it is read twice.
theorem repeated_index_collision :
    partialCollision (fun _ : Bool => (none : Option Bool)) false false = 1 := by
  norm_num [partialCollision]
example : partialCollision (fun _ : Bool => (none : Option Bool)) false true = 1 / 2 := by
  norm_num [partialCollision]

-- Known equal and known unequal labels give exact indicators, not fractional probabilities.
example : partialCollision (fun _ : Bool => some false) false true = 1 := by
  norm_num [partialCollision]
example : partialCollision (fun b : Bool => some b) false true = 0 := by
  norm_num [partialCollision]

private abbrev Word := Bool → Bool
private def unknown : Bool → Option Word := fun _ => none

-- A whole two-bit label has four possibilities, but its observed coordinate has only two.
example : partialCollision unknown false true = 1 / 4 := by
  norm_num [partialCollision, unknown, Fintype.card_fun]
example : partialCoordinateCollision unknown false false true = 1 / 2 := by
  norm_num [partialCoordinateCollision, partialCollision, unknown]

-- Shared variable: only the factor equality is random. Naive independent incidence
-- sampling would incorrectly give 1/16.
example : partialIncidenceCollision unknown unknown false false false true = 1 / 4 := by
  norm_num [partialIncidenceCollision, partialCollision, unknown, Fintype.card_fun]
example : partialIncidenceCollision unknown unknown false false false true ≠ 1 / 16 := by
  norm_num [partialIncidenceCollision, partialCollision, unknown, Fintype.card_fun]
example : partialIncidenceCollision unknown unknown false true false true = 1 / 16 := by
  norm_num [partialIncidenceCollision, partialCollision, unknown, Fintype.card_fun]

-- Overwriting an already assigned index is not an admissible conditional-expectation step.
example : (𝔼 x : Bool, partialCollision
    (Function.update (fun _ : Bool => some false) false (some x)) false true) = 1 / 2 := by
  norm_num [partialCollision, Function.update, Finset.expect, NNRat.smul_def]
example : partialCollision (fun _ : Bool => some false) false true ≠ (1 / 2 : ℚ) := by
  norm_num [partialCollision]

-- No queries exist in an empty index type; completing that empty function changes nothing.
example (filler : Fin 0 → Bool) : completeLabels (fun _ => none) filler = filler := by
  funext i
  exact Fin.elim0 i

private def edge (v : Bool) : Unit × Bool := ((), v)
private def zeroWord : Word := fun _ => false
private def oneWord : Word := fun _ => true
private def initialVariables (v : Bool) : Option Word := if v then none else some zeroWord
private def initialFactors : Unit → Option Word := fun _ => none
private def candidates : List Word := [zeroWord, id, Bool.not, oneWord]

-- A real two-incidence score: one factor reads two original variables.
example : normalizedPartialScore edge initialVariables initialFactors 2 = 17 / 16 := by
  norm_num [normalizedPartialScore, partialIncidencePotential, partialIncidenceCollision,
    partialGroupPotential, partialCoordinateCollision, partialCollision, edge, initialVariables,
    initialFactors, zeroWord, Fintype.card_fun]

-- The actual computable selector chooses a complementary whole word, balancing both points.
private theorem selected_complement :
    (bestVariableLabel edge initialVariables initialFactors 2 true candidates).map
    (fun word => (word false, word true)) = some (true, true) := by
  norm_num [bestVariableLabel, candidates, List.argmin_cons, normalizedPartialScore,
    partialIncidencePotential, partialIncidenceCollision, partialGroupPotential,
    partialCoordinateCollision, partialCollision, edge, initialVariables, initialFactors,
    zeroWord, oneWord, Function.update, Fintype.card_fun, funext_iff]

-- Empty candidate input is reported rather than silently inventing a label.
example : bestVariableLabel edge initialVariables initialFactors 2 true [] = none := by
  simp only [bestVariableLabel, List.argmin_nil]

-- The concrete candidate table is exhaustive for whole two-bit words.
example : ∀ word : Word, word ∈ candidates := by
  intro word
  cases h0 : word false <;> cases h1 : word true <;>
    simp [candidates, funext_iff, zeroWord, oneWord, h0, h1]

-- Dropping exhaustive enumeration can really increase the normalized score: 31/16 > 17/16.
example : (bestVariableLabel edge initialVariables initialFactors 2 true [zeroWord]).map
    (fun word => normalizedPartialScore edge
      (Function.update initialVariables true (some word)) initialFactors 2) =
        some (31 / 16 : ℚ) := by
  simp only [bestVariableLabel, List.argmin_singleton, Option.map_some]
  norm_num [normalizedPartialScore, partialIncidencePotential, partialIncidenceCollision,
    partialGroupPotential, partialCoordinateCollision, partialCollision, edge, initialVariables,
    initialFactors, zeroWord, Function.update, Fintype.card_fun]

-- Factor selection changes no variable groups. Ties among three unequal factor words
-- are resolved by the supplied list order, so the first mixed word is chosen.
example : (bestFactorLabel (fun f : Bool => (f, ())) (fun _ : Unit => some zeroWord)
    initialVariables 2 true candidates).map (fun word => (word false, word true)) =
      some (false, true) := by
  norm_num [bestFactorLabel, candidates, List.argmin_cons, normalizedPartialScore,
    partialIncidencePotential, partialIncidenceCollision, partialGroupPotential,
    partialCoordinateCollision, partialCollision, initialVariables,
    zeroWord, oneWord, Function.update, Fintype.card_fun, funext_iff]

end Cslib.Tests.PartialLabelScores
