/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Fagin.Witness
import ComplexityTests.FaginEncoding

/-!
# Tests for materialized existential relation witnesses

A mixed unary/binary/nullary family checks block selection, tuple orientation, source table
preservation and exact encoded lengths. Its layout deliberately leaves a block unused. The
tests also cover empty families, short and excessive certificates, and malformed source inputs.
-/

namespace ComplexityTests.FaginWitness

open FirstOrder Language Cslib.Logic Cslib.Logic.ESO
open ComplexityTests.FaginEncoding

/-- No input relation tables are present, so the universe size alone determines input length. -/
private def emptyVocabulary : Vocabulary Language.empty where
  count := 0
  symbol := Equiv.equivOfIsEmpty _ _

/-- Three witness variables, respectively unary, binary, and nullary. -/
private abbrev mixed : ESO.Sentence Language.empty :=
  ⟨Fin 3, ![1, 2, 0], ⊤⟩

/-- Block zero is unused; the three variables occupy blocks one, two, and three. -/
private def mixedLayout : mixed.Layout where
  blocks := 4
  block := ⟨Fin.succ, Fin.succ_injective 3⟩
  degree := 2
  arity_le i := by fin_cases i <;> decide

private abbrev mixedVocabulary :=
  varLanguage.vocabulary mixed.arity (Equiv.refl (Fin 3))

private abbrev expandedVocabulary := emptyVocabulary.sum mixedVocabulary

/-- At universe size two and input length five, the block width is twenty-five. The unary
relation contains zero, the binary relation contains only `(1, 0)`, and the nullary relation
is true. -/
private def certificate : List Bool :=
  (List.range 100).map fun j => decide (j = 25 ∨ j = 51 ∨ j = 75)

/-- The certificate has exactly the layout's prescribed length. -/
example : (encStructure (2, [])).length = 5 ∧
    certificate.length = mixedLayout.polynomial.eval (encStructure (2, [])).length := by
  rw [Sentence.Layout.eval_polynomial]
  decide +kernel

/-- Concrete materialization retains relation order and each declared arity. -/
example : mixedLayout.witnessInput (Equiv.refl _) ((2, []), certificate) =
    (2, [ [true, false], [false, true, false, false], [true] ]) := by
  decide +kernel

example : expandedVocabulary.WellFormed
    (mixedLayout.witnessInput (Equiv.refl _) ((2, []), certificate)) := by
  rw [Sentence.Layout.wellFormed_witnessInput_iff]
  decide +kernel

/-- The first tuple coordinate is the least significant radix digit: `(1, 0)` is true,
whereas `(0, 1)` is false. -/
example :
    (expandedVocabulary.decode
      (mixedLayout.witnessInput (Equiv.refl _) ((2, []), certificate))).RelMap
      (Sum.inr ⟨1, rfl⟩) ![(1 : Fin 2), (0 : Fin 2)] ∧
    ¬ (expandedVocabulary.decode
      (mixedLayout.witnessInput (Equiv.refl _) ((2, []), certificate))).RelMap
      (Sum.inr ⟨1, rfl⟩) ![(0 : Fin 2), (1 : Fin 2)] := by
  change _ = true ∧ ¬ _ = true
  decide +kernel

/-- The nullary relation is a single truth value, independent of any argument. -/
example : (expandedVocabulary.decode
    (mixedLayout.witnessInput (Equiv.refl _) ((2, []), certificate))).RelMap
      (Sum.inr ⟨2, rfl⟩) ![] := by
  change _ = true
  decide +kernel

/-- Reordering the variable enumeration reorders tables while retaining their relation meanings. -/
example : mixedLayout.witnessInput (Equiv.swap (0 : Fin 3) 2) ((2, []), certificate) =
    (2, [ [true], [false, true, false, false], [true, false] ]) := by
  decide +kernel

/-- Changing every bit of the unused block has no effect on the materialized relations. -/
example : mixedLayout.witnessInput (Equiv.refl _)
    ((2, []), List.replicate 25 true ++ certificate.drop 25) =
    mixedLayout.witnessInput (Equiv.refl _) ((2, []), certificate) := by
  decide +kernel

/-- A short word supplies false for absent positions, even though the tables retain full size. -/
example : mixedLayout.witnessInput (Equiv.refl _)
    ((2, []), List.replicate 25 false ++ [true]) =
    (2, [ [true, false], [false, false, false, false], [false] ]) := by
  decide +kernel

/-- Additional bits outside all queried positions are ignored by the total materializer. -/
example : mixedLayout.witnessInput (Equiv.refl _) ((2, []), certificate ++ [true, true]) =
    mixedLayout.witnessInput (Equiv.refl _) ((2, []), certificate) := by
  decide +kernel

/-- In an empty universe, positive-arity tables are empty but a nullary table still has one bit.
The materializer itself is independent of the ordered query's separate `n ≥ 2` restriction. -/
example : mixedLayout.witnessInput (Equiv.refl _) ((0, []), [false, false, false, true]) =
    (0, [ [], [], [true] ]) := by
  decide +kernel

/-- Existing source relations stay in front of the guessed tables. A missing certificate has
all-false witness relations. -/
example : mixedLayout.witnessInput (Equiv.refl _) (edge, []) =
    (2, [ [false, true, true, false], [false, false], [false, false, false, false], [false] ]) := by
  decide +kernel

private abbrev graphExpandedVocabulary := graphVocabulary.sum mixedVocabulary

/-- Source adjacency survives decoding the enlarged structure. -/
example :
    (graphExpandedVocabulary.decode (mixedLayout.witnessInput (Equiv.refl _) (edge, []))).RelMap
      (Sum.inl adj) ![(0 : Fin 2), (1 : Fin 2)] ∧
    ¬ (graphExpandedVocabulary.decode (mixedLayout.witnessInput (Equiv.refl _) (edge, []))).RelMap
      (Sum.inl adj) ![(0 : Fin 2), (0 : Fin 2)] := by
  change _ = true ∧ ¬ _ = true
  decide +kernel

/-- Appending witnesses cannot repair missing source tables, for any certificate. -/
example (w : List Bool) : ¬ graphExpandedVocabulary.WellFormed
    (mixedLayout.witnessInput (Equiv.refl _) ((2, []), w)) := by
  rw [Sentence.Layout.wellFormed_witnessInput_iff]
  decide +kernel

/-- Extra source tables remain invalid. -/
example (w : List Bool) : ¬ graphExpandedVocabulary.WellFormed
    (mixedLayout.witnessInput (Equiv.refl _) ((2, [ [false, true, true, false], [] ]), w)) := by
  rw [Sentence.Layout.wellFormed_witnessInput_iff]
  decide +kernel

/-- A source relation with the wrong number of entries remains invalid. -/
example (w : List Bool) : ¬ graphExpandedVocabulary.WellFormed
    (mixedLayout.witnessInput (Equiv.refl _) ((2, [ [false, true, true] ]), w)) := by
  rw [Sentence.Layout.wellFormed_witnessInput_iff]
  decide +kernel

/-- Exact lengths include the frame around each materialized table. -/
example :
    (encStructure (mixedLayout.witnessInput (Equiv.refl _) ((2, []), certificate))).length = 22 ∧
    (encStructure (mixedLayout.witnessInput (Equiv.refl _) (edge, []))).length = 31 := by
  decide +kernel

/-- A family with no relation variables needs no blocks. -/
private abbrev noWitness : ESO.Sentence Language.graph :=
  ⟨Fin 0, fun _ => 0, ⊤⟩

private def noWitnessLayout : noWitness.Layout where
  blocks := 0
  block := (Equiv.refl _).toEmbedding
  degree := 0
  arity_le _ := le_rfl

/-- The empty family neither reads the certificate nor adds relation tables. -/
example : noWitnessLayout.witnessInput (Equiv.refl _) (edge, [true, false]) = edge ∧
    noWitnessLayout.witnessInput (Equiv.refl _) ((2, []), [true]) = (2, []) ∧
    noWitnessLayout.polynomial.eval 14 = 0 := by
  rw [Sentence.Layout.eval_polynomial]
  decide +kernel

end ComplexityTests.FaginWitness
