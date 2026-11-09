/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.ImmermanVardi
import Complexity.Computability.Complexity.Fagin.Verifier

/-! # Native polynomial-time queries produce uniform checked FO(LFP) sentences -/

namespace ComplexityTests.ImmermanVardi

open FirstOrder Language Turing Turing.MultiTapeTM
open Cslib.Logic Cslib.Logic.FO Cslib.Complexity

section Queries

variable {L : Language} [L.IsRelational] (v : Vocabulary L)

-- The public characterization uses the existing source encoding and native machine class.
example (K : Ordered.Query L) :
    Ordered.LFPDefinable K ↔ Ordered.Query.encodedLanguage K v ∈ P encStructure :=
  Ordered.lfpDefinable_iff_encodedLanguage_mem_P v K

-- Start from a native constant decider, then obtain one sentence rejecting every ordered input.
example : ∃ φ : LFP.Formula (Ordered.language L) [] Empty,
    ∀ M : Ordered.Structure L, ¬ φ.Realize (M := M) Operator.RelEnv.empty Empty.elim := by
  have hP : Ordered.Query.encodedLanguage (∅ : Ordered.Query L) v ∈ P encStructure := by
    refine ⟨fun _ => false, ComputableInPolyTime.const false, ?_⟩
    intro a
    simp [Ordered.Query.encodedLanguage]
  obtain ⟨φ, hφ⟩ := Ordered.LFPDefinable.of_encodedLanguage_mem_P v hP
  exact ⟨φ, fun M h => (hφ M).mpr h⟩

-- Accepting every ordered structure still requires rejecting malformed encodings and n < 2.
-- The native guard is certified directly, before applying the machine-to-LFP direction.
example : ∃ φ : LFP.Formula (Ordered.language L) [] Empty,
    ∀ M : Ordered.Structure L, φ.Realize (M := M) Operator.RelEnv.empty Empty.elim := by
  have hP : Ordered.Query.encodedLanguage (Set.univ : Ordered.Query L) v ∈ P encStructure := by
    refine ⟨fun a => v.checkShape a && decide (2 ≤ a.1), ?_, ?_⟩
    · fun_prop
    · intro a
      simp [Ordered.Query.encodedLanguage, Vocabulary.checkShape_eq_true_iff]
  obtain ⟨φ, hφ⟩ := Ordered.LFPDefinable.of_encodedLanguage_mem_P v hP
  exact ⟨φ, fun M => (hφ M).mp (Set.mem_univ M)⟩

end Queries

private def vocabulary : Vocabulary Language.empty where
  count := 0
  symbol := Equiv.equivOfIsEmpty _ _

private def input : EncodedStructure := (2, [])

private theorem wellFormed : vocabulary.WellFormed input := by decide +kernel

private instance : Fact (2 ≤ 8) := ⟨by decide⟩

private instance : vocabulary.powerLanguage.Structure (Fin 8) :=
  vocabulary.powerStructure input 8

-- The word is [true,true,true,true,false]: native input position one reads its first bit.
example : (vocabulary.inputSymbol none).Realize ![(0 : Fin 8)] ∧
    (vocabulary.inputSymbol (some true)).Realize ![(1 : Fin 8)] ∧
    (vocabulary.inputSymbol (some false)).Realize ![(5 : Fin 8)] := by
  rw [vocabulary.realize_inputSymbol wellFormed (by decide),
    vocabulary.realize_inputSymbol wellFormed (by decide),
    vocabulary.realize_inputSymbol wellFormed (by decide)]
  decide

-- The right endmarker and padding are blank; the final false data bit is not blank.
example : (vocabulary.inputSymbol none).Realize ![(6 : Fin 8)] ∧
    (vocabulary.inputSymbol none).Realize ![(7 : Fin 8)] ∧
    ¬ (vocabulary.inputSymbol none).Realize ![(5 : Fin 8)] := by
  rw [vocabulary.realize_inputSymbol wellFormed (by decide),
    vocabulary.realize_inputSymbol wellFormed (by decide),
    vocabulary.realize_inputSymbol wellFormed (by decide)]
  decide

-- Neither endmarker is misclassified as a data bit.
example : ¬ (vocabulary.inputSymbol (some true)).Realize ![(0 : Fin 8)] ∧
    ¬ (vocabulary.inputSymbol (some false)).Realize ![(6 : Fin 8)] := by
  rw [vocabulary.realize_inputSymbol wellFormed (by decide),
    vocabulary.realize_inputSymbol wellFormed (by decide)]
  decide

end ComplexityTests.ImmermanVardi
