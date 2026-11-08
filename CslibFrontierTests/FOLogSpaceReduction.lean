/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Reduction
import CslibFrontierTests.FOLogSpace

/-!
# Tests: order-free interpretations as logarithmic-space transducers

The total transducer applies to interpretations with a genuinely empty domain, and to dimension
zero, including on an empty input universe. Nullary output relations still have one-bit truth
tables in both cases. Malformed inputs produce malformed outputs. A restricted two-dimensional
interpretation has two output elements and a binary relation;
its two ranks and full output are checked explicitly. Definable graph queries instantiate the
reduction theorem and both class-closure corollaries.
-/

namespace ComplexityTests.FOLogSpaceReduction

open FirstOrder Language Structure CategoryTheory Cslib.Logic Cslib.Complexity
open FO FO.Interpretation ComplexityTests.FaginEncoding ComplexityTests.FOLogSpace

/-- An interpretation with no elements but a true nullary relation. -/
def emptyDomain : Interpretation Language.graph nullaryLanguage (Fin 1) where
  domain := ⊥
  rel _ := ⊤

/-- A zero-dimensional interpretation with one element and a false nullary relation. -/
def zeroDimension : Interpretation Language.graph nullaryLanguage (Fin 0) where
  domain := ⊤
  rel _ := ⊥

example : Turing.MultiTapeTM.ComputableInLogSpace
    (emptyDomain.encodedMap graphVocabulary nullaryVocabulary (Equiv.refl _))
    encStructure encStructure :=
  emptyDomain.computableInLogSpace_encodedMap graphVocabulary nullaryVocabulary (Equiv.refl _)

example : Turing.MultiTapeTM.ComputableInLogSpace
    (zeroDimension.encodedMap graphVocabulary nullaryVocabulary (Equiv.refl _))
    encStructure encStructure :=
  zeroDimension.computableInLogSpace_encodedMap graphVocabulary nullaryVocabulary (Equiv.refl _)

/-- The domain filter can discard every element of a nonempty input. The nullary relation's
one-bit table survives. -/
example : emptyDomain.encodedMap graphVocabulary nullaryVocabulary (Equiv.refl _) edge =
    (0, [ [true] ]) := by
  classical
  have ha : graphVocabulary.WellFormed edge := by decide +kernel
  rw [encodedMap_of_wellFormed _ _ _ _ ha]
  let _ := graphVocabulary.decode edge
  apply Prod.ext
  · change modelCard emptyDomain (Equiv.refl _) edge.1 = 0
    rw [modelCard, domainRank, Nat.count_eq_card_filter_range]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro u _
    rintro ⟨_, hd⟩
    exact hd
  · simp only [Vocabulary.encode, nullaryVocabulary, List.ofFn_succ, List.ofFn_zero]
    simp only [Vocabulary.relTable]
    simp only [FO.Interpretation.relMap_model]
    simp only [emptyDomain, Formula.Realize, BoundedFormula.realize_top, decide_true,
      List.ofFn_const]
    rfl

/-- A dimension-zero interpretation produces one element even on the empty input universe;
the false nullary relation is encoded by a one-bit false table. -/
example : zeroDimension.encodedMap graphVocabulary nullaryVocabulary (Equiv.refl _)
    (0, [ [] ]) = (1, [ [false] ]) := by
  classical
  have ha : graphVocabulary.WellFormed (0, [ [] ]) := by decide +kernel
  rw [encodedMap_of_wellFormed _ _ _ _ ha]
  let _ := graphVocabulary.decode (0, [ [] ])
  apply Prod.ext
  · change modelCard zeroDimension (Equiv.refl _) 0 = 1
    simp only [modelCard, domainRank, pow_zero, Nat.count_one]
    have h : zeroDimension.InDomain (Equiv.refl _) 0 0 :=
      ⟨by decide, by simp [zeroDimension, Formula.Realize]⟩
    rw [ite_eq_left h]
  · simp only [Vocabulary.encode, nullaryVocabulary, List.ofFn_succ, List.ofFn_zero]
    simp only [Vocabulary.relTable]
    simp only [FO.Interpretation.relMap_model]
    simp only [zeroDimension, Formula.Realize, BoundedFormula.realize_bot, decide_false,
      List.ofFn_const]
    rfl

/-- A malformed input cannot accidentally become a valid target instance. -/
example : ¬ nullaryVocabulary.WellFormed
    (zeroDimension.encodedMap graphVocabulary nullaryVocabulary (Equiv.refl _) (0, [])) := by
  have ha : ¬ graphVocabulary.WellFormed (0, []) := by decide +kernel
  rw [encodedMap_of_not_wellFormed _ _ _ _ ha]
  simp [Vocabulary.WellFormed]

private theorem loopClass_isoClosed :
    IsoClosed {M : Bundled Language.graph.Structure | M ⊨ hasLoop} :=
  (show Definable {M | M ⊨ hasLoop} from ⟨hasLoop, fun _ _ => Iff.rfl⟩).isoClosed

/-- The class has both positive and negative instances, as checked in `FOLogSpace`. -/
example : LogSpaceReducible encStructure encStructure
    (graphVocabulary.queryLanguage {M | M ⊨ hasLoop})
    (graphVocabulary.queryLanguage {M | M ⊨ hasLoop}) :=
  (Reduces.refl loopClass_isoClosed).logSpaceReducible graphVocabulary graphVocabulary
    loopClass_isoClosed

example : graphVocabulary.queryLanguage {M | M ⊨ hasLoop} ∈ L encStructure :=
  (Reduces.refl loopClass_isoClosed).queryLanguage_mem_L graphVocabulary graphVocabulary
    loopClass_isoClosed (graphVocabulary.queryLanguage_mem_L hasLoop)

example : graphVocabulary.queryLanguage {M | M ⊨ hasLoop} ∈ P encStructure :=
  (Reduces.refl loopClass_isoClosed).queryLanguage_mem_P graphVocabulary graphVocabulary
    loopClass_isoClosed (L_subset_P (graphVocabulary.queryLanguage_mem_L hasLoop))

/-! ### A restricted two-dimensional interpretation -/

/-- Distinct ordered pairs form the domain. Two pairs are related when their first coordinates
are equal. On a two-element input this yields two looped, mutually unrelated output vertices. -/
def distinctPairs : Interpretation Language.graph Language.graph (Fin 2) where
  domain := ∼(varEq 0 1)
  rel
    | .adj => varEq (0, 0) (1, 0)

section DistinctPairs

local instance : Language.graph.Structure (Fin 2) := graphVocabulary.decode edge

private theorem distinctPairs_inDomain (u : ℕ) :
    distinctPairs.InDomain (Equiv.refl _) 2 u ↔ u = 1 ∨ u = 2 := by
  by_cases hu : u < 4
  · interval_cases u <;>
      simp only [FO.Interpretation.InDomain, distinctPairs, Formula.realize_not, realize_varEq]
      <;> decide +kernel
  · constructor
    · rintro ⟨h, _⟩
      exact (hu h).elim
    · omega

private theorem distinctPairs_rank (u : ℕ) :
    distinctPairs.domainRank (Equiv.refl _) 2 u = Nat.count (fun k => k = 1 ∨ k = 2) u := by
  classical
  unfold domainRank
  congr 1
  funext k
  exact propext (distinctPairs_inDomain k)

private theorem distinctPairs_card : distinctPairs.modelCard (Equiv.refl _) 2 = 2 := by
  rw [modelCard, distinctPairs_rank]
  decide +kernel

/-- Rank zero is tuple `(1, 0)`: tuple index zero is outside the domain. -/
example : (rankEquiv distinctPairs (Equiv.refl _) 2
    ⟨![1, 0], by change (1 : Fin 2) ≠ 0; decide +kernel⟩).val = 0 := by
  change distinctPairs.domainRank (Equiv.refl _) 2 (tupleEquiv (Equiv.refl _) ![1, 0]).val = 0
  rw [distinctPairs_rank, tupleEquiv_apply_val, tupleIndex_apply]
  decide +kernel

/-- Rank one is tuple `(0, 1)`: tuple indices one and two occur in that order. -/
example : (rankEquiv distinctPairs (Equiv.refl _) 2
    ⟨![0, 1], by change (0 : Fin 2) ≠ 1; decide +kernel⟩).val = 1 := by
  change distinctPairs.domainRank (Equiv.refl _) 2 (tupleEquiv (Equiv.refl _) ![0, 1]).val = 1
  rw [distinctPairs_rank, tupleEquiv_apply_val, tupleIndex_apply]
  decide +kernel

private theorem distinctPairs_rel (t : Fin 2 → distinctPairs.Model (Fin 2)) :
    RelMap adj t ↔ t 0 = t 1 := by
  change (t 0).1 0 = (t 1).1 0 ↔ t 0 = t 1
  constructor
  · intro h
    apply Model.ext
    funext i
    fin_cases i
    · exact h
    · apply Fin.ext
      change ((t 0).1 1).val = ((t 1).1 1).val
      have hx : (t 0).1 0 ≠ (t 0).1 1 := (t 0).2
      have hy : (t 1).1 0 ≠ (t 1).1 1 := (t 1).2
      simp only [ne_eq, Fin.ext_iff] at hx hy h
      have h00 := ((t 0).1 0).isLt
      have h01 := ((t 0).1 1).isLt
      have h10 := ((t 1).1 0).isLt
      have h11 := ((t 1).1 1).isLt
      omega
  · intro h
    rw [h]

/-- This executes the public encoded map with a restricted domain of dimension two, ranks
skipping both diagonal tuples, and a positive-arity relation on two output elements. -/
example : distinctPairs.encodedMap graphVocabulary graphVocabulary (Equiv.refl _) edge =
    (2, [ [true, false, false, true] ]) := by
  classical
  have ha : graphVocabulary.WellFormed edge := by decide +kernel
  rw [encodedMap_of_wellFormed _ _ _ _ ha]
  apply Prod.ext
  · exact distinctPairs_card
  · simp only [Vocabulary.encode, graphVocabulary_count, List.ofFn_succ, List.ofFn_zero]
    congr 1
    change Vocabulary.relTable (distinctPairs.Model (Fin 2))
      (rankEquiv distinctPairs (Equiv.refl _) 2) ⟨2, adj⟩ = [true, false, false, true]
    simp only [Vocabulary.relTable, distinctPairs_rel, Function.comp_apply,
      Equiv.apply_eq_iff_eq, Fin.ext_iff, finFunctionFinEquiv_symm_apply_val]
    simp only [distinctPairs_card]
    decide +kernel

/-- The reduction theorem also applies to this non-identity, restricted-domain interpretation. -/
example : LogSpaceReducible encStructure encStructure
    (graphVocabulary.queryLanguage {M | M ⊨ distinctPairs.onSentence hasLoop})
    (graphVocabulary.queryLanguage {M | M ⊨ hasLoop}) :=
  (Reduces.of_interpretation distinctPairs fun M _ =>
    distinctPairs.realize_onSentence M hasLoop).logSpaceReducible
      graphVocabulary graphVocabulary loopClass_isoClosed

end DistinctPairs

end ComplexityTests.FOLogSpaceReduction
