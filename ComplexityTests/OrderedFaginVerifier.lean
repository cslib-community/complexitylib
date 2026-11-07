/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Fagin.Ordered.Verifier
import ComplexityTests.OrderedFagin

/-!
# Ordered ESO verifier regression tests

Existential colorings exercise source relations and canonical constants together. A second
sentence forces its unary witness to agree with canonical BIT under a quantifier. Concrete
positive and negative instances test the ordered semantics, while the new characterization
supplies native NP membership without any verifier or complexity assumption.
-/

namespace ComplexityTests.OrderedFaginVerifier

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered
open Cslib.Complexity Turing.MultiTapeTM
open ComplexityTests.OrderedFagin (graphVocabulary oneEdge)

/-- The new forward direction accepts the existing query whose truth changes under a swap of
the two input vertices, so it requires no invariance under unordered input isomorphisms. -/
example : ComplexityTests.OrderedFagin.edgeZeroMaxQuery.encodedLanguage graphVocabulary ∈
    NP encStructure :=
  ESODefinable.encodedLanguage_mem_NP graphVocabulary
    (show Ordered.Definable ComplexityTests.OrderedFagin.edgeZeroMaxQuery from
      ⟨ComplexityTests.OrderedFagin.edgeZeroMax, fun _ => Iff.rfl⟩).esoDefinable

private abbrev witnessLanguage (L : Language) :=
  (language L).sum (ESO.varLanguage fun _ : Fin 1 => 1)

private def marked {L : Language} {k : ℕ}
    (t : (witnessLanguage L).Term (Empty ⊕ Fin k)) :
    (witnessLanguage L).BoundedFormula Empty k :=
  Relations.boundedFormula₁ (Sum.inr ⟨0, rfl⟩) t

private def numeric {L : Language} {k : ℕ} (c : NumericFunction 0) :
    (witnessLanguage L).Term (Empty ⊕ Fin k) :=
  .func (Sum.inl (Sum.inr c)) Fin.elim0

/-- The two sides of a coloring are distinguished by canonical zero and maximum. -/
private abbrev coloring : ESO.Sentence (language Language.graph) where
  Var := Fin 1
  arity _ := 1
  matrix := marked (numeric .zero) ⊓
    ((marked (numeric .max)).not ⊓
      ((Relations.boundedFormula₂ (Sum.inl (Sum.inl adj)) (.var (.inr 0)) (.var (.inr 1))).imp
        ((marked (.var (.inr 0))).iff ((marked (.var (.inr 1))).not))).all.all)

private def coloringQuery : Query Language.graph := {M | coloring.Realize M}

/-- One self-loop forces the same vertex to have opposite colors. -/
private def loop : Ordered.Structure Language.graph where
  size := 2
  size_ge_two := le_refl _
  input.RelMap
    | .adj, xs => xs 0 = 0 ∧ xs 1 = 0

private theorem coloring_forward : coloring.Realize (oneEdge true) := by
  let _ : Fact (2 ≤ 2) := ⟨by decide⟩
  let _ : Language.graph.Structure (Fin 2) := (oneEdge true).input
  let R : Fin 1 → Set (Fin 1 → Fin 2) := fun _ => {xs | xs 0 = 0}
  refine ⟨R, ?_⟩
  let _ := ESO.varLanguage.structure (arity := fun _ : Fin 1 => 1) R
  change Fin 2 ⊨ coloring.matrix
  simp only [coloring, FirstOrder.Language.Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_iff]
  change (0 : Fin 2) = 0 ∧ (¬ (1 : Fin 2) = 0) ∧
    ∀ x y : Fin 2, (x = 0 ∧ y = 1) → (x = 0 ↔ ¬ y = 0)
  refine ⟨rfl, by decide, ?_⟩
  rintro x y ⟨rfl, rfl⟩
  decide

private theorem coloring_loop : ¬ coloring.Realize loop := by
  rintro ⟨R, hR⟩
  change Fin 1 → Set (Fin 1 → Fin 2) at R
  let _ : Fact (2 ≤ 2) := ⟨by decide⟩
  let _ : Language.graph.Structure (Fin 2) := loop.input
  let _ := ESO.varLanguage.structure (arity := fun _ : Fin 1 => 1) R
  change Fin 2 ⊨ coloring.matrix at hR
  simp only [coloring, FirstOrder.Language.Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_iff] at hR
  have hz := hR.1
  have he := hR.2.2 (0 : Fin 2) (0 : Fin 2)
  simp only [marked] at hz he
  erw [BoundedFormula.realize_rel₁] at hz
  erw [BoundedFormula.realize_rel₂, BoundedFormula.realize_rel₁,
    BoundedFormula.realize_rel₁] at he
  change ![(0 : Fin 2)] ∈ R 0 at hz
  change ((0 : Fin 2) = 0 ∧ (0 : Fin 2) = 0) →
    (![(0 : Fin 2)] ∈ R 0 ↔ ¬ ![(0 : Fin 2)] ∈ R 0) at he
  exact ((he ⟨rfl, rfl⟩).mp hz) hz

/-- These are actual source-only encodings of accepted and rejected ordered structures. -/
example : encode graphVocabulary (oneEdge true) ∈ coloringQuery.encodedLanguage graphVocabulary ∧
    encode graphVocabulary loop ∉ coloringQuery.encodedLanguage graphVocabulary := by
  simp only [mem_encodedLanguage_encode]
  exact ⟨coloring_forward, coloring_loop⟩

/-- The new direction certifies the query with genuine existential witnesses. -/
example : coloringQuery.encodedLanguage graphVocabulary ∈ NP encStructure :=
  ESODefinable.encodedLanguage_mem_NP graphVocabulary ⟨coloring, fun _ => Iff.rfl⟩

/-- Both directions of the characterization apply to the same concrete existential query. -/
example : ESODefinable coloringQuery :=
  (esoDefinable_iff_encodedLanguage_mem_NP graphVocabulary coloringQuery).mpr
    (coloring.ordered_queryLanguage_mem_NP graphVocabulary)

private def colorLayout : coloring.Layout where
  blocks := 1
  block := (Equiv.refl _).toEmbedding
  degree := 1
  arity_le _ := le_rfl

private def colorInput : EncodedStructure := (2, [ [false, false, true, false] ])
private def colorCertificate : List Bool := true :: List.replicate 13 false

/-- The witness layout checks the actual directed-edge encoding, with its original framing. -/
example : ∃ w : List Bool,
    w.length = colorLayout.polynomial.eval (encStructure colorInput).length ∧
    colorLayout.witnessInput (Equiv.refl _) (colorInput, w) ∈
      queryLanguage (graphVocabulary.sum
        (ESO.varLanguage.vocabulary coloring.arity (Equiv.refl _))) coloring.orderedMatrix := by
  refine ⟨colorCertificate, ?_, ?_⟩
  · rw [ESO.Sentence.Layout.eval_polynomial]
    decide +kernel
  · apply (colorLayout.mem_queryLanguage_witnessInput (Equiv.refl _) graphVocabulary _ _).mpr
    refine ⟨by decide, by decide, ?_⟩
    let _ : Fact (2 ≤ 2) := ⟨by decide⟩
    let _ : Language.graph.Structure (Fin 2) := graphVocabulary.decode colorInput
    let _ := ESO.varLanguage.structure (arity := fun _ : Fin 1 => 1)
      (colorLayout.certRel 2 (encStructure colorInput).length colorCertificate)
    change Fin 2 ⊨ coloring.matrix
    simp only [coloring, FirstOrder.Language.Sentence.Realize, Formula.Realize,
      BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_all,
      BoundedFormula.realize_imp, BoundedFormula.realize_iff]
    refine ⟨rfl, ?_, ?_⟩
    · change ¬ false = true
      decide
    · intro x y
      fin_cases x <;> fin_cases y <;>
        change (_ = true → (_ = true ↔ ¬ _ = true)) <;> decide +kernel

/-- The strict guard accepts the prescribed length even for an always-accepting inner checker. -/
example : strictVerifier encStructure colorLayout.polynomial (fun _ => true)
    (colorInput, colorCertificate) = true := by
  rw [strictVerifier_eq_true_iff, ESO.Sentence.Layout.eval_polynomial]
  decide +kernel

/-- Neither truncation nor padding can bypass the explicit length guard. -/
example : strictVerifier encStructure colorLayout.polynomial (fun _ => true)
      (colorInput, colorCertificate.drop 1) ≠ true ∧
    strictVerifier encStructure colorLayout.polynomial (fun _ => true)
      (colorInput, colorCertificate ++ [false]) ≠ true := by
  constructor
  · intro h
    have hlen := length_eq_of_strictVerifier_eq_true h
    rw [ESO.Sentence.Layout.eval_polynomial] at hlen
    change 13 = 14 at hlen
    omega
  · intro h
    have hlen := length_eq_of_strictVerifier_eq_true h
    rw [ESO.Sentence.Layout.eval_polynomial] at hlen
    change 15 = 14 at hlen
    omega

private def emptyVocabulary : Vocabulary Language.empty where
  count := 0
  symbol := Equiv.equivOfIsEmpty _ _

private def emptyInput (n : ℕ) (hn : 2 ≤ n) : Ordered.Structure Language.empty where
  size := n
  size_ge_two := hn
  input.funMap f := isEmptyElim f
  input.RelMap r := isEmptyElim r

/-- The witness must equal bit one everywhere, and contain the maximum element. -/
private abbrev bitWitness : ESO.Sentence (language Language.empty) where
  Var := Fin 1
  arity _ := 1
  matrix := ((marked (.var (.inr 0))).iff
    (Relations.boundedFormula₂ (Sum.inl (Sum.inr NumericRelation.bit))
      (.var (.inr 0)) (numeric .one))).all ⊓ marked (numeric .max)

private def bitQuery : Query Language.empty := {M | bitWitness.Realize M}

private theorem bitWitness_three : bitWitness.Realize (emptyInput 3 (by decide)) := by
  let _ : Fact (2 ≤ 3) := ⟨by decide⟩
  let _ : Language.empty.Structure (Fin 3) := (emptyInput 3 (by decide)).input
  let R : Fin 1 → Set (Fin 1 → Fin 3) := fun _ => {xs | (xs 0).val.testBit 1 = true}
  refine ⟨R, ?_⟩
  let _ := ESO.varLanguage.structure (arity := fun _ : Fin 1 => 1) R
  change Fin 3 ⊨ bitWitness.matrix
  simp only [bitWitness, FirstOrder.Language.Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_inf, BoundedFormula.realize_all, BoundedFormula.realize_iff]
  change (∀ x : Fin 3, (x.val.testBit 1 = true ↔ x.val.testBit 1 = true)) ∧
    (2 : ℕ).testBit 1 = true
  exact ⟨fun _ => Iff.rfl, by decide⟩

private theorem bitWitness_two : ¬ bitWitness.Realize (emptyInput 2 (by decide)) := by
  rintro ⟨R, hR⟩
  change Fin 1 → Set (Fin 1 → Fin 2) at R
  let _ : Fact (2 ≤ 2) := ⟨by decide⟩
  let _ : Language.empty.Structure (Fin 2) := (emptyInput 2 (by decide)).input
  let _ := ESO.varLanguage.structure (arity := fun _ : Fin 1 => 1) R
  change Fin 2 ⊨ bitWitness.matrix at hR
  simp only [bitWitness, FirstOrder.Language.Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_inf, BoundedFormula.realize_all, BoundedFormula.realize_iff] at hR
  have hmax := hR.2
  have hbit := hR.1 (1 : Fin 2)
  simp only [marked] at hmax hbit
  erw [BoundedFormula.realize_rel₁] at hmax
  erw [BoundedFormula.realize_rel₁, BoundedFormula.realize_rel₂] at hbit
  change ![(1 : Fin 2)] ∈ R 0 at hmax
  change ![(1 : Fin 2)] ∈ R 0 ↔ (1 : ℕ).testBit 1 = true at hbit
  exact (by decide : ¬ (1 : ℕ).testBit 1 = true) (hbit.mp hmax)

/-- Canonical BIT is computed from the size and indices; it is absent from the source tables. -/
example : encode emptyVocabulary (emptyInput 3 (by decide)) ∈
      bitQuery.encodedLanguage emptyVocabulary ∧
    encode emptyVocabulary (emptyInput 2 (by decide)) ∉
      bitQuery.encodedLanguage emptyVocabulary := by
  simp only [mem_encodedLanguage_encode]
  exact ⟨bitWitness_three, bitWitness_two⟩

example : bitQuery.encodedLanguage emptyVocabulary ∈ NP encStructure :=
  (esoDefinable_iff_encodedLanguage_mem_NP emptyVocabulary bitQuery).mp
    ⟨bitWitness, fun _ => Iff.rfl⟩

/-- An empty witness family and a true matrix do not waive source validity. -/
private def always : Query Language.graph :=
  {M | (ESO.Sentence.ofSentence (⊤ : (language Language.graph).Sentence)).Realize M}

example : always.encodedLanguage graphVocabulary ∈ NP encStructure :=
  (ESO.Sentence.ofSentence (⊤ : (language Language.graph).Sentence)).ordered_queryLanguage_mem_NP
    graphVocabulary

/-- Missing, extra, and incorrectly sized source tables are rejected even with a true matrix. -/
example : (2, []) ∉ always.encodedLanguage graphVocabulary ∧
    (2, [ [false, false, false, false], [] ]) ∉ always.encodedLanguage graphVocabulary ∧
    (2, [ [false] ]) ∉ always.encodedLanguage graphVocabulary :=
  ⟨Query.not_mem_encodedLanguage_of_not_wellFormed _ _ (by decide),
    Query.not_mem_encodedLanguage_of_not_wellFormed _ _ (by decide),
    Query.not_mem_encodedLanguage_of_not_wellFormed _ _ (by decide)⟩

/-- Correctly shaped universes below two remain outside the ordered convention. -/
example : (0, [ [] ]) ∉ always.encodedLanguage graphVocabulary ∧
    (1, [ [false] ]) ∉ always.encodedLanguage graphVocabulary :=
  ⟨Query.not_mem_encodedLanguage_of_lt_two _ _ (by decide),
    Query.not_mem_encodedLanguage_of_lt_two _ _ (by decide)⟩

end ComplexityTests.OrderedFaginVerifier
