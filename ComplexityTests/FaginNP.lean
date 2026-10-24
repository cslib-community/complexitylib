/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Fagin.Verifier
import Complexity.Logics.SecondOrder.Coloring
import ComplexityTests.FaginEncoding

/-!
# Tests: existential second-order definable classes are in NP

A concrete sentence, `∃ U, ∀ x, U x` over graphs with a unary relation variable `U`, has a
computable verifier once a layout is fixed: the tests run it on the edge with an accepting
certificate of exactly the prescribed length, a rejecting certificate, and a malformed input.
Colorability, through `Cslib.Logic.ESO.Definable.colorable`, gives the headline membership in
`NP` a nonvacuous client, and the axiom checks record the dependencies of the main results.
-/

namespace ComplexityTests.FaginNP

open FirstOrder Language Structure CategoryTheory Cslib.Logic Cslib.Logic.ESO Cslib.Complexity
open Turing.MultiTapeTM
open ComplexityTests.FaginEncoding

/-- The sentence `∃ U, ∀ x, U x` with one unary relation variable. -/
def allMarked : ESO.Sentence Language.graph :=
  ⟨Fin 1, fun _ => 1, ∀' (Relations.boundedFormula₁ (Sum.inr ⟨0, rfl⟩) &0)⟩

/-- Its layout: one block, degree one, so a certificate for an input of encoded length `N` has
`N` bits, the first `n` being the truth table of `U`. -/
def allMarkedLayout : allMarked.Layout where
  blocks := 1
  block := (Equiv.refl _).toEmbedding
  degree := 1
  arity_le _ := le_rfl

/-- The encoded length of the edge. -/
example : (encStructure edge).length = 14 := by decide +kernel

/-- The verifier accepts the edge with the all-ones certificate of the prescribed length. -/
example : ∃ w : List Bool, w.length = allMarkedLayout.polynomial.eval (encStructure edge).length ∧
    allMarkedLayout.verifier graphVocabulary (edge, w) = true :=
  ⟨List.replicate 14 true, by rw [Sentence.Layout.eval_polynomial]; decide, by decide +kernel⟩

/-- It rejects a certificate marking only the first vertex. -/
example :
    allMarkedLayout.verifier graphVocabulary (edge, true :: List.replicate 13 false) = false := by
  decide

/-- It rejects the malformed input with a short table, whatever the certificate. -/
example :
    allMarkedLayout.verifier graphVocabulary ((2, [ [true] ]), List.replicate 14 true) = false := by
  decide

/-- The accepted certificates read as relations satisfying the first-order part. -/
example : (letI := graphVocabulary.decode edge; allMarked.Realize (Fin edge.1)) :=
  (allMarkedLayout.realize_iff_exists_certificate (v := graphVocabulary)
    (card_le_length_encStructure edge)
    (by decide +kernel)).2 ⟨List.replicate 14 true, by decide +kernel, by decide +kernel⟩

/-- The sentence holds in the empty structure, whose encoded length is two, with a certificate of
two unused bits. -/
example : ∃ w : List Bool,
    w.length = allMarkedLayout.polynomial.eval (encStructure (0, [ [] ])).length ∧
      allMarkedLayout.verifier graphVocabulary ((0, [ [] ]), w) = true :=
  ⟨List.replicate 2 false, by rw [Sentence.Layout.eval_polynomial]; decide, by decide +kernel⟩

/-! ### Membership in NP -/

/-- The problem of `allMarked` is in `NP`. -/
example : graphVocabulary.queryLanguage
    {M : Bundled Language.graph.Structure | allMarked.Realize M} ∈ NP encStructure :=
  allMarked.queryLanguage_mem_NP graphVocabulary

/-- **Colorability is in NP**: the inputs encoding `n`-colorable finite directed graphs. -/
theorem colorable_mem_NP (n : ℕ) :
    graphVocabulary.queryLanguage
      {M | ∃ f : M → Fin n, ∀ x y, RelMap adj ![x, y] → f x ≠ f y} ∈ NP encStructure :=
  (Definable.colorable n).queryLanguage_mem_NP graphVocabulary

/-- **Colorability of simple graphs is in NP.** -/
theorem colorable_simpleGraph_mem_NP (n : ℕ) :
    graphVocabulary.queryLanguage {M | M ⊨ Theory.simpleGraph ∧
      ∃ f : M → Fin n, ∀ x y, RelMap adj ![x, y] → f x ≠ f y} ∈ NP encStructure :=
  (Definable.colorable_simpleGraph n).queryLanguage_mem_NP graphVocabulary

/-- The query language of three-colorability contains the encoding of every three-colorable
simple graph, along any numbering. -/
example {V : Type} (G : SimpleGraph V) (hG : G.Colorable 3) {m : ℕ} (e : V ≃ Fin m) :
    (letI := G.structure; graphVocabulary.encode V e) ∈ graphVocabulary.queryLanguage
      {M | M ⊨ Theory.simpleGraph ∧ ∃ f : M → Fin 3, ∀ x y, RelMap adj ![x, y] → f x ≠ f y} := by
  let _ := G.structure
  rw [Vocabulary.mem_queryLanguage_encode (Definable.colorable_simpleGraph 3).isoClosed]
  obtain ⟨C⟩ := hG
  exact ⟨inferInstance, C, fun x y h => C.valid h⟩

/-! ### Axioms -/

/--
info: 'Cslib.Logic.ESO.Definable.queryLanguage_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.queryLanguage_mem_NP

/--
info: 'Cslib.Logic.ESO.Sentence.queryLanguage_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Sentence.queryLanguage_mem_NP

/--
info: 'Cslib.Logic.ESO.Sentence.Layout.computableInPolyTime_verifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Sentence.Layout.computableInPolyTime_verifier

/--
info: 'Cslib.Logic.Vocabulary.mem_queryLanguage_encode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.Vocabulary.mem_queryLanguage_encode

/--
info: 'Cslib.Logic.Vocabulary.wellFormed_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.Vocabulary.wellFormed_iff

end ComplexityTests.FaginNP
