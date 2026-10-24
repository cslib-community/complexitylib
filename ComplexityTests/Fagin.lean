/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Fagin.Converse
import ComplexityTests.FaginNP

/-!
# Tests: Fagin's theorem (`ESO.Definable K ↔ v.queryLanguage K ∈ NP encStructure`)

This test file exercises the converse direction of Fagin's theorem and the full equivalence:
* length-checked verifiers (`strictVerifier`),
* existential projection of relation variables and guessed strict linear orders, including the
  unfolding of `isStrictLinearOrderSentence` on an infinite domain,
* small-domain (`n ≤ 1`) truth-table sentences including nullary relations on the empty structure,
* little-endian colexicographic tuple ordering and the `k`-tuple power interpretation,
* input-tape layout synthesis (`layoutESOSentence`) and tableau axiomatization
  (`tableauESOSentence`, `npPowerSentence`),
* the converse theorem `Cslib.Logic.ESO.Definable.of_queryLanguage_mem_NP` and the full equivalences
  `Cslib.Logic.ESO.definable_iff_queryLanguage_mem_NP` and
  `Cslib.Logic.ESO.definable_iff_isoClosed_and_queryLanguage_mem_NP`, and
* axiom hygiene checks for all headline theorems.
-/

namespace ComplexityTests.Fagin

open FirstOrder Language Structure CategoryTheory Cslib.Logic Cslib.Logic.ESO Cslib.Complexity
open Turing.MultiTapeTM
open ComplexityTests.FaginEncoding ComplexityTests.FaginNP

/-! ### Length-checked verifiers -/

/-- `strictVerifier` accepts `edge` with a certificate of the prescribed length `14`. -/
example : strictVerifier encStructure allMarkedLayout.polynomial
    (allMarkedLayout.verifier graphVocabulary) (edge, List.replicate 14 true) = true := by
  rw [strictVerifier_eq_true_iff, Sentence.Layout.eval_polynomial]
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- `strictVerifier` rejects a certificate that is too long (`15` bits instead of `14`), even when
all bits are `true`. -/
example : strictVerifier encStructure allMarkedLayout.polynomial
    (allMarkedLayout.verifier graphVocabulary) (edge, List.replicate 15 true) = false := by
  unfold strictVerifier
  rw [Sentence.Layout.eval_polynomial]
  decide +kernel

/-- `strictVerifier` rejects a certificate that is too short (`2` bits instead of `14`), even when
its prefix marks both vertices of `edge`. -/
example : strictVerifier encStructure allMarkedLayout.polynomial
    (allMarkedLayout.verifier graphVocabulary) (edge, [true, true]) = false := by
  unfold strictVerifier
  rw [Sentence.Layout.eval_polynomial]
  decide +kernel

/-! ### Small-domain and nullary-relation boundaries -/

/-- `cardEqSentence Language.graph 0` holds on `Fin 0` and fails on `Fin 1`. -/
example : (letI := graphVocabulary.decode (0, [ [] ]);
    (Fin 0) ⊨ FO.cardEqSentence Language.graph 0) :=
  letI := graphVocabulary.decode (0, [ [] ])
  (FO.realize_cardEqSentence 0).2 (by simp)

example : ¬ (letI := graphVocabulary.decode (1, [ [false] ]);
    (Fin 1) ⊨ FO.cardEqSentence Language.graph 0) := by
  let _ := graphVocabulary.decode (1, [ [false] ])
  rw [FO.realize_cardEqSentence]
  simp

/-- On the empty domain `Fin 0`, `nullarySymbolSentence` and `truthTableSentence` distinguish the
two nullary structures `(0, [[true]])` and `(0, [[false]])`. -/
example : (letI := nullaryVocabulary.decode (0, [ [true] ]);
    (Fin 0) ⊨ FO.truthTableSentence nullaryVocabulary.nullarySymbolSentence
      fun s => s ⟨0, by decide⟩ = true) := by
  classical
  let _ := nullaryVocabulary.decode (0, [ [true] ])
  rw [FO.realize_truthTableSentence, decide_eq_true_eq]
  exact (Vocabulary.relMap_decode (v := nullaryVocabulary) (a := (0, [ [true] ]))
    nullarySymbol _).2 (by decide +kernel)

example : ¬ (letI := nullaryVocabulary.decode (0, [ [false] ]);
    (Fin 0) ⊨ FO.truthTableSentence nullaryVocabulary.nullarySymbolSentence
      fun s => s ⟨0, by decide⟩ = true) := by
  classical
  let _ := nullaryVocabulary.decode (0, [ [false] ])
  rw [FO.realize_truthTableSentence, decide_eq_true_eq]
  exact mt (Vocabulary.relMap_decode (v := nullaryVocabulary) (a := (0, [ [false] ]))
    nullarySymbol _).1 (by decide +kernel)

/-! ### Guessed strict linear orders on arbitrary domains -/

/-- The usual strict order `<` on `ℕ`, as an interpretation of `orderLanguage`. -/
def natLt : ∀ _ : Unit, Set (Fin 2 → ℕ) := fun _ => {x | x 0 < x 1}

/-- The empty binary relation on `ℕ`, as an interpretation of `orderLanguage`. -/
def natEmpty : ∀ _ : Unit, Set (Fin 2 → ℕ) := fun _ => ∅

/-- On an infinite domain, where `realize_isStrictLinearOrderSentence` does not apply, the
unfolding lemma shows that the usual order `<` on `ℕ` satisfies `isStrictLinearOrderSentence`. -/
example : (letI := varLanguage.structure (arity := fun _ : Unit => 2) natLt;
    ℕ ⊨ isStrictLinearOrderSentence) :=
  (realize_isStrictLinearOrderSentence_iff_irrefl_trans_trichotomous natLt).2
    ⟨⟨fun a => lt_irrefl a, fun a _ c h => (lt_trans h.1 h.2 : a < c)⟩,
      fun a b => lt_trichotomy a b⟩

/-- The empty relation on `ℕ` is not a strict linear order: trichotomy fails at `0, 1`. -/
example : ¬ (letI := varLanguage.structure (arity := fun _ : Unit => 2) natEmpty;
    ℕ ⊨ isStrictLinearOrderSentence) := by
  rw [realize_isStrictLinearOrderSentence_iff_irrefl_trans_trichotomous]
  rintro ⟨-, htri⟩
  simpa [natEmpty] using htri 0 1

/-! ### Little-endian tuple order (`tupleIndex_lt_iff`) -/

/-- `tupleIndex` is little-endian (`x 0 + n * x 1`), so its strict order compares the highest
differing coordinate (`![2, 0] < ![0, 1]` on `Fin 2 → Fin 3`). -/
example : tupleIndex (![2, 0] : Fin 2 → Fin 3) < tupleIndex (![0, 1] : Fin 2 → Fin 3) := by
  decide +kernel

/-! ### Fagin's theorem on concrete classes -/

/-- **Converse of Fagin's theorem applied to `n`-colorability**: because the query language of
`n`-colorable directed graphs belongs to `NP encStructure`, the class of `n`-colorable directed
graphs is existential second-order definable via `Definable.of_queryLanguage_mem_NP`. -/
theorem colorable_definable_of_mem_NP (n : ℕ) :
    ESO.Definable {M : Bundled.{0} Language.graph.Structure |
      ∃ f : M → Fin n, ∀ x y, RelMap adj ![x, y] → f x ≠ f y} :=
  Definable.of_queryLanguage_mem_NP graphVocabulary (Definable.colorable n).isoClosed
    (colorable_mem_NP n)

/-- The triangle: three vertices, all distinct pairs adjacent. -/
def triangle : EncodedStructure :=
  (3, [ [false, true, true, true, false, true, true, true, false] ])

/-- **Semantic test of the `Definable` statement**: any existential second-order sentence
characterizing 2-colorability, such as the one whose existence `Definable.of_queryLanguage_mem_NP`
asserts, holds on the decoded 2-vertex edge and fails on the decoded 3-vertex triangle. This
exercises structure decoding (`Vocabulary.decode`) and the statement of `ESO.Definable`, not the
sentence built in the proof. -/
example :
    ∃ Φ : ESO.Sentence Language.graph,
      (∀ (M : Bundled.{0} Language.graph.Structure) [Finite M],
        (∃ f : M → Fin 2, ∀ x y, RelMap adj ![x, y] → f x ≠ f y) ↔ Φ.Realize M) ∧
      (letI := graphVocabulary.decode edge; Φ.Realize (Fin edge.1)) ∧
      ¬ (letI := graphVocabulary.decode triangle; Φ.Realize (Fin triangle.1)) := by
  obtain ⟨Φ, hΦ⟩ := colorable_definable_of_mem_NP 2
  refine ⟨Φ, fun M _ => hΦ M, ?_, ?_⟩
  · let _ := graphVocabulary.decode edge
    exact (hΦ ⟨Fin edge.1, inferInstance⟩).1 ⟨id, fun x y h => (relMap_decode_edge x y).1 h⟩
  · let _ := graphVocabulary.decode triangle
    rw [← hΦ ⟨Fin triangle.1, inferInstance⟩]
    rintro ⟨f, hf⟩
    have h01 : f (0 : Fin 3) ≠ f (1 : Fin 3) :=
      hf (0 : Fin 3) (1 : Fin 3)
        ((Vocabulary.relMap_decode graphVocabulary triangle adj _).2 (by decide +kernel))
    have h02 : f (0 : Fin 3) ≠ f (2 : Fin 3) :=
      hf (0 : Fin 3) (2 : Fin 3)
        ((Vocabulary.relMap_decode graphVocabulary triangle adj _).2 (by decide +kernel))
    have h12 : f (1 : Fin 3) ≠ f (2 : Fin 3) :=
      hf (1 : Fin 3) (2 : Fin 3)
        ((Vocabulary.relMap_decode graphVocabulary triangle adj _).2 (by decide +kernel))
    revert h01 h02 h12
    generalize f (0 : Fin 3) = c0, f (1 : Fin 3) = c1, f (2 : Fin 3) = c2
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> decide

/-- **Fagin's equivalence on directed graphs**: for any isomorphism-closed class `K` of finite
directed graphs, `ESO.Definable K ↔ graphVocabulary.queryLanguage K ∈ NP encStructure`. -/
theorem graph_definable_iff_mem_NP {K : Set (Bundled.{0} Language.graph.Structure)}
    (hK : IsoClosed K) :
    ESO.Definable K ↔ graphVocabulary.queryLanguage K ∈ NP encStructure :=
  graphVocabulary.definable_iff_queryLanguage_mem_NP hK

/-- **Fagin's equivalence on nullary structures**: for any isomorphism-closed class `K` over
`nullaryLanguage`, `ESO.Definable K ↔ nullaryVocabulary.queryLanguage K ∈ NP encStructure`. -/
theorem nullary_definable_iff_mem_NP {K : Set (Bundled.{0} nullaryLanguage.Structure)}
    (hK : IsoClosed K) :
    ESO.Definable K ↔ nullaryVocabulary.queryLanguage K ∈ NP encStructure :=
  nullaryVocabulary.definable_iff_queryLanguage_mem_NP hK

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.IsVerifier.strictVerifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.IsVerifier.strictVerifier

/--
info: 'Cslib.Complexity.computableInPolyTime_strictVerifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.computableInPolyTime_strictVerifier

/--
info: 'Cslib.Complexity.CookLevin.exists_tableau_satisfiable_iff_of_strictVerifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.exists_tableau_satisfiable_iff_of_strictVerifier

/--
info: 'Cslib.Logic.ESO.Sentence.realize_project' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Sentence.realize_project

/--
info: 'Cslib.Logic.ESO.realize_isStrictLinearOrderSentence' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.realize_isStrictLinearOrderSentence

/--
info: 'Cslib.Logic.ESO.Definable.of_withLinearOrder' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.of_withLinearOrder

/--
info: 'Cslib.Logic.FO.Definable.inter_card_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Definable.inter_card_le_one

/--
info: 'Cslib.Logic.ESO.Definable.of_card_ge_two' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.of_card_ge_two

/--
info: 'Cslib.Logic.ESO.Definable.of_powerLanguage' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.of_powerLanguage

/--
info: 'Cslib.Logic.Vocabulary.realize_layoutESOSentence' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.Vocabulary.realize_layoutESOSentence

/--
info: 'Cslib.Logic.Vocabulary.realize_tableauESOSentence' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.Vocabulary.realize_tableauESOSentence

/--
info: 'Cslib.Logic.Vocabulary.realize_npPowerSentence' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.Vocabulary.realize_npPowerSentence

/--
info: 'Cslib.Logic.ESO.Definable.of_queryLanguage_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.of_queryLanguage_mem_NP

/--
info: 'Cslib.Logic.ESO.definable_iff_queryLanguage_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.definable_iff_queryLanguage_mem_NP

/--
info: 'Cslib.Logic.ESO.definable_iff_isoClosed_and_queryLanguage_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.definable_iff_isoClosed_and_queryLanguage_mem_NP

/--
info: 'Cslib.Logic.Vocabulary.definable_iff_queryLanguage_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.Vocabulary.definable_iff_queryLanguage_mem_NP

end ComplexityTests.Fagin
