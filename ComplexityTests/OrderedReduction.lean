/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Reduction
public import ComplexityTests.OrderedModelChecking
import Mathlib.Tactic.FinCases

/-! # Native ordered full-tuple interpretation transducer clients -/

@[expose] public section

namespace Cslib.Tests.OrderedReduction

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered
open Turing Turing.MultiTapeTM Cslib.Tests.OrderedModelChecking

/-- The language with a single nullary relation symbol. -/
def nullaryLanguage : Language :=
  ⟨fun _ => Empty, fun | 0 => Unit | _ + 1 => Empty⟩

instance : nullaryLanguage.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

/-- The vocabulary with the single nullary symbol. -/
def nullaryVocabulary : Vocabulary nullaryLanguage where
  count := 1
  symbol :=
    { toFun := fun _ => ⟨0, ()⟩
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun
        | ⟨0, ()⟩ => rfl
        | ⟨_ + 1, s⟩ => s.elim }

/-- Empty relational vocabulary. -/
def emptyVocabulary : Vocabulary Language.empty where
  count := 0
  symbol :=
    { toFun := fun i => i.elim0
      invFun := fun s => s.2.elim
      left_inv := fun i => i.elim0
      right_inv := fun s => s.2.elim }

/-- Adversarial two-dimensional interpretation from the unary-mark vocabulary `L` to graphs:
`x₁ = 0 ∧ y₀ = 0 ∧ y₁ = 1 ∧ ∃ z, (mark(z) ∧ z = x₀ ∧ BIT(z, 0) ∧ y₁ ≤ z)`.
On `n = 3` with `mark` true only at `1`, the unique related pair of 2-tuples is
`x = (1, 0)` (rank `3`) and `y = (0, 1)` (rank `1`), at table slot `3 + 9 * 1 = 12`. -/
def advInterp : FullTupleInterpretation L Language.graph 2 where
  rel
    | .adj =>
      let x0 : (language L).Term ((Fin 2 × Fin 2) ⊕ Fin 1) := .var (.inl (0, 0))
      let x1 : (language L).Term ((Fin 2 × Fin 2) ⊕ Fin 1) := .var (.inl (0, 1))
      let y0 : (language L).Term ((Fin 2 × Fin 2) ⊕ Fin 1) := .var (.inl (1, 0))
      let y1 : (language L).Term ((Fin 2 × Fin 2) ⊕ Fin 1) := .var (.inl (1, 1))
      let z : (language L).Term ((Fin 2 × Fin 2) ⊕ Fin 1) := .var (.inr 0)
      (Term.bdEqual (.var (.inl (0, 1))) (zero L)) ⊓
      (Term.bdEqual (.var (.inl (1, 0))) (zero L)) ⊓
      (Term.bdEqual (.var (.inl (1, 1))) (one L)) ⊓
      ((Relations.boundedFormula₁ (L := language L) (.inl Relation.mark) z) ⊓
        (z.bdEqual x0) ⊓
        (Relations.boundedFormula₂ (L := language L) (.inr NumericRelation.bit) z (zero L)) ⊓
        (Relations.boundedFormula₂ (L := language L) (.inr NumericRelation.le) y1 z) ⊓
        (x1.bdEqual (zero L)) ⊓ (y0.bdEqual (zero L))).ex

/-- Non-cancelling two-dimensional orientation client on `n = 3, k = 2`:
`x₀ = 1 ∧ x₁ = 0 ∧ y₀ = 0 ∧ y₁ = max`.
The unique related pair is `x = (1, 0)` (rank `3`) and `y = (0, 2)` (rank `2`), at table slot
`3 + 9 * 2 = 21`, distinguishing correct indexing from outer reversal (`29`), inner reversal
(`55`), and simultaneous inner+outer reversal (`15`). -/
def nonCancellingInterp : FullTupleInterpretation L Language.graph 2 where
  rel
    | .adj =>
      (Term.bdEqual (.var (.inl (0, 0))) (one L)) ⊓
      (Term.bdEqual (.var (.inl (0, 1))) (zero L)) ⊓
      (Term.bdEqual (.var (.inl (1, 0))) (zero L)) ⊓
      (Term.bdEqual (.var (.inl (1, 1))) (max L))

/-- Dimension-one identity interpretation on `L`. -/
def idInterp : FullTupleInterpretation L L 1 where
  rel
    | .mark => Relations.boundedFormula₁ (L := language L) (.inl Relation.mark) (.var (.inl (0, 0)))

/-- Positive-dimensional interpretation into a nullary target vocabulary. -/
def nullaryInterp : FullTupleInterpretation L nullaryLanguage 1 where
  rel {r} R :=
    match r, R with
    | 0, () => Relations.boundedFormula₁ (L := language L) (.inl Relation.mark) (one L)

/-- Positive-dimensional interpretation into an empty target vocabulary. -/
def emptyTargetInterp : FullTupleInterpretation L Language.empty 1 where
  rel {_} R := R.elim

/-- Source structure on `n = 3` with `mark` true only at `1`. -/
def input3P : EncodedStructure := (3, [ [false, true, false] ])

/-- Source structure on `n = 3` with `mark` empty. -/
def input3Empty : EncodedStructure := (3, [ [false, false, false] ])

/-- Source structure on `n = 2` with `mark` true at `1`. -/
def input2P : EncodedStructure := (2, [ [false, true] ])

/-- Target sentence `∃ u, adj(u, 1) ∧ BIT(max, u)`. On `Fin 9` (`max = 8`), `BIT(8, u)` holds
uniquely at `u = 3`, which is a bit index beyond the source universe size `3`. -/
def targetSent : (language Language.graph).Sentence :=
  ((Relations.boundedFormula₂ (L := language Language.graph) (.inl adj)
      (.var (.inr 0)) (one Language.graph)) ⊓
    (Relations.boundedFormula₂ (L := language Language.graph) (.inr NumericRelation.bit)
      (max Language.graph) (.var (.inr 0)))).ex

/-- Log-space computability, query-language reduction, output cardinality `3^2 = 9`, and framed
output length `2 * 9 + 1 + (2 * 81 + 1) = 182` on `input3P`. -/
example :
    ComputableInLogSpace (advInterp.encodedMap vocabulary graphVocabulary)
      encStructure encStructure ∧
    Cslib.Complexity.LogSpaceReducible encStructure encStructure
      (Ordered.queryLanguage vocabulary (advInterp.onSentence targetSent))
      (Ordered.queryLanguage graphVocabulary targetSent) ∧
    (advInterp.encodedMap vocabulary graphVocabulary input3P).1 = 9 ∧
    (encStructure (advInterp.encodedMap vocabulary graphVocabulary input3P)).length = 182 :=
  ⟨advInterp.computableInLogSpace_encodedMap vocabulary graphVocabulary,
    advInterp.logSpaceReducible_onSentence vocabulary graphVocabulary (by decide) targetSent,
    advInterp.card_encodedMap vocabulary graphVocabulary (by decide) (by decide),
    by
      rw [advInterp.length_encStructure_encodedMap vocabulary graphVocabulary
        (by decide) (by decide)]
      decide⟩

private theorem realize_advInterp {a : EncodedStructure} [Fact (2 ≤ a.1)]
    (v : Fin 2 × Fin 2 → Fin a.1) :
    (letI := vocabulary.decode a; (advInterp.rel adj).Realize v) ↔
      ((v (0, 1) = ⟨0, by have : 2 ≤ a.1 := Fact.out; lia⟩ ∧
        v (1, 0) = ⟨0, by have : 2 ≤ a.1 := Fact.out; lia⟩) ∧
        v (1, 1) = ⟨1, by have : 2 ≤ a.1 := Fact.out; lia⟩) ∧
      ∃ z : Fin a.1,
        (((((vocabulary.table a ⟨1, Relation.mark⟩).getD (tupleIndex ![z]) false = true ∧
          z = v (0, 0)) ∧
          z.val.testBit 0 = true) ∧
          v (1, 1) ≤ z) ∧
          v (0, 1) = ⟨0, by have : 2 ≤ a.1 := Fact.out; lia⟩) ∧
          v (1, 0) = ⟨0, by have : 2 ≤ a.1 := Fact.out; lia⟩ := by
  let _ := vocabulary.decode a
  simp only [advInterp, Formula.Realize, BoundedFormula.realize_inf, BoundedFormula.realize_ex,
    BoundedFormula.realize_bdEqual]
  rfl

private theorem table_advInterp_input3P (x0 x1 : Fin 9) :
    (graphVocabulary.table
      (advInterp.encodedMap vocabulary graphVocabulary input3P)
      ⟨2, adj⟩).getD (tupleIndex ![x0, x1]) false = true ↔
      x0 = 3 ∧ x1 = 1 := by
  refine (advInterp.table_encodedMap vocabulary graphVocabulary
    (a := input3P) (by decide) (by decide) adj ![x0, x1]).trans ?_
  let _ : Fact (2 ≤ input3P.1) := ⟨by decide⟩
  rw [realize_advInterp (a := input3P)]
  revert x0 x1
  decide

/-- Slot `12` (`tupleIndex ![3, 1]`) is `true` and transposed slot `28` (`tupleIndex ![1, 3]`)
is `false`. -/
example :
    (graphVocabulary.table
      (advInterp.encodedMap vocabulary graphVocabulary input3P)
      ⟨2, adj⟩).getD 12 false = true ∧
    (graphVocabulary.table
      (advInterp.encodedMap vocabulary graphVocabulary input3P)
      ⟨2, adj⟩).getD 28 false = false := by
  have h12 : tupleIndex ![(3 : Fin 9), (1 : Fin 9)] = 12 := by decide
  have h28 : tupleIndex ![(1 : Fin 9), (3 : Fin 9)] = 28 := by decide
  rw [← h12, ← h28]
  refine ⟨(table_advInterp_input3P 3 1).mpr ⟨rfl, rfl⟩, ?_⟩
  rw [Bool.eq_false_iff]
  intro h
  have := (table_advInterp_input3P 1 3).mp h
  revert this
  decide

private theorem table_nonCancelling_input3P (x0 x1 : Fin 9) :
    (graphVocabulary.table
      (nonCancellingInterp.encodedMap vocabulary
        graphVocabulary input3P)
      ⟨2, adj⟩).getD (tupleIndex ![x0, x1]) false = true ↔
      x0 = 3 ∧ x1 = 2 := by
  refine (nonCancellingInterp.table_encodedMap vocabulary
    graphVocabulary (a := input3P) (by decide) (by decide) adj ![x0, x1]).trans ?_
  let _ : Fact (2 ≤ input3P.1) := ⟨by decide⟩
  let _ := vocabulary.decode input3P
  fin_cases x0 <;> fin_cases x1 <;>
    simp only [nonCancellingInterp, Formula.Realize, BoundedFormula.realize_inf,
      BoundedFormula.realize_bdEqual] <;>
    decide

/-- Non-cancelling orientation guard at `n = 3, k = 2`: sole pair `(3, 2)` makes slot `21` true
and slots `29`, `55`, and `15` false. -/
example :
    (graphVocabulary.table
      (nonCancellingInterp.encodedMap vocabulary
        graphVocabulary input3P)
      ⟨2, adj⟩).getD 21 false = true ∧
    (graphVocabulary.table
      (nonCancellingInterp.encodedMap vocabulary
        graphVocabulary input3P)
      ⟨2, adj⟩).getD 29 false = false ∧
    (graphVocabulary.table
      (nonCancellingInterp.encodedMap vocabulary
        graphVocabulary input3P)
      ⟨2, adj⟩).getD 55 false = false ∧
    (graphVocabulary.table
      (nonCancellingInterp.encodedMap vocabulary
        graphVocabulary input3P)
      ⟨2, adj⟩).getD 15 false = false := by
  have h21 : tupleIndex ![(3 : Fin 9), (2 : Fin 9)] = 21 := by decide
  have h29 : tupleIndex ![(2 : Fin 9), (3 : Fin 9)] = 29 := by decide
  have h55 : tupleIndex ![(1 : Fin 9), (6 : Fin 9)] = 55 := by decide
  have h15 : tupleIndex ![(6 : Fin 9), (1 : Fin 9)] = 15 := by decide
  rw [← h21, ← h29, ← h55, ← h15]
  refine ⟨(table_nonCancelling_input3P 3 2).mpr ⟨rfl, rfl⟩,
    ?_, ?_, ?_⟩
  · rw [Bool.eq_false_iff]
    intro h
    have := (table_nonCancelling_input3P 2 3).mp h
    revert this
    decide
  · rw [Bool.eq_false_iff]
    intro h
    have := (table_nonCancelling_input3P 1 6).mp h
    revert this
    decide
  · rw [Bool.eq_false_iff]
    intro h
    have := (table_nonCancelling_input3P 6 1).mp h
    revert this
    decide

/-- `input3P` satisfies the pulled-back sentence (witnessed at target rank `u = 3`, with
`BIT(8, 3) = true`), via `mem_queryLanguage_encodedMap_iff`. -/
example : input3P ∈ Ordered.queryLanguage vocabulary (advInterp.onSentence targetSent) := by
  rw [← advInterp.mem_queryLanguage_encodedMap_iff vocabulary
    graphVocabulary (by decide) targetSent]
  have hwf : graphVocabulary.WellFormed
      (advInterp.encodedMap vocabulary graphVocabulary input3P) :=
    (advInterp.wellFormed_encodedMap_iff vocabulary
      graphVocabulary).mpr ⟨by decide, by decide⟩
  have hcard : (advInterp.encodedMap vocabulary
      graphVocabulary input3P).1 = 9 :=
    advInterp.card_encodedMap vocabulary graphVocabulary
      (by decide) (by decide)
  refine ⟨hwf, by lia, ?_⟩
  let _ : Fact (2 ≤ (advInterp.encodedMap vocabulary
      graphVocabulary input3P).1) := ⟨by lia⟩
  let _ := graphVocabulary.decode
    (advInterp.encodedMap vocabulary graphVocabulary input3P)
  simp only [targetSent, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf]
  refine ⟨⟨3, by lia⟩, ?_⟩
  have hrel : (graphVocabulary.table
      (advInterp.encodedMap vocabulary graphVocabulary input3P)
      ⟨2, adj⟩).getD 12 false = true := by
    have h12 : tupleIndex ![(3 : Fin 9), (1 : Fin 9)] = 12 := by decide
    rw [← h12]
    exact (table_advInterp_input3P 3 1).mpr ⟨rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · change (graphVocabulary.table
        (advInterp.encodedMap vocabulary graphVocabulary input3P)
        ⟨2, adj⟩).getD (3 + (advInterp.encodedMap vocabulary
          graphVocabulary input3P).1 * (1 +
          (advInterp.encodedMap vocabulary
            graphVocabulary input3P).1 * 0)) false = true
    simpa [hcard] using hrel
  · change ((advInterp.encodedMap vocabulary
        graphVocabulary input3P).1 - 1).testBit 3 = true
    rw [hcard]
    decide

/-- Clearing `mark` on `n = 3` makes the pulled-back sentence false. -/
example : input3Empty ∉ Ordered.queryLanguage vocabulary (advInterp.onSentence targetSent) := by
  rintro ⟨_, _, hsat⟩
  let _ : Fact (2 ≤ input3Empty.1) := ⟨by decide⟩
  let _ := vocabulary.decode input3Empty
  change Fin input3Empty.1 ⊨ advInterp.onSentence targetSent at hsat
  rw [advInterp.realize_onSentence (by decide) targetSent] at hsat
  let _ := advInterp.inputStructure (n := input3Empty.1)
  let _ : Fact (2 ≤ input3Empty.1 ^ 2) := ⟨by decide⟩
  change Fin (input3Empty.1 ^ 2) ⊨ targetSent at hsat
  simp only [targetSent, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf] at hsat
  obtain ⟨u, hu, -⟩ := hsat
  have hu' : (letI := vocabulary.decode input3Empty;
      (advInterp.rel adj).Realize
        (fun p : Fin 2 × Fin 2 =>
          (lexEquiv (n := input3Empty.1) (k := 2)).symm
            (![u, (1 : Fin 9)] p.1) p.2)) := hu
  clear hu
  rw [realize_advInterp (a := input3Empty)] at hu'
  revert u hu'
  decide

/-- Size-`2` boundary (`n = 2, k = 2`, output cardinality `4`), dimension-`1` identity,
nullary target, empty target vocabulary, and rejection of small sizes (`0`, `1`) and malformed
shapes (missing, extra, or wrong-length tables). -/
example (x0 : Fin 3) (x : Fin 0 → Fin (input3P.1 ^ 1)) :
    (advInterp.encodedMap vocabulary graphVocabulary input2P).1 = 4 ∧
    ((vocabulary.table (idInterp.encodedMap vocabulary vocabulary input3P)
      ⟨1, Relation.mark⟩).getD (tupleIndex ![x0]) false = true ↔ x0 = 1) ∧
    (nullaryVocabulary.table (nullaryInterp.encodedMap vocabulary nullaryVocabulary input3P)
      ⟨0, ()⟩).getD (tupleIndex x) false = true ∧
    emptyTargetInterp.encodedMap vocabulary emptyVocabulary input3P = (3, []) ∧
    ¬emptyVocabulary.WellFormed
      (emptyTargetInterp.encodedMap vocabulary emptyVocabulary (0, [ [] ])) ∧
    ¬emptyVocabulary.WellFormed
      (emptyTargetInterp.encodedMap vocabulary emptyVocabulary (1, [ [false] ])) ∧
    ¬graphVocabulary.WellFormed
      (advInterp.encodedMap vocabulary graphVocabulary (3, [])) ∧
    ¬graphVocabulary.WellFormed
      (advInterp.encodedMap vocabulary graphVocabulary (3, [ [false, true, false], [] ])) ∧
    ¬graphVocabulary.WellFormed
      (advInterp.encodedMap vocabulary graphVocabulary (3, [ [false] ])) := by
  refine ⟨advInterp.card_encodedMap vocabulary graphVocabulary (by decide) (by decide),
    ?_, ?_,
    by
      rw [emptyTargetInterp.encodedMap_of_admissible vocabulary emptyVocabulary
        (by decide) (by decide)]
      decide,
    by rw [emptyTargetInterp.wellFormed_encodedMap_iff]; decide,
    by rw [emptyTargetInterp.wellFormed_encodedMap_iff]; decide,
    by rw [advInterp.wellFormed_encodedMap_iff]; decide,
    by rw [advInterp.wellFormed_encodedMap_iff]; decide,
    by rw [advInterp.wellFormed_encodedMap_iff]; decide⟩
  · refine (idInterp.table_encodedMap vocabulary vocabulary (a := input3P)
      (by decide) (by decide) Relation.mark ![x0]).trans ?_
    change (vocabulary.table input3P ⟨1, Relation.mark⟩).getD
        (tupleIndex ![(lexEquiv (n := 3) (k := 1)).symm x0 0]) false = true ↔ x0 = 1
    revert x0
    decide
  · rw [nullaryInterp.table_encodedMap vocabulary nullaryVocabulary (a := input3P)
      (by decide) (by decide) (r := 0) () x]
    change (vocabulary.table input3P ⟨1, Relation.mark⟩).getD
        (tupleIndex ![(1 : Fin 3)]) false = true
    decide

/-- One-dimensional restriction to the marked elements, keeping `mark`. On `input3P` its domain
has a single tuple, below the ordered size proviso; the encoded map is still defined and well
formed. -/
def markedInterp : DomainInterpretation L L 1 where
  domain := Relations.formula₁ (L := language L) (.inl Relation.mark) (.var 0)
  rel
    | .mark => Relations.boundedFormula₁ (L := language L) (.inl Relation.mark) (.var (.inl (0, 0)))

/-- Domain-interpretation log-space computability, well-formedness on `input3P`, rejection on size
`1`, and level-1 reduction through `advInterp.toDomainInterpretation`. -/
example (K' : Query Language.graph) :
    ComputableInLogSpace (markedInterp.encodedMap vocabulary vocabulary)
      encStructure encStructure ∧
    vocabulary.WellFormed (markedInterp.encodedMap vocabulary vocabulary input3P) ∧
    ¬vocabulary.WellFormed (markedInterp.encodedMap vocabulary vocabulary (1, [ [true] ])) ∧
    Cslib.Complexity.LogSpaceReducible encStructure encStructure
      (Query.encodedLanguage (L := L) {M | advInterp.toDomainInterpretation.map
        (advInterp.admissible_toDomainInterpretation (by decide)) M ∈ K'} vocabulary)
      (K'.encodedLanguage graphVocabulary) :=
  ⟨markedInterp.computableInLogSpace_encodedMap vocabulary vocabulary,
    (markedInterp.wellFormed_encodedMap_iff vocabulary vocabulary).mpr ⟨by decide, by decide⟩,
    by rw [markedInterp.wellFormed_encodedMap_iff]; decide,
    advInterp.toDomainInterpretation.logSpaceReducible vocabulary graphVocabulary
      (advInterp.admissible_toDomainInterpretation (by decide)) fun _ => Iff.rfl⟩

end Cslib.Tests.OrderedReduction
