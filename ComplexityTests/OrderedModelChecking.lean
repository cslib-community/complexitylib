/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit
public import Mathlib.ModelTheory.Graph

/-! # Native ordered model-checking clients -/

@[expose] public section

namespace Cslib.Tests.OrderedModelChecking

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered
open Turing Turing.MultiTapeTM Turing.CounterProgram

inductive Relation : ℕ → Type
  | mark : Relation 1

abbrev L : Language where
  Functions _ := Empty
  Relations := Relation

instance : L.IsRelational := fun _ => inferInstance

def vocabulary : Vocabulary L where
  count := 1
  symbol :=
    { toFun := fun _ => ⟨1, Relation.mark⟩
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := by rintro ⟨_, r⟩; cases r; rfl }

instance : Fact (2 ≤ 2) := ⟨by decide⟩
instance : Fact (2 ≤ 3) := ⟨by decide⟩
instance : Fact (2 ≤ 9) := ⟨by decide⟩

/-- The input relation agrees with bit one, with both order bounds checked under the quantifier. -/
def mixed : (language L).Sentence :=
  ((Relations.boundedFormula₁ (L := language L) (Sum.inl Relation.mark) (.var (.inr 0))).iff
      (Relations.boundedFormula₂ (L := language L) (Sum.inr NumericRelation.bit)
        (.var (.inr 0)) (one L)) ⊓
    (Relations.boundedFormula₂ (L := language L) (Sum.inr NumericRelation.le)
      (zero L) (.var (.inr 0))) ⊓
    (Relations.boundedFormula₂ (L := language L) (Sum.inr NumericRelation.le)
      (.var (.inr 0)) (max L))).all

/-- A constant occurs directly as an argument of an input relation. -/
def markedMax : (language L).Sentence :=
  Relations.boundedFormula₁ (L := language L) (Sum.inl Relation.mark) (max L)

/-- The numeric constants occur directly in equalities. -/
def sizeTwo : (language L).Sentence :=
  ((zero L).equal (one L)).not ⊓ (one L).equal (max L)

/-- A maximal bit index exercises implicit zero padding. -/
def highBit : (language L).Sentence :=
  Relations.boundedFormula₂ (L := language L) (Sum.inr NumericRelation.bit) (max L) (max L)

/-- A second quantified variable must equal the first and obey the upper order bound. -/
def nested : (language L).Sentence :=
  ((Term.var (Sum.inr (0 : Fin 2)) : (language L).Term (Empty ⊕ Fin 2)).bdEqual
      (.var (.inr 1)) ⊓
    Relations.boundedFormula₂ (L := language L) (Sum.inr NumericRelation.le)
      (.var (.inr 1)) (max L)).ex.all

def input3 : EncodedStructure := (3, [ [false, false, true] ])
def input2 : EncodedStructure := (2, [ [false, false] ])

example :
    queryLanguage vocabulary mixed ∈ Cslib.Complexity.L encStructure ∧
    queryLanguage vocabulary nested ∈ Cslib.Complexity.L encStructure :=
  ⟨queryLanguage_mem_L vocabulary mixed, queryLanguage_mem_L vocabulary nested⟩

lemma realize_mixed {a : EncodedStructure} [Fact (2 ≤ a.1)] :
    (letI := vocabulary.decode a; Fin a.1 ⊨ mixed) ↔
      ∀ x : Fin a.1,
        ((vocabulary.table a ⟨1, Relation.mark⟩).getD (tupleIndex ![x]) false = true ↔
          x.val.testBit 1 = true) ∧ (0 : ℕ) ≤ x.val ∧ x.val ≤ a.1 - 1 := by
  simp only [mixed, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_inf, BoundedFormula.realize_iff, and_assoc]
  rfl

/-- A non-power-of-two universe with a genuinely nonempty input predicate. -/
example : input3 ∈ queryLanguage vocabulary mixed := by
  let _ : Fact (2 ≤ input3.1) := ⟨by decide⟩
  refine ⟨by decide, by decide, ?_⟩
  rw [realize_mixed (a := input3)]
  intro x
  fin_cases x <;> decide

/-- The minimum permitted universe also runs through the quantified compiler. -/
example : input2 ∈ queryLanguage vocabulary mixed := by
  let _ : Fact (2 ≤ input2.1) := ⟨by decide⟩
  refine ⟨by decide, by decide, ?_⟩
  rw [realize_mixed (a := input2)]
  intro x
  fin_cases x <;> decide

/-- Changing the input relation changes the verdict even though numeric semantics stay canonical. -/
example : (3, [ [false, true, true] ]) ∉ queryLanguage vocabulary mixed := by
  rintro ⟨_, hn, h⟩
  let _ : Fact (2 ≤ (3 : ℕ)) := ⟨hn⟩
  have h₁ := (realize_mixed.mp h) (1 : Fin 3)
  exact (by decide : ¬((vocabulary.table (3, [ [false, true, true] ]) ⟨1, Relation.mark⟩).getD
    (tupleIndex ![(1 : Fin 3)]) false = true ↔ (1 : ℕ).testBit 1 = true)) h₁.1

example : input3 ∈ queryLanguage vocabulary markedMax := by
  refine ⟨by decide, by decide, ?_⟩
  change (vocabulary.table input3 ⟨1, Relation.mark⟩).getD
    (tupleIndex ![(2 : Fin 3)]) false = true
  decide

example : input2 ∈ queryLanguage vocabulary sizeTwo := by
  refine ⟨by decide, by decide, ?_⟩
  simp only [sizeTwo, Sentence.Realize, Formula.realize_inf, Formula.realize_not,
    Formula.realize_equal]
  change ¬(⟨0, by decide⟩ : Fin 2) = ⟨1, by decide⟩ ∧
    (⟨1, by decide⟩ : Fin 2) = ⟨1, by decide⟩
  decide

example : input3 ∈ queryLanguage vocabulary nested := by
  refine ⟨by decide, by decide, ?_⟩
  simp only [nested, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, BoundedFormula.realize_bdEqual]
  intro x
  refine ⟨x, ?_⟩
  change x = x ∧ x.val ≤ 2
  exact ⟨rfl, by have hx : x.val < 3 := x.isLt; lia⟩

example : (9, [List.replicate 9 false]) ∉ queryLanguage vocabulary highBit := by
  rintro ⟨_, _, h⟩
  change (8 : ℕ).testBit 8 = true at h
  contradiction

/-- Well-shaped sizes zero and one, missing tables, and incorrectly sized tables are rejected. -/
example :
    (0, [ [] ]) ∉ queryLanguage vocabulary mixed ∧
    (1, [ [false] ]) ∉ queryLanguage vocabulary mixed ∧
    (3, []) ∉ queryLanguage vocabulary nested ∧
    (3, [ [false] ]) ∉ queryLanguage vocabulary nested :=
  ⟨notMem_queryLanguage_of_lt_two vocabulary (by decide) mixed,
    notMem_queryLanguage_of_lt_two vocabulary (by decide) mixed,
    fun h => absurd h.1 (by decide),
    fun h => absurd h.1 (by decide)⟩

/-- A single binary relation for checking the existing table-index orientation. -/
def graphVocabulary : Vocabulary Language.graph where
  count := 1
  symbol :=
    { toFun := fun _ => ⟨2, adj⟩
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun ⟨_, .adj⟩ => rfl }

/-- Input table coordinates retain the first-coordinate-least-significant convention. -/
def forwardEdge : (language Language.graph).Sentence :=
  Relations.boundedFormula₂ (L := language Language.graph) (Sum.inl adj)
    (zero Language.graph) (max Language.graph)

def backwardEdge : (language Language.graph).Sentence :=
  Relations.boundedFormula₂ (L := language Language.graph) (Sum.inl adj)
    (max Language.graph) (zero Language.graph)

/-- Only tuple `(0,2)`, at table index six, is related; `(2,0)` has index two. -/
def directedEdge : EncodedStructure :=
  (3, [ [false, false, false, false, false, false, true, false, false] ])

example : directedEdge ∈ queryLanguage graphVocabulary
    forwardEdge := by
  refine ⟨by decide, by decide, ?_⟩
  change true = true
  rfl

example : directedEdge ∉ queryLanguage graphVocabulary
    backwardEdge := by
  rintro ⟨_, _, h⟩
  change false = true at h
  contradiction

/-- The compiled input atom reads the framed table position for `(0,max)`, and `Expr.bit` /
`Expr.sub` evaluate within logarithmic space. -/
example :
    (match ModelChecker.formulaCode graphVocabulary Empty.elim 3 forwardEdge 0 1 2 with
      | [.read e _ _ _] => e.eval [3]
      | _ => 0) = 20 ∧
    ComputableTidilyInSpace (fun p : ℕ × ℕ => p.1.testBit p.2)
      (encPair encNat encNat) encBool (fun p => (encPair encNat encNat p).length) ∧
    (Expr.bit (.const 8) (.const 3)).eval [] = 1 ∧
    (Expr.bit (.const 8) (.const 8)).eval [] = 0 ∧
    (Expr.sub (.const 0) (.const 1)).eval [] = 0 ∧
    (Expr.bit (.sub (.reg 0) (.const 1)) (.const 0)).eval [9] = 0 ∧
    ComputableTidilyInSpace
      (fun regs => (Expr.bit (.sub (.reg 0) (.const 1)) (.reg 1)).eval regs)
      (encList encNat) encNat (fun regs => (encList encNat regs).length) :=
  ⟨by decide,
    ComputableTidilyInSpace.natTestBit.weaken (ComputableTidilyInSpace.linear_mul 32),
    by decide, by decide, rfl, by decide,
    Expr.eval_inSpace _⟩

end Cslib.Tests.OrderedModelChecking
