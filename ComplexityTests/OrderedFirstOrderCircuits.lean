/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.FirstOrder.Ordered
import Complexity.Computability.Circuit.Boolean.FirstOrder.Ordered.Parity

/-!
# Canonical ordered first-order circuit clients

These examples evaluate the generated formulas on actual input bits. They cover genuine numeric
constants in input atoms, least-significant-bit indexing, quantifier binding, exact gate and leaf
counts, the minimum permitted universe, and a numeric-only sentence with no input bits.
-/

namespace ComplexityTests.OrderedFirstOrderCircuits

open FirstOrder Language
open Cslib.Circuits.Boolean

private inductive Relation : ℕ → Type
  | mark : Relation 1

private abbrev inputLanguage : Language where
  Functions _ := Empty
  Relations := Relation

private instance : inputLanguage.IsRelational := fun _ => inferInstance

private def atomEquiv (n : ℕ) : ModelChecking.Atom inputLanguage n ≃ Fin n where
  toFun a := match a with | ⟨⟨_, .mark⟩, xs⟩ => xs 0
  invFun i := ⟨⟨1, .mark⟩, fun _ => i⟩
  left_inv := by
    rintro ⟨⟨_, r⟩, xs⟩
    cases r
    exact congrArg
      (fun t : Fin 1 → Fin n => (⟨⟨1, Relation.mark⟩, t⟩ : ModelChecking.Atom inputLanguage n))
      (funext fun i => congrArg xs (Subsingleton.elim 0 i))
  right_inv _ := rfl

open Cslib.Logic.FO.Ordered

private instance : Fact (2 ≤ 2) := ⟨by decide⟩
private instance : Fact (2 ≤ 3) := ⟨by decide⟩
private instance : Fact (2 ≤ 9) := ⟨by decide⟩

private def compile {n : ℕ} [Fact (2 ≤ n)] (φ : (language inputLanguage).Sentence) :=
  ModelChecking.Ordered.toUnbounded (atomEquiv n) φ Fin.elim0

private def marked (t : (language inputLanguage).Term Empty) :
    (language inputLanguage).Sentence :=
  Relations.formula₁ (L := language inputLanguage) (Sum.inl Relation.mark) t

-- All three numeric constants can occur directly in an input-relation argument.
example :
    (compile (n := 3) (marked (zero inputLanguage))).eval Unbounded.interpretation
      ![true, false, true] = true ∧
    (compile (n := 3) (marked (one inputLanguage))).eval Unbounded.interpretation
      ![true, false, true] = false ∧
    (compile (n := 3) (marked (max inputLanguage))).eval Unbounded.interpretation
      ![true, false, true] = true := by decide

-- Compiling an input atom produces exactly one input leaf and no operation gate.
example :
    (compile (n := 3) (marked (max inputLanguage))).size = 0 ∧
    (compile (n := 3) (marked (max inputLanguage))).depth = 0 ∧
    (compile (n := 3) (marked (max inputLanguage))).leafSize = 1 := by decide

private def lowBit : (language inputLanguage).Sentence :=
  bit inputLanguage (max inputLanguage) (zero inputLanguage)

private def nextBit : (language inputLanguage).Sentence :=
  bit inputLanguage (max inputLanguage) (one inputLanguage)

-- In the non-power-of-two universe of size three, max is binary 10.
example :
    (compile (n := 3) lowBit).eval Unbounded.interpretation ![true, true, true] = false ∧
    (compile (n := 3) nextBit).eval Unbounded.interpretation ![false, false, false] = true ∧
    (compile (n := 2) lowBit).eval Unbounded.interpretation ![false, false] = true := by decide

-- Numeric predicates read no input leaves, even when all source bits change.
example (x y : Fin 3 → Bool) :
    (compile (n := 3) nextBit).eval Unbounded.interpretation x =
      (compile (n := 3) nextBit).eval Unbounded.interpretation y ∧
    (compile (n := 3) nextBit).size = 1 ∧
    (compile (n := 3) nextBit).depth = 1 ∧
    (compile (n := 3) nextBit).leafSize = 0 := by
  refine ⟨?_, by decide⟩
  change (ModelChecking.constUnbounded true).eval Unbounded.interpretation x =
    (ModelChecking.constUnbounded true).eval Unbounded.interpretation y
  simp

private def mixed : (language inputLanguage).Sentence :=
  ((Relations.boundedFormula₁ (L := language inputLanguage) (Sum.inl Relation.mark)
      (.var (.inr 0))).iff
    (Relations.boundedFormula₂ (L := language inputLanguage) (Sum.inr NumericRelation.bit)
      (.var (.inr 0)) (one inputLanguage)) ⊓
    (Relations.boundedFormula₂ (L := language inputLanguage) (Sum.inr NumericRelation.le)
      (zero inputLanguage) (.var (.inr 0))) ⊓
    (Relations.boundedFormula₂ (L := language inputLanguage) (Sum.inr NumericRelation.le)
      (.var (.inr 0)) (max inputLanguage))).all

-- A quantified formula accepts exactly the intended input predicate, with fixed numeric data.
example :
    (compile (n := 3) mixed).eval Unbounded.interpretation ![false, false, true] = true ∧
    (compile (n := 3) mixed).eval Unbounded.interpretation ![false, true, true] = false ∧
    (compile (n := 2) mixed).eval Unbounded.interpretation ![false, false] = true := by decide

private def nested : (language inputLanguage).Sentence :=
  ((Term.var (Sum.inr (0 : Fin 2)) : (language inputLanguage).Term (Empty ⊕ Fin 2)).bdEqual
    (.var (.inr 1)) ⊓
    Relations.boundedFormula₂ (L := language inputLanguage) (Sum.inr NumericRelation.le)
      (.var (.inr 1)) (max inputLanguage)).ex.all

-- The existentially bound variable can equal the surrounding universally bound variable.
example :
    (compile (n := 3) nested).eval Unbounded.interpretation ![false, true, false] = true ∧
    (compile (n := 2) nested).eval Unbounded.interpretation ![true, false] = true := by decide

private def markedAbove : (language inputLanguage).Sentence :=
  (Relations.boundedFormula₂ (L := language inputLanguage) (Sum.inr NumericRelation.le)
    (.var (.inr (0 : Fin 2))) (.var (.inr 1)) ⊓
    Relations.boundedFormula₁ (L := language inputLanguage) (Sum.inl Relation.mark)
      (.var (.inr 1))).ex.all

-- Every x has a marked y above it exactly when max is marked. Reversing the two bound
-- variables, or capturing the outer variable, changes one of these two verdicts.
example :
    (compile (n := 3) markedAbove).eval Unbounded.interpretation ![false, false, true] = true ∧
    (compile (n := 3) markedAbove).eval Unbounded.interpretation ![true, false, false] = false :=
  by decide

private def allMarked : (language inputLanguage).Sentence :=
  (Relations.boundedFormula₁ (L := language inputLanguage) (Sum.inl Relation.mark)
    (.var (.inr 0))).all

-- Quantifier expansion adds one gate, while its three relation-table leaves remain inputs.
example :
    (compile (n := 3) allMarked).size = 1 ∧
    (compile (n := 3) allMarked).depth = 1 ∧
    (compile (n := 3) allMarked).leafSize = 3 := by decide

-- The correctness theorem applies to the same explicit enumeration used by computation.
example (s : inputLanguage.Structure (Fin 3)) :
    letI := s;
    (compile (n := 3) mixed).eval Unbounded.interpretation
      (ModelChecking.atomsOf (L := inputLanguage) (Equiv.refl _) ∘ (atomEquiv 3).symm) = true ↔
        Fin 3 ⊨ mixed := by
  let _ := s
  exact (ModelChecking.Ordered.eval_toUnbounded_atomsOf (atomEquiv 3) mixed Fin.elim0).trans (by
    rw [Sentence.Realize, Formula.Realize]
    exact iff_of_eq (congrArg₂
      (fun (v : Empty → Fin 3) (xs : Fin 0 → Fin 3) => BoundedFormula.Realize mixed v xs)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)))

private def emptyAtoms (n : ℕ) : ModelChecking.Atom Language.empty n ≃ Fin 0 where
  toFun a := a.1.2.elim
  invFun := Fin.elim0
  left_inv a := a.1.2.elim
  right_inv i := i.elim0

-- No positive-arity input symbol is required: this is a formula on zero input bits.
example :
    (ModelChecking.Ordered.toUnbounded (n := 3) (emptyAtoms 3)
      (bit Language.empty (max Language.empty) (one Language.empty)) Fin.elim0).eval
        Unbounded.interpretation Fin.elim0 = true ∧
    (ModelChecking.Ordered.toUnbounded (n := 2) (emptyAtoms 2)
      ((zero Language.empty).equal (one Language.empty)) Fin.elim0).eval
        Unbounded.interpretation Fin.elim0 = false := by decide

private inductive NullaryRelation : ℕ → Type
  | flag : NullaryRelation 0

private abbrev nullaryLanguage : Language where
  Functions _ := Empty
  Relations := NullaryRelation

private instance : nullaryLanguage.IsRelational := fun _ => inferInstance

private def nullaryAtoms (n : ℕ) : ModelChecking.Atom nullaryLanguage n ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨⟨0, .flag⟩, Fin.elim0⟩
  left_inv := by
    rintro ⟨⟨_, r⟩, xs⟩
    cases r
    exact congrArg
      (fun t : Fin 0 → Fin n => (⟨⟨0, NullaryRelation.flag⟩, t⟩ :
        ModelChecking.Atom nullaryLanguage n)) (Subsingleton.elim _ _)
  right_inv i := Subsingleton.elim _ _

private def flag : (language nullaryLanguage).Sentence :=
  .rel (Sum.inl NullaryRelation.flag) Fin.elim0

-- A nullary input relation still contributes one input bit at every universe size.
example :
    (ModelChecking.Ordered.toUnbounded (n := 2) (nullaryAtoms 2) flag Fin.elim0).eval
      Unbounded.interpretation ![true] = true ∧
    (ModelChecking.Ordered.toUnbounded (n := 3) (nullaryAtoms 3) flag Fin.elim0).eval
      Unbounded.interpretation ![false] = false ∧
    (ModelChecking.Ordered.toUnbounded (n := 3) (nullaryAtoms 3) flag Fin.elim0).leafSize = 1 :=
  by decide

private instance : Fintype (Σ l, inputLanguage.Relations l) where
  elems := {⟨1, Relation.mark⟩}
  complete := by rintro ⟨_, r⟩; cases r; simp

private def markedStructure {n : ℕ} [Fact (2 ≤ n)] (x : Fin n → Bool) :
    Cslib.Logic.FO.Ordered.Structure inputLanguage :=
  ⟨n, Fact.out, { RelMap := fun r t => match r with | .mark => x (t 0) = true }⟩

private def evenMarked : Query inputLanguage :=
  {M | Even (Nat.card {x : M //
    FirstOrder.Language.Structure.RelMap (L := inputLanguage) Relation.mark ![x]})}

-- The separated query has both accepting and rejecting canonical structures, including
-- the empty predicate, an even nonempty predicate, and a singleton predicate.
example : markedStructure ![false, false] ∈ evenMarked := by
  change Even (Nat.card {x : Fin 2 // ![false, false] x = true})
  rw [Nat.card_eq_fintype_card]
  decide

example : markedStructure ![true, true] ∈ evenMarked := by
  change Even (Nat.card {x : Fin 2 // ![true, true] x = true})
  rw [Nat.card_eq_fintype_card]
  decide

example : markedStructure ![true, false] ∉ evenMarked := by
  change ¬ Even (Nat.card {x : Fin 2 // ![true, false] x = true})
  rw [Nat.card_eq_fintype_card]
  decide

example : ¬ Definable evenMarked :=
  ModelChecking.Ordered.not_definable_even_card (L := inputLanguage) Relation.mark

end ComplexityTests.OrderedFirstOrderCircuits
