/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Trakhtenbrot.Sentence
public import CslibFrontierTests.Trakhtenbrot
public import Mathlib.ModelTheory.Graph

/-! # Trakhtenbrot's theorem for Mathlib sentences: checked instances

The raw coding of sentences in the language of graphs: a computed raw formula, decoding of a
well-scoped code, rejection of ill-scoped codes (wrong binder, out-of-scope bound name, free name,
unknown symbol, wrong arity), the level-naming of a raw sentence, a finitely satisfiable and a
finitely valid sentence on both sides of the translation, the reduction on a finitely satisfiable
formula and on the axiom of infinity, and the headline theorems for both the language of graphs and
a finite relational language whose only relation symbol is ternary (no binary symbol). -/

@[expose] public section

namespace Cslib.Tests.TrakhtenbrotSentence

open FirstOrder FirstOrder.Language FirstOrder.Language.BoundedFormula Cslib.Logic.FO
open Cslib.Tests.Trakhtenbrot
open scoped FirstOrder.Language.BoundedFormula.RawCoding

/-- The relation symbols of the language of graphs: the single symbol `adj`. -/
def graphSymbols : (Σ l, Language.graph.Relations l) ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨2, .adj⟩
  left_inv := fun ⟨_, .adj⟩ => rfl
  right_inv := fun _ => rfl

instance : Encodable (Σ l, Language.graph.Relations l) := Encodable.ofEquiv Unit graphSymbols

instance : Finite (Σ l, Language.graph.Relations l) := .of_equiv Unit graphSymbols.symm

/-- `adj` has symbol code `0`. -/
example : Encodable.encode (⟨2, adj⟩ : Σ l, Language.graph.Relations l) = 0 := rfl

/-- Symmetry of the adjacency relation. -/
def symm : Language.graph.Sentence :=
  ∀' ∀' (adj.boundedFormula₂ &0 &1 ⟹ adj.boundedFormula₂ &1 &0)

/-- Irreflexivity of the adjacency relation. -/
def irrefl : Language.graph.Sentence :=
  ∀' ∼(adj.boundedFormula₂ &0 &0)

/-! ### The translation -/

/-- The outer quantifier binds `0`, the inner one `2`. -/
theorem toRaw_symm :
    toRaw symm = .all 0 (.all 2 (.imp (.rel 0 [0, 2]) (.rel 0 [2, 0]))) := rfl

/-- The raw formula of `symm` decodes to `symm`. -/
example : fromRaw 0 (.all 0 (.all 2 (.imp (.rel 0 [0, 2]) (.rel 0 [2, 0])))) = some symm := by
  rw [← toRaw_symm, fromRaw_toRaw]

/-- The decoding of the code of `symm` is `symm`. -/
example : Encodable.decode (Encodable.encode symm) = some symm := Encodable.encodek symm

/-- A raw code that is well scoped at depth `0`, checked through `isSome_fromRaw`. -/
example : (fromRaw (L := Language.graph) (α := Empty) 0 (.all 0 (.rel 0 [0, 0]))).isSome := by
  refine isSome_fromRaw.2 ⟨rfl, ⟨⟨2, adj⟩, rfl, rfl⟩, ?_⟩
  simp [RawFormula.NameOk]

/-- The quantifier at depth `0` must bind `0`. -/
example : fromRaw (L := Language.graph) (α := Empty) 0 (.all 2 (.rel 0 [2, 2])) = none := by
  rw [← Option.not_isSome_iff_eq_none, isSome_fromRaw]
  simp [RawFormula.WellScoped]

/-- The level `2` is not bound at depth `1`. -/
example : fromRaw (L := Language.graph) (α := Empty) 0 (.all 0 (.rel 0 [0, 2])) = none := by
  rw [← Option.not_isSome_iff_eq_none, isSome_fromRaw]
  simp [RawFormula.WellScoped, RawFormula.NameOk]

/-- A sentence has no free variables, so the odd name `1` is rejected. -/
example : fromRaw (L := Language.graph) (α := Empty) 0 (.all 0 (.rel 0 [0, 1])) = none := by
  rw [← Option.not_isSome_iff_eq_none, isSome_fromRaw]
  simp [RawFormula.WellScoped, RawFormula.NameOk]

/-- As a formula with free variables in `ℕ`, the same code decodes. -/
example : (fromRaw (L := Language.graph) (α := ℕ) 0 (.all 0 (.rel 0 [0, 1]))).isSome := by
  refine isSome_fromRaw.2 ⟨rfl, ⟨⟨2, adj⟩, rfl, rfl⟩, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨Or.inl ⟨rfl, by decide⟩, Or.inr ⟨rfl, 0, rfl⟩⟩

/-- The symbol code `1` names no relation symbol. -/
example : fromRaw (L := Language.graph) (α := Empty) 0 (.all 0 (.rel 1 [0, 0])) = none := by
  rw [← Option.not_isSome_iff_eq_none, isSome_fromRaw]
  rintro ⟨-, ⟨R, hR, -⟩, -⟩
  have : Encodable.encode R = 0 := rfl
  omega

/-- `adj` is binary, so it cannot be applied to three arguments. -/
example : fromRaw (L := Language.graph) (α := Empty) 0 (.all 0 (.rel 0 [0, 0, 0])) = none := by
  rw [← Option.not_isSome_iff_eq_none, isSome_fromRaw]
  rintro ⟨-, ⟨⟨_, R⟩, -, h⟩, -⟩
  cases R
  simp at h

/-! ### Level names -/

/-- `levels` renames the variables of `∀ x₅ ∀ x₃, R(x₃, x₅)` into level names. -/
example :
    RawFormula.levels (.all 5 (.all 3 (.rel 0 [3, 5]))) = .all 0 (.all 2 (.rel 0 [2, 0])) := by
  decide

/-- The level image of `∀ x₅ ∀ x₃, R(x₃, x₅)` decodes to the sentence `∀ ∀ adj(&1, &0)`. -/
example : fromRaw 0 (RawFormula.levels (.all 5 (.all 3 (.rel 0 [3, 5])))) =
    some (∀' ∀' adj.boundedFormula₂ &1 &0 : Language.graph.Sentence) := by
  rw [show RawFormula.levels (.all 5 (.all 3 (.rel 0 [3, 5]))) =
      toRaw (∀' ∀' adj.boundedFormula₂ &1 &0 : Language.graph.Sentence) by decide, fromRaw_toRaw]

/-! ### Finite satisfiability and finite validity -/

/-- The one-point structure with no edges. -/
@[instance_reducible]
def noLoop : Language.graph.Structure Unit := (⊥ : SimpleGraph Unit).structure

/-- The one-point structure with a loop. -/
@[instance_reducible]
def loop : Language.graph.Structure Unit where
  RelMap _ _ := True

theorem finSat_irrefl : Sentence.FinSat irrefl := by
  refine ⟨Unit, noLoop, inferInstance, inferInstance, ?_⟩
  simp only [irrefl, Sentence.Realize, Formula.Realize, realize_all, realize_not, realize_rel₂]
  -- `simp` does not rewrite instance arguments, so `RelMap` under `noLoop` is unfolded by `exact`.
  exact fun _ h => h

theorem not_finValid_irrefl : ¬Sentence.FinValid irrefl := fun h => by
  have := @h Unit loop _ _
  simp only [irrefl, Sentence.Realize, Formula.Realize, realize_all, realize_not,
    realize_rel₂] at this
  exact this () trivial

/-- The raw formula of `irrefl` is finitely satisfiable. -/
example : RawFormula.FinSat (toRaw irrefl) := (Sentence.finSat_iff_toRaw irrefl).1 finSat_irrefl

/-- The raw formula of `irrefl` is not finitely valid. -/
example : ¬RawFormula.FinValid (toRaw irrefl) := fun h =>
  not_finValid_irrefl ((Sentence.finValid_iff_toRaw irrefl).2 h)

/-- `∀ x, x = x` is finitely valid; the proof goes through its raw formula. -/
example : Sentence.FinValid (∀' (&0 =' &0) : Language.graph.Sentence) := by
  refine (Sentence.finValid_iff_toRaw _).2 fun M _ _ I ρ => ?_
  simp [Term.bdEqual]

/-! ### The reduction -/

/-- The reduction of the axiom of infinity has no finite model. -/
example : ¬Sentence.FinSat (Sentence.singleRel adj infAx) :=
  fun h => not_finSat_infAx ((Sentence.finSat_singleRel adj le_rfl infAx).1 h)

/-- The reduction of `x₀ = x₀` has a finite model. -/
example : Sentence.FinSat (Sentence.singleRel adj (.equal 0 0)) :=
  (Sentence.finSat_singleRel adj le_rfl _).2 finSat_equal

/-! ### The headline theorems for the language of graphs -/

/-- **Trakhtenbrot's theorem** for the language of graphs. -/
example : ¬ComputablePred (Sentence.FinSat (L := Language.graph)) :=
  Sentence.not_computablePred_finSat adj le_rfl

/-- Finite satisfiability of graph sentences is r.e. -/
example : REPred (Sentence.FinSat (L := Language.graph)) := Sentence.rePred_finSat

/-- Finite validity of graph sentences is not r.e. -/
example : ¬REPred (Sentence.FinValid (L := Language.graph)) :=
  Sentence.not_rePred_finValid adj le_rfl

/-! ### A finite relational language whose only relation symbol is ternary -/

/-- Relation symbols of `ternaryLang`: a single ternary symbol `rel3` and no symbols of any other
arity. -/
inductive TernaryRel : ℕ → Type
  | rel3 : TernaryRel 3
  deriving DecidableEq

/-- The relational language with a single ternary relation symbol and no binary, unary or nullary
symbols. -/
def ternaryLang : Language := ⟨fun _ => Empty, TernaryRel⟩
  deriving Language.IsRelational

/-- The single ternary relation symbol of `ternaryLang`. -/
abbrev rel3 : ternaryLang.Relations 3 := .rel3

/-- `ternaryLang` has no relation symbols of arity other than `3` (in particular no binary
symbol). -/
example (l : ℕ) (hl : l ≠ 3) : IsEmpty (ternaryLang.Relations l) :=
  ⟨fun r => by cases r; exact hl rfl⟩

example : IsEmpty (ternaryLang.Relations 2) := ⟨fun r => nomatch r⟩

/-- Equivalence of `ternaryLang` relation symbols with `Unit`. -/
def ternarySymbols : (Σ l, ternaryLang.Relations l) ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨3, .rel3⟩
  left_inv := fun ⟨_, .rel3⟩ => rfl
  right_inv := fun _ => rfl

instance : Encodable (Σ l, ternaryLang.Relations l) := Encodable.ofEquiv Unit ternarySymbols

instance : Finite (Σ l, ternaryLang.Relations l) := .of_equiv Unit ternarySymbols.symm

/-- Diagonal irreflexivity `∀ x, ¬R(x, x, x)` in `ternaryLang`. -/
def irrefl3 : ternaryLang.Sentence :=
  ∀' ∼(BoundedFormula.rel rel3 ![&0, &0, &0])

/-- The one-point empty ternary structure. -/
@[instance_reducible]
def emptyTernary : ternaryLang.Structure Unit where
  RelMap _ _ := False

/-- The one-point full ternary structure. -/
@[instance_reducible]
def fullTernary : ternaryLang.Structure Unit where
  RelMap _ _ := True

example : Sentence.FinSat irrefl3 := by
  refine ⟨Unit, emptyTernary, inferInstance, inferInstance, ?_⟩
  simp only [irrefl3, Sentence.Realize, Formula.Realize, realize_all, realize_not]
  exact fun _ h => h

example : ¬Sentence.FinValid irrefl3 := fun h => by
  have := @h Unit fullTernary _ _
  simp only [irrefl3, Sentence.Realize, Formula.Realize, realize_all, realize_not] at this
  exact this () trivial

/-- The ternary reduction of the axiom of infinity has no finite model. -/
example : ¬Sentence.FinSat (Sentence.singleRel rel3 infAx) :=
  fun h => not_finSat_infAx ((Sentence.finSat_singleRel rel3 (by decide) infAx).1 h)

/-- The ternary reduction of `x₀ = x₀` has a finite model. -/
example : Sentence.FinSat (Sentence.singleRel rel3 (.equal 0 0)) :=
  (Sentence.finSat_singleRel rel3 (by decide) _).2 finSat_equal

/-- **Trakhtenbrot's theorem** for a language whose only relation symbol has arity `3`. -/
example : ¬ComputablePred (Sentence.FinSat (L := ternaryLang)) :=
  Sentence.not_computablePred_finSat rel3 (by decide)

/-- Finite satisfiability of `ternaryLang` sentences is r.e. -/
example : REPred (Sentence.FinSat (L := ternaryLang)) := Sentence.rePred_finSat

/-- Finite validity of `ternaryLang` sentences is not r.e. -/
example : ¬REPred (Sentence.FinValid (L := ternaryLang)) :=
  Sentence.not_rePred_finValid rel3 (by decide)

/-- Finite validity of `ternaryLang` sentences is undecidable. -/
example : ¬ComputablePred (Sentence.FinValid (L := ternaryLang)) :=
  Sentence.not_computablePred_finValid rel3 (by decide)

/-! ### Independence of the symbol encoding -/

/-- Another encoding of the symbols, giving `adj` the code `5`. -/
@[instance_reducible]
def otherEncoding : Encodable (Σ l, Language.graph.Relations l) :=
  Encodable.ofLeftInjection (fun _ => 5) (fun n => if n = 5 then some ⟨2, .adj⟩ else none)
    fun ⟨_, .adj⟩ => rfl

/-- The two codings of graph sentences are primitive recursively equivalent. -/
example : @Primrec _ _ primcodableRaw (@primcodableRaw _ _ 0 _ otherEncoding _ _)
    (id : Language.graph.Sentence → _) :=
  primrec_id_primcodableRaw _ otherEncoding

end Cslib.Tests.TrakhtenbrotSentence
