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

/-! # Trakhtenbrot's theorem and the monadic dichotomy for Mathlib sentences: checked instances

The raw coding of sentences in the language of graphs: a computed raw formula, quantifier rank via
raw quantifier depth, decoding of a well-scoped code, rejection of ill-scoped codes (wrong binder,
out-of-scope bound name, free name, unknown symbol, wrong arity), the level-naming of a raw
sentence, a finitely satisfiable and a finitely valid sentence on both sides of the translation, the
reduction on a finitely satisfiable formula and on the axiom of infinity, the headline theorems for
both the language of graphs and a ternary-only relational language, and a monadic language with both
unary and nullary relation symbols witnessing the positive half and both directions of the
Trakhtenbrot–Löwenheim dichotomy (including the rank-`0` and size-`2 ^ k` small-model cases). -/

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

/-- Raw quantifier depth computes sentence quantifier rank. -/
example : quantifierRank symm = 2 := by rw [← quantifierDepth_toRaw]; decide
example : quantifierRank irrefl = 1 := by rw [← quantifierDepth_toRaw]; decide

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

/-! ### A monadic language with unary and nullary symbols, and the dichotomy -/

/-- Relation symbols of `monadicLang`: one nullary symbol `flag` and two unary symbols `p0`,
`p1`. -/
inductive MonadicRel : ℕ → Type
  | flag : MonadicRel 0
  | p0 : MonadicRel 1
  | p1 : MonadicRel 1
  deriving DecidableEq

/-- A finite monadic relational language containing both unary symbols (`p0`, `p1`) and a nullary
symbol (`flag`). -/
def monadicLang : Language := ⟨fun _ => Empty, MonadicRel⟩
  deriving Language.IsRelational

/-- The nullary relation symbol of `monadicLang`. -/
abbrev flag : monadicLang.Relations 0 := .flag

/-- The first unary relation symbol of `monadicLang`. -/
abbrev p0 : monadicLang.Relations 1 := .p0

/-- The second unary relation symbol of `monadicLang`. -/
abbrev p1 : monadicLang.Relations 1 := .p1

/-- Every relation symbol of `monadicLang` has arity at most `1`. -/
theorem monadicLang_monadic : ∀ l, 2 ≤ l → IsEmpty (monadicLang.Relations l) :=
  fun _ hl => ⟨fun r => by cases r <;> omega⟩

/-- Equivalence of `monadicLang` relation symbols with `Fin 3`. -/
def monadicSymbols : (Σ l, monadicLang.Relations l) ≃ Fin 3 where
  toFun
    | ⟨_, .flag⟩ => 0
    | ⟨_, .p0⟩ => 1
    | ⟨_, .p1⟩ => 2
  invFun
    | ⟨0, _⟩ => ⟨0, .flag⟩
    | ⟨1, _⟩ => ⟨1, .p0⟩
    | ⟨_ + 2, _⟩ => ⟨1, .p1⟩
  left_inv := fun ⟨_, r⟩ => by cases r <;> rfl
  right_inv := fun ⟨i, hi⟩ => by
    rcases i with _ | _ | _ | i
    · rfl
    · rfl
    · rfl
    · omega

instance : Encodable (Σ l, monadicLang.Relations l) := Encodable.ofEquiv (Fin 3) monadicSymbols

instance : Finite (Σ l, monadicLang.Relations l) := .of_equiv (Fin 3) monadicSymbols.symm

/-- Equivalence of the unary relation symbols of `monadicLang` with `Bool`. -/
def monadicUnary : monadicLang.Relations 1 ≃ Bool where
  toFun
    | .p0 => false
    | .p1 => true
  invFun
    | false => .p0
    | true => .p1
  left_inv := fun r => by cases r <;> rfl
  right_inv := fun b => by cases b <;> rfl

instance : Finite (monadicLang.Relations 1) := .of_equiv Bool monadicUnary.symm

theorem card_monadicLang_unary : Nat.card (monadicLang.Relations 1) = 2 := by
  rw [Nat.card_congr monadicUnary]
  simp

/-- The rank-`0` sentence consisting of the nullary relation symbol `flag`. -/
def flagSentence : monadicLang.Sentence := BoundedFormula.rel flag ![]

theorem quantifierRank_flagSentence : quantifierRank flagSentence = 0 := by
  rw [← quantifierDepth_toRaw]
  decide

/-- Without `max (quantifierRank _) 1`, the bound `q * 2 ^ k` vanishes at rank `0`, leaving no
candidate size `n < 0`. -/
example : ¬∃ n < quantifierRank flagSentence * 2 ^ Nat.card (monadicLang.Relations 1),
    RawFormula.SatOnFin n flagSentence.toRaw := by
  simp [quantifierRank_flagSentence]

/-- One-point `monadicLang`-structure where `flag` holds. -/
@[instance_reducible]
def flagTrueStruct : monadicLang.Structure (Fin 1) where
  RelMap
    | .flag, _ => True
    | _, _ => False

/-- One-point `monadicLang`-structure where `flag` fails. -/
@[instance_reducible]
def flagFalseStruct : monadicLang.Structure (Fin 1) where
  RelMap _ _ := False

theorem satOnFin_zero_flagSentence : RawFormula.SatOnFin 0 flagSentence.toRaw :=
  (Sentence.exists_structure_fin_realize_iff_satOnFin 0 flagSentence).1 ⟨flagTrueStruct, trivial⟩

theorem finSat_flagSentence : Sentence.FinSat flagSentence :=
  (Sentence.finSat_iff_exists_lt_satOnFin monadicLang_monadic flagSentence).2
    ⟨0, by rw [quantifierRank_flagSentence, card_monadicLang_unary]; decide,
      satOnFin_zero_flagSentence⟩

theorem not_finValid_flagSentence : ¬Sentence.FinValid flagSentence :=
  fun h => @h (Fin 1) flagFalseStruct inferInstance inferInstance

/-- Rank-`1` sentence requiring all four unary `(p0, p1)` color combinations to occur. -/
def allFourColors : monadicLang.Sentence :=
  ((∃' (p0.boundedFormula₁ &0 ⊓ p1.boundedFormula₁ &0)) ⊓
    (∃' (p0.boundedFormula₁ &0 ⊓ ∼(p1.boundedFormula₁ &0)))) ⊓
  ((∃' (∼(p0.boundedFormula₁ &0) ⊓ p1.boundedFormula₁ &0)) ⊓
    (∃' (∼(p0.boundedFormula₁ &0) ⊓ ∼(p1.boundedFormula₁ &0))))

theorem quantifierRank_allFourColors : quantifierRank allFourColors = 1 := by
  rw [← quantifierDepth_toRaw]
  decide

/-- `allFourColors` has no model on `Fin 3` (`n = 2`), since four mutually exclusive unary types
cannot fit in three elements. -/
theorem not_satOnFin_two_allFourColors : ¬RawFormula.SatOnFin 2 allFourColors.toRaw := by
  intro h
  obtain ⟨S, hS⟩ := (Sentence.exists_structure_fin_realize_iff_satOnFin 2 allFourColors).2 h
  simp only [allFourColors, Sentence.Realize, Formula.Realize, realize_inf, realize_ex,
    realize_not, realize_rel₁] at hS
  obtain ⟨⟨⟨a, ha0, ha1⟩, ⟨b, hb0, hb1⟩⟩, ⟨⟨c, hc0, hc1⟩, ⟨d, hd0, hd1⟩⟩⟩ := hS
  have hab : a.val ≠ b.val := fun heq => hb1 (Fin.ext heq ▸ ha1)
  have hac : a.val ≠ c.val := fun heq => hc0 (Fin.ext heq ▸ ha0)
  have had : a.val ≠ d.val := fun heq => hd0 (Fin.ext heq ▸ ha0)
  have hbc : b.val ≠ c.val := fun heq => hc0 (Fin.ext heq ▸ hb0)
  have hbd : b.val ≠ d.val := fun heq => hd0 (Fin.ext heq ▸ hb0)
  have hcd : c.val ≠ d.val := fun heq => hd1 (Fin.ext heq ▸ hc1)
  omega

/-- Four-element `monadicLang`-structure realizing all four `(p0, p1)` combinations. -/
@[instance_reducible]
def fourColorStruct : monadicLang.Structure (Fin 4) where
  RelMap
    | .flag, _ => False
    | .p0, xs => (xs 0).val / 2 = 1
    | .p1, xs => (xs 0).val % 2 = 1

/-- `allFourColors` holds on `Fin 4` (`n = 3`), attaining `max 1 1 * 2 ^ 2 = 4`. -/
theorem satOnFin_three_allFourColors : RawFormula.SatOnFin 3 allFourColors.toRaw := by
  refine (Sentence.exists_structure_fin_realize_iff_satOnFin 3 allFourColors).1
    ⟨fourColorStruct, ?_⟩
  simp only [allFourColors, Sentence.Realize, Formula.Realize, realize_inf, realize_ex,
    realize_not, realize_rel₁]
  refine ⟨⟨⟨3, ?_, ?_⟩, ⟨2, ?_, ?_⟩⟩, ⟨⟨1, ?_, ?_⟩, ⟨0, ?_, ?_⟩⟩⟩
  · exact (rfl : (3 : Fin 4).val / 2 = 1)
  · exact (rfl : (3 : Fin 4).val % 2 = 1)
  · exact (rfl : (2 : Fin 4).val / 2 = 1)
  · exact fun (h : (2 : Fin 4).val % 2 = 1) => by omega
  · exact fun (h : (1 : Fin 4).val / 2 = 1) => by omega
  · exact (rfl : (1 : Fin 4).val % 2 = 1)
  · exact fun (h : (0 : Fin 4).val / 2 = 1) => by omega
  · exact fun (h : (0 : Fin 4).val % 2 = 1) => by omega

example : Sentence.FinSat allFourColors :=
  (Sentence.finSat_iff_exists_lt_satOnFin monadicLang_monadic allFourColors).2
    ⟨3, by rw [quantifierRank_allFourColors, card_monadicLang_unary]; decide,
      satOnFin_three_allFourColors⟩

/-- Positive half of the dichotomy on `monadicLang`: `FinSat` and `FinValid` are primitive
recursive, decidable, and r.e. -/
example : PrimrecPred (Sentence.FinSat (L := monadicLang)) :=
  Sentence.primrecPred_finSat_of_monadic monadicLang_monadic

example : ComputablePred (Sentence.FinSat (L := monadicLang)) :=
  Sentence.computablePred_finSat_iff.2 monadicLang_monadic

example : PrimrecPred (Sentence.FinValid (L := monadicLang)) :=
  Sentence.primrecPred_finValid_of_monadic monadicLang_monadic

example : ComputablePred (Sentence.FinValid (L := monadicLang)) :=
  Sentence.computablePred_finValid_iff.2 monadicLang_monadic

example : REPred (Sentence.FinValid (L := monadicLang)) :=
  Sentence.rePred_finValid_iff.2 monadicLang_monadic

example : REPred (fun φ : monadicLang.Sentence => ¬Sentence.FinSat φ) :=
  Sentence.rePred_not_finSat_iff.2 monadicLang_monadic

/-- Forward (contrapositive) direction of the dichotomy on `Language.graph` and `ternaryLang`. -/
theorem not_monadic_graph : ¬∀ l, 2 ≤ l → IsEmpty (Language.graph.Relations l) :=
  fun h => (h 2 le_rfl).false adj

example : ¬ComputablePred (Sentence.FinSat (L := Language.graph)) :=
  mt Sentence.computablePred_finSat_iff.1 not_monadic_graph

example : ¬ComputablePred (Sentence.FinValid (L := Language.graph)) :=
  mt Sentence.computablePred_finValid_iff.1 not_monadic_graph

example : ¬REPred (Sentence.FinValid (L := Language.graph)) :=
  mt Sentence.rePred_finValid_iff.1 not_monadic_graph

example : ¬REPred (fun φ : Language.graph.Sentence => ¬Sentence.FinSat φ) :=
  mt Sentence.rePred_not_finSat_iff.1 not_monadic_graph

theorem not_monadic_ternaryLang : ¬∀ l, 2 ≤ l → IsEmpty (ternaryLang.Relations l) :=
  fun h => (h 3 (by decide)).false rel3

example : ¬ComputablePred (Sentence.FinSat (L := ternaryLang)) :=
  mt Sentence.computablePred_finSat_iff.1 not_monadic_ternaryLang

example : ¬ComputablePred (Sentence.FinValid (L := ternaryLang)) :=
  mt Sentence.computablePred_finValid_iff.1 not_monadic_ternaryLang

example : ¬REPred (Sentence.FinValid (L := ternaryLang)) :=
  mt Sentence.rePred_finValid_iff.1 not_monadic_ternaryLang

example : ¬REPred (fun φ : ternaryLang.Sentence => ¬Sentence.FinSat φ) :=
  mt Sentence.rePred_not_finSat_iff.1 not_monadic_ternaryLang

end Cslib.Tests.TrakhtenbrotSentence
