/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import CslibFrontierAbstracts.SubsetSumBridge
import CslibFrontier.Computability.Complexity.Fagin.Converse

/-! # Fagin transfer with explicit ESO semantics and finite-vocabulary serialization -/

namespace ComplexityTests.Abstracts.FaginBridge

/-- Frame each bit as `[true, b]` and terminate the word with `[false]`. -/
def frame (w : List Bool) : List Bool := w.flatMap (fun b => [true, b]) ++ [false]

/-- Encode a pair by framing its first component and appending its second component. -/
def encodePair {α β : Type} (a : α → List Bool) (b : β → List Bool) (p : α × β) :
    List Bool := frame (a p.1) ++ b p.2

/-- Encode a list by concatenating its framed elements. -/
def encodeList {α : Type} (enc : α → List Bool) (l : List α) : List Bool :=
  l.flatMap (frame ∘ enc)

theorem encodePair_injective {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) :
    Function.Injective (encodePair a b) := CookLevinBridge.encodePair_injective a b

theorem encodeList_injective {α : Type} (enc : α ↪ List Bool) :
    Function.Injective (encodeList enc) := SubsetSumBridge.encodeList_injective enc

/-- Pair encoding; `↪` records injectivity. -/
def encPair {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨encodePair a b, encodePair_injective a b⟩

/-- List encoding. -/
def encList {α : Type} (enc : α ↪ List Bool) : List α ↪ List Bool :=
  ⟨encodeList enc, encodeList_injective enc⟩

/-- A Boolean is encoded by a single bit. -/
def encBool : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; injection h⟩

/-- Bitstrings encode themselves. -/
def encBits : List Bool ↪ List Bool := Function.Embedding.refl _

/-- A single finite-state binary multi-tape machine computes `f` on every encoded input,
within polynomial time and work space. Inputs are read-only; outputs are write-only.
`Cslib.PolynomiallyBounded` means bounded above by some polynomial. -/
def ComputableInPolyTime {α β : Type} (f : α → β)
    (a : α ↪ List Bool) (b : β ↪ List Bool) : Prop :=
  ∃ t s : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f a b t s

/-- NP consists of problems with a polynomial-time deterministic verifier and binary
certificates of an exact polynomial length. The verifier halts on every input pair. -/
def NP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
    ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true}

/-- Relation variables with prescribed arities, used for existential second-order quantifiers.
There are no function symbols; a relation symbol is its index together with its arity equation. -/
def relationVariables {ι : Type} (arity : ι → ℕ) : FirstOrder.Language where
  Functions _ := Empty
  Relations n := {i : ι // arity i = n}

/-- Interpret a relation variable by the chosen relation on the universe. -/
@[instance_reducible] def relationStructure {ι : Type} {arity : ι → ℕ} {M : Type}
    (R : ∀ i, Set (Fin (arity i) → M)) : (relationVariables arity).Structure M where
  funMap f := isEmptyElim (show Empty from f)
  RelMap r x := x ∘ Fin.cast r.2 ∈ R r.1

/-- A class is ESO-definable if one first-order sentence, preceded by finitely many existential
relation quantifiers, defines its members among finite structures. Infinite structures are
outside the contract. Nullary relation variables and the empty universe are permitted. -/
def ESODefinable {L : FirstOrder.Language}
    (K : Set (CategoryTheory.Bundled.{0} L.Structure)) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (arity : ι → ℕ)
    (matrix : (L.sum (relationVariables arity)).Sentence),
    ∀ (M : CategoryTheory.Bundled.{0} L.Structure) [Finite M], M ∈ K ↔
      ∃ R : ∀ i, Set (Fin (arity i) → M), letI := relationStructure R;
        FirstOrder.Language.Sentence.Realize M matrix

/-- Membership is invariant under isomorphism of finite structures. -/
def IsoClosed {L : FirstOrder.Language} (K : Set (CategoryTheory.Bundled.{0} L.Structure)) : Prop :=
  ∀ ⦃M N : CategoryTheory.Bundled.{0} L.Structure⦄ [Finite M],
    (FirstOrder.Language.Equiv L M N) → (M ∈ K ↔ N ∈ K)

/-- Parsed input data: cardinality and one Boolean truth table for each relation symbol. -/
abbrev Input := ℕ × List (List Bool)

/-- An injective encoding of cardinalities in unary. -/
def encUnary : ℕ ↪ List Bool :=
  ⟨fun n => List.replicate n true, by
    intro a b h
    simpa only [List.length_replicate] using congrArg List.length h⟩

/-- Encode the unary cardinality and the framed list of relation truth tables. -/
def encInput : Input ↪ List Bool := encPair encUnary (encList encBits)

/-- Decode input data according to a finite enumeration of all relation symbols, with arities.
The first tuple coordinate is least significant (`finFunctionFinEquiv`); missing entries read
false. The theorem's query language separately rejects incorrect table sizes. -/
@[instance_reducible] def decode {L : FirstOrder.Language} [L.IsRelational] {count : ℕ}
    (symbols : Fin count ≃ Σ n, L.Relations n) (a : Input) : L.Structure (Fin a.1) where
  funMap f := isEmptyElim f
  RelMap r x := (a.2.getD (symbols.symm ⟨_, r⟩).val []).getD
    (finFunctionFinEquiv x).val false = true

/-- Parsed data is well formed when every relation symbol has a table of exactly `n^arity`
bits, including one bit for every nullary relation even when `n=0`. -/
def WellFormed {L : FirstOrder.Language} {count : ℕ}
    (symbols : Fin count ≃ Σ n, L.Relations n) (a : Input) : Prop :=
  a.2.length = count ∧ ∀ i : Fin count, (a.2.getD i.val []).length = a.1 ^ (symbols i).1

/-- The encoded query contains precisely well-formed data whose decoded finite structure
belongs to the class. Incorrect table shapes are excluded. -/
def queryLanguage {L : FirstOrder.Language} [L.IsRelational] {count : ℕ}
    (symbols : Fin count ≃ Σ n, L.Relations n)
    (K : Set (CategoryTheory.Bundled.{0} L.Structure)) : Set Input :=
  {a | WellFormed symbols a ∧
    (⟨Fin a.1, decode symbols a⟩ : CategoryTheory.Bundled L.Structure) ∈ K}

theorem eso_iff {L : FirstOrder.Language} {K : Set (CategoryTheory.Bundled.{0} L.Structure)} :
    ESODefinable K ↔ Cslib.Logic.ESO.Definable K := by
  constructor
  · rintro ⟨ι, hfin, arity, matrix, h⟩
    exact ⟨{ Var := ι, finite := hfin, arity := arity, matrix := matrix }, h⟩
  · rintro ⟨Φ, h⟩
    exact ⟨Φ.Var, Φ.finite, Φ.arity, Φ.matrix, h⟩

theorem fagin {L : FirstOrder.Language} [L.IsRelational] {count : ℕ}
    (symbols : Fin count ≃ Σ n, L.Relations n) (K : Set (CategoryTheory.Bundled.{0} L.Structure)) :
    ESODefinable K ↔ IsoClosed K ∧ queryLanguage symbols K ∈ NP encInput := by
  rw [eso_iff]
  exact (Cslib.Logic.ESO.definable_iff_isoClosed_and_queryLanguage_mem_NP
    ⟨count, symbols⟩).trans (and_congr Iff.rfl CookLevinBridge.mem_NP_iff.symm)

end ComplexityTests.Abstracts.FaginBridge
