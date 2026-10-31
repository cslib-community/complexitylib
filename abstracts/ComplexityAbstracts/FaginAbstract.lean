/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import ComplexityAbstracts.FaginBridge

/-! # Fagin's theorem

An existential second-order sentence guesses finite relations and then checks a first-order
condition. Fagin's theorem says that this is exactly polynomial-time verification for properties
of finite structures that do not depend on how their elements are named. The guessed relations
can describe an accepting computation, with local consistency enforced by the formula.
Conversely, their truth tables have polynomial size and a fixed first-order condition can be
checked in polynomial time.

The vocabulary is finite and relational, with no function symbols or built-in order. Universe
size is encoded in unary, followed by framed relation truth tables; incorrect table shapes are
excluded from the query language. Empty and singleton universes and nullary relations are included.

Lean checks the explicit logical and computational correspondence through the bridge, and
`#check_abstract` audits the public dependency boundary.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

namespace ComplexityTests.Abstracts.FaginAbstract

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

/-! ## Efficient verification

`Computation.PolyTimeVerifier enc V` means one deterministic verifier running in polynomial
time in the combined encoded length of its instance and certificate, on every such pair.
The fixed certificate length is the polynomial `p` evaluated at the instance bit length.
The machine and encoding conventions are collected in the foundations appendix.
-/

/-- NP consists of problems with a polynomial-time deterministic verifier and binary
certificates of an exact polynomial length. The verifier halts on every input pair. -/
def NP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    Computation.PolyTimeVerifier enc V ∧
    ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true}

/-- Parsed input data: cardinality and one Boolean truth table for each relation symbol. -/
abbrev Input := ℕ × List (List Bool)

/-! ## Representation details

An input gives the universe size in unary and one truth table per relation symbol. Unary size
ensures that input length is at least the universe size, even for an empty vocabulary.
A `CategoryTheory.Bundled L.Structure` is simply a universe together with an interpretation
of the symbols of `L`. The decoder below uses the universe `Fin a.1`.
-/

/-- Encode the unary cardinality and the framed list of relation truth tables. -/
def encInput : Input ↪ List Bool :=
  Encoding.encPair Encoding.encUnary (Encoding.encList Encoding.encBits)

/-- Decode input data according to a finite enumeration of all relation symbols, with arities.
The first tuple coordinate is least significant (`finFunctionFinEquiv`); missing entries read
false. The theorem's query language separately rejects incorrect table sizes. -/
@[instance_reducible] def decode {L : FirstOrder.Language} [L.IsRelational] {count : ℕ}
    (symbols : Fin count ≃ Σ n, L.Relations n) (a : Input) : L.Structure (Fin a.1) where
  funMap f := isEmptyElim f
  RelMap r x := (a.2.getD (symbols.symm ⟨_, r⟩).val []).getD
    (finFunctionFinEquiv x).val false = true

/-! ## The query language -/

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

/-- Over a finite relational vocabulary, ESO-definability is exactly isomorphism closure
on finite structures together with NP membership of the encoded query language. -/
theorem fagin {L : FirstOrder.Language} [L.IsRelational] {count : ℕ}
    (symbols : Fin count ≃ Σ n, L.Relations n) (K : Set (CategoryTheory.Bundled.{0} L.Structure)) :
    ESODefinable K ↔ IsoClosed K ∧ queryLanguage symbols K ∈ NP encInput :=
  FaginBridge.fagin symbols K

/--
info: abstract audit passed for `ComplexityTests.Abstracts.FaginAbstract`:
12 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.FaginAbstract allowing [
  ComplexityAbstracts.Encoding, ComplexityAbstracts.Computation
]

end ComplexityTests.Abstracts.FaginAbstract
