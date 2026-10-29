/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Reduction
public import Complexity.Logics.FirstOrder.Tuple
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.GetD
import Complexity.Foundations.Data.List.Lookup

/-!
# Binary encodings of finite relational structures

A finite structure is given to a machine as a bit string. Fix a **vocabulary**
(`Cslib.Logic.Vocabulary`): a relational language `L` together with an enumeration of its relation
symbols, which fixes the order of their truth tables. A finite `L`-structure `M` is encoded, along
a numbering `e : M ≃ Fin n` of its elements, as its cardinality `n` followed by one truth table per
relation symbol (`Cslib.Logic.Vocabulary.encode`): the table of a symbol of arity `k` lists the
truth values of the relation on the `n ^ k` tuples of `Fin n`, in the order of their index
`Cslib.Logic.tupleIndex`, the order of `finFunctionFinEquiv`. The cardinality is written in unary
and the tables as raw bit strings, framed as a pair and a list
(`Cslib.Logic.encStructure`), so that the input has polynomial length in the number of
tuples and polynomial-time programs can read its components.

Conversely, every input `(n, tables)` decodes to an `L`-structure on `Fin n`
(`Cslib.Logic.Vocabulary.decode`), a missing table entry reading as false. The input is **well
formed** (`Cslib.Logic.Vocabulary.WellFormed`) when it has exactly one table of the right length
per symbol; the well-formed inputs are exactly the encodings of their decoded structures
(`Cslib.Logic.Vocabulary.wellFormed_iff`). The empty structure, `n = 0`, is included: its tables
are empty except for those of nullary symbols, which hold a single truth value.

The **query language** of a class `K` of finite structures (`Cslib.Logic.Vocabulary.queryLanguage`)
is the set of well-formed inputs whose decoded structure belongs to `K`; malformed inputs never
belong to it. When `K` is closed under isomorphism, whether an encoding of `M` belongs to the
query language does not depend on the numbering (`Cslib.Logic.Vocabulary.mem_queryLanguage_encode`).
This is the convention of [Immerman, Section 2.1][Immerman1999] and
[Fagin, Section 3][Fagin1974], with the order of tuples and the treatment of malformed inputs
spelled out.

## Main definitions

* `Cslib.Logic.Vocabulary`, `Cslib.Logic.Vocabulary.index`, `Cslib.Logic.Vocabulary.arity`,
  `Cslib.Logic.Vocabulary.maxArity`: an enumeration of the relation symbols of a language, with
  their indices, arities, and a positive upper bound on their arities.
* `Cslib.Logic.EncodedStructure`, `Cslib.Logic.encStructure`, `Cslib.Logic.Vocabulary.table`:
  inputs, their binary encoding, and relation table lookup.
* `Cslib.Logic.Vocabulary.decode`, `Cslib.Logic.Vocabulary.decoded`,
  `Cslib.Logic.Vocabulary.WellFormed`, `Cslib.Logic.Vocabulary.checkShape`,
  `Cslib.Logic.Vocabulary.relTable`, `Cslib.Logic.Vocabulary.encode`: decoding, well-formedness and
  its check, and encoding along a numbering.
* `Cslib.Logic.Vocabulary.queryLanguage`: the inputs encoding the members of a class.

## Main results

* `Cslib.Logic.Vocabulary.encode_congr`: encodings agree when a size cast preserves every
  relation.
* `Cslib.Logic.Vocabulary.decodeEncodeEquiv`: decoding an encoding of `M` gives a structure
  isomorphic to `M`.
* `Cslib.Logic.Vocabulary.wellFormed_iff`: an input is well formed exactly when it is the
  encoding of its decoded structure.
* `Cslib.Logic.Vocabulary.mem_queryLanguage_encode`: for a class closed under isomorphism, an
  encoding of `M` belongs to the query language exactly when `M` belongs to the class.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v

open FirstOrder Language Structure CategoryTheory Turing.MultiTapeTM

namespace Cslib.Logic

/-! ### Vocabularies and inputs -/

/-- A **vocabulary**: an enumeration of the relation symbols of a language, with their arities.
It fixes the order of the truth tables in encoded structures. -/
structure Vocabulary (L : Language.{u, v}) where
  /-- The number of relation symbols. -/
  count : ℕ
  /-- The enumeration of the relation symbols. -/
  symbol : Fin count ≃ Σ n, L.Relations n

/-- An input over finite structures: a cardinality and a list of truth tables. -/
abbrev EncodedStructure : Type := ℕ × List (List Bool)

/-- The binary encoding of inputs: the cardinality in unary, then the framed list of raw truth
tables. -/
abbrev encStructure : EncodedStructure ↪ List Bool :=
  encPair encUnary (encList encBits)

/-- The cardinality is at most the length of the encoded input. -/
theorem card_le_length_encStructure (a : EncodedStructure) : a.1 ≤ (encStructure a).length := by
  simp only [encStructure, length_encPair, encUnary_apply, List.length_replicate]
  omega

namespace Vocabulary

variable {L : Language.{u, v}} (v : Vocabulary L)

/-- The position of the table of a relation symbol. -/
def index (r : Σ n, L.Relations n) : ℕ :=
  v.symbol.symm r

/-- The table index of any relation symbol `r` is strictly less than `v.count`. -/
theorem index_lt (r : Σ n, L.Relations n) : v.index r < v.count :=
  (v.symbol.symm r).2

/-- The arity of the relation symbol at a position. -/
def arity (i : Fin v.count) : ℕ :=
  (v.symbol i).1

/-- One more than the largest relation arity of `v`: a positive upper bound on all relation
arities of `v`. -/
def maxArity : ℕ :=
  Finset.univ.sup v.arity + 1

theorem one_le_maxArity : 1 ≤ v.maxArity :=
  Nat.le_add_left 1 _

theorem arity_le_maxArity (i : Fin v.count) : v.arity i ≤ v.maxArity :=
  (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_add_right _ 1)

/-- The truth table of a relation symbol in an input, empty if the input has none. -/
def table (a : EncodedStructure) (r : Σ n, L.Relations n) : List Bool :=
  a.2.getD (v.index r) []

/-! ### Decoding -/

/-- The structure decoded from an input: a relation holds of a tuple when its table has `true` at
the index of the tuple; a missing entry reads as false. -/
@[instance_reducible]
def decode [L.IsRelational] (a : EncodedStructure) : L.Structure (Fin a.1) where
  funMap f := isEmptyElim f
  RelMap r x := (v.table a ⟨_, r⟩).getD (tupleIndex x) false = true

/-- In the decoded structure `v.decode a`, relation `r` holds on `x` iff its truth table has
`true` at `tupleIndex x`. -/
theorem relMap_decode [L.IsRelational] (a : EncodedStructure) {n : ℕ} (r : L.Relations n)
    (x : Fin n → Fin a.1) :
    (v.decode a).RelMap r x ↔ (v.table a ⟨_, r⟩).getD (tupleIndex x) false = true :=
  Iff.rfl

/-- The decoded structure, bundled. -/
def decoded [L.IsRelational] (a : EncodedStructure) : Bundled.{0} L.Structure :=
  ⟨Fin a.1, v.decode a⟩

/-- An input is **well formed** when it has exactly one table per relation symbol, of length the
number of tuples of the arity of the symbol. -/
def WellFormed (a : EncodedStructure) : Prop :=
  a.2.length = v.count ∧ ∀ i : Fin v.count, (a.2.getD i []).length = a.1 ^ v.arity i

/-- The program checking that an input is well formed. -/
def checkShape (a : EncodedStructure) : Bool :=
  (a.2.length == v.count) && (List.finRange v.count).all fun i =>
    (a.2.getD i []).length == a.1 ^ v.arity i

/-- `v.checkShape a` returns `true` if and only if `v.WellFormed a` holds. -/
theorem checkShape_eq_true_iff (a : EncodedStructure) : v.checkShape a = true ↔ v.WellFormed a := by
  simp [checkShape, WellFormed]

/-- Decidability of `v.WellFormed a` via `v.checkShape a`. -/
instance (a : EncodedStructure) : Decidable (v.WellFormed a) :=
  decidable_of_iff _ (v.checkShape_eq_true_iff a)

/-- In a well-formed input `a`, the table for a relation symbol `r` of arity `r.1` has length
`a.1 ^ r.1`. -/
theorem WellFormed.length_table {a : EncodedStructure} (h : v.WellFormed a)
    (r : Σ n, L.Relations n) : (v.table a r).length = a.1 ^ r.1 := by
  have := h.2 (v.symbol.symm r)
  simpa [table, index, arity] using this

/-! ### Encoding -/

open scoped Classical in
/-- The truth table of a relation on a numbered finite structure: the truth values on all tuples,
in the order of their index. -/
noncomputable def relTable (M : Type) [L.Structure M] {n : ℕ} (e : M ≃ Fin n)
    (r : Σ k, L.Relations k) : List Bool :=
  List.ofFn fun i : Fin (n ^ r.1) => decide (RelMap r.2 (e.symm ∘ finFunctionFinEquiv.symm i))

/-- The encoding of a finite structure along a numbering of its elements: the cardinality and
the truth tables of the relation symbols, in the order of the vocabulary. -/
noncomputable def encode (M : Type) [L.Structure M] {n : ℕ} (e : M ≃ Fin n) : EncodedStructure :=
  (n, List.ofFn fun i : Fin v.count => relTable M e (v.symbol i))

variable {v}

/-- The truth table `relTable M e r` of a relation of arity `r.1` over `Fin n` has length
`n ^ r.1`. -/
theorem length_relTable (M : Type) [L.Structure M] {n : ℕ} (e : M ≃ Fin n)
    (r : Σ k, L.Relations k) : (relTable M e r).length = n ^ r.1 := by
  simp [relTable]

open scoped Classical in
/-- Looking up `tupleIndex x` in `relTable M e ⟨k, r⟩` yields `true` iff `RelMap r (e.symm ∘ x)`
holds in `M`. -/
theorem getD_relTable_eq_true_iff (M : Type) [L.Structure M] {n : ℕ} (e : M ≃ Fin n) {k : ℕ}
    (r : L.Relations k) (x : Fin k → Fin n) :
    (relTable M e ⟨k, r⟩).getD (tupleIndex x) false = true ↔ RelMap r (e.symm ∘ x) := by
  rw [relTable, List.getD_ofFn_of_lt _ (tupleIndex_lt x), decide_eq_true_eq]
  simp only [tupleIndex]
  rw [Fin.eta, finFunctionFinEquiv.symm_apply_apply x]

/-- In `v.encode M e`, the table associated to relation symbol `r` is `relTable M e r`. -/
theorem table_encode (M : Type) [L.Structure M] {n : ℕ} (e : M ≃ Fin n)
    (r : Σ k, L.Relations k) : v.table (v.encode M e) r = relTable M e r := by
  rw [table, encode, List.getD_ofFn_of_lt _ (v.index_lt r)]
  simp [index]

/-- Encodings are well formed. -/
theorem wellFormed_encode (M : Type) [L.Structure M] {n : ℕ} (e : M ≃ Fin n) :
    v.WellFormed (v.encode M e) := by
  refine ⟨by simp [encode], fun i => ?_⟩
  rw [encode, List.getD_ofFn]
  simp [arity, length_relTable]

variable (v) in
/-- Encodings agree when the numberings have equal sizes and the size cast preserves every
relation. -/
theorem encode_congr {M N : Type} [L.Structure M] [L.Structure N] {m n : ℕ} (e₁ : M ≃ Fin m)
    (e₂ : N ≃ Fin n) (h : m = n)
    (hrel : ∀ {r} (R : L.Relations r) (x : Fin r → Fin m),
      RelMap R (e₁.symm ∘ x) ↔ RelMap R (e₂.symm ∘ Fin.cast h ∘ x)) :
    v.encode M e₁ = v.encode N e₂ := by
  subst h
  simp only [encode, relTable]
  congr 2
  funext i
  congr 1
  funext j
  exact decide_eq_decide.mpr (hrel _ _)

/-- The structure decoded from an encoding of `M` interprets a relation of the tuples numbering
the elements related in `M`. -/
theorem relMap_decode_encode [L.IsRelational] (M : Type) [L.Structure M] {n : ℕ} (e : M ≃ Fin n)
    {k : ℕ} (r : L.Relations k) (x : Fin k → Fin n) :
    (v.decode (v.encode M e)).RelMap r x ↔ RelMap r (e.symm ∘ x) := by
  change (v.table (v.encode M e) ⟨_, r⟩).getD (tupleIndex x) false = true ↔ _
  rw [table_encode]
  exact getD_relTable_eq_true_iff M e r x

/-- **Decoding an encoding** of `M` along `e` gives a structure isomorphic to `M`, by `e`. -/
def decodeEncodeEquiv [L.IsRelational] (M : Type) [L.Structure M] {n : ℕ} (e : M ≃ Fin n) :
    letI := v.decode (v.encode M e); M ≃[L] Fin (v.encode M e).1 :=
  letI := v.decode (v.encode M e)
  { toEquiv := e
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun r x =>
      (relMap_decode_encode M e r (e ∘ x)).trans (by simp [Function.comp_def]) }

/-- An input is well formed exactly when it is the encoding of its decoded structure, numbered
by itself. -/
theorem wellFormed_iff [L.IsRelational] (a : EncodedStructure) :
    v.WellFormed a ↔ @encode L v (Fin a.1) (v.decode a) a.1 (Equiv.refl _) = a := by
  constructor
  · rintro ⟨hlen, htab⟩
    refine Prod.ext rfl (List.ext_getElem (by simp [encode, hlen]) fun i hi hi' => ?_)
    have hi₀ : i < v.count := by simpa [encode] using hi
    have htab' := htab ⟨i, hi₀⟩
    rw [List.getD_eq_getElem _ _ hi'] at htab'
    simp only [encode, List.getElem_ofFn]
    refine List.ext_getElem (by simp [length_relTable, htab', arity]) fun j hj hj' => ?_
    simp only [relTable, List.getElem_ofFn]
    rw [show a.2[i][j] = decide (a.2[i][j] = true) from Bool.decide_eq_true.symm,
      decide_eq_decide, relMap_decode, table, index, Sigma.eta, Equiv.symm_apply_apply,
      List.getD_eq_getElem _ _ hi']
    simp only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp, tupleIndex_symm,
      List.getD_eq_getElem _ _ hj']
  · intro h
    have := @wellFormed_encode L v (Fin a.1) (v.decode a) a.1 (Equiv.refl _)
    rwa [h] at this

/-! ### Query languages -/

variable (v)

/-- The **query language** of a class `K` of finite structures: the well-formed inputs whose
decoded structure belongs to `K`. Malformed inputs never belong to it. -/
def queryLanguage [L.IsRelational] (K : Set (Bundled.{0} L.Structure)) : Set EncodedStructure :=
  {a | v.WellFormed a ∧ v.decoded a ∈ K}

variable {v}

/-- An input `a` belongs to `v.queryLanguage K` iff `v.WellFormed a` and `v.decoded a ∈ K`. -/
theorem mem_queryLanguage [L.IsRelational] {K : Set (Bundled.{0} L.Structure)}
    {a : EncodedStructure} : a ∈ v.queryLanguage K ↔ v.WellFormed a ∧ v.decoded a ∈ K :=
  Iff.rfl

/-- For a well-formed input `a`, `a ∈ v.queryLanguage K` iff `v.decoded a ∈ K`. -/
theorem WellFormed.mem_queryLanguage_iff [L.IsRelational] {K : Set (Bundled.{0} L.Structure)}
    {a : EncodedStructure} (h : v.WellFormed a) : a ∈ v.queryLanguage K ↔ v.decoded a ∈ K :=
  and_iff_right h

/-- For a class closed under isomorphism, an encoding of `M` belongs to the query language exactly
when `M` belongs to the class, whatever the numbering. -/
theorem mem_queryLanguage_encode [L.IsRelational] {K : Set (Bundled.{0} L.Structure)}
    (hK : IsoClosed K) (M : Type) [L.Structure M] {n : ℕ} (e : M ≃ Fin n) :
    v.encode M e ∈ v.queryLanguage K ↔ (Bundled.of M : Bundled.{0} L.Structure) ∈ K := by
  have : Finite M := Finite.of_equiv _ e.symm
  rw [(wellFormed_encode M e).mem_queryLanguage_iff]
  exact (@hK (Bundled.of M) (v.decoded (v.encode M e)) this (decodeEncodeEquiv M e)).symm

end Vocabulary

end Cslib.Logic
