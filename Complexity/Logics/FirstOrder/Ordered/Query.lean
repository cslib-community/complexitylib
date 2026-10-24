/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Encoding
public import Complexity.Logics.FirstOrder.Ordered.Basic

/-!
# Arbitrary canonically ordered queries

An ordered query may depend on the fixed numbering of its input relations. Its source-only
encoding serializes no numeric tables: the canonical numeric vocabulary is supplied by
`Ordered.Basic`. Malformed relation tables and universes of size zero or one are rejected.

## Main definitions

* `Cslib.Logic.FO.Ordered.Structure`: an input structure on `Fin n`, with `n ≥ 2`.
* `Cslib.Logic.FO.Ordered.Query`: arbitrary classes of these structures.
* `Cslib.Logic.FO.Ordered.decoded`, `Cslib.Logic.FO.Ordered.encode`,
  `Cslib.Logic.FO.Ordered.Query.encodedLanguage`: decoding and encoding of ordered structures and
  their source-only encoded languages.
* `Cslib.Logic.FO.Ordered.Definable`: definability by one canonical ordered sentence.

## Main results

* `Cslib.Logic.FO.Ordered.Structure.ext`: equality of ordered structures through a size cast.
* `Cslib.Logic.FO.Ordered.mem_encodedLanguage_encode`: exact canonical encoding membership.

## References

* [N. Immerman, *Descriptive Complexity*, Provisos 1.14–1.15][Immerman1999]
-/

@[expose] public section

universe u v

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language

/-- A finite structure on the canonical universe `{0, …, n - 1}`, with distinct `0` and `1`. -/
structure Structure (L : Language.{u, v}) where
  /-- The size of the universe. -/
  size : ℕ
  /-- Immerman's Boolean-constant proviso. -/
  size_ge_two : 2 ≤ size
  /-- The interpretation of the input symbols. Numeric symbols are supplied separately. -/
  input : L.Structure (Fin size)

/-- Coerce an ordered structure `M` to its canonical carrier `Fin M.size`. -/
instance structureCoeSort {L : Language.{u, v}} : CoeSort (Structure L) Type :=
  ⟨fun M => Fin M.size⟩

/-- Equip `Fin M.size` with the input relations of `M`. -/
instance structureInput {L : Language.{u, v}} (M : Structure L) : L.Structure M := M.input

/-- Record the size bound `2 ≤ M.size` as a `Fact` instance. -/
instance structureSize {L : Language.{u, v}} (M : Structure L) : Fact (2 ≤ M.size) :=
  ⟨M.size_ge_two⟩

/-- Ordered structures over a relational language are equal when their sizes are and the size
cast preserves every relation. -/
theorem Structure.ext {L : Language} [L.IsRelational] {M N : Structure L} (h : M.size = N.size)
    (hrel : ∀ {r} (R : L.Relations r) (x : Fin r → Fin M.size),
      Language.Structure.RelMap R x ↔ Language.Structure.RelMap R (Fin.cast h ∘ x)) : M = N := by
  obtain ⟨m, hm, s⟩ := M
  obtain ⟨n, hn, t⟩ := N
  change m = n at h
  subst h
  congr 1
  apply FirstOrder.Language.Structure.ext
  · funext r f
    exact isEmptyElim f
  · funext r R x
    exact propext (hrel R x)

/-- An ordered query is an arbitrary class of canonically ordered structures. Input relations
need not be invariant under permutations that change the fixed order. -/
abbrev Query (L : Language.{u, v}) := Set (Structure L)

/-- An ordered query is first-order definable if a sentence defines it on every canonical ordered
structure. -/
def Definable {L : Language.{u, v}} (K : Query L) : Prop :=
  ∃ φ : (language L).Sentence, ∀ M : Structure L, M ∈ K ↔ φ.Realize M

/-- Decode a source-only input with a universe of size at least two. -/
def decoded {L : Language} [L.IsRelational] (v : Vocabulary L) (a : EncodedStructure)
    (hn : 2 ≤ a.1) : Structure L := ⟨a.1, hn, v.decode a⟩

/-- The language of an ordered query. Only original relation tables occur in the input;
malformed shapes and universes of size zero or one are rejected. -/
def Query.encodedLanguage {L : Language} [L.IsRelational] (K : Query L) (v : Vocabulary L) :
    Set EncodedStructure := {a | v.WellFormed a ∧ ∃ hn : 2 ≤ a.1, decoded v a hn ∈ K}

/-- Malformed source tables are rejected independently of the query. -/
theorem Query.not_mem_encodedLanguage_of_not_wellFormed {L : Language} [L.IsRelational]
    (K : Query L) (v : Vocabulary L) {a : EncodedStructure} (ha : ¬ v.WellFormed a) :
    a ∉ K.encodedLanguage v := fun h => ha h.1

/-- Universes of size zero or one are rejected independently of the query. -/
theorem Query.not_mem_encodedLanguage_of_lt_two {L : Language} [L.IsRelational]
    (K : Query L) (v : Vocabulary L) {a : EncodedStructure} (ha : a.1 < 2) :
    a ∉ K.encodedLanguage v := fun h => (Nat.not_le_of_gt ha) h.2.choose

/-- The canonical source-only encoding of an ordered structure. -/
noncomputable def encode {L : Language} (v : Vocabulary L) (M : Structure L) : EncodedStructure :=
  v.encode M (Equiv.refl _)

/-- Decoding the canonical encoding returns the same ordered structure. -/
@[simp]
theorem decoded_encode {L : Language} [L.IsRelational] (v : Vocabulary L) (M : Structure L) :
    decoded v (encode v M) M.size_ge_two = M :=
  Structure.ext rfl fun r xs => v.relMap_decode_encode M (Equiv.refl _) r xs

/-- The canonical encoding of an ordered structure is in the encoded language of a query exactly
when the structure is in the query. -/
@[simp]
theorem mem_encodedLanguage_encode {L : Language} [L.IsRelational] (v : Vocabulary L)
    (K : Query L) (M : Structure L) : encode v M ∈ K.encodedLanguage v ↔ M ∈ K := by
  simp only [Query.encodedLanguage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, hn, h⟩
    simpa only [decoded_encode] using h
  · intro h
    exact ⟨v.wellFormed_encode M (Equiv.refl _), M.size_ge_two, by simpa using h⟩

end Cslib.Logic.FO.Ordered
