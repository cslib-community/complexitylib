/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.DomainInterpretation
public import Complexity.Logics.FirstOrder.Encoding.Layout

/-!
# Encoding ordered interpretations with a domain formula

A well-formed source of size at least two is mapped to the encoding of its image, whose universe
is numbered by the lexicographic rank of the domain tuples. This is defined for every source,
including those with fewer than two domain tuples, whose encoded image has no canonical ordered
decoding. Only the target input relations are serialized; the canonical order, `BIT` and constants
are determined by the cardinality. Malformed sources and sizes zero and one map to the same
malformed target as `FullTupleInterpretation.encodedMap`.

Partial decoding of source-only encodings turns an ordered query language into the set of
encodings that decode to members, and an admissible interpretation commutes with decoding. This is
the simulation hypothesis of `Cslib.Complexity.ManyOneReducibleBy.lift`.

## Main definitions

* `Cslib.Logic.FO.Ordered.decode?`: partial decoding of source-only encodings.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.encodedMap`: the total map on parsed instances.

## Main results

* `Cslib.Logic.FO.Ordered.Query.encodedLanguage_eq`: query languages by partial decoding.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.card_encodedMap`: the number of domain tuples.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.wellFormed_encodedMap_iff`: exact shape guard.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.table_encodedMap`: exact table numbering.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.decode?_encodedMap`: commutation with decoding.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Proviso 1.15 and Definition 1.26.
-/

@[expose] public section

open FirstOrder Language Structure

namespace Cslib.Logic.FO.Ordered

variable {L L' : Language} [L.IsRelational] [L'.IsRelational]

/-- Decode a source-only encoding as a canonically ordered structure, when it is well formed and
has at least two elements. -/
def decode? (v : Vocabulary L) (a : EncodedStructure) : Option (Structure L) :=
  if h : v.WellFormed a ∧ 2 ≤ a.1 then some (decoded v a h.2) else none

/-- A well-formed encoding of size at least two decodes to `some (decoded v a hn)`. -/
theorem decode?_of_admissible (v : Vocabulary L) {a : EncodedStructure} (ha : v.WellFormed a)
    (hn : 2 ≤ a.1) : decode? v a = some (decoded v a hn) :=
  dite_eq_left ⟨ha, hn⟩

/-- An encoding that is not well formed or has size below two decodes to `none`. -/
theorem decode?_of_not_admissible (v : Vocabulary L) {a : EncodedStructure}
    (ha : ¬(v.WellFormed a ∧ 2 ≤ a.1)) : decode? v a = none :=
  dite_eq_right ha

/-- Canonical encodings decode to their structures. -/
@[simp] theorem decode?_encode (v : Vocabulary L) (M : Structure L) :
    decode? v (encode v M) = some M :=
  (decode?_of_admissible v (v.wellFormed_encode M (Equiv.refl _)) M.size_ge_two).trans
    (congrArg some (decoded_encode v M))

/-- `decode? v a = some M` iff `a` is well formed of size at least two and decodes to `M`. -/
theorem decode?_eq_some_iff (v : Vocabulary L) {a : EncodedStructure} {M : Structure L} :
    decode? v a = some M ↔ ∃ (_ : v.WellFormed a) (hn : 2 ≤ a.1), decoded v a hn = M := by
  by_cases h : v.WellFormed a ∧ 2 ≤ a.1
  · rw [decode?_of_admissible v h.1 h.2, Option.some_inj]
    exact ⟨fun hM => ⟨h.1, h.2, hM⟩, fun ⟨_, _, hM⟩ => hM⟩
  · rw [decode?_of_not_admissible v h]
    exact iff_of_false (by simp) fun ⟨ha, hn, _⟩ => h ⟨ha, hn⟩

/-- An ordered query language consists of the encodings decoding to members of the query. -/
theorem Query.encodedLanguage_eq (K : Query L) (v : Vocabulary L) :
    K.encodedLanguage v = {a | ∃ M ∈ K, decode? v a = some M} := by
  ext a
  simp only [Query.encodedLanguage, Set.mem_ofPred_eq, decode?_eq_some_iff]
  constructor
  · rintro ⟨ha, hn, hK⟩
    exact ⟨_, hK, ha, hn, rfl⟩
  · rintro ⟨M, hK, ha, hn, rfl⟩
    exact ⟨ha, hn, hK⟩

namespace DomainInterpretation

variable {k : ℕ} (I : DomainInterpretation L L' k) (v : Vocabulary L) (v' : Vocabulary L')

/-- Encode the target input relations on the ranks of the domain tuples. Invalid shapes or sizes
below two produce one empty table too many, outside every target query language. -/
noncomputable def encodedMap (a : EncodedStructure) : EncodedStructure :=
  if h : v.WellFormed a ∧ 2 ≤ a.1 then
    letI := I.inputStructure (decoded v a h.2)
    v'.encode (Fin (I.card (decoded v a h.2))) (Equiv.refl _)
  else (0, List.replicate (v'.count + 1) [])

variable {a : EncodedStructure}

/-- On a well-formed encoding of size at least two, `encodedMap` encodes the target input
structure on the domain ranks. -/
theorem encodedMap_of_admissible (ha : v.WellFormed a) (hn : 2 ≤ a.1) :
    I.encodedMap v v' a =
      (letI := I.inputStructure (decoded v a hn)
       v'.encode (Fin (I.card (decoded v a hn))) (Equiv.refl _)) :=
  dite_eq_left ⟨ha, hn⟩

/-- On an inadmissible encoding, `encodedMap` returns the fixed malformed encoding
`(0, List.replicate (v'.count + 1) [])`. -/
theorem encodedMap_of_not_admissible (ha : ¬(v.WellFormed a ∧ 2 ≤ a.1)) :
    I.encodedMap v v' a = (0, List.replicate (v'.count + 1) []) :=
  dite_eq_right ha

/-- The encoded image has one element per domain tuple. -/
theorem card_encodedMap (ha : v.WellFormed a) (hn : 2 ≤ a.1) :
    (I.encodedMap v v' a).1 = I.card (decoded v a hn) := by
  rw [I.encodedMap_of_admissible v v' ha hn]
  rfl

/-- Shape validity of the result is exactly source admissibility, whatever the number of domain
tuples. -/
@[simp] theorem wellFormed_encodedMap_iff :
    v'.WellFormed (I.encodedMap v v' a) ↔ v.WellFormed a ∧ 2 ≤ a.1 := by
  by_cases h : v.WellFormed a ∧ 2 ≤ a.1
  · rw [I.encodedMap_of_admissible v v' h.1 h.2]
    let := I.inputStructure (decoded v a h.2)
    exact iff_of_true (Vocabulary.wellFormed_encode _ _) h
  · rw [I.encodedMap_of_not_admissible v v' h]
    refine iff_of_false (fun h' => ?_) h
    have := h'.1
    simp only [List.length_replicate] at this
    lia

/-- The bit at the table index of some target ranks is the defining formula on the domain tuples
of these ranks. Numeric predicates are not serialized as extra tables. -/
theorem table_encodedMap (ha : v.WellFormed a) (hn : 2 ≤ a.1) {r : ℕ}
    (R : L'.Relations r) (x : Fin r → Fin (I.card (decoded v a hn))) :
    (v'.table (I.encodedMap v v' a) ⟨r, R⟩).getD (tupleIndex x) false = true ↔
      (I.rel R).Realize (fun p => I.unrank (decoded v a hn) (x p.1) p.2) := by
  rw [I.encodedMap_of_admissible v v' ha hn]
  let := I.inputStructure (decoded v a hn)
  rw [Vocabulary.table_encode, Vocabulary.getD_relTable_eq_true_iff]
  rfl

/-- The output length includes its unary cardinality and every framed relation table. -/
theorem length_encStructure_encodedMap (ha : v.WellFormed a) (hn : 2 ≤ a.1) :
    (encStructure (I.encodedMap v v' a)).length =
      2 * I.card (decoded v a hn) + 1 +
        ∑ j : Fin v'.count, (2 * I.card (decoded v a hn) ^ v'.arity j + 1) := by
  rw [I.encodedMap_of_admissible v v' ha hn, encStructure_eq]
  simp [Vocabulary.encode, Vocabulary.length_relTable, Turing.MultiTapeTM.length_frame,
    Vocabulary.arity, List.sum_ofFn]

/-- For an admissible interpretation, the encoded image is the canonical encoding of the image. -/
theorem encodedMap_eq_encode (hI : I.Admissible) (ha : v.WellFormed a) (hn : 2 ≤ a.1) :
    I.encodedMap v v' a = encode v' (I.map hI (decoded v a hn)) :=
  I.encodedMap_of_admissible v v' ha hn

/-- **Decoding commutes with an admissible interpretation.** Undecodable sources map to
undecodable targets. -/
theorem decode?_encodedMap (hI : I.Admissible) (a : EncodedStructure) :
    decode? v' (I.encodedMap v v' a) = (decode? v a).map (I.map hI) := by
  by_cases h : v.WellFormed a ∧ 2 ≤ a.1
  · rw [I.encodedMap_eq_encode v v' hI h.1 h.2, decode?_encode, decode?_of_admissible v h.1 h.2,
      Option.map_some]
  · rw [decode?_of_not_admissible v h, Option.map_none, decode?_of_not_admissible v']
    rw [wellFormed_encodedMap_iff]
    exact fun h' => h h'.1

end DomainInterpretation

end Cslib.Logic.FO.Ordered
