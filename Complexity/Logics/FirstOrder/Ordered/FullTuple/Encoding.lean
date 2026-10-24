/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.FullTuple
public import Complexity.Logics.FirstOrder.Ordered.DomainInterpretation.Encoding

/-!
# Encoding canonical full-tuple interpretations

A full-tuple interpretation is the ordered interpretation whose domain formula is `true`
(`FullTupleInterpretation.toDomainInterpretation`), with ranks given by lexicographic rank on all
tuples. A valid source of size at least two is mapped to the full tuple universe, numbered by
`lexRank`, agreeing with `DomainInterpretation.encodedMap`
(`FullTupleInterpretation.encodedMap_toDomainInterpretation`). Only the target input relations are
serialized; canonical order, BIT and constants are computed from the target cardinality. Relation
tables keep `tupleIndex` order across their arguments. Malformed sources and sizes zero and one map
to a fixed malformed target.

## Main definitions

* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.toDomainInterpretation`: embedding as an
  interpretation with domain formula `⊤`.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.encodedMap`,
  `Cslib.Logic.FO.Ordered.FullTupleInterpretation.encodedModelEquiv`: the total map on parsed
  instances and the isomorphism of the interpreted model with the decoded output.

## Main results

* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.unrank_toDomainInterpretation`: ranks are
  lexicographic ranks.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.encodedMap_toDomainInterpretation`: agreement
  with `DomainInterpretation.encodedMap`.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.card_encodedMap`: exact target cardinality.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.table_encodedMap`: exact table numbering.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.wellFormed_encodedMap_iff`: exact shape guard.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Remark 1.32, Exercise 1.33 and
  Proposition 3.5. The full-domain hypothesis is essential; restricted domains still require
  explicit definitions and correctness proofs for their numeric symbols.
-/

@[expose] public section

open FirstOrder Language Structure

namespace Cslib.Logic.FO.Ordered.FullTupleInterpretation

section DomainInterpretation

variable {L L' : Language} {k : ℕ} (I : FullTupleInterpretation L L' k)

/-- A full-tuple interpretation is the ordered interpretation with domain formula `true`. -/
def toDomainInterpretation : DomainInterpretation L L' k where
  domain := ⊤
  rel := I.rel

variable {I}

/-- The domain of `I.toDomainInterpretation` on `M` has `M.size ^ k` elements. -/
theorem card_toDomainInterpretation (M : Structure L) :
    I.toDomainInterpretation.card M = M.size ^ k :=
  DomainInterpretation.card_of_forall fun _ => Formula.realize_top.mpr trivial

variable {M : Structure L}

/-- The ranks of a full-tuple interpretation are the lexicographic ranks of all tuples. -/
theorem unrank_toDomainInterpretation (i : Fin (I.toDomainInterpretation.card M)) :
    I.toDomainInterpretation.unrank M i =
      lexEquiv.symm (Fin.cast (card_toDomainInterpretation M) i) :=
  DomainInterpretation.unrank_of_forall (fun _ => Formula.realize_top.mpr trivial) i

/-- Unranking the `i`-th tuple of `I.toDomainInterpretation` gives the tuple of lexicographic
rank `i`. -/
@[simp] theorem lexRank_unrank_toDomainInterpretation (i : Fin (I.toDomainInterpretation.card M)) :
    lexRank (I.toDomainInterpretation.unrank M i) = i :=
  DomainInterpretation.lexRank_unrank_of_forall (fun _ => Formula.realize_top.mpr trivial) i

/-- Positive-dimensional full-tuple interpretations are admissible. -/
theorem admissible_toDomainInterpretation (hk : 0 < k) : I.toDomainInterpretation.Admissible :=
  fun M => (card_toDomainInterpretation M).symm ▸ two_le_pow (n := M.size) hk

end DomainInterpretation

variable {L L' : Language} [L.IsRelational] [L'.IsRelational] {k : ℕ}
  (I : FullTupleInterpretation L L' k) (v : Vocabulary L) (v' : Vocabulary L')

/-- Encode the interpreted input relations on the canonical rank universe. Invalid shapes or
sizes below two produce one empty table too many, outside every target query language. -/
noncomputable def encodedMap (a : EncodedStructure) : EncodedStructure :=
  if h : v.WellFormed a ∧ 2 ≤ a.1 then
    letI : Fact (2 ≤ a.1) := ⟨h.2⟩
    letI := v.decode a
    letI := I.inputStructure (n := a.1)
    v'.encode (Fin (a.1 ^ k)) (Equiv.refl _)
  else (0, List.replicate (v'.count + 1) [])

variable {a : EncodedStructure}

/-- On a well-formed encoding of size at least two, `encodedMap` encodes `I.inputStructure` on
`Fin (a.1 ^ k)`. -/
theorem encodedMap_of_admissible (ha : v.WellFormed a) (hn : 2 ≤ a.1) :
    I.encodedMap v v' a =
      (letI : Fact (2 ≤ a.1) := ⟨hn⟩;
       letI := v.decode a;
       letI := I.inputStructure (n := a.1);
       v'.encode (Fin (a.1 ^ k)) (Equiv.refl _)) :=
  dite_eq_left ⟨ha, hn⟩

/-- On an inadmissible encoding, `encodedMap` returns `(0, List.replicate (v'.count + 1) [])`. -/
theorem encodedMap_of_not_admissible (ha : ¬(v.WellFormed a ∧ 2 ≤ a.1)) :
    I.encodedMap v v' a = (0, List.replicate (v'.count + 1) []) :=
  dite_eq_right ha

/-- **The encoded maps agree**: the full-tuple encoded map is that of the embedded interpretation,
for every dimension and every input. -/
theorem encodedMap_toDomainInterpretation {I : FullTupleInterpretation L L' k} (v : Vocabulary L)
    (v' : Vocabulary L') : I.toDomainInterpretation.encodedMap v v' = I.encodedMap v v' := by
  funext a
  by_cases h : v.WellFormed a ∧ 2 ≤ a.1
  · rw [DomainInterpretation.encodedMap_of_admissible _ v v' h.1 h.2,
      I.encodedMap_of_admissible v v' h.1 h.2]
    let _ : Fact (2 ≤ a.1) := ⟨h.2⟩
    let _ := v.decode a
    let _ := I.toDomainInterpretation.inputStructure (decoded v a h.2)
    let _ := I.inputStructure (n := a.1)
    refine v'.encode_congr _ _ (card_toDomainInterpretation (decoded v a h.2)) fun R x => ?_
    change (I.rel R).Realize
      (fun p => I.toDomainInterpretation.unrank (decoded v a h.2) (x p.1) p.2) ↔ _
    simp only [unrank_toDomainInterpretation]
    rfl
  · rw [DomainInterpretation.encodedMap_of_not_admissible _ v v' h,
      I.encodedMap_of_not_admissible v v' h]

/-- The canonical rank universe has exactly one element per source tuple. -/
theorem card_encodedMap (ha : v.WellFormed a) (hn : 2 ≤ a.1) :
    (I.encodedMap v v' a).1 = a.1 ^ k := by
  rw [I.encodedMap_of_admissible v v' ha hn]
  rfl

/-- Shape validity of the result is exactly source admissibility. Positive dimension is only
needed when asking for canonical target numerics, not for this shape statement. -/
@[simp] theorem wellFormed_encodedMap_iff :
    v'.WellFormed (I.encodedMap v v' a) ↔ v.WellFormed a ∧ 2 ≤ a.1 := by
  rw [← I.encodedMap_toDomainInterpretation, DomainInterpretation.wellFormed_encodedMap_iff]

/-- A positive-dimensional admissible source produces an admissible target cardinality. -/
theorem two_le_card_encodedMap (hk : 0 < k) (ha : v.WellFormed a) (hn : 2 ≤ a.1) :
    2 ≤ (I.encodedMap v v' a).1 := by
  rw [I.card_encodedMap v v' ha hn]
  exact hn.trans (Nat.le_pow hk)

/-- The bit at the existing table index of the target arguments is the defining formula on
their inverse lexicographic ranks. Numeric predicates are not serialized as extra tables. -/
theorem table_encodedMap (ha : v.WellFormed a) (hn : 2 ≤ a.1) {r : ℕ}
    (R : L'.Relations r) (x : Fin r → Fin (a.1 ^ k)) :
    (v'.table (I.encodedMap v v' a) ⟨r, R⟩).getD (tupleIndex x) false = true ↔
      letI : Fact (2 ≤ a.1) := ⟨hn⟩
      letI := v.decode a
      (I.rel R).Realize (fun p => lexEquiv.symm (x p.1) p.2) := by
  rw [I.encodedMap_of_admissible v v' ha hn]
  let : Fact (2 ≤ a.1) := ⟨hn⟩
  let := v.decode a
  let := I.inputStructure (n := a.1)
  rw [Vocabulary.table_encode, Vocabulary.getD_relTable_eq_true_iff]
  rfl

/-- The output length includes its unary cardinality and every framed relation table. -/
theorem length_encStructure_encodedMap (ha : v.WellFormed a) (hn : 2 ≤ a.1) :
    (encStructure (I.encodedMap v v' a)).length =
      2 * a.1 ^ k + 1 + ∑ j : Fin v'.count, (2 * (a.1 ^ k) ^ v'.arity j + 1) := by
  rw [← I.encodedMap_toDomainInterpretation,
    DomainInterpretation.length_encStructure_encodedMap _ v v' ha hn, card_toDomainInterpretation]
  rfl

/-- The decoded output, with its own canonical numerics, is the interpreted full ordered
structure. Its underlying numbering is the exact lexicographic rank, not an arbitrary input
relation isomorphism. -/
noncomputable def encodedModelEquiv (hk : 0 < k) (ha : v.WellFormed a)
    [Fact (2 ≤ a.1)] :
    letI := v.decode a
    letI := I.modelStructure hk (n := a.1)
    letI := v'.decode (I.encodedMap v v' a)
    letI : Fact (2 ≤ (I.encodedMap v v' a).1) :=
      ⟨I.two_le_card_encodedMap v v' hk ha Fact.out⟩
    I.toInterpretation.Model (Fin a.1) ≃[language L'] Fin (I.encodedMap v v' a).1 := by
  letI := v.decode a
  letI := I.modelStructure hk (n := a.1)
  letI := v'.decode (I.encodedMap v v' a)
  letI : Fact (2 ≤ (I.encodedMap v v' a).1) :=
    ⟨I.two_le_card_encodedMap v v' hk ha Fact.out⟩
  letI := I.inputStructure (n := a.1)
  letI : Fact (2 ≤ a.1 ^ k) := ⟨two_le_pow (n := a.1) hk⟩
  let e := I.modelEquiv hk (n := a.1)
  let hcard := I.card_encodedMap v v' ha Fact.out
  refine { toEquiv := e.toEquiv.trans (finCongr hcard.symm), map_fun' := ?_, map_rel' := ?_ }
  · intro r f x
    cases f with
    | inl f => exact isEmptyElim f
    | inr f =>
      apply Fin.ext
      cases f
      · exact I.lexRank_constants_value hk .zero
      · exact I.lexRank_constants_value hk .one
      · change lexRank (I.constants.value (I.constants_valid hk (n := a.1)) .max).val =
          (I.encodedMap v v' a).1 - 1
        rw [hcard]
        exact I.lexRank_constants_value hk .max
  · intro r R x
    cases R with
    | inl R =>
      change (v'.table (I.encodedMap v v' a) ⟨r, R⟩).getD
        (tupleIndex (fun j => finCongr hcard.symm (e (x j)))) false = true ↔ _
      have hi : tupleIndex (fun j => finCongr hcard.symm (e (x j))) =
          tupleIndex (fun j => e (x j)) := by
        simp only [tupleIndex_apply, finCongr_apply, Fin.val_cast]
        rw [hcard]
      rw [hi, I.table_encodedMap v v' ha Fact.out]
      change (I.rel R).Realize (fun p => lexEquiv.symm (lexEquiv (x p.1).val) p.2) ↔ _
      simp only [Equiv.symm_apply_apply]
      rfl
    | inr R =>
      cases R
      · exact (realize_tupleLe (L := L) (fun p => (x p.1).val p.2)).symm
      · exact (realize_tupleBit (L := L) (fun p => (x p.1).val p.2)).symm

/-- Every element retains its exact natural-number rank in the decoded target. -/
theorem encodedModelEquiv_apply_val (hk : 0 < k) (ha : v.WellFormed a)
    [Fact (2 ≤ a.1)] (x : letI := v.decode a; I.toInterpretation.Model (Fin a.1)) :
    ((I.encodedModelEquiv v v' hk ha) x).val = lexRank x.val := by
  rfl

end Cslib.Logic.FO.Ordered.FullTupleInterpretation
