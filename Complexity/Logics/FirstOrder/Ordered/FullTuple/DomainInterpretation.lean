/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.FullTuple.Encoding
public import Complexity.Logics.FirstOrder.Ordered.DomainInterpretation.Encoding
public import Complexity.Logics.FirstOrder.Ordered.Reduction

/-!
# Full-tuple interpretations as interpretations with a domain formula

A full-tuple interpretation is the ordered interpretation whose domain formula is `true`, the usual
case of [Immerman1999, Definition 1.26]. Its ranks are the lexicographic ranks of all tuples, so
its image and its encoded map agree with the existing full-tuple semantics. For positive
dimension it is admissible, and the native tuple formulas for order, `BIT` and constants
[Immerman1999, Exercise 1.33] form its numeric certificate. Full-tuple interpretations of positive
dimension therefore give first-order reductions.

## Main definitions

* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.certificate`: the native numeric certificate for
  `FullTupleInterpretation.toDomainInterpretation` (defined in
  `Complexity/Logics/FirstOrder/Ordered/FullTuple/Encoding.lean`).

## Main results

* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.relMap_map_toDomainInterpretation`: agreement
  with `FullTupleInterpretation.inputStructure`.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.isFirstOrderMap_map_toDomainInterpretation`:
  full-tuple images are first-order maps.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.reduces`: full-tuple interpretations of positive
  dimension give first-order reductions.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Definition 1.26, Remark 1.32 and
  Exercise 1.33.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

namespace FullTupleInterpretation

variable {L L' : Language} {k : ℕ} {I : FullTupleInterpretation L L' k} {M : Structure L}

/-- The lexicographic rank of `constantTuple c` is `c.index (n ^ (k + 1))`. -/
theorem lexRank_constantTuple {n : ℕ} [Fact (2 ≤ n)] (c : NumericFunction 0) :
    lexRank (constantTuple (n := n) (k := k) c) = c.index (n ^ (k + 1)) :=
  Ordered.lexRank_constantTuple c

variable (I) in
/-- The native tuple formulas for order, `BIT` and constants certify a positive-dimensional
full-tuple interpretation. -/
noncomputable def certificate (hk : 0 < k) : I.toDomainInterpretation.Certificate where
  le := tupleLe L k
  bit := tupleBit L k
  const := I.constants.constant
  realize_le M v := by
    rw [realize_tupleLe]
    simp only [lexRank_unrank_toDomainInterpretation]
    exact Iff.rfl
  realize_bit M v := by
    rw [realize_tupleBit]
    simp only [lexRank_unrank_toDomainInterpretation]
  realize_const M c i := by
    cases k with
    | zero => lia
    | succ k =>
      change ((tupleConstants L k).constant c).Realize _ ↔ _
      rw [realize_tupleConstants, ← lexRank_injective.eq_iff,
        lexRank_unrank_toDomainInterpretation, lexRank_constantTuple]
      simp only [card_toDomainInterpretation]

variable [L'.IsRelational]

/-- The image of a full-tuple interpretation is its canonical rank structure, up to the size cast.
-/
theorem relMap_map_toDomainInterpretation (hk : 0 < k) {r : ℕ} (R : L'.Relations r)
    (x : Fin r → I.toDomainInterpretation.map (admissible_toDomainInterpretation hk) M) :
    RelMap R x ↔ (I.inputStructure (n := M.size)).RelMap R
      (Fin.cast (card_toDomainInterpretation M) ∘ x) := by
  change (I.rel R).Realize (fun p => I.toDomainInterpretation.unrank M (x p.1) p.2) ↔ _
  exact iff_of_eq (congrArg (I.rel R).Realize
    (funext fun p => congrFun (unrank_toDomainInterpretation (x p.1)) p.2))

/-- Full-tuple images of positive dimension are first-order maps. -/
theorem isFirstOrderMap_map_toDomainInterpretation (hk : 0 < k) :
    IsFirstOrderMap (I.toDomainInterpretation.map (admissible_toDomainInterpretation hk)) :=
  DomainInterpretation.isFirstOrderMap _ (I.certificate hk)

/-- **Full-tuple interpretations give first-order reductions.** A full-tuple interpretation of
positive dimension that maps exactly the members of `K` into `K'` reduces `K` to `K'`. -/
theorem reduces (hk : 0 < k) {K : Query L} {K' : Query L'}
    (h : ∀ M, M ∈ K ↔
      I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk) M ∈ K') :
    Reduces K K' :=
  Reduces.of_interpretation _ (I.certificate hk) h

end FullTupleInterpretation

end Cslib.Logic.FO.Ordered
