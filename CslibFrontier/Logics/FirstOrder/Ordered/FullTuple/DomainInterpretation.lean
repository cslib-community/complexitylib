/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple.Composition
public import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple.Encoding
public import CslibFrontier.Logics.FirstOrder.Ordered.DomainInterpretation.Encoding
public import CslibFrontier.Logics.FirstOrder.Ordered.Reduction

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
  `CslibFrontier/Logics/FirstOrder/Ordered/FullTuple/Encoding.lean`).

## Main results

* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.relMap_map_toDomainInterpretation`: agreement
  with `FullTupleInterpretation.inputStructure`.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.map_congr`: full-tuple images depend only on
  canonical formula realization.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.map_comp`: the image of
  `FullTupleInterpretation.comp` is the iterated image.
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

/-- Helper expressing `relMap_map_toDomainInterpretation` with an explicit `.size` equality so
rewrites remain well-typed at `implicit` transparency. -/
private theorem relMap_map_eq (I : FullTupleInterpretation L L' k) (hk : 0 < k) (M : Structure L)
    (hc : (I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk) M).size =
      M.size ^ k)
    {r : ℕ} (R : L'.Relations r)
    (x : Fin r →
      Fin (I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk) M).size) :
    RelMap (M := I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk) M) R x ↔
      (I.inputStructure (n := M.size)).RelMap R (Fin.cast hc ∘ x) :=
  I.relMap_map_toDomainInterpretation hk R x

/-- Two full-tuple interpretations of positive dimension whose relation formulas agree on every
canonical ordered structure induce the same image map. -/
theorem map_congr {I I' : FullTupleInterpretation L L' k} (hk : 0 < k)
    (h : ∀ {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {r : ℕ} (R : L'.Relations r)
      (x : Fin r × Fin k → Fin n), (I.rel R).Realize x ↔ (I'.rel R).Realize x) :
    I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk) =
      I'.toDomainInterpretation.map (I'.admissible_toDomainInterpretation hk) := by
  funext M
  let hc : (I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk) M).size =
      M.size ^ k := card_toDomainInterpretation M
  let hc' : (I'.toDomainInterpretation.map (I'.admissible_toDomainInterpretation hk) M).size =
      M.size ^ k := card_toDomainInterpretation M
  have hsize :
      (I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk) M).size =
        (I'.toDomainInterpretation.map (I'.admissible_toDomainInterpretation hk) M).size :=
    hc.trans hc'.symm
  refine Structure.ext hsize fun R x => ?_
  refine (I.relMap_map_eq hk M hc R x).trans
    ((?_ : _ ↔ _).trans (I'.relMap_map_eq hk M hc' R (Fin.cast hsize ∘ x)).symm)
  have hcast : (Fin.cast hc' ∘ Fin.cast hsize ∘ x) = Fin.cast hc ∘ x :=
    funext fun _ => Fin.ext rfl
  rw [hcast]
  exact h (n := M.size) R _

/-- Isomorphism between the `DomainInterpretation.map` image of `I` on `M` and `Fin (M.size ^ k)`
equipped with `I.inputStructure`. -/
private noncomputable def mapInputEquiv (I : FullTupleInterpretation L L' k) (hk : 0 < k)
    (M : Structure L) :
    letI := I.inputStructure (n := M.size)
    letI : Fact (2 ≤ M.size ^ k) := ⟨two_le_pow (n := M.size) hk⟩
    (I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk) M) ≃[language L']
      Fin (M.size ^ k) := by
  letI := I.inputStructure (n := M.size)
  letI : Fact (2 ≤ M.size ^ k) := ⟨two_le_pow (n := M.size) hk⟩
  let hc : (I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk) M).size =
      M.size ^ k := card_toDomainInterpretation M
  refine { finCongr hc with map_fun' := ?_, map_rel' := ?_ }
  · intro r f x
    cases f with
    | inl f => exact isEmptyElim f
    | inr f =>
      cases f <;> apply Fin.ext
      · rfl
      · rfl
      · exact congrArg (· - 1) hc
  · intro r R x
    cases R with
    | inl R => exact (I.relMap_map_toDomainInterpretation hk R x).symm
    | inr R => cases R <;> rfl

/-- **The image of `FullTupleInterpretation.comp` is the iterated image** for positive
dimensions. -/
theorem map_comp {L'' : Language} [L''.IsRelational] {l : ℕ}
    (J : FullTupleInterpretation L' L'' l) (I : FullTupleInterpretation L L' k)
    (hk : 0 < k) (hl : 0 < l) (M : Structure L) :
    (J.comp I).toDomainInterpretation.map
        ((J.comp I).admissible_toDomainInterpretation (Nat.mul_pos hl hk)) M =
      J.toDomainInterpretation.map (J.admissible_toDomainInterpretation hl)
        (I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk) M) := by
  let M₁ := I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk) M
  have hc₁ : M₁.size = M.size ^ k := card_toDomainInterpretation M
  have hcL :
      ((J.comp I).toDomainInterpretation.map
        ((J.comp I).admissible_toDomainInterpretation (Nat.mul_pos hl hk)) M).size =
        M.size ^ (l * k) :=
    card_toDomainInterpretation M
  have hcR :
      (J.toDomainInterpretation.map (J.admissible_toDomainInterpretation hl) M₁).size =
        M₁.size ^ l :=
    card_toDomainInterpretation M₁
  have hpow : M.size ^ (l * k) = (M.size ^ k) ^ l := by rw [← pow_mul, Nat.mul_comm l k]
  have hsize :
      ((J.comp I).toDomainInterpretation.map
        ((J.comp I).admissible_toDomainInterpretation (Nat.mul_pos hl hk)) M).size =
        (J.toDomainInterpretation.map (J.admissible_toDomainInterpretation hl) M₁).size := by
    rw [hcL, hcR, hc₁, hpow]
  refine Structure.ext hsize fun R x => ?_
  refine ((J.comp I).relMap_map_eq (Nat.mul_pos hl hk) M hcL R x).trans
    ((?_ : _ ↔ _).trans (J.relMap_map_eq hl M₁ hcR R (Fin.cast hsize ∘ x)).symm)
  let := I.inputStructure (n := M.size)
  let : Fact (2 ≤ M.size ^ k) := ⟨two_le_pow (n := M.size) hk⟩
  let := J.inputStructure (n := M.size ^ k)
  let : Fact (2 ≤ (M.size ^ k) ^ l) := ⟨two_le_pow (n := M.size ^ k) hl⟩
  let := (J.comp I).inputStructure (n := M.size)
  let : Fact (2 ≤ M.size ^ (l * k)) := ⟨two_le_pow (n := M.size) (Nat.mul_pos hl hk)⟩
  let eComp := J.compEquiv I hk hl (n := M.size)
  let y : Fin _ → Fin ((M.size ^ k) ^ l) := fun a => eComp.symm (Fin.cast hcL (x a))
  have hL :
      ((J.comp I).inputStructure (n := M.size)).RelMap R (Fin.cast hcL ∘ x) ↔
        (J.inputStructure (n := M.size ^ k)).RelMap R y := by
    have hy : (Fin.cast hcL ∘ x) = eComp ∘ y := funext fun _ => (eComp.apply_symm_apply _).symm
    rw [hy]
    exact eComp.map_rel (.inl R) y
  rw [hL]
  let e₁ := mapInputEquiv I hk M
  let u : Fin _ → Fin (M₁.size ^ l) := Fin.cast hcR ∘ Fin.cast hsize ∘ x
  change (J.rel R).Realize (fun p => lexEquiv.symm (y p.1) p.2) ↔
    (J.rel R).Realize (M := M₁) (fun p => lexEquiv.symm (u p.1) p.2)
  rw [← StrongHomClass.realize_formula e₁ (J.rel R)]
  refine iff_of_eq (congrArg (J.rel R).Realize (funext fun ⟨a, j⟩ => ?_))
  have htuple : lexEquiv.symm (y a) = fun j' => e₁ (lexEquiv.symm (u a) j') := by
    apply lexRank_injective
    have hyval : lexRank (lexEquiv.symm (y a)) = (x a).val := by
      have h₁ : lexRank (lexEquiv.symm (y a)) = (y a).val :=
        congrArg Fin.val (lexEquiv.apply_symm_apply (y a))
      have h₂ : (y a).val = (eComp (y a)).val := (J.compEquiv_apply_val I hk hl (y a)).symm
      rw [h₁, h₂, eComp.apply_symm_apply, Fin.val_cast]
    have huval : lexRank (fun j' => e₁ (lexEquiv.symm (u a) j')) = (x a).val := by
      rw [lexRank_apply]
      have hsum :
          (∑ j' : Fin l, (e₁ (lexEquiv.symm (u a) j')).val * (M.size ^ k) ^ j'.rev.val) =
            ∑ j' : Fin l, (lexEquiv.symm (u a) j').val * M₁.size ^ j'.rev.val :=
        Finset.sum_congr rfl fun j' _ =>
          congrArg₂ (· * ·) rfl (congrArg (· ^ j'.rev.val) hc₁.symm)
      rw [hsum, ← lexRank_apply]
      exact (congrArg Fin.val (lexEquiv.apply_symm_apply (u a))).trans
        (by simp only [u, Function.comp_apply, Fin.val_cast])
    exact hyval.trans huval.symm
  exact congrFun htuple j

end FullTupleInterpretation

end Cslib.Logic.FO.Ordered
