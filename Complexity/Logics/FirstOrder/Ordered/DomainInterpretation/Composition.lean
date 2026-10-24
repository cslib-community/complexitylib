/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.DomainInterpretation.Certificate
public import Complexity.Logics.FirstOrder.Ordered.Tuple.Flatten

/-!
# Composition of certified ordered interpretations

An outer ordered interpretation `J` is composed with an inner interpretation `I` carrying a
numeric certificate. The composite has dimension `l * k`, flattening the outer coordinate before
the inner one. Its domain says that every block is a domain tuple of `I` and that the ranks of the
blocks satisfy the pullback of the domain formula of `J`; its relation formulas are pullbacks of
those of `J`. The inner certificate is what makes these pullbacks possible: the formulas of `J`
mention the numeric symbols of the image of `I`.

Flattened lexicographic order on the composite domain is lexicographic order on the ranks of the
blocks, so the composite ranks are exactly the ranks of `J` in the image of `I`. Hence the image of
the composite is the image of `J` in the image of `I`. Pulling back an outer certificate through
the inner one certifies the composite. This is the substitution proof of
[Immerman1999, Proposition 1.28 and Exercise 2.15(1)].

## Main definitions

* `Cslib.Logic.FO.Ordered.DomainInterpretation.Certificate.pullback`: flattened pullback of a
  formula on blocks of target variables.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.comp`: composition with a certified interpretation.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.Certificate.comp`: the composite certificate.

## Main results

* `Cslib.Logic.FO.Ordered.DomainInterpretation.card_comp`,
  `Cslib.Logic.FO.Ordered.DomainInterpretation.unrank_comp`: composite ranks.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.map_comp`: the composite image is the iterated one.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Proposition 1.28, Remark 1.32 and
  Exercise 2.15(1).
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

namespace DomainInterpretation

variable {L L' L'' : Language} {k l : ℕ} [L'.IsRelational]

/-- Pull back a formula on blocks of `l` target variables along a certified interpretation, and
flatten each block of blocks to `l * k` source variables. -/
noncomputable def Certificate.pullback {I : DomainInterpretation L L' k} (C : I.Certificate)
    {β : Type*} (φ : (language L').Formula (β × Fin l)) :
    (language L).Formula (β × Fin (l * k)) :=
  (C.onFormula φ).relabel fun p => (p.1.1, finProdFinEquiv (p.1.2, p.2))

/-- Compose an outer interpretation with a certified inner interpretation, flattening `(j, i)` to
`j * k + i`. -/
noncomputable def comp (J : DomainInterpretation L' L'' l) {I : DomainInterpretation L L' k}
    (C : I.Certificate) : DomainInterpretation L L'' (l * k) where
  domain := Formula.iInf (fun j : Fin l => I.domain.relabel fun i => finProdFinEquiv (j, i)) ⊓
    (C.onFormula J.domain).relabel finProdFinEquiv
  rel R := C.pullback (J.rel R)

variable (J : DomainInterpretation L' L'' l) {I : DomainInterpretation L L' k}
  (C : I.Certificate) {M : Structure L}

/-- A flattened tuple satisfies `(J.comp C).domain` iff each block satisfies `I.domain` and the
blocks satisfy the pullback `C.onFormula J.domain`. -/
theorem realize_comp_domain (x : Fin (l * k) → Fin M.size) :
    (J.comp C).domain.Realize x ↔
      (∀ j, I.domain.Realize fun i => x (finProdFinEquiv (j, i))) ∧
        (C.onFormula J.domain).Realize fun p => x (finProdFinEquiv p) := by
  simp only [comp, Formula.realize_inf, Formula.realize_iInf, Formula.realize_relabel,
    Function.comp_def]

private theorem exists_unrank_comp (hI : I.Admissible) :
    ∃ h : (J.comp C).card M = J.card (I.map hI M), ∀ i, (J.comp C).unrank M i =
      flattenTuple fun j => I.unrank M (J.unrank (I.map hI M) (Fin.cast h i) j) := by
  have hdom (i : Fin (J.card (I.map hI M))) :
      (J.comp C).domain.Realize (flattenTuple fun j => I.unrank M (J.unrank (I.map hI M) i j)) := by
    rw [realize_comp_domain]
    simp only [flattenTuple_finProdFinEquiv_apply]
    exact ⟨fun j => realize_domain_unrank _,
      (C.realize_onFormula hI J.domain (J.unrank (I.map hI M) i)).mpr (realize_domain_unrank i)⟩
  have hsurj (x : Fin (l * k) → Fin M.size) (hx : (J.comp C).domain.Realize x) :
      ∃ i, (flattenTuple fun j => I.unrank M (J.unrank (I.map hI M) i j)) = x := by
    rw [realize_comp_domain] at hx
    obtain ⟨hb, hJ⟩ := hx
    let r : Fin l → I.map hI M := fun j => I.rank M _ (hb j)
    have hr : (fun p : Fin l × Fin k => x (finProdFinEquiv p)) =
        fun p => I.unrank M (r p.1) p.2 := by
      funext p
      exact (congrFun (unrank_rank (hb p.1)) p.2).symm
    rw [hr, C.realize_onFormula hI J.domain r] at hJ
    obtain ⟨i, hi⟩ := exists_unrank_eq hJ
    refine ⟨i, ?_⟩
    rw [hi]
    conv_rhs => rw [← flattenTuple_finProdFinEquiv x]
    congr 1
    funext j
    exact unrank_rank (hb j)
  have hφ : StrictMono fun r : Fin (I.card M) => lexEquiv (I.unrank M r) :=
    fun _ _ h => Fin.lt_def.mpr (strictMono_lexRank_unrank h)
  have hmono : StrictMono fun i : Fin (J.card (I.map hI M)) =>
      lexRank (flattenTuple fun j => I.unrank M (J.unrank (I.map hI M) i j)) := by
    intro i i' h
    simp only [lexRank_flattenTuple]
    exact (lexRank_comp_lt_lexRank_comp_iff hφ _ _).mpr (strictMono_lexRank_unrank h)
  exact unrank_eq_of_strictMono _ hdom hsurj hmono

/-- The composite image has one element per domain tuple of `J` in the image of `I`. -/
theorem card_comp (hI : I.Admissible) (M : Structure L) :
    (J.comp C).card M = J.card (I.map hI M) :=
  (J.exists_unrank_comp C hI).1

/-- The composite ranks flatten the blocks of the ranks of `J` in the image of `I`. -/
theorem unrank_comp (hI : I.Admissible) (i : Fin ((J.comp C).card M)) :
    (J.comp C).unrank M i = flattenTuple fun j =>
      I.unrank M (J.unrank (I.map hI M) (Fin.cast (J.card_comp C hI M) i) j) :=
  (J.exists_unrank_comp C hI).2 i

/-- The composite of admissible interpretations is admissible. -/
theorem admissible_comp (hI : I.Admissible) (hJ : J.Admissible) : (J.comp C).Admissible :=
  fun M => (J.card_comp C hI M).symm ▸ hJ _

/-- A pulled-back formula holds of composite ranks when it holds of the corresponding ranks of `J`
in the image of `I`. -/
theorem realize_pullback_comp (hI : I.Admissible) {β : Type*}
    (φ : (language L').Formula (β × Fin l)) (v : β → Fin ((J.comp C).card M)) :
    (C.pullback φ).Realize (fun p => (J.comp C).unrank M (v p.1) p.2) ↔
      φ.Realize (M := I.map hI M)
        (fun p => J.unrank (I.map hI M) (Fin.cast (J.card_comp C hI M) (v p.1)) p.2) := by
  simp only [Certificate.pullback, Formula.realize_relabel, Function.comp_def,
    J.unrank_comp C hI, flattenTuple_apply]
  exact C.realize_onFormula hI φ
    (fun q => J.unrank (I.map hI M) (Fin.cast (J.card_comp C hI M) (v q.1)) q.2)

variable [L''.IsRelational]

/-- **The composite image is the iterated image.** -/
theorem map_comp (hI : I.Admissible) (hJ : J.Admissible) (M : Structure L) :
    (J.comp C).map (J.admissible_comp C hI hJ) M = J.map hJ (I.map hI M) :=
  Structure.ext (J.card_comp C hI M) fun R x => J.realize_pullback_comp C hI (J.rel R) x

namespace Certificate

/-- Pull back the outer numeric definitions through the inner certificate. -/
noncomputable def comp {J : DomainInterpretation L' L'' l} (C' : J.Certificate)
    {I : DomainInterpretation L L' k} (C : I.Certificate) (hI : I.Admissible) :
    (J.comp C).Certificate where
  le := C.pullback C'.le
  bit := C.pullback C'.bit
  const c := (C.onFormula (C'.const c)).relabel finProdFinEquiv
  realize_le M v := by
    rw [J.realize_pullback_comp C hI]
    exact (C'.realize_le (I.map hI M) fun a => Fin.cast _ (v a)).trans (Fin.cast_le_cast _)
  realize_bit M v := by
    rw [J.realize_pullback_comp C hI]
    exact (C'.realize_bit (I.map hI M) fun a => Fin.cast _ (v a)).trans
      (by simp only [Fin.val_cast])
  realize_const M c i := by
    simp only [Formula.realize_relabel, Function.comp_def, J.unrank_comp C hI,
      flattenTuple_finProdFinEquiv_apply]
    rw [C.realize_onFormula hI (C'.const c) (J.unrank (I.map hI M) (Fin.cast _ i)),
      C'.realize_const (I.map hI M), Fin.val_cast, ← J.card_comp C hI M]

end Certificate

end DomainInterpretation

end Cslib.Logic.FO.Ordered
