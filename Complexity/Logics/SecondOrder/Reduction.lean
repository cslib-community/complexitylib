/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.SecondOrder.Existential
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Existential second-order logic and first-order reductions

An existential second-order sentence `∃ R₁ … Rₖ, φ` of a relational language `L'` pulls back along a
first-order interpretation `I` of `L'` in `L` of dimension `κ`: a relation variable of arity `n`
becomes a relation variable of arity `n * Nat.card κ`, holding of the concatenated coordinates of
`n` tuples, and `φ` pulls back along the extension of `I` that defines each relation variable by
the corresponding new one [Immerman, Definition 3.3][Immerman1999]. The pullback holds in `M`
exactly when the sentence holds in `I.Model M` (`FO.Interpretation.realize_onESOSentence`), so
existential second-order definability is closed under first-order reductions
[Immerman, Framework 3.12][Immerman1999].

## Main definitions

* `Cslib.Logic.FO.Interpretation.blockEquiv`, `Cslib.Logic.FO.Interpretation.flatten`,
  `Cslib.Logic.FO.Interpretation.modelRel`: coordinate concatenation of `n` tuples and induced
  relations on `I.Model M`.
* `Cslib.Logic.FO.Interpretation.sumVar`, `Cslib.Logic.FO.Interpretation.sumVarEquiv`: an
  interpretation extended to relation variables and the isomorphism of its interpreted model with
  the expanded model.
* `Cslib.Logic.FO.Interpretation.onESOSentence`: the pullback of an existential second-order
  sentence along an interpretation.

## Main results

* `Cslib.Logic.FO.Interpretation.realize_onESOSentence`: the pullback holds in `M` exactly when the
  sentence holds in `I.Model M`.
* `Cslib.Logic.ESO.Definable.of_reduces`: existential second-order definability is closed under
  first-order reductions.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v u' v' w

namespace Cslib.Logic.FO.Interpretation

open FirstOrder Language Structure ESO

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {κ : Type} [Finite κ]
  (I : Interpretation L L' κ) {ι : Type} (arity : ι → ℕ)

/-- The positions of `n` tuples indexed by `κ`, concatenated into a sequence of length
`n * Nat.card κ`: each position is a coordinate of one of the tuples. -/
noncomputable def blockEquiv (κ : Type) [Finite κ] (n : ℕ) : Fin (n * Nat.card κ) ≃ Fin n × κ :=
  finProdFinEquiv.symm.trans ((Equiv.refl _).prodCongr (Finite.equivFin κ).symm)

/-- The extension of `I` to relation variables: a relation variable of arity `n` is defined by the
relation variable of arity `n * Nat.card κ` applied to the concatenated coordinates of its
arguments. -/
noncomputable def sumVar :
    Interpretation (L.sum (varLanguage fun i => arity i * Nat.card κ))
      (L'.sum (varLanguage arity)) κ where
  domain := LHom.sumInl.onFormula I.domain
  rel r := r.elim (fun R => LHom.sumInl.onFormula (I.rel R)) fun r =>
    Relations.formula (Sum.inr ⟨r.1, rfl⟩) fun m =>
      .var ((blockEquiv κ _ m).map (Fin.cast r.2) _root_.id)

variable {I} {M : Type w} [L.Structure M] {arity}

/-- The concatenated coordinates of a sequence of elements of an interpreted structure. -/
noncomputable def flatten {n : ℕ} (x : Fin n → I.Model M) : Fin (n * Nat.card κ) → M :=
  fun m => (x (blockEquiv κ n m).1).1 (blockEquiv κ n m).2

private theorem flatten_injective {n : ℕ} :
    Function.Injective (flatten (I := I) (M := M) (n := n)) := by
  intro x y h
  funext a
  refine Model.ext (funext fun j => ?_)
  have := congrFun h ((blockEquiv κ n).symm (a, j))
  simpa [flatten] using this

/-- Relations on `M` of arities multiplied by `Nat.card κ` define relations on `I.Model M`: a
sequence of elements is related when its concatenated coordinates are. -/
noncomputable def modelRel (R : ∀ i, Set (Fin (arity i * Nat.card κ) → M)) (i : ι) :
    Set (Fin (arity i) → I.Model M) :=
  flatten ⁻¹' R i

private theorem modelRel_surjective :
    Function.Surjective (modelRel (I := I) (M := M) (arity := arity)) :=
  fun R => ⟨fun i => flatten '' R i, funext fun _ => Set.preimage_image_eq _ flatten_injective⟩

variable [L'.IsRelational]

/-- The pullback of an existential second-order sentence along `I`: the arity of each relation
variable is multiplied by the number of coordinates, and the first-order part is pulled back along
the extension of `I` to the relation variables. -/
noncomputable def onESOSentence (Φ : ESO.Sentence L') : ESO.Sentence L where
  Var := Φ.Var
  arity i := Φ.arity i * Nat.card κ
  matrix := (I.sumVar Φ.arity).onSentence Φ.matrix

/-- The structure interpreted by the extension of `I` in the expansion of `M` by relations `R` is
isomorphic to the expansion of `I.Model M` by the relations `modelRel R`. -/
def sumVarEquiv (R : ∀ i, Set (Fin (arity i * Nat.card κ) → M)) :
    letI := varLanguage.structure R
    letI := varLanguage.structure (modelRel (I := I) R)
    (I.sumVar arity).Model M ≃[L'.sum (varLanguage arity)] I.Model M :=
  letI := varLanguage.structure R
  letI := varLanguage.structure (modelRel (I := I) R)
  { toEquiv := Equiv.subtypeEquivRight fun _ => LHom.realize_onFormula _ I.domain
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun r _ => match r with
      | .inl R => (LHom.realize_onFormula _ (I.rel R)).symm
      | .inr _ => Iff.rfl }

/-- **The pullback of an existential second-order sentence** along `I` holds in `M` exactly when
the sentence holds in the structure interpreted by `I` in `M`. -/
theorem realize_onESOSentence (Φ : ESO.Sentence L') :
    (I.onESOSentence Φ).Realize M ↔ Φ.Realize (I.Model M) := by
  constructor
  · rintro ⟨R, h⟩
    let _ := varLanguage.structure (arity := fun i => Φ.arity i * Nat.card κ) R
    let _ := varLanguage.structure (modelRel (I := I) (arity := Φ.arity) R)
    have h' := (realize_onSentence (I := I.sumVar Φ.arity) M Φ.matrix).1 h
    exact ⟨modelRel R, (StrongHomClass.realize_sentence (sumVarEquiv (arity := Φ.arity) R)
      Φ.matrix).1 h'⟩
  · rintro ⟨R, h⟩
    obtain ⟨R, rfl⟩ := modelRel_surjective R
    let _ := varLanguage.structure (arity := fun i => Φ.arity i * Nat.card κ) R
    let _ := varLanguage.structure (modelRel (I := I) (arity := Φ.arity) R)
    have h' := (StrongHomClass.realize_sentence (sumVarEquiv (arity := Φ.arity) R) Φ.matrix).2 h
    exact ⟨R, (realize_onSentence (I := I.sumVar Φ.arity) M Φ.matrix).2 h'⟩

end Cslib.Logic.FO.Interpretation

namespace Cslib.Logic.ESO

open FirstOrder Language CategoryTheory

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L'.IsRelational]

/-- **Existential second-order definability is closed under first-order reductions**: if `K`
reduces to a class `K'` defined by `Φ`, then `K` is defined by the pullback of `Φ`
[Immerman, Framework 3.12][Immerman1999]. -/
theorem Definable.of_reduces {K : Set (Bundled.{w} L.Structure)}
    {K' : Set (Bundled.{w} L'.Structure)} (hK' : Definable K') (h : FO.Reduces K K') :
    Definable K := by
  obtain ⟨κ, _, I, hI⟩ := h
  obtain ⟨Φ, hΦ⟩ := hK'
  refine ⟨I.onESOSentence Φ, fun M _ => ?_⟩
  rw [hI M, hΦ (Bundled.of (I.Model M)), I.realize_onESOSentence]
  rfl

end Cslib.Logic.ESO
