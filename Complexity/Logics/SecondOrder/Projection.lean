/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.SecondOrder.Existential
public import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Finset.Sort

/-!
# Existential projection of relation variables and guessed linear orders

Existential second-order sentences are closed under existentially quantifying additional relation
variables: an existential second-order sentence `Φ` over `L.sum (varLanguage ar₀)` projects to an
existential second-order sentence `Φ.project` over `L` whose relation variables are `ι₀ ⊕ Φ.Var`,
holding in `M` iff some interpretation of `ar₀` on `M` makes `Φ` hold (`Sentence.realize_project`).

In descriptive complexity on unordered structures, a standard application of `Sentence.project` is
guessing an arbitrary strict linear order on a finite domain [Fagin, Proof of Theorem 6][Fagin1974],
[Immerman, Proof of Theorem 7.8][Immerman1999]. The language `orderLanguage` has a single binary
relation symbol `ltSym`, constrained by `isStrictLinearOrderSentence` to be irreflexive, transitive,
and trichotomous. On a finite structure `M`, the expansions satisfying `isStrictLinearOrderSentence`
are precisely the linear orders `orderRelOfEquiv e` induced by bijections `e : M ≃ Fin (Nat.card M)`
(`realize_isStrictLinearOrderSentence`).

## Implementation notes

`orderLanguage` is defined as `varLanguage (fun _ : Unit => 2)` (with strict `<` symbol `ltSym` and
`isStrictLinearOrderSentence`) rather than Mathlib's `Language.order` for two reasons:
1. Existential second-order quantification (`ESO.Sentence` and `ESO.Sentence.project`) quantifies
   over relation blocks of the form `varLanguage arity` adjoined via `Language.sum`. Defining
   `orderLanguage` directly as `varLanguage (fun _ : Unit => 2)` makes `Sentence.withLinearOrder` an
   immediate instance of `Sentence.project`.
2. Mathlib's `Language.order` represents a weak order `≤` (`Language.IsOrdered`), whereas the
   colexicographic tuple order in Fagin's power interpretation compares the highest differing
   coordinate via an irreflexive strict `<` relation.

## Main definitions

* `Cslib.Logic.ESO.varLanguage.sumAssoc`: the homomorphism combining two blocks of relation
  variables into one.
* `Cslib.Logic.ESO.Sentence.project`: existential projection of an outer block of relation
  variables.
* `Cslib.Logic.ESO.orderLanguage`, `Cslib.Logic.ESO.ltSym`,
  `Cslib.Logic.ESO.isStrictLinearOrderSentence`: the binary relation variable for a guessed strict
  linear order and its first-order axioms.
* `Cslib.Logic.ESO.orderRelOfEquiv`: the binary relation on `M` induced by a numbering
  `e : M ≃ Fin n`.
* `Cslib.Logic.ESO.Sentence.withLinearOrder`: existentially quantifying a strict linear order on
  the domain before evaluating an `ESO.Sentence (L.sum orderLanguage)`.

## Main results

* `Cslib.Logic.ESO.Sentence.realize_project`: `Φ.project` holds in `M` iff `Φ` holds in some
  expansion of `M` by relations for `ar₀`.
* `Cslib.Logic.ESO.realize_isStrictLinearOrderSentence_iff_irrefl_trans_trichotomous`: on any
  domain, a binary relation satisfies `isStrictLinearOrderSentence` iff it is irreflexive,
  transitive, and trichotomous.
* `Cslib.Logic.ESO.realize_isStrictLinearOrderSentence`: on a finite domain `M`, a binary
  relation satisfies `isStrictLinearOrderSentence` iff it is `orderRelOfEquiv e` for some
  `e : M ≃ Fin (Nat.card M)`.
* `Cslib.Logic.ESO.Sentence.realize_withLinearOrder`: on a finite structure `M`,
  `Φ.withLinearOrder` holds iff `Φ` holds on `(M, orderRelOfEquiv e)` for some numbering
  `e : M ≃ Fin (Nat.card M)`.
* `Cslib.Logic.ESO.Definable.of_withLinearOrder`: a class characterized on every finite structure
  under every numbering by a sentence over `L.sum orderLanguage` is existential second-order
  definable over `L`.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v w

namespace Cslib.Logic.ESO

open FirstOrder Language Structure CategoryTheory BoundedFormula

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-! ### Projection of relation variables -/

namespace varLanguage

variable {ι₁ ι₂ : Type} {ar₁ : ι₁ → ℕ} {ar₂ : ι₂ → ℕ}

/-- The homomorphism combining two successive blocks of relation variables `ar₁` and `ar₂` into a
single block `Sum.elim ar₁ ar₂`. -/
def sumAssoc :
    (L.sum (varLanguage ar₁)).sum (varLanguage ar₂) →ᴸ L.sum (varLanguage (Sum.elim ar₁ ar₂)) where
  onFunction _ f := match f with
    | .inl (.inl f) => .inl f
    | .inl (.inr f) => isEmptyElim f
    | .inr f => isEmptyElim f
  onRelation _ r := match r with
    | .inl (.inl r) => .inl r
    | .inl (.inr r) => .inr ⟨.inl r.1, r.2⟩
    | .inr r => .inr ⟨.inr r.1, r.2⟩

/-- The structure for `Sum.rec R₁ R₂` is an expansion along `sumAssoc` of the iterated sum
structure for `R₁` and `R₂`. -/
theorem sumAssoc_isExpansionOn (R₁ : ∀ i, Set (Fin (ar₁ i) → M))
    (R₂ : ∀ j, Set (Fin (ar₂ j) → M)) :
    @LHom.IsExpansionOn _ _ (sumAssoc (L := L) (ar₁ := ar₁) (ar₂ := ar₂)) M
      (@sumStructure _ _ M (@sumStructure _ _ M _ (varLanguage.structure R₁))
        (varLanguage.structure R₂))
      (@sumStructure _ _ M _
        (varLanguage.structure (arity := Sum.elim ar₁ ar₂) (Sum.rec R₁ R₂))) :=
  @LHom.IsExpansionOn.mk _ _ _ M
    (@sumStructure _ _ M (@sumStructure _ _ M _ (varLanguage.structure R₁))
      (varLanguage.structure R₂))
    (@sumStructure _ _ M _
      (varLanguage.structure (arity := Sum.elim ar₁ ar₂) (Sum.rec R₁ R₂)))
    (fun f _ => match f with
      | .inl (.inl _) => rfl
      | .inl (.inr f) => isEmptyElim f
      | .inr f => isEmptyElim f)
    (fun r _ => match r with
      | .inl (.inl _) => rfl
      | .inl (.inr _) => rfl
      | .inr _ => rfl)

end varLanguage

namespace Sentence

/-- Existentially quantify an additional block of relation variables `ar₀`, turning an existential
second-order sentence over `L.sum (varLanguage ar₀)` into one over `L`. -/
def project {ι₀ : Type} [Finite ι₀] {ar₀ : ι₀ → ℕ}
    (Φ : Sentence (L.sum (varLanguage ar₀))) : Sentence L where
  Var := ι₀ ⊕ Φ.Var
  arity := Sum.elim ar₀ Φ.arity
  matrix := varLanguage.sumAssoc.onSentence Φ.matrix

/-- **Existential projection**: `Φ.project` holds in `M` exactly when `Φ` holds in some expansion
of `M` by relations for `ar₀`. -/
@[simp]
theorem realize_project {ι₀ : Type} [Finite ι₀] {ar₀ : ι₀ → ℕ}
    (Φ : Sentence (L.sum (varLanguage ar₀))) :
    Φ.project.Realize M ↔
      ∃ R₀ : ∀ i, Set (Fin (ar₀ i) → M),
        letI := varLanguage.structure R₀
        Φ.Realize M := by
  unfold project Realize
  constructor
  · rintro ⟨R, hR⟩
    let R₀ : ∀ i, Set (Fin (ar₀ i) → M) := fun i => R (.inl i)
    let R₁ : ∀ j, Set (Fin (Φ.arity j) → M) := fun j => R (.inr j)
    have hR_eq : R = Sum.rec R₀ R₁ := by
      funext k; rcases k with i | j <;> rfl
    rw [hR_eq] at hR
    let _ := varLanguage.structure R₀
    let _ := varLanguage.structure R₁
    let _ := varLanguage.structure (arity := Sum.elim ar₀ Φ.arity) (Sum.rec R₀ R₁)
    have hexp := varLanguage.sumAssoc_isExpansionOn (L := L) R₀ R₁
    exact ⟨R₀, R₁, (@LHom.realize_onSentence _ _ M _ _ _ hexp Φ.matrix).1 hR⟩
  · rintro ⟨R₀, R₁, hR⟩
    let _ := varLanguage.structure R₀
    let _ := varLanguage.structure R₁
    let _ := varLanguage.structure (arity := Sum.elim ar₀ Φ.arity) (Sum.rec R₀ R₁)
    have hexp := varLanguage.sumAssoc_isExpansionOn (L := L) R₀ R₁
    exact ⟨Sum.rec R₀ R₁, (@LHom.realize_onSentence _ _ M _ _ _ hexp Φ.matrix).2 hR⟩

end Sentence

/-! ### Guessed strict linear order -/

/-- The language of a single binary relation variable, used for an existentially guessed strict
linear order on the domain. -/
abbrev orderLanguage : Language.{0, 0} :=
  varLanguage (fun _ : Unit => 2)

/-- The binary relation symbol `<` of `orderLanguage`. -/
def ltSym : orderLanguage.Relations 2 :=
  ⟨(), rfl⟩

/-- The first-order sentence over `orderLanguage` asserting that `ltSym` is a strict linear order
(irreflexive, transitive, and trichotomous). -/
def isStrictLinearOrderSentence : orderLanguage.Sentence :=
  ltSym.irreflexive ⊓ ltSym.transitive ⊓
    (∀' ∀' (ltSym.boundedFormula₂ &0 &1 ⊔ (&0 =' &1 ⊔ ltSym.boundedFormula₂ &1 &0)))

/-- The binary relation on `N` induced by a numbering `e : N ≃ Fin n`: `x 0` precedes `x 1` when
`e (x 0) < e (x 1)`. -/
def orderRelOfEquiv {N : Type w} {n : ℕ} (e : N ≃ Fin n) : ∀ _ : Unit, Set (Fin 2 → N) :=
  fun _ => {x | e (x 0) < e (x 1)}

/-- In `varLanguage.structure R`, the relation symbol `ltSym` holds of `x` iff `x ∈ R ()`. -/
theorem relMap_ltSym {N : Type w} (R : ∀ _ : Unit, Set (Fin 2 → N)) (x : Fin 2 → N) :
    (varLanguage.structure (arity := fun _ : Unit => 2) R).RelMap ltSym x ↔ x ∈ R () :=
  Iff.rfl

/-- On any type `N` (finite or not), a binary relation satisfies `isStrictLinearOrderSentence` iff
it is irreflexive, transitive, and trichotomous. -/
theorem realize_isStrictLinearOrderSentence_iff_irrefl_trans_trichotomous {N : Type w}
    (R : ∀ _ : Unit, Set (Fin 2 → N)) :
    (letI := varLanguage.structure (arity := fun _ : Unit => 2) R;
      N ⊨ isStrictLinearOrderSentence) ↔
      ((∀ a : N, ![a, a] ∉ R ()) ∧
        ∀ a b c : N, ![a, b] ∈ R () ∧ ![b, c] ∈ R () → ![a, c] ∈ R ()) ∧
      ∀ a b : N, ![a, b] ∈ R () ∨ a = b ∨ ![b, a] ∈ R () := by
  let _ := varLanguage.structure (arity := fun _ : Unit => 2) R
  rw [isStrictLinearOrderSentence, FirstOrder.Language.Sentence.realize_inf,
    FirstOrder.Language.Sentence.realize_inf, Relations.realize_irreflexive,
    Relations.realize_transitive, irrefl_def, isTrans_def]
  simp [and_imp, FirstOrder.Language.Sentence.Realize, Formula.Realize, relMap_ltSym, Fin.snoc]

/-- Every numbering `e : N ≃ Fin n` induces a strict linear order satisfying
`isStrictLinearOrderSentence`. -/
theorem realize_isStrictLinearOrderSentence_orderRelOfEquiv {N : Type w} {n : ℕ} (e : N ≃ Fin n) :
    (letI := varLanguage.structure (arity := fun _ : Unit => 2) (orderRelOfEquiv e);
      N ⊨ isStrictLinearOrderSentence) := by
  rw [realize_isStrictLinearOrderSentence_iff_irrefl_trans_trichotomous]
  refine ⟨⟨fun a => ?_, fun a b c ⟨h₁, h₂⟩ => ?_⟩, fun a b => ?_⟩
  · change ¬ (e a < e a)
    exact lt_irrefl _
  · change e a < e c
    exact lt_trans h₁ h₂
  · change e a < e b ∨ a = b ∨ e b < e a
    rw [← e.injective.eq_iff]
    exact lt_trichotomy (e a) (e b)

/-- On a finite type `N`, a binary relation satisfies `isStrictLinearOrderSentence` iff it is
`orderRelOfEquiv e` for some bijection `e : N ≃ Fin (Nat.card N)`. -/
theorem realize_isStrictLinearOrderSentence {N : Type w} [Finite N]
    (R : ∀ _ : Unit, Set (Fin 2 → N)) :
    (letI := varLanguage.structure (arity := fun _ : Unit => 2) R;
      N ⊨ isStrictLinearOrderSentence) ↔
      ∃ e : N ≃ Fin (Nat.card N), R = orderRelOfEquiv e := by
  constructor
  · intro h
    rcases (realize_isStrictLinearOrderSentence_iff_irrefl_trans_trichotomous R).1 h with
      ⟨⟨hirr, htrans⟩, htri⟩
    let r : N → N → Prop := fun a b => ![a, b] ∈ R ()
    have : Std.Irrefl r := ⟨hirr⟩
    have : IsTrans N r := ⟨fun a b c hab hbc => htrans a b c ⟨hab, hbc⟩⟩
    have : Std.Trichotomous r :=
      ⟨fun a b hab hba => (htri a b).resolve_left hab |>.resolve_right hba⟩
    have : IsStrictTotalOrder N r := {}
    classical
    let _ := Fintype.ofFinite N
    let _ : LinearOrder N := linearOrderOfSTO r
    let iso := (Fintype.orderIsoFinOfCardEq N Nat.card_eq_fintype_card.symm).symm
    refine ⟨iso.toEquiv, funext fun ⟨⟩ => Set.ext fun x => ?_⟩
    have hx : x = ![x 0, x 1] := List.ofFn_inj.1 (by simp [List.ofFn_succ])
    conv_lhs => rw [hx]
    exact iso.lt_iff_lt.symm
  · rintro ⟨e, rfl⟩
    exact realize_isStrictLinearOrderSentence_orderRelOfEquiv e

namespace Sentence

/-- Existentially quantify a strict linear order on the domain before evaluating an existential
second-order sentence `Φ` over `L.sum orderLanguage`. -/
def withLinearOrder (Φ : Sentence (L.sum orderLanguage)) : Sentence L :=
  (Sentence.ofSentence (LHom.sumInr.onSentence isStrictLinearOrderSentence) ⊓ Φ).project

/-- On a finite structure `M`, `Φ.withLinearOrder` holds iff `Φ` holds on `(M, orderRelOfEquiv e)`
for some numbering `e : M ≃ Fin (Nat.card M)`. -/
theorem realize_withLinearOrder [Finite M] (Φ : Sentence (L.sum orderLanguage)) :
    Φ.withLinearOrder.Realize M ↔
      ∃ e : M ≃ Fin (Nat.card M),
        letI := varLanguage.structure (arity := fun _ : Unit => 2) (orderRelOfEquiv e)
        Φ.Realize M := by
  rw [withLinearOrder, realize_project]
  constructor
  · rintro ⟨R, hR⟩
    let _ := varLanguage.structure (arity := fun _ : Unit => 2) R
    obtain ⟨hlin, hΦ⟩ := (realize_inf (M := M)).1 hR
    rw [realize_ofSentence, LHom.realize_onSentence] at hlin
    obtain ⟨e, rfl⟩ := (realize_isStrictLinearOrderSentence R).1 hlin
    exact ⟨e, hΦ⟩
  · rintro ⟨e, hΦ⟩
    let _ := varLanguage.structure (arity := fun _ : Unit => 2) (orderRelOfEquiv e)
    refine ⟨orderRelOfEquiv e, (realize_inf (M := M)).2 ⟨?_, hΦ⟩⟩
    rw [realize_ofSentence, LHom.realize_onSentence]
    exact realize_isStrictLinearOrderSentence_orderRelOfEquiv e

end Sentence

/-- If `Φ : Sentence (L.sum orderLanguage)` agrees with `K` on every finite structure `M` under
every numbering `e : M ≃ Fin (Nat.card M)`, then `K` is existential second-order definable over `L`
(witnessed by `Φ.withLinearOrder`). -/
theorem Definable.of_withLinearOrder {K : Set (Bundled.{w} L.Structure)}
    (Φ : Sentence (L.sum orderLanguage))
    (hΦ : ∀ (M : Bundled.{w} L.Structure) [Finite M] (e : M ≃ Fin (Nat.card M)),
      M ∈ K ↔
        letI := varLanguage.structure (arity := fun _ : Unit => 2) (orderRelOfEquiv e)
        Φ.Realize M) :
    Definable K := by
  refine ⟨Φ.withLinearOrder, fun M _ => ?_⟩
  rw [Sentence.realize_withLinearOrder]
  exact ⟨fun hM => ⟨Finite.equivFin M, (hΦ M (Finite.equivFin M)).1 hM⟩,
    fun ⟨e, h⟩ => (hΦ M e).2 h⟩

end Cslib.Logic.ESO
