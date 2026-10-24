/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Tactic.FirstOrder.Init
public import Mathlib.ModelTheory.Semantics

/-!
# First-order interpretations

A first-order interpretation `I` of a relational language `L'` in a language `L`, of dimension `ι`
(a finite type), consists of a domain formula `δ` of `L` in variables `ι` and, for each relation
symbol `R` of `L'` of arity `n`, a formula `I.rel R` of `L` with a block of variables `ι` for each
of the `n` arguments. In an `L`-structure `M` it defines the `L'`-structure `I.Model M` whose
elements are the tuples `x : ι → M` satisfying `δ`, with `R` holding of `x₁, …, xₙ` when `I.rel R`
holds of their coordinates. Equality of the interpreted structure is equality of tuples. These are
Immerman's first-order queries [Immerman, Section 1.4][Immerman1999], with a finite type of
coordinates in place of the dimension `k`, so that composites need no reindexing.

Every formula `φ` of `L'` pulls back to a formula `I.onFormula φ` of `L`, obtained by replacing each
variable by a tuple of variables, each relation symbol by its defining formula, equality by
equality of coordinates, and each quantifier by a quantifier over a block of variables relativized
to `δ`. Truth is preserved: `M ⊨ I.onSentence φ ↔ I.Model M ⊨ φ`
[Immerman, Definition 3.3 and Proposition 3.5][Immerman1999]. Interpretations act on isomorphisms
(`Interpretation.mapEquiv`) and compose (`Interpretation.comp`), the interpreted structure of a
composite being isomorphic to the iterated one (`Interpretation.compEquiv`).

The arguments of `Interpretation L L' ι` are in the order of the map on structures, which turns
`L`-structures into `L'`-structures as a reduction turns instances of one problem into instances
of another; formulas are mapped the other way, from `L'` to `L`.

Senellart and Gnatenko build interpretations, the pullback of formulas and first-order reductions
over Mathlib's model theory as well [Senellart and Gnatenko][SenellartGnatenko2026]. Their
interpretations are tagged: the interpreted universe is all of `Tag × (Fin dim → M)` for a finite
type of tags, with no domain formula (a relativized variant restricts it), and a relation symbol
has a defining formula for each choice of tags of its arguments. Here the interpreted universe is
the set of tuples `ι → M` defined by the domain formula, with no tags, and the coordinates range
over any finite type `ι` rather than `Fin dim`, so that the coordinates `κ × ι` of a composite
need no reindexing.

## Main definitions

* `Cslib.Logic.FO.Interpretation`, `Cslib.Logic.FO.Interpretation.empty`, `Cslib.Logic.FO.termVar`:
  a first-order interpretation of `L'` in `L` of dimension `ι`, the empty interpretation, and
  variable extraction for relational terms.
* `Cslib.Logic.FO.Interpretation.Model`, `Cslib.Logic.FO.Interpretation.Model.mk`: the
  `L'`-structure interpreted in an `L`-structure and its element constructor.
* `Cslib.Logic.FO.Interpretation.snocVar`, `Cslib.Logic.FO.Interpretation.onBoundedFormula`,
  `Cslib.Logic.FO.Interpretation.onFormula`, `Cslib.Logic.FO.Interpretation.onSentence`: the
  pullback of bounded formulas, formulas, and sentences of `L'` to `L`.
* `Cslib.Logic.FO.Interpretation.id`: the identity interpretation of a relational language.
* `Cslib.Logic.FO.Interpretation.comp`: the composite of two interpretations.

## Main results

* `Cslib.Logic.FO.Interpretation.realize_onFormula`,
  `Cslib.Logic.FO.Interpretation.realize_onSentence`: the pullback of a formula holds in `M`
  exactly when the formula holds in the interpreted structure.
* `Cslib.Logic.FO.Interpretation.mapEquiv`: isomorphic structures interpret isomorphic structures.
* `Cslib.Logic.FO.Interpretation.idEquiv`, `Cslib.Logic.FO.Interpretation.compEquiv`: the identity
  and composite interpretations, up to isomorphism.
* `Cslib.Logic.FO.Interpretation.realize_comp_domain`,
  `Cslib.Logic.FO.Interpretation.relMap_comp_model`: the domain and relations of a composite
  interpreted structure are those of the iterated one.

## Implementation notes

The interpreted language is relational, as in finite model theory: interpreting function symbols
would need, in every structure, a proof that their defining formulas define functions. There is no
congruence relation, so equality is interpreted by equality of tuples, as in Immerman's
first-order queries. The pullback uses Mathlib's `FirstOrder.Language.Formula.iAlls` and
`FirstOrder.Language.Formula.iInf`, which choose an enumeration of `ι`, so it is noncomputable.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [P. Senellart and A. Gnatenko, *Descriptive Complexity in Lean: Completeness by First-Order
  Reductions*][SenellartGnatenko2026]
-/

@[expose] public section

universe u v u' v' u'' v'' w

namespace Cslib.Logic.FO

open FirstOrder Language Structure

/-- A **first-order interpretation** of the language `L'` in the language `L`, of dimension `ι`:
a domain formula in variables `ι`, and for each relation symbol of `L'` of arity `n` a formula with
variables `Fin n × ι`, a block of `ι` variables for each argument. -/
structure Interpretation (L : Language.{u, v}) (L' : Language.{u', v'}) (ι : Type*) where
  /-- The domain formula: the elements of an interpreted structure are the tuples satisfying it. -/
  domain : L.Formula ι
  /-- The formula defining a relation symbol, with a block of variables for each argument. -/
  rel : ∀ {n : ℕ}, L'.Relations n → L.Formula (Fin n × ι)

/-- The interpretation of dimension one with an empty domain. -/
def Interpretation.empty (L : Language.{u, v}) (L' : Language.{u', v'}) :
    Interpretation L L' Unit where
  domain := ⊥
  rel _ := ⊥

/-- In a relational language a term is a variable; this is that variable. -/
def termVar {L' : Language.{u', v'}} [L'.IsRelational] {β : Type*} : L'.Term β → β
  | .var x => x
  | .func f _ => isEmptyElim f

/-- Extracting the variable of `Term.var x` returns `x`. -/
@[simp]
theorem termVar_var {L' : Language.{u', v'}} [L'.IsRelational] {β : Type*} (x : β) :
    termVar (Term.var x : L'.Term β) = x :=
  rfl

/-- In a relational language a term takes the value of its variable. -/
theorem realize_termVar {L' : Language.{u', v'}} [L'.IsRelational] {β N : Type*} [L'.Structure N]
    (t : L'.Term β) (v : β → N) : t.realize v = v (termVar t) := by
  cases t with
  | var => rfl
  | func f => exact isEmptyElim f

namespace Interpretation

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {ι : Type*}
  (I : Interpretation L L' ι) (M : Type w) [L.Structure M]

/-- The universe of the structure interpreted by `I` in `M`: the tuples satisfying the domain
formula. -/
def Model : Type _ :=
  {x : ι → M // I.domain.Realize x}

variable {I M}

/-- Construct an element of the interpreted structure from a tuple satisfying the domain formula.
Using this constructor rather than `Subtype.mk` keeps the syntactic type `I.Model M` at reducible
transparency. -/
def Model.mk (x : ι → M) (hx : I.domain.Realize x) : I.Model M :=
  ⟨x, hx⟩

/-- The underlying tuple of `Model.mk x hx` is `x`. -/
@[simp, fo_realize]
theorem Model.val_mk (x : ι → M) (hx : I.domain.Realize x) : (Model.mk x hx).1 = x :=
  rfl

/-- Two elements of `I.Model M` are equal if their underlying tuples are equal. -/
theorem Model.ext {x y : I.Model M} (h : x.1 = y.1) : x = y :=
  Subtype.ext h

/-- Elements of an interpreted structure are equal when all their coordinates are. -/
@[fo_realize]
theorem Model.ext_iff {x y : I.Model M} : x = y ↔ ∀ i, x.1 i = y.1 i :=
  ⟨fun h _ => h ▸ rfl, fun h => Model.ext (funext h)⟩

/-- When `ι` and `M` are finite, the interpreted domain `I.Model M` is finite. -/
instance [Finite ι] [Finite M] : Finite (I.Model M) :=
  Subtype.finite

variable [L'.IsRelational]

/-- The structure interpreted by `I` in `M`: a relation symbol holds of some tuples when its
defining formula holds of their coordinates. -/
instance : L'.Structure (I.Model M) where
  RelMap R x := (I.rel R).Realize fun p => (x p.1).1 p.2

/-- A relation symbol `R` holds on `x` in `I.Model M` iff `I.rel R` holds of the coordinates
`p ↦ (x p.1).1 p.2`. -/
@[fo_realize]
theorem relMap_model {n : ℕ} (R : L'.Relations n) (x : Fin n → I.Model M) :
    RelMap R x ↔ (I.rel R).Realize fun p => (x p.1).1 p.2 :=
  Iff.rfl

/-! ### Isomorphisms -/

variable {N : Type*} [L.Structure N]

/-- **Interpretations act on isomorphisms**: an isomorphism `M ≃[L] N` maps tuples of `M`
coordinatewise to tuples of `N`. -/
def mapEquiv (I : Interpretation L L' ι) (e : M ≃[L] N) : I.Model M ≃[L'] I.Model N where
  toFun x := ⟨e ∘ x.1, (StrongHomClass.realize_formula e _).2 x.2⟩
  invFun y := ⟨e.symm ∘ y.1, (StrongHomClass.realize_formula e.symm _).2 y.2⟩
  left_inv _ := Model.ext <| funext fun _ => e.symm_apply_apply _
  right_inv _ := Model.ext <| funext fun _ => e.apply_symm_apply _
  map_fun' f := isEmptyElim f
  map_rel' R x := StrongHomClass.realize_formula e (I.rel R) (v := fun p => (x p.1).1 p.2)

/-- The underlying tuple of `I.mapEquiv e x` is `e ∘ x.1`. -/
@[simp]
theorem mapEquiv_apply_val (e : M ≃[L] N) (x : I.Model M) : (I.mapEquiv e x).1 = e ∘ x.1 :=
  rfl

/-! ### The pullback of formulas -/

variable [Finite ι] {α : Type*}

/-- The variables of the pullback of the body of a quantifier: the coordinates of the newly bound
variable become the variables `Sum.inr`, to be quantified. -/
def snocVar {n : ℕ} (p : (α ⊕ Fin (n + 1)) × ι) : ((α ⊕ Fin n) × ι) ⊕ ι :=
  p.1.elim (fun a => .inl (.inl a, p.2))
    (Fin.lastCases (.inr p.2) (fun j => .inl (.inr j, p.2)))

variable (I) in
/-- The pullback of a bounded formula of `L'` along `I`, with each free or bound variable replaced
by a block of free variables: relation symbols are replaced by their defining formulas, equality by
equality of all coordinates, and quantifiers by quantifiers over tuples satisfying the domain
formula. -/
noncomputable def onBoundedFormula : ∀ {n : ℕ}, L'.BoundedFormula α n → L.Formula ((α ⊕ Fin n) × ι)
  | _, .falsum => ⊥
  | _, .equal t₁ t₂ =>
    Formula.iInf fun i => Term.equal (.var (termVar t₁, i)) (.var (termVar t₂, i))
  | _, .rel R ts => (I.rel R).relabel fun p => (termVar (ts p.1), p.2)
  | _, .imp φ ψ => (onBoundedFormula φ).imp (onBoundedFormula ψ)
  | _, .all φ =>
    Formula.iAlls ι ((I.domain.relabel Sum.inr).imp ((onBoundedFormula φ).relabel snocVar))

omit [L'.IsRelational] [Finite ι] in
/-- Under `snocVar`, the values of the coordinates of a sequence of elements extended by `y` are
those of the extended sequence. -/
private theorem sumElim_comp_snocVar {n : ℕ} (v : α → I.Model M) (xs : Fin n → I.Model M)
    (y : I.Model M) :
    Sum.elim (fun p : (α ⊕ Fin n) × ι => (Sum.elim v xs p.1).1 p.2) y.1 ∘ snocVar =
      fun p => (Sum.elim v (Fin.snoc xs y) p.1).1 p.2 := by
  funext p
  rcases p with ⟨a | j, i⟩
  · rfl
  · induction j using Fin.lastCases with
    | last => simp [snocVar]
    | cast j => simp [snocVar]

/-- **The pullback of a bounded formula** holds of the coordinates of some elements of the
interpreted structure exactly when the formula holds of these elements. -/
theorem realize_onBoundedFormula {n : ℕ} (φ : L'.BoundedFormula α n) (v : α → I.Model M)
    (xs : Fin n → I.Model M) :
    (I.onBoundedFormula φ).Realize (fun p => (Sum.elim v xs p.1).1 p.2) ↔ φ.Realize v xs := by
  induction φ with
  | falsum => simp [onBoundedFormula, BoundedFormula.Realize]
  | equal t₁ t₂ =>
    simp only [onBoundedFormula, Formula.realize_iInf, Formula.realize_equal, Term.realize_var,
      BoundedFormula.Realize, realize_termVar t₁, realize_termVar t₂]
    exact ⟨fun h => Model.ext (funext h), fun h _ => by rw [h]⟩
  | rel R ts =>
    simp only [onBoundedFormula, Formula.realize_relabel, BoundedFormula.Realize]
    change _ ↔ (I.rel R).Realize fun p => ((ts p.1).realize (Sum.elim v xs)).1 p.2
    simp only [realize_termVar]
    rfl
  | imp φ ψ ihφ ihψ =>
    simp only [onBoundedFormula, Formula.Realize, BoundedFormula.realize_imp] at *
    rw [ihφ, ihψ]
  | all φ ih =>
    simp only [onBoundedFormula, Formula.realize_iAlls, Formula.realize_imp,
      Formula.realize_relabel, BoundedFormula.realize_all]
    refine ⟨fun h y => ?_, fun h y hy => ?_⟩
    · rw [← ih, ← sumElim_comp_snocVar]
      exact h y.1 y.2
    · exact (congrArg (I.onBoundedFormula φ).Realize (sumElim_comp_snocVar v xs ⟨y, hy⟩)).mpr
        ((ih _).2 (h ⟨y, hy⟩))

variable (I) in
/-- The pullback of a formula of `L'` along `I`: a formula of `L` with a block of variables `ι`
for each free variable. -/
noncomputable def onFormula (φ : L'.Formula α) : L.Formula (α × ι) :=
  (I.onBoundedFormula φ).relabel fun p => (p.1.elim id finZeroElim, p.2)

/-- **The pullback of a formula** holds of the coordinates of some elements of the interpreted
structure exactly when the formula holds of these elements
[Immerman, Proposition 3.5 and Remark 3.6][Immerman1999]. -/
@[simp, fo_realize]
theorem realize_onFormula (φ : L'.Formula α) (v : α → I.Model M) :
    (I.onFormula φ).Realize (fun p => (v p.1).1 p.2) ↔ φ.Realize v := by
  rw [onFormula, Formula.realize_relabel]
  refine Iff.trans (iff_of_eq (congrArg _ (funext fun p => ?_)))
    (realize_onBoundedFormula φ v default)
  rcases p with ⟨a | j, i⟩
  · rfl
  · exact j.elim0

variable (I) in
/-- The pullback of a sentence of `L'` along `I`, a sentence of `L`
[Immerman, Definition 3.3][Immerman1999]. -/
noncomputable def onSentence (φ : L'.Sentence) : L.Sentence :=
  (I.onFormula φ).relabel Prod.fst

variable (M) in
/-- **The pullback of a sentence** holds in `M` exactly when the sentence holds in the structure
interpreted by `I` in `M` [Immerman, Proposition 3.5][Immerman1999]. -/
@[simp, fo_realize]
theorem realize_onSentence (φ : L'.Sentence) : M ⊨ I.onSentence φ ↔ I.Model M ⊨ φ := by
  rw [onSentence, Sentence.Realize, Formula.realize_relabel, Sentence.Realize,
    ← realize_onFormula φ default]
  exact iff_of_eq (congrArg _ (funext fun p => p.1.elim))

end Interpretation

/-! ### The identity and composite interpretations -/

namespace Interpretation

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {L'' : Language.{u'', v''}}
  {M : Type w} [L.Structure M]

variable (L) in
/-- The identity interpretation of a relational language, of dimension one: every element is in
the domain and every relation symbol defines itself. -/
protected def id : Interpretation L L Unit where
  domain := ⊤
  rel R := R.formula fun i => .var (i, ())

/-- The structure interpreted by the identity interpretation is the structure itself. -/
def idEquiv [L.IsRelational] : (Interpretation.id L).Model M ≃[L] M where
  toFun x := x.1 ()
  invFun x := ⟨fun _ => x, Formula.realize_top.2 trivial⟩
  left_inv _ := Model.ext rfl
  right_inv _ := rfl
  map_fun' f := isEmptyElim f
  map_rel' _ _ := Iff.rfl

variable {ι κ : Type*} [Finite ι] [L'.IsRelational]

/-- The composite of an interpretation `I` of `L'` in `L` and an interpretation `J` of `L''` in
`L'`, an interpretation of `L''` in `L` whose tuples are indexed by pairs: the domain formula says
that each block is in the domain of `I` and that the blocks satisfy the pullback of the domain
formula of `J`, and the relation symbols are defined by the pullbacks of their definitions in `J`.
-/
noncomputable def comp [Finite κ] (J : Interpretation L' L'' κ) (I : Interpretation L L' ι) :
    Interpretation L L'' (κ × ι) where
  domain := Formula.iInf (fun j : κ => I.domain.relabel (j, ·)) ⊓ I.onFormula J.domain
  rel R := (I.onFormula (J.rel R)).relabel (Equiv.prodAssoc _ _ _)

variable [L''.IsRelational]

/-- **The composite of interpretations** interprets, up to isomorphism, the structure interpreted
by `J` in the structure interpreted by `I`. -/
def compEquiv [Finite κ] (J : Interpretation L' L'' κ)
    (I : Interpretation L L' ι) : J.Model (I.Model M) ≃[L''] (J.comp I).Model M where
  toFun x := ⟨fun p => (x.1 p.1).1 p.2, by
    simp only [comp, Formula.realize_inf, Formula.realize_iInf, Formula.realize_relabel]
    exact ⟨fun j => (x.1 j).2, (realize_onFormula J.domain x.1).2 x.2⟩⟩
  invFun z := ⟨fun j => ⟨fun i => z.1 (j, i), by
    have h := z.2
    simp only [comp, Formula.realize_inf, Formula.realize_iInf, Formula.realize_relabel] at h
    exact h.1 j⟩, by
    have h := z.2
    simp only [comp, Formula.realize_inf] at h
    exact (realize_onFormula J.domain _).1 h.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_fun' f := isEmptyElim f
  map_rel' R x := by
    change ((I.onFormula (J.rel R)).relabel (Equiv.prodAssoc _ _ _)).Realize _ ↔
      (J.rel R).Realize fun p => (x p.1).1 p.2
    rw [Formula.realize_relabel, ← realize_onFormula]
    rfl

/-- Evaluating `(compEquiv J I).symm z` at outer coordinate `j` and inner coordinate `i` yields
`z.1 (j, i)`. -/
@[simp, fo_realize]
theorem compEquiv_symm_apply_val_val [Finite κ] (J : Interpretation L' L'' κ)
    (I : Interpretation L L' ι) (z : (J.comp I).Model M) (j : κ) (i : ι) :
    (((compEquiv J I).symm z).1 j).1 i = z.1 (j, i) :=
  rfl

omit [L''.IsRelational] in
/-- The domain formula of a composite holds of a tuple exactly when each of its blocks is in the
domain of `I` and the blocks, as elements of the structure interpreted by `I`, satisfy the domain
formula of `J`. -/
@[fo_realize]
theorem realize_comp_domain [Finite κ] (J : Interpretation L' L'' κ) (I : Interpretation L L' ι)
    (v : κ × ι → M) :
    (J.comp I).domain.Realize v ↔ ∃ h : ∀ j, I.domain.Realize fun i => v (j, i),
      @Formula.Realize L' (I.Model M) _ κ J.domain fun j => Model.mk (fun i => v (j, i)) (h j) := by
  simp only [comp, Formula.realize_inf, Formula.realize_iInf, Formula.realize_relabel]
  exact ⟨fun h => ⟨h.1, (realize_onFormula J.domain _).1 h.2⟩,
    fun ⟨h, h'⟩ => ⟨h, (realize_onFormula J.domain _).2 h'⟩⟩

/-- A relation of a composite interpreted structure holds exactly when it holds in the iterated
interpreted structure. -/
@[fo_realize high]
theorem relMap_comp_model [Finite κ] (J : Interpretation L' L'' κ) (I : Interpretation L L' ι)
    {n : ℕ} (R : L''.Relations n) (x : Fin n → (J.comp I).Model M) :
    RelMap R x ↔ RelMap R fun i => (compEquiv J I).symm (x i) :=
  ((compEquiv J I).symm.map_rel R x).symm

end Interpretation

end Cslib.Logic.FO
