/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Interpretation.Tuple
public import Complexity.Logics.FirstOrder.ProjectionFormula

/-!
# Relativized first-order projections

A `Projection N N' L L' ι` interprets numeric vocabulary `N'` using only numeric vocabulary `N`,
and each output relation of `L'` by a projection formula over `N` and the input vocabulary `L`.
The domain is numeric as well: input bits affect neither the output universe nor numeric tests.

This is a relativized, vocabulary-parametric extension of first-order projections
[Immerman and Landau, Definitions 3.3--3.6][ImmermanLandau1995]. Classical projections additionally
use a positive-dimensional full tuple
universe and preserve the canonical numeric predicates. Neither those restrictions nor a
logarithmic-space encoding theorem are implicit here. The target vocabularies are relational,
as required by `Interpretation`; numeric constants can instead be represented by unary predicates.

## Main definitions

* `Cslib.Logic.FO.Projection`: a numeric interpretation and a projection formula for each output
  relation.
* `Cslib.Logic.FO.Projection.toInterpretation`: the ordinary interpretation on the sum vocabularies.
* `Cslib.Logic.FO.Projection.inputStructure`: the output input-relation structure on the numeric
  model.
* `Cslib.Logic.FO.Projection.tupleInputStructure`: the output input-relation structure on the full
  tuple domain.
* `Cslib.Logic.FO.Projection.onLiteral`, `Cslib.Logic.FO.Projection.onFormula`: pull back an input
  literal or a projection formula to a projection formula.
* `Cslib.Logic.FO.Projection.id`, `Cslib.Logic.FO.Projection.idEquiv`,
  `Cslib.Logic.FO.Projection.comp`: the identity projection, its isomorphism, and composition with
  product coordinates.
* `Cslib.Logic.FO.Projection.IsQF`: quantifier-free relativized projections.

## Main results

* `Cslib.Logic.FO.Projection.realize_onFormula`: projection pullback preserves truth.
* `Cslib.Logic.FO.Projection.modelEquiv`: agreement with the ordinary interpretation of sum
  vocabularies.
* `Cslib.Logic.FO.Projection.tupleModelEquiv`: isomorphism of the numeric model with the full tuple
  domain when the numeric domain formula always holds.
* `Cslib.Logic.FO.Projection.compEquiv`: composition agrees with successive interpretations of both
  vocabularies.
* `Cslib.Logic.FO.Projection.relMap_comp_inputStructure`,
  `Cslib.Logic.FO.Projection.realize_comp_rel_tupleStructure`: the input relations of a composite
  projection are those of the iterated projection.
* `Cslib.Logic.FO.Projection.IsQF.comp`: quantifier-free relativized projections compose.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995]
-/

@[expose] public section

universe u v u' v' u'' v'' w

namespace Cslib.Logic.FO

open FirstOrder Language Structure

/-- A relativized projection between two numeric/input vocabulary pairs. Numeric predicates and
the output domain are interpreted without access to the input relations. -/
structure Projection (N N' L L' : Language) (ι : Type*) where
  /-- Interpret the output numeric structure and domain using numeric formulas alone. -/
  numeric : Interpretation N N' ι
  /-- Each output input-relation bit is a numeric choice of a constant or input literal. -/
  rel : ∀ {n : ℕ}, L'.Relations n → ProjectionFormula N L (Fin n × ι)

namespace Projection

variable {N N' N'' L L' L'' : Language} {ι κ α : Type*}

/-- Forget the projection restriction, retaining an ordinary interpretation. -/
def toInterpretation (I : Projection N N' L L' ι) :
    Interpretation (N.sum L) (N'.sum L') ι where
  domain := LHom.sumInl.onFormula I.numeric.domain
  rel
    | .inl R => LHom.sumInl.onFormula (I.numeric.rel R)
    | .inr R => (I.rel R).toFormula

/-- The output input-relation structure. It is supplied explicitly so that it does not compete
with the numeric structure instance on the same universe. -/
@[instance_reducible]
def inputStructure (I : Projection N N' L L' ι) (M : Type*)
    [N.Structure M] [L.Structure M] [L'.IsRelational] : L'.Structure (I.numeric.Model M) where
  RelMap R x := (I.rel R).toFormula.Realize fun p => (x p.1).1 p.2

/-- An output relation holds in `I.inputStructure M` iff its defining projection formula holds on
the underlying coordinate tuples. -/
@[fo_realize]
theorem relMap_inputStructure [L'.IsRelational] (I : Projection N N' L L' ι) {M : Type*}
    [N.Structure M] [L.Structure M] {n : ℕ} (R : L'.Relations n) (x : Fin n → I.numeric.Model M) :
    (I.inputStructure M).RelMap R x ↔ (I.rel R).toFormula.Realize fun p => (x p.1).1 p.2 :=
  Iff.rfl

/-- The numeric model with projected input relations agrees with the ordinary interpretation
of the sum vocabularies. This connects projection semantics to the existing interpretation API. -/
def modelEquiv [N'.IsRelational] [L'.IsRelational]
    (I : Projection N N' L L' ι) (M : Type*) [N.Structure M] [L.Structure M] :
    letI := I.inputStructure M
    I.numeric.Model M ≃[N'.sum L'] I.toInterpretation.Model M := by
  letI := I.inputStructure M
  exact
    { toFun x := ⟨x.1, (LHom.realize_onFormula LHom.sumInl I.numeric.domain).2 x.2⟩
      invFun x := ⟨x.1, (LHom.realize_onFormula LHom.sumInl I.numeric.domain).1 x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_fun' f := isEmptyElim f
      map_rel' R x := by
        cases R with
        | inl R => exact LHom.realize_onFormula LHom.sumInl (I.numeric.rel R)
        | inr R => rfl }

/-- Pull back one literal, substituting a projection for its relation and preserving polarity. -/
def onLiteral (I : Projection N N' L L' ι) :
    InputLiteral L' α → ProjectionFormula N L (α × ι)
  | .const b => .leaf (.const b)
  | .rel R args neg =>
    let p := (I.rel R).relabel fun q => (args q.1, q.2)
    if neg then p.not else p

/-- Pull back a projection formula. Numeric tests use the ordinary numeric interpretation;
input literals are replaced by projections. -/
noncomputable def onFormula [Finite ι] [N'.IsRelational]
    (I : Projection N N' L L' ι) (p : ProjectionFormula N' L' α) :
    ProjectionFormula N L (α × ι) :=
  p.subst I.numeric.onFormula I.onLiteral

/-- Projection pullback is truth preserving on the interpreted numeric universe, equipped with
the input relations specified by the projection. -/
theorem realize_onFormula [Finite ι] [N'.IsRelational] [L'.IsRelational]
    (I : Projection N N' L L' ι) {M : Type*} [N.Structure M] [L.Structure M]
    (p : ProjectionFormula N' L' α) (x : α → I.numeric.Model M) :
    letI := I.inputStructure M
    (I.onFormula p).toFormula.Realize (fun q => (x q.1).1 q.2) ↔ p.toFormula.Realize x := by
  let := I.inputStructure M
  apply ProjectionFormula.realize_subst
  · exact fun g => I.numeric.realize_onFormula g x
  · intro l
    cases l with
    | const b => simp [onLiteral, ProjectionFormula.toFormula, InputLiteral.Realize]
    | rel R args neg =>
      cases neg
      · change ((I.rel R).relabel _).toFormula.Realize _ ↔ _
        rw [ProjectionFormula.realize_relabel]
        rfl
      · change ((I.rel R).relabel _).not.toFormula.Realize _ ↔ _
        rw [ProjectionFormula.realize_not, ProjectionFormula.realize_relabel]
        rfl

/-- The identity projection, with one coordinate and unchanged numeric and input relations. -/
protected def id (N L : Language) : Projection N N L L Unit where
  numeric := .id N
  rel R := .leaf (.rel R (fun i => (i, ())) false)

/-- The identity projection preserves both numeric and input relations. -/
def idEquiv [N.IsRelational] [L.IsRelational] (M : Type*) [N.Structure M] [L.Structure M] :
    letI := (Projection.id N L).inputStructure M
    (Projection.id N L).numeric.Model M ≃[N.sum L] M := by
  letI := (Projection.id N L).inputStructure M
  exact
    { (Interpretation.idEquiv (L := N) (M := M)).toEquiv with
      map_fun' f := isEmptyElim f
      map_rel' R x := by cases R <;> rfl }

/-- Compose projections, including their numeric interpretations. The output coordinate type is
the product of the two coordinate types. -/
noncomputable def comp [Finite ι] [Finite κ] [N'.IsRelational]
    (J : Projection N' N'' L' L'' κ) (I : Projection N N' L L' ι) :
    Projection N N'' L L'' (κ × ι) where
  numeric := J.numeric.comp I.numeric
  rel R := (I.onFormula (J.rel R)).relabel (Equiv.prodAssoc _ _ _)

/-- A composite projection is isomorphic to successive interpretation, preserving both numeric
and input relations. The underlying equivalence is the existing numeric composition map. -/
def compEquiv [Finite ι] [Finite κ]
    [N'.IsRelational] [N''.IsRelational] [L'.IsRelational] [L''.IsRelational]
    (J : Projection N' N'' L' L'' κ) (I : Projection N N' L L' ι)
    (M : Type*) [N.Structure M] [L.Structure M] :
    letI := I.inputStructure M
    letI := J.inputStructure (I.numeric.Model M)
    letI := (J.comp I).inputStructure M
    J.numeric.Model (I.numeric.Model M) ≃[N''.sum L''] (J.comp I).numeric.Model M := by
  letI := I.inputStructure M
  letI := J.inputStructure (I.numeric.Model M)
  letI := (J.comp I).inputStructure M
  exact
    { (Interpretation.compEquiv J.numeric I.numeric).toEquiv with
      map_fun' f := isEmptyElim f
      map_rel' R x := by
        cases R with
        | inl R => exact (Interpretation.compEquiv J.numeric I.numeric).map_rel' R x
        | inr R =>
          change ((I.onFormula (J.rel R)).relabel (Equiv.prodAssoc _ _ _)).toFormula.Realize _ ↔
            (J.rel R).toFormula.Realize (fun p => (x p.1).1 p.2)
          rw [ProjectionFormula.realize_relabel]
          exact I.realize_onFormula (J.rel R) (fun p => (x p.1).1 p.2) }

/-- The numeric interpretation of a composite projection is the composite of the numeric
interpretations. -/
theorem comp_numeric [Finite ι] [Finite κ] [N'.IsRelational]
    (J : Projection N' N'' L' L'' κ) (I : Projection N N' L L' ι) :
    (J.comp I).numeric = J.numeric.comp I.numeric :=
  rfl

/-- The numeric domain of `J.comp I` is the domain of `J.numeric.comp I.numeric`. -/
@[fo_realize]
theorem comp_numeric_domain [Finite ι] [Finite κ] [N'.IsRelational]
    (J : Projection N' N'' L' L'' κ) (I : Projection N N' L L' ι) :
    (J.comp I).numeric.domain = (J.numeric.comp I.numeric).domain :=
  rfl

/-- Each numeric relation of `J.comp I` is that of `J.numeric.comp I.numeric`. -/
@[fo_realize]
theorem comp_numeric_rel [Finite ι] [Finite κ] [N'.IsRelational]
    (J : Projection N' N'' L' L'' κ) (I : Projection N N' L L' ι) {n : ℕ}
    (R : N''.Relations n) :
    (J.comp I).numeric.rel R = (J.numeric.comp I.numeric).rel R :=
  rfl

/-- Uncurrying a tuple via `(Interpretation.compEquiv J.numeric I.numeric).symm` reads coordinate
`(j, i)`. -/
@[simp, fo_realize]
theorem compEquiv_numeric_symm_apply_val_val [Finite ι] [Finite κ] [N'.IsRelational]
    [N''.IsRelational] (J : Projection N' N'' L' L'' κ) (I : Projection N N' L L' ι)
    {M : Type*} [N.Structure M] (z : (J.comp I).numeric.Model M) (j : κ) (i : ι) :
    (((Interpretation.compEquiv J.numeric I.numeric).symm z).1 j).1 i = z.1 (j, i) :=
  rfl

/-- An input relation of a composite projection holds exactly when it holds after successive
interpretation. -/
@[fo_realize high]
theorem relMap_comp_inputStructure [Finite ι] [Finite κ] [N'.IsRelational] [N''.IsRelational]
    [L'.IsRelational] [L''.IsRelational] (J : Projection N' N'' L' L'' κ)
    (I : Projection N N' L L' ι) {M : Type*} [N.Structure M] [L.Structure M] {n : ℕ}
    (R : L''.Relations n) (x : Fin n → (J.comp I).numeric.Model M) :
    ((J.comp I).inputStructure M).RelMap R x ↔
      (@inputStructure _ _ _ _ _ J (I.numeric.Model M) _ (I.inputStructure M) _).RelMap R
        fun i => (Interpretation.compEquiv J.numeric I.numeric).symm (x i) := by
  let := I.inputStructure M
  change ((I.onFormula (J.rel R)).relabel (Equiv.prodAssoc _ _ _)).toFormula.Realize _ ↔ _
  rw [ProjectionFormula.realize_relabel]
  exact I.realize_onFormula (J.rel R)
    fun p => ((Interpretation.compEquiv J.numeric I.numeric).symm (x p.1)).1 p.2

/-! ### Projections on all tuples -/

/-- The input relations defined by a projection on all tuples `ι → M`, beside the numeric
relations `Interpretation.tupleStructure` of its numeric interpretation. -/
@[instance_reducible]
def tupleInputStructure (I : Projection N N' L L' ι) (M : Type*) [N.Structure M] [L.Structure M]
    [L'.IsRelational] : L'.Structure (ι → M) where
  RelMap R x := (I.rel R).toFormula.Realize fun p => x p.1 p.2

/-- An output relation holds in `I.tupleInputStructure M` iff its projection formula holds on the
tuples. -/
@[fo_realize]
theorem relMap_tupleInputStructure [L'.IsRelational] (I : Projection N N' L L' ι) {M : Type*}
    [N.Structure M] [L.Structure M] {n : ℕ} (R : L'.Relations n) (x : Fin n → ι → M) :
    (I.tupleInputStructure M).RelMap R x ↔ (I.rel R).toFormula.Realize fun p => x p.1 p.2 :=
  Iff.rfl

/-- When the numeric domain formula of a projection holds of every tuple, the numeric model with
projected input relations is isomorphic to the tuples with the numeric and input relations
defined by the projection. -/
def tupleModelEquiv [N'.IsRelational] [L'.IsRelational] (I : Projection N N' L L' ι) (M : Type*)
    [N.Structure M] [L.Structure M] (hdom : ∀ x : ι → M, I.numeric.domain.Realize x) :
    letI := I.inputStructure M
    letI := I.numeric.tupleStructure M
    letI := I.tupleInputStructure M
    I.numeric.Model M ≃[N'.sum L'] (ι → M) :=
  letI := I.inputStructure M
  letI := I.numeric.tupleStructure M
  letI := I.tupleInputStructure M
  { (I.numeric.tupleModelEquiv M hdom).toEquiv with
    map_fun' f := isEmptyElim f
    map_rel' R x := by cases R <;> rfl }

/-- `tupleModelEquiv` projects a model element to its underlying tuple. -/
@[simp]
theorem tupleModelEquiv_apply [N'.IsRelational] [L'.IsRelational]
    (I : Projection N N' L L' ι) (M : Type*) [N.Structure M] [L.Structure M]
    (hdom : ∀ x : ι → M, I.numeric.domain.Realize x) (x : I.numeric.Model M) :
    I.tupleModelEquiv M hdom x = x.1 :=
  rfl

/-- The pullback of a projection formula along a projection whose numeric domain formula holds of
every tuple is realized as the projection formula on tuples. -/
theorem realize_onFormula_tupleStructure [Finite ι] [N'.IsRelational] [L'.IsRelational]
    (I : Projection N N' L L' ι) {M : Type*} [N.Structure M] [L.Structure M]
    (hdom : ∀ x : ι → M, I.numeric.domain.Realize x) (p : ProjectionFormula N' L' α)
    (v : α → ι → M) :
    letI := I.numeric.tupleStructure M
    letI := I.tupleInputStructure M
    (I.onFormula p).toFormula.Realize (fun q => v q.1 q.2) ↔ p.toFormula.Realize v := by
  let := I.inputStructure M
  let := I.numeric.tupleStructure M
  let := I.tupleInputStructure M
  let w : α → I.numeric.Model M := fun a => ⟨v a, hdom (v a)⟩
  exact (I.realize_onFormula p w).trans
    (StrongHomClass.realize_formula (I.tupleModelEquiv M hdom) p.toFormula (v := w)).symm

/-- An input relation formula of a composite projection `J.comp I`, when the numeric domain
formula of `I` holds of every tuple, is realized as that of `J` on the tuples of `I`. -/
@[fo_realize high]
theorem realize_comp_rel_tupleStructure [Finite ι] [Finite κ] [N'.IsRelational]
    [L'.IsRelational] (J : Projection N' N'' L' L'' κ) (I : Projection N N' L L' ι) {M : Type*}
    [N.Structure M] [L.Structure M] (hdom : ∀ x : ι → M, I.numeric.domain.Realize x) {n : ℕ}
    (R : L''.Relations n) (v : Fin n × (κ × ι) → M) :
    ((J.comp I).rel R).toFormula.Realize v ↔
      letI := I.numeric.tupleStructure M
      letI := I.tupleInputStructure M
      (J.rel R).toFormula.Realize fun p i => v (p.1, p.2, i) :=
  (ProjectionFormula.realize_relabel _ _ _).trans
    (I.realize_onFormula_tupleStructure hdom (J.rel R) fun p i => v (p.1, p.2, i))

/-- A quantifier-free relativized projection has a quantifier-free numeric interpretation and
quantifier-free numeric guards in every input-relation definition. A classical qfp further
restricts the numeric vocabulary and its interpretation; in particular the convention of
[Immerman and Landau, Definition 3.6][ImmermanLandau1995] excludes BIT. -/
structure IsQF (I : Projection N N' L L' ι) : Prop where
  /-- The numeric domain and relation definitions are quantifier-free. -/
  numeric : I.numeric.IsQF
  /-- The numeric guards in each output input-relation definition are quantifier-free. -/
  rel : ∀ {n} (R : L'.Relations n), (I.rel R).IsQF

-- A concrete projection is split into its numeric interpretation and relation definitions only
-- when no lemma about its construction applies. A hypothesis is split into its fields.
attribute [aesop safe 10 apply (rule_sets := [FirstOrder])] IsQF.mk
attribute [aesop safe forward (rule_sets := [FirstOrder])] IsQF.numeric IsQF.rel

/-- Forgetting a quantifier-free projection yields a quantifier-free ordinary interpretation. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem IsQF.toInterpretation {I : Projection N N' L L' ι} (hI : I.IsQF) :
    I.toInterpretation.IsQF := by
  refine ⟨hI.numeric.domain.onBoundedFormula _, ?_⟩
  rintro _ (R | R)
  · exact (hI.numeric.rel R).onBoundedFormula _
  · exact (hI.rel R).toFormula

/-- Pulling back an input literal along a quantifier-free projection yields a quantifier-free
projection formula. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem IsQF.onLiteral {I : Projection N N' L L' ι} (hI : I.IsQF)
    (l : InputLiteral L' α) : (I.onLiteral l).IsQF := by
  cases l with
  | const => trivial
  | rel R args neg =>
    cases neg
    · exact (hI.rel R).relabel _
    · exact ((hI.rel R).relabel _).not

/-- Pulling back a quantifier-free projection formula along a quantifier-free projection yields a
quantifier-free projection formula. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem IsQF.onFormula [Finite ι] [N'.IsRelational] {I : Projection N N' L L' ι}
    (hI : I.IsQF) {p : ProjectionFormula N' L' α} (hp : p.IsQF) : (I.onFormula p).IsQF :=
  hp.subst _ _ (fun _ h => hI.numeric.onFormula h) hI.onLiteral

/-- The identity projection is quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isQF_id (N L : Language) : (Projection.id N L).IsQF :=
  ⟨Interpretation.isQF_id N, fun _ => trivial⟩

/-- Quantifier-free relativized projections compose. Requiring both numeric interpretations to
be quantifier-free prevents the substitution from introducing quantified numeric tests. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem IsQF.comp [Finite ι] [Finite κ] [N'.IsRelational]
    {J : Projection N' N'' L' L'' κ} {I : Projection N N' L L' ι}
    (hJ : J.IsQF) (hI : I.IsQF) : (J.comp I).IsQF :=
  ⟨hJ.numeric.comp hI.numeric, fun R => (hI.onFormula (hJ.rel R)).relabel _⟩

end Projection

end Cslib.Logic.FO
