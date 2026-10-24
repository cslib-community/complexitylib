/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Basic
public import Complexity.Logics.FirstOrder.Reduction
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FinCases

/-!
# Tagged interpretations

Reductions between problems often build structures whose elements are of several kinds: the
literal vertices and the clause gadgets of a graph built from a formula, the variables and the
clauses of a formula built from a structure. A **tagged interpretation** `I` of `L'` in `L`
(`Cslib.Logic.FO.TaggedInterpretation`) has a finite type `T` of tags and, for each tag `t`, a
type `ι t` of coordinates and a domain formula; the interpreted structure `I.Model M` is the
disjoint union over the tags `t` of the tuples `ι t → M` satisfying the domain formula of `t`,
and a relation symbol is defined, for each choice of tags of its arguments, by a formula in the
coordinates of the arguments. Senellart and Gnatenko's interpretations are tagged in this way, with
the same coordinates `Fin dim` for every tag [Senellart and Gnatenko][SenellartGnatenko2026].

The first-order interpretations of this library (`Cslib.Logic.FO.Interpretation`) are untagged,
and the structures are unordered and have no constants, so a tag cannot be named by a fixed
element. It is named by an equality pattern instead: the coordinates of the compiled
interpretation `I.toInterpretation S` are two coordinates `p ≠ q`, a coordinate per tag, equal to
`q` at the tag of the element and to `p` at the others, and the coordinates of every tag, those of
the other tags equal to `p`. Every ordered pair `p ≠ q` thus carries a copy of `I.Model M`, and
the compiled structure is isomorphic to `Copies J (I.Model M)`, the disjoint union of copies
indexed by the pairs `J` (`Cslib.Logic.FO.TaggedInterpretation.copiesEquiv`). A structure with at
most one element has no such pair; on it, the compiled interpretation is a given interpretation
`S` of dimension one (`Cslib.Logic.FO.TaggedInterpretation.subsingletonEquiv`).

So a tagged interpretation gives an order-free reduction to every class that is closed under
isomorphism and under taking a positive number of disjoint copies, such as satisfiability of
formulas in conjunctive normal form or colorability of graphs
(`Cslib.Logic.FO.Reduces.of_tagged`).

Binary relations of tagged interpretations are conveniently defined by templates
(`Cslib.Logic.FO.TaggedInterpretation.Template`): a template from tag `t` relates an element of tag
`t` whose coordinates satisfy a guard to the elements of a target tag whose coordinates are copied
from it, or are arbitrary.

## Main definitions

* `Cslib.Logic.FO.TaggedInterpretation`, `Cslib.Logic.FO.TaggedInterpretation.Model`,
  `Cslib.Logic.FO.TaggedInterpretation.Model.toSigma`, `Cslib.Logic.FO.subsingletonFormula`:
  tagged interpretations, the structures they interpret, and the subsingleton guard formula.
* `Cslib.Logic.FO.TaggedInterpretation.reindex`,
  `Cslib.Logic.FO.TaggedInterpretation.reindexEquiv`: renaming the tags and the induced
  isomorphism.
* `Cslib.Logic.FO.Copies`, `Cslib.Logic.FO.Copies.equivProd`, `Cslib.Logic.FO.CopyInvariant`:
  disjoint copies of a structure, their product equivalence, and the classes closed under them.
* `Cslib.Logic.FO.TaggedInterpretation.Coord`, `Cslib.Logic.FO.TaggedInterpretation.Coord.tag`,
  `Cslib.Logic.FO.TaggedInterpretation.Coord.data`,
  `Cslib.Logic.FO.TaggedInterpretation.domainAt`, `Cslib.Logic.FO.TaggedInterpretation.relAt`,
  `Cslib.Logic.FO.TaggedInterpretation.toInterpretation`: coordinates, component formulas, and
  the compiled first-order interpretation.
* `Cslib.Logic.FO.TaggedInterpretation.Pairs`, `Cslib.Logic.FO.TaggedInterpretation.coords`,
  `Cslib.Logic.FO.TaggedInterpretation.ofCopies`: distinct-element pairs, coordinate encoding, and
  the map from copies into the compiled model.
* `Cslib.Logic.FO.TaggedInterpretation.Template`,
  `Cslib.Logic.FO.TaggedInterpretation.Template.Compat`,
  `Cslib.Logic.FO.TaggedInterpretation.Template.Holds`,
  `Cslib.Logic.FO.TaggedInterpretation.Template.formula`,
  `Cslib.Logic.FO.TaggedInterpretation.Template.listFormula`,
  `Cslib.Logic.FO.TaggedInterpretation.binaryRel`: templates and formulas for binary relations.

## Main results

* `Cslib.Logic.FO.TaggedInterpretation.copiesEquiv`: on a structure with two distinct elements,
  the compiled interpretation is a disjoint union of copies of the tagged one.
* `Cslib.Logic.FO.TaggedInterpretation.subsingletonEquiv`: on a structure with at most one
  element, it is the given interpretation of dimension one.
* `Cslib.Logic.FO.Reduces.of_tagged`: tagged interpretations give order-free reductions to
  classes closed under isomorphism and copies.
* `Cslib.Logic.FO.TaggedInterpretation.Template.realize_formula`: the semantics of templates.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [P. Senellart and A. Gnatenko, *Descriptive Complexity in Lean: Completeness by First-Order
  Reductions*][SenellartGnatenko2026]
-/

@[expose] public section

universe u v u' v' w

namespace Cslib.Logic.FO

open FirstOrder Language Structure CategoryTheory

/-- A **tagged interpretation** of `L'` in `L`: for each tag `t` a domain formula in the
coordinates `ι t`, and for each relation symbol of arity `n` and each choice of tags of its `n`
arguments a formula in their coordinates. -/
structure TaggedInterpretation (L : Language.{u, v}) (L' : Language.{u', v'}) (T : Type*)
    (ι : T → Type*) where
  /-- The domain formula of each tag. -/
  domain : ∀ t, L.Formula (ι t)
  /-- The formula defining a relation symbol among arguments of the given tags. -/
  rel : ∀ {n : ℕ}, L'.Relations n → ∀ ts : Fin n → T, L.Formula (Σ j, ι (ts j))

/-- In a structure with at most one element: the formula `∀ x y, x = y`. -/
def subsingletonFormula (L : Language.{u, v}) (α : Type*) : L.Formula α :=
  ∀' ∀' ((&0 : L.Term (α ⊕ Fin 2)) =' &1)

/-- `subsingletonFormula L α` holds in `M` if and only if `M` is a `Subsingleton`. -/
@[simp]
theorem realize_subsingletonFormula {L : Language.{u, v}} {α : Type*} {M : Type w}
    [L.Structure M] (v : α → M) : (subsingletonFormula L α).Realize v ↔ Subsingleton M := by
  simp only [subsingletonFormula, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_bdEqual]
  refine ⟨fun h => ⟨fun x y => ?_⟩, fun h x y => Subsingleton.elim _ _⟩
  simpa [Fin.snoc] using h x y

namespace TaggedInterpretation

variable {L : Language.{u, v}} {L' : Language.{u', v'}}

section Model

variable {T : Type*} {ι : T → Type*} (I : TaggedInterpretation L L' T ι) (M : Type w)
  [L.Structure M]

/-- The universe of the structure interpreted by `I` in `M`: for each tag, the tuples satisfying
its domain formula. -/
def Model : Type _ :=
  Σ t, {x : ι t → M // (I.domain t).Realize x}

variable {I M}

/-- When `T`, each `ι t`, and `M` are finite, the tagged model `I.Model M` is finite. -/
instance [Finite T] [∀ t, Finite (ι t)] [Finite M] : Finite (I.Model M) :=
  inferInstanceAs (Finite (Σ t, {x : ι t → M // (I.domain t).Realize x}))

/-- The tag and coordinates of an element of the interpreted structure. -/
def Model.toSigma (e : I.Model M) : Σ t, ι t → M :=
  ⟨e.1, e.2.1⟩

/-- Two elements of `I.Model M` with equal `toSigma` projections are equal. -/
theorem Model.ext_toSigma {e e' : I.Model M} (h : e.toSigma = e'.toSigma) : e = e' := by
  obtain ⟨t, x, hx⟩ := e
  obtain ⟨t', x', hx'⟩ := e'
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
  cases eq_of_heq h
  rfl

variable [L'.IsRelational]

/-- The structure interpreted by `I`: a relation holds of some elements when its defining formula
for their tags holds of their coordinates. -/
instance : L'.Structure (I.Model M) where
  RelMap R xs := (I.rel R fun j => (xs j).1).Realize fun p => (xs p.1).2.1 p.2

/-- A relation `R` holds on `xs` in `I.Model M` iff `I.rel R` for their tags holds of their
coordinates. -/
theorem relMap_model {n : ℕ} (R : L'.Relations n) (xs : Fin n → I.Model M) :
    RelMap R xs ↔ (I.rel R fun j => (xs j).1).Realize fun p => (xs p.1).2.1 p.2 :=
  Iff.rfl

end Model

/-! ### Renaming tags -/

section Reindex

variable {T T' : Type*} {ι : T → Type*} (I : TaggedInterpretation L L' T ι)

/-- The tagged interpretation with tags renamed along `e`. -/
def reindex (e : T ≃ T') : TaggedInterpretation L L' T' (ι ∘ e.symm) where
  domain t := I.domain (e.symm t)
  rel R ts := I.rel R (e.symm ∘ ts)

/-- Renaming the tags of a tagged interpretation does not change the interpreted structure, up to
isomorphism. -/
def reindexEquiv [L'.IsRelational] (e : T ≃ T') (M : Type w) [L.Structure M] :
    (I.reindex e).Model M ≃[L'] I.Model M where
  toEquiv := Equiv.sigmaCongrLeft (β := fun t => {x : ι t → M // (I.domain t).Realize x}) e.symm
  map_fun' f := isEmptyElim f
  map_rel' _ _ := Iff.rfl

end Reindex

end TaggedInterpretation

/-! ### Disjoint copies -/

/-- The disjoint union of copies of `N` indexed by `J`: a relation holds of some elements of one
copy when it holds of them in `N`. -/
structure Copies (J : Type*) (N : Type*) where
  /-- The copy containing the element. -/
  idx : J
  /-- The element of `N` it is a copy of. -/
  val : N

namespace Copies

variable {L' : Language.{u', v'}} {J N : Type*}

/-- The copies, as pairs. -/
def equivProd : Copies J N ≃ J × N where
  toFun x := (x.idx, x.val)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- When `J` and `N` are finite, `Copies J N` is finite. -/
instance [Finite J] [Finite N] : Finite (Copies J N) :=
  Finite.of_equiv _ equivProd.symm

/-- Relational structure on `Copies J N`: a relation holds on a tuple iff all arguments lie in the
same copy and the relation holds on their underlying values in `N`. -/
instance [L'.IsRelational] [L'.Structure N] : L'.Structure (Copies J N) where
  RelMap R xs := (∀ i j, (xs i).idx = (xs j).idx) ∧ RelMap R fun i => (xs i).val

/-- A relation `R` holds on `xs` in `Copies J N` iff all `xs i` share the same copy index and `R`
holds on `i ↦ (xs i).val` in `N`. -/
theorem relMap_copies [L'.IsRelational] [L'.Structure N] {n : ℕ} (R : L'.Relations n)
    (xs : Fin n → Copies J N) :
    RelMap R xs ↔ (∀ i j, (xs i).idx = (xs j).idx) ∧ RelMap R fun i => (xs i).val :=
  Iff.rfl

/-- A binary relation holds of two elements of the copies when they are in the same copy and
related in `N`. -/
theorem relMap_copies_two [L'.IsRelational] [L'.Structure N] (R : L'.Relations 2)
    (a b : Copies J N) : RelMap R ![a, b] ↔ a.idx = b.idx ∧ RelMap R ![a.val, b.val] := by
  rw [relMap_copies]
  refine and_congr ⟨fun h => h 0 1, fun h i j => ?_⟩ (iff_of_eq (congrArg _ (funext fun i => ?_)))
  · fin_cases i <;> fin_cases j <;> simp [h]
  · fin_cases i <;> rfl

/-- A unary relation in a copy holds exactly when it holds of the underlying element. -/
theorem relMap_copies_one [L'.IsRelational] [L'.Structure N]
    (R : L'.Relations 1) (a : Copies J N) :
    RelMap R ![a] ↔ RelMap R ![a.val] := by
  rw [Copies.relMap_copies]
  refine ⟨fun h => ?_, fun h => ⟨fun i j => by fin_cases i; fin_cases j; rfl, ?_⟩⟩
  · exact (iff_of_eq (congrArg _ (funext fun i => by fin_cases i; rfl))).1 h.2
  · exact (iff_of_eq (congrArg _ (funext fun i => by fin_cases i; rfl))).2 h

/-- The copies of a set have cardinality the number of copies times its cardinality. -/
theorem ncard_set_val (s : Set N) :
    {x : Copies J N | x.val ∈ s}.ncard = Nat.card J * s.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun x => (x.1.idx, ⟨x.1.val, x.2⟩)
      invFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Copies

/-- A class of structures is **invariant under copies** when a finite structure belongs to it
exactly when the disjoint union of a finite positive number of copies of it does. -/
def CopyInvariant {L' : Language.{u', v'}} [L'.IsRelational]
    (K : Set (Bundled.{w} L'.Structure)) : Prop :=
  ∀ (J N : Type w) [L'.Structure N] [Finite J] [Finite N] [Nonempty J],
    Bundled.of (c := L'.Structure) (Copies J N) ∈ K ↔ Bundled.of (c := L'.Structure) N ∈ K

namespace TaggedInterpretation

/-! ### The compiled interpretation -/

section Compile

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {T : Type} {ι : T → Type}

/-- The coordinates of the compiled interpretation: the two coordinates `p` and `q` of a copy, a
coordinate for each tag, and the coordinates of every tag. -/
abbrev Coord (T : Type) (ι : T → Type) : Type :=
  Bool ⊕ T ⊕ (Σ t, ι t)

namespace Coord

/-- The first coordinate of a copy. -/
abbrev p : Coord T ι :=
  .inl false

/-- The second coordinate of a copy, distinct from the first. -/
abbrev q : Coord T ι :=
  .inl true

/-- The coordinate of a tag, equal to `q` at the tag of an element and to `p` at the others. -/
abbrev tag (t : T) : Coord T ι :=
  .inr (.inl t)

/-- A coordinate of a tag, equal to `p` unless the element has this tag. -/
abbrev data (σ : Σ t, ι t) : Coord T ι :=
  .inr (.inr σ)

end Coord

variable [Finite T] [∀ t, Finite (ι t)] (I : TaggedInterpretation L L' T ι)

open Coord

open scoped Classical in
/-- The domain formula of the compiled interpretation on elements of tag `t`: the coordinates
`p` and `q` are distinct, the coordinate of each tag is `q` at `t` and `p` elsewhere, the
coordinates of the other tags are `p`, and the coordinates of `t` satisfy its domain formula. -/
noncomputable def domainAt (t : T) : L.Formula (Coord T ι) :=
  ∼(varEq p q) ⊓ Formula.iInf (fun t' => varEq (tag t') (if t' = t then q else p)) ⊓
    Formula.iInf (fun σ : Σ t', ι t' => if σ.1 = t then ⊤ else varEq (data σ) p) ⊓
    (I.domain t).relabel fun i => data ⟨t, i⟩

/-- The formula defining a relation symbol in the compiled interpretation: all arguments belong to
the same copy, and the formula of `I` for their tags holds of their coordinates. -/
noncomputable def relAt {n : ℕ} (R : L'.Relations n) : L.Formula (Fin n × Coord T ι) :=
  Formula.iInf (fun jj : Fin n × Fin n =>
      varEq (jj.1, p) (jj.2, p) ⊓ varEq (jj.1, q) (jj.2, q)) ⊓
    Formula.iSup fun ts : Fin n → T =>
      Formula.iInf (fun j => varEq (j, tag (ts j)) (j, q)) ⊓
        (I.rel R ts).relabel fun σ => (σ.1, data ⟨ts σ.1, σ.2⟩)

/-- The **compiled interpretation** of a tagged interpretation `I`, using the interpretation `S`
of dimension one on structures with at most one element. -/
noncomputable def toInterpretation (S : Interpretation L L' Unit) :
    Interpretation L L' (Coord T ι) where
  domain := (subsingletonFormula L _ ⊓ S.domain.relabel fun _ => p) ⊔
    (∼(subsingletonFormula L _) ⊓ Formula.iSup I.domainAt)
  rel R := (subsingletonFormula L _ ⊓ (S.rel R).relabel fun x => (x.1, p)) ⊔
    (∼(subsingletonFormula L _) ⊓ I.relAt R)

variable {I} {M : Type w} [L.Structure M]

open scoped Classical in
/-- `I.domainAt t` holds of `c` iff `c p ≠ c q`, `c (tag t')` is `c q` at `t` and `c p` elsewhere,
all data coordinates for tags `t' ≠ t` equal `c p`, and the `t`-coordinates satisfy `I.domain t`. -/
theorem realize_domainAt (t : T) (c : Coord T ι → M) :
    (I.domainAt t).Realize c ↔ c p ≠ c q ∧ (∀ t', c (tag t') = if t' = t then c q else c p) ∧
      (∀ σ : Σ t', ι t', σ.1 ≠ t → c (data σ) = c p) ∧
        (I.domain t).Realize fun i => c (data ⟨t, i⟩) := by
  simp only [domainAt, Formula.realize_inf, Formula.realize_not, realize_varEq,
    Formula.realize_iInf, Formula.realize_relabel, Function.comp_def, and_assoc]
  refine and_congr Iff.rfl (and_congr ?_ (and_congr ?_ Iff.rfl))
  · refine forall_congr' fun t' => ?_
    split_ifs <;> simp
  · refine forall_congr' fun σ => ?_
    split_ifs with h <;> simp [h]

omit [∀ t, Finite (ι t)] in
/-- `I.relAt R` holds of `c` iff all arguments share the same copy pair `(p, q)` and there is a tag
assignment `ts` selected by the `tag` coordinates whose data coordinates satisfy `I.rel R ts`. -/
theorem realize_relAt {n : ℕ} (R : L'.Relations n) (c : Fin n × Coord T ι → M) :
    (I.relAt R).Realize c ↔ (∀ j j', c (j, p) = c (j', p) ∧ c (j, q) = c (j', q)) ∧
      ∃ ts : Fin n → T, (∀ j, c (j, tag (ts j)) = c (j, q)) ∧
        (I.rel R ts).Realize fun σ => c (σ.1, data ⟨ts σ.1, σ.2⟩) := by
  simp only [relAt, Formula.realize_inf, Formula.realize_iInf, Formula.realize_iSup,
    realize_varEq, Formula.realize_relabel, Function.comp_def, Prod.forall]

variable (S : Interpretation L L' Unit)

/-- On a subsingleton structure `M`, the domain formula of `I.toInterpretation S` reduces to
`S.domain` at coordinate `p`. -/
theorem realize_toInterpretation_domain_of_subsingleton [Subsingleton M] (c : Coord T ι → M) :
    (I.toInterpretation S).domain.Realize c ↔ S.domain.Realize fun _ => c p := by
  simp only [toInterpretation, Formula.realize_sup, Formula.realize_inf,
    realize_subsingletonFormula, Formula.realize_not, Formula.realize_relabel, Function.comp_def]
  simp only [show Subsingleton M from inferInstance, true_and, not_true_eq_false, false_and,
    or_false]

/-- On a nontrivial structure `M`, the domain formula of `I.toInterpretation S` holds iff
`I.domainAt t` holds for some tag `t`. -/
theorem realize_toInterpretation_domain_of_nontrivial [Nontrivial M] (c : Coord T ι → M) :
    (I.toInterpretation S).domain.Realize c ↔ ∃ t, (I.domainAt t).Realize c := by
  simp only [toInterpretation, Formula.realize_sup, Formula.realize_inf,
    realize_subsingletonFormula, Formula.realize_not, Formula.realize_iSup, not_subsingleton,
    false_and, not_false_eq_true, true_and, false_or]

/-- On a subsingleton structure `M`, the relation formula of `I.toInterpretation S` for `R` reduces
to `S.rel R` at coordinate `p`. -/
theorem realize_toInterpretation_rel_of_subsingleton [Subsingleton M] {n : ℕ}
    (R : L'.Relations n) (c : Fin n × Coord T ι → M) :
    ((I.toInterpretation S).rel R).Realize c ↔ (S.rel R).Realize fun x => c (x.1, p) := by
  simp only [toInterpretation, Formula.realize_sup, Formula.realize_inf,
    realize_subsingletonFormula, Formula.realize_not, Formula.realize_relabel, Function.comp_def]
  simp only [show Subsingleton M from inferInstance, true_and, not_true_eq_false, false_and,
    or_false]

/-- On a nontrivial structure `M`, the relation formula of `I.toInterpretation S` for `R` reduces
to `I.relAt R`. -/
theorem realize_toInterpretation_rel_of_nontrivial [Nontrivial M] {n : ℕ}
    (R : L'.Relations n) (c : Fin n × Coord T ι → M) :
    ((I.toInterpretation S).rel R).Realize c ↔ (I.relAt R).Realize c := by
  simp only [toInterpretation, Formula.realize_sup, Formula.realize_inf,
    realize_subsingletonFormula, Formula.realize_not, not_subsingleton, false_and,
    not_false_eq_true, true_and, false_or]

/-! #### Structures with at most one element -/

/-- On a structure with at most one element, the compiled interpretation is the interpretation
`S`. -/
def subsingletonEquiv [L'.IsRelational] [Subsingleton M] :
    (I.toInterpretation S).Model M ≃[L'] S.Model M where
  toFun c := ⟨fun _ => c.1 p, (realize_toInterpretation_domain_of_subsingleton S c.1).1 c.2⟩
  invFun x := ⟨fun _ => x.1 (), (realize_toInterpretation_domain_of_subsingleton S _).2 <| by
    simpa only [show (fun _ : Unit => x.1 ()) = x.1 from funext fun _ => rfl] using x.2⟩
  left_inv _ := Interpretation.Model.ext (funext fun _ => Subsingleton.elim _ _)
  right_inv _ := Interpretation.Model.ext (funext fun _ => rfl)
  map_fun' f := isEmptyElim f
  map_rel' R xs := by
    change _ ↔ ((I.toInterpretation S).rel R).Realize (M := M) _
    rw [realize_toInterpretation_rel_of_subsingleton]
    exact Iff.rfl

/-! #### Structures with two distinct elements -/

/-- The ordered pairs of distinct elements, each indexing a copy of the tagged structure. -/
def Pairs (M : Type w) : Type w :=
  {pq : M × M // pq.1 ≠ pq.2}

/-- When `M` is finite, `Pairs M` is finite. -/
instance [Finite M] : Finite (Pairs M) :=
  inferInstanceAs (Finite {pq : M × M // pq.1 ≠ pq.2})

/-- When `M` is nontrivial, `Pairs M` is nonempty. -/
instance [Nontrivial M] : Nonempty (Pairs M) :=
  let ⟨x, y, h⟩ := exists_pair_ne M
  ⟨⟨(x, y), h⟩⟩

open scoped Classical in
omit [Finite T] [∀ t, Finite (ι t)] in
/-- The coordinates of an element `e` of the tagged structure in the copy of the pair `(a, b)`:
the coordinates `p` and `q` are `a` and `b`. -/
noncomputable def coords (a b : M) (e : I.Model M) : Coord T ι → M
  | .inl false => a
  | .inl true => b
  | .inr (.inl t) => if t = e.1 then b else a
  | .inr (.inr ⟨t, i⟩) => if h : t = e.1 then e.2.1 (h ▸ i) else a

omit [Finite T] [∀ t, Finite (ι t)] in
/-- At the tag `e.1` of `e`, `coords a b e` evaluates `data ⟨e.1, i⟩` to `e.2.1 i`. -/
@[simp]
theorem coords_data_self (a b : M) (e : I.Model M) (i : ι e.1) :
    coords a b e (data ⟨e.1, i⟩) = e.2.1 i := by
  simp [coords]

omit [Finite T] [∀ t, Finite (ι t)] in
private theorem coords_data_mk (a b : M) (t : T) (x : ι t → M) (hx : (I.domain t).Realize x)
    (i : ι t) : coords a b ⟨t, x, hx⟩ (data ⟨t, i⟩) = x i :=
  coords_data_self a b ⟨t, x, hx⟩ i

omit [Finite T] [∀ t, Finite (ι t)] in
private theorem coords_tag_eq_iff {a b : M} (h : a ≠ b) (e : I.Model M) (t : T) :
    coords a b e (tag t) = b ↔ t = e.1 := by
  simp only [coords]
  split_ifs with ht <;> simp [ht, h]

omit [Finite T] [∀ t, Finite (ι t)] in
private theorem coords_injective {a b a' b' : M} (h : a ≠ b) {e e' : I.Model M}
    (heq : coords a b e = coords a' b' e') : a = a' ∧ b = b' ∧ e = e' := by
  have ha : a = a' := congrFun heq Coord.p
  have hb : b = b' := congrFun heq Coord.q
  subst ha hb
  refine ⟨rfl, rfl, ?_⟩
  have ht : e.1 = e'.1 := by
    have := congrFun heq (tag e.1)
    rwa [(coords_tag_eq_iff h e e.1).2 rfl, eq_comm, coords_tag_eq_iff h] at this
  obtain ⟨t, x, hx⟩ := e
  obtain ⟨t', x', hx'⟩ := e'
  obtain rfl : t = t' := ht
  refine Model.ext_toSigma (Sigma.ext rfl (heq_of_eq (funext fun (i : ι t) => ?_)))
  have := congrFun heq (data ⟨t, i⟩)
  rwa [coords_data_mk, coords_data_mk] at this

/-- For distinct elements `a ≠ b` and `e : I.Model M`, `coords a b e` satisfies
`I.domainAt e.1`. -/
theorem realize_domainAt_coords (a b : M) (h : a ≠ b) (e : I.Model M) :
    (I.domainAt e.1).Realize (coords a b e) := by
  refine (realize_domainAt _ _).2 ⟨h, fun t' => ?_, fun ⟨t', i⟩ ht => ?_, ?_⟩
  · simp only [coords]
  · simp only [coords, ht, dite_false]
  · simpa only [coords_data_self] using e.2.2

/-- The map from the copies of the tagged structure to the compiled structure. -/
noncomputable def ofCopies [Nontrivial M] (x : Copies (Pairs M) (I.Model M)) :
    (I.toInterpretation S).Model M :=
  ⟨coords x.idx.1.1 x.idx.1.2 x.val, (realize_toInterpretation_domain_of_nontrivial S _).2
    ⟨x.val.1, realize_domainAt_coords _ _ x.idx.2 x.val⟩⟩

/-- On a nontrivial structure `M`, `ofCopies S` is a bijection from `Copies (Pairs M) (I.Model M)`
to `(I.toInterpretation S).Model M`. -/
theorem ofCopies_bijective [Nontrivial M] :
    Function.Bijective (ofCopies (I := I) (M := M) S) := by
  constructor
  · rintro ⟨⟨⟨a, b⟩, h⟩, e⟩ ⟨⟨⟨a', b'⟩, h'⟩, e'⟩ heq
    obtain ⟨rfl, rfl, rfl⟩ := coords_injective h (congrArg Subtype.val heq)
    rfl
  · rintro ⟨c, hc⟩
    obtain ⟨t, hct⟩ := (realize_toInterpretation_domain_of_nontrivial S c).1 hc
    obtain ⟨hpq, htag, hdata, hdom⟩ := (realize_domainAt t c).1 hct
    refine ⟨⟨⟨(c p, c q), hpq⟩, ⟨t, fun i => c (data ⟨t, i⟩), hdom⟩⟩,
      Interpretation.Model.ext (funext fun k => ?_)⟩
    rcases k with (_ | _) | t' | ⟨t', i⟩
    · rfl
    · rfl
    · simp only [ofCopies, coords]
      rw [htag t']
    · simp only [ofCopies, coords]
      split_ifs with ht
      · subst ht
        rfl
      · exact (hdata ⟨t', i⟩ ht).symm

/-- **On a structure with two distinct elements, the compiled interpretation is a disjoint union
of copies of the tagged one**, a copy for each ordered pair of distinct elements. -/
noncomputable def copiesEquiv [L'.IsRelational] [Nontrivial M] :
    Copies (Pairs M) (I.Model M) ≃[L'] (I.toInterpretation S).Model M where
  toEquiv := Equiv.ofBijective _ (ofCopies_bijective S)
  map_fun' f := isEmptyElim f
  map_rel' {n} R xs := by
    change ((I.toInterpretation S).rel R).Realize (fun x => coords (xs x.1).idx.1.1
      (xs x.1).idx.1.2 (xs x.1).val x.2) ↔ _
    rw [realize_toInterpretation_rel_of_nontrivial, realize_relAt, Copies.relMap_copies,
      relMap_model]
    refine and_congr ?_ ⟨fun ⟨ts, hts, h⟩ => ?_, fun h => ⟨fun j => (xs j).val.1, fun j => ?_, ?_⟩⟩
    · refine ⟨fun h i j => Subtype.ext (Prod.ext (h i j).1 (h i j).2), fun h i j => ?_⟩
      have := congrArg Subtype.val (h i j)
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    · obtain rfl : ts = fun j => (xs j).val.1 :=
        funext fun j => (coords_tag_eq_iff (xs j).idx.2 _ _).1 (hts j)
      simpa only [coords_data_self] using h
    · exact (coords_tag_eq_iff (xs j).idx.2 _ _).2 rfl
    · simpa only [coords_data_self] using h

end Compile

end TaggedInterpretation

/-- On a structure with two distinct elements, the compiled interpretation of a tagged
interpretation whose structures are nonempty is nontrivial: there are at least two copies. -/
theorem TaggedInterpretation.nontrivial_toInterpretation_model
    {L : Language.{u, v}} {L' : Language.{u', v'}} {T : Type} [Finite T]
    {ι : T → Type} [∀ t, Finite (ι t)] (I : TaggedInterpretation L L' T ι)
    (S : Interpretation L L' Unit) {M : Type w} [L.Structure M] [Nontrivial M]
    [Nonempty (I.Model M)] : Nontrivial ((I.toInterpretation S).Model M) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne M
  obtain ⟨e⟩ := ‹Nonempty (I.Model M)›
  refine ⟨⟨TaggedInterpretation.ofCopies S ⟨⟨(x, y), hxy⟩, e⟩,
    TaggedInterpretation.ofCopies S ⟨⟨(y, x), hxy.symm⟩, e⟩, fun h => hxy ?_⟩⟩
  have := (TaggedInterpretation.ofCopies_bijective S).1 h
  exact congrArg (fun c : Copies (TaggedInterpretation.Pairs M) (I.Model M) => c.idx.1.1) this


/-! ### Reductions by tagged interpretations -/

/-- **Tagged interpretations give order-free reductions** to classes closed under isomorphism and
under copies: if the structure interpreted by `I` decides membership on the finite structures
with two distinct elements, and the interpretation `S` of dimension one decides it on those with
at most one element, then the compiled interpretation is a order-free reduction. -/
theorem Reduces.of_tagged {L : Language.{u, v}} {L' : Language.{u', v'}} [L'.IsRelational]
    {K : Set (Bundled.{w} L.Structure)} {K' : Set (Bundled.{w} L'.Structure)} (hK' : IsoClosed K')
    (hcopy : CopyInvariant K') {T : Type} [Finite T] {ι : T → Type} [∀ t, Finite (ι t)]
    (I : TaggedInterpretation L L' T ι) (S : Interpretation L L' Unit)
    (hlarge : ∀ (M : Bundled.{w} L.Structure) [Finite M], Nontrivial M →
      (M ∈ K ↔ (Bundled.of (I.Model M) : Bundled.{w} L'.Structure) ∈ K'))
    (hsmall : ∀ (M : Bundled.{w} L.Structure) [Finite M], Subsingleton M →
      (M ∈ K ↔ (Bundled.of (S.Model M) : Bundled.{w} L'.Structure) ∈ K')) :
    Reduces K K' := by
  refine .of_interpretation (I.toInterpretation S) fun M _ => ?_
  rcases subsingleton_or_nontrivial M with hM | hM
  · rw [hsmall M hM]
    exact (hK' (TaggedInterpretation.subsingletonEquiv S).symm)
  · have : Finite (Bundled.of (c := L'.Structure)
        (Copies (TaggedInterpretation.Pairs M) (I.Model M))) :=
      inferInstanceAs (Finite (Copies _ _))
    rw [hlarge M hM, ← hcopy (TaggedInterpretation.Pairs M)]
    exact hK' (TaggedInterpretation.copiesEquiv S)

/-! ### Templates for binary relations -/

namespace TaggedInterpretation

variable {L : Language.{u, v}} {T : Type*} {ι : T → Type*}

/-- A **template** for a binary relation from elements of tag `t`: it relates an element of tag
`t` whose coordinates `x` satisfy the guard to the elements of tag `target` whose coordinate `j`
is `x i` whenever `map j = some i`, the coordinates `j` with `map j = none` being arbitrary. -/
structure Template (L : Language.{u, v}) {T : Type*} (ι : T → Type*) (t : T) where
  /-- The tag of the related elements. -/
  target : T
  /-- The condition on the coordinates of the element of tag `t`. -/
  guard : L.Formula (ι t)
  /-- The coordinates of the related elements copied from the element of tag `t`. -/
  map : ι target → Option (ι t)

namespace Template

variable {t : T} (τ : Template L ι t) {M : Type w}

/-- The tuples of tag `τ.target` related to the coordinates `x` of an element of tag `t`. -/
def Compat (x : ι t → M) (y : ι τ.target → M) : Prop :=
  ∀ j i, τ.map j = some i → y j = x i

/-- The template relates the coordinates `x` of an element of tag `t` to an element of tag `w`
with coordinates `y`. -/
def Holds [L.Structure M] (x : ι t → M) (e : Σ w, ι w → M) : Prop :=
  τ.guard.Realize x ∧ ∃ y, e = ⟨τ.target, y⟩ ∧ τ.Compat x y

variable [∀ t, Finite (ι t)]

open scoped Classical in
/-- The formula of a template, relating an element of tag `t` to an element of tag `w`. -/
noncomputable def formula (w : T) : L.Formula (ι t ⊕ ι w) :=
  if h : τ.target = w then
    h ▸ (τ.guard.relabel Sum.inl ⊓
      Formula.iInf fun j => (τ.map j).elim ⊤ fun i => varEq (Sum.inl i) (Sum.inr j))
  else ⊥

/-- The formula of a template holds of the coordinates of two elements exactly when the template
relates them. -/
theorem realize_formula [L.Structure M] {w : T} (x : ι t → M) (y : ι w → M) :
    (τ.formula w).Realize (Sum.elim x y) ↔ τ.Holds x ⟨w, y⟩ := by
  unfold formula Holds
  by_cases h : τ.target = w
  · subst h
    simp only [dite_true, Formula.realize_inf, Formula.realize_relabel, Formula.realize_iInf,
      Sum.elim_comp_inl, Sigma.mk.inj_iff, heq_eq_eq, true_and, exists_eq_left', Compat]
    refine and_congr Iff.rfl (forall_congr' fun j => ?_)
    cases τ.map j <;> simp [eq_comm]
  · simp only [h, dite_false, Formula.realize_bot, false_iff, not_and, not_exists]
    intro _ y' he
    exact absurd (congrArg Sigma.fst he).symm h

/-- The disjunction of the formulas of a list of templates. -/
noncomputable def listFormula (l : List (Template L ι t)) (w : T) : L.Formula (ι t ⊕ ι w) :=
  Formula.iSup fun k : Fin l.length => (l.get k).formula w

/-- The formula of a list of templates holds exactly when one of them relates the elements. -/
theorem realize_listFormula [L.Structure M] (l : List (Template L ι t)) {w : T} (x : ι t → M)
    (y : ι w → M) :
    (listFormula l w).Realize (Sum.elim x y) ↔ ∃ τ ∈ l, τ.Holds x ⟨w, y⟩ := by
  simp only [listFormula, Formula.realize_iSup, realize_formula, List.mem_iff_get]
  exact ⟨fun ⟨k, h⟩ => ⟨_, ⟨k, rfl⟩, h⟩, fun ⟨_, ⟨k, hk⟩, h⟩ => ⟨k, hk ▸ h⟩⟩

end Template

/-- The formula of a binary relation among arguments of tags `ts 0` and `ts 1`, from a formula in
the coordinates of the two arguments. -/
def binaryRel (F : ∀ t w : T, L.Formula (ι t ⊕ ι w)) (ts : Fin 2 → T) :
    L.Formula (Σ j : Fin 2, ι (ts j)) :=
  (F (ts 0) (ts 1)).relabel (Sum.elim (fun i => ⟨0, i⟩) fun i => ⟨1, i⟩)

/-- When `I.rel R` is defined by `binaryRel F`, `RelMap R ![a, b]` holds in `I.Model M` iff
`F a.1 b.1` holds of `Sum.elim a.2.1 b.2.1`. -/
theorem relMap_binaryRel {L' : Language.{u', v'}} [L'.IsRelational]
    {I : TaggedInterpretation L L' T ι} {M : Type w} [L.Structure M] {R : L'.Relations 2}
    {F : ∀ t w : T, L.Formula (ι t ⊕ ι w)} (hR : ∀ ts, I.rel R ts = binaryRel F ts)
    (a b : I.Model M) : RelMap R ![a, b] ↔ (F a.1 b.1).Realize (Sum.elim a.2.1 b.2.1) := by
  rw [relMap_model, hR, binaryRel, Formula.realize_relabel]
  refine iff_of_eq (congrArg _ (funext fun i => ?_))
  rcases i with i | i <;> rfl

end TaggedInterpretation


end Cslib.Logic.FO
