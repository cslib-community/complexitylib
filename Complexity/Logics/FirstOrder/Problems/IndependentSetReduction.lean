/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Problems.CNF
public import Complexity.Logics.FirstOrder.Problems.SizedGraph
public import Complexity.Logics.FirstOrder.Reduction.Nontrivial
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FinCases

/-!
# The order-free first-order interpretation from SAT to independent set

The reductions in this module use order-free first-order interpretations. Input structures have
no built-in order or numeric predicates; these are variants of the standard ordered setting.

The complement of Karp's SAT-to-clique occurrence graph [Karp1972] gives an order-free
interpretation from satisfiability to independent set on CNF structures
of at least two elements (`Cslib.Logic.FO.cnf.reducesNontrivial_SAT_IndependentSet`). The graph
has a vertex for each occurrence of a literal in a clause; two occurrences in the same clause are
adjacent, and so are two occurrences of complementary literals. An independent set with one vertex
per clause picks a literal of each clause, consistently, so it exists exactly when the formula is
satisfiable. The target size, a relation of the vocabulary `sizedGraph`, is given by one extra
vertex per clause, adjacent to every vertex; on a structure with at least two clauses no
independent set of the target size contains one. Clauses of any width are handled, so no reduction
to 3SAT is needed.

The reduction is not correct on all finite structures: every `sizedGraph` structure with at most
one element has an independent set of its target size, and an interpretation maps a structure with
one element to a structure with at most one element, while the empty clause on one element is an
unsatisfiable CNF structure. So SAT is not order-free reducible to independent set in the sense of
`Cslib.Logic.FO.Reduces`; the reduction is one on nontrivial structures
(`Cslib.Logic.FO.ReducesNontrivial`). Hardness consequences for existential second-order definable
classes remain a separate development; definability of the target classes is proved in
`Complexity.Logics.SecondOrder.IndependentSet`.

## Main definitions

* `Cslib.Logic.FO.cnf.OccurrenceTag`, `Cslib.Logic.FO.cnf.OccurrenceTag.Coord`,
  `Cslib.Logic.FO.cnf.occurrenceEdges`, `Cslib.Logic.FO.cnf.occurrenceAdj`: the vertex tags,
  coordinates, and edge templates of the occurrence graph.
* `Cslib.Logic.FO.cnf.independentSetInterpretation`: the occurrence graph, a tagged
  interpretation.

## Main results

* `Cslib.Logic.FO.sizedGraph.copyInvariant_IndependentSet`: independent set is invariant under
  copies.
* `Cslib.Logic.FO.sizedGraph.mem_IndependentSet_of_subsingleton`: structures with at most one
  element are instances with a solution.
* `Cslib.Logic.FO.cnf.mem_independentSet_iff_satisfiable`: on a CNF structure with at least two
  elements, the occurrence graph has an independent set of the target size exactly when the
  structure is satisfiable.
* `Cslib.Logic.FO.cnf.not_reduces_SAT_IndependentSet`: the singleton obstruction to an
  unrestricted order-free reduction.
* `Cslib.Logic.FO.cnf.reducesNontrivial_SAT_IndependentSet`: SAT reduces to independent set on
  nontrivial structures.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v w

open FirstOrder Language Structure CategoryTheory

namespace Cslib.Logic.FO

/-! ### Independent sets of copies and of small structures -/

namespace sizedGraph

variable {J M : Type w} [sizedGraph.Structure M]

/-- Every structure with at most one element has an independent set of the requested size. -/
theorem mem_IndependentSet_of_subsingleton [Subsingleton M] :
    (Bundled.of M : Bundled.{w} sizedGraph.Structure) ∈ IndependentSet := by
  rw [mem_IndependentSet]
  exact ⟨_, rfl, fun x _ y _ hxy => absurd (Subsingleton.elim (α := M) x y) hxy⟩

/-- **Independent set is invariant under copies**: the largest independent sets of `J` disjoint
copies of a graph are unions of largest independent sets of the copies. -/
private theorem independentSet_copies_iff [Finite J] [Finite M] [Nonempty J] :
    (Bundled.of (Copies J M) : Bundled.{w} sizedGraph.Structure) ∈ IndependentSet ↔
      (Bundled.of M : Bundled.{w} sizedGraph.Structure) ∈ IndependentSet := by
  have hsize : {x : Copies J M | RelMap sizedGraph.size ![x]}.ncard =
      Nat.card J * {x : M | RelMap sizedGraph.size ![x]}.ncard := by
    rw [← Copies.ncard_set_val]
    congr 1
    ext x
    exact Copies.relMap_copies_one _ x
  simp only [mem_IndependentSet]
  have := Fintype.ofFinite J
  constructor
  · rintro ⟨S, hS, hind⟩
    have hS : S.ncard = Nat.card J * {x : M | RelMap sizedGraph.size ![x]}.ncard :=
      hS.trans hsize
    have hsum : S.ncard = ∑ j, {v : M | (⟨j, v⟩ : Copies J M) ∈ S}.ncard := by
      rw [← Nat.card_coe_set_eq]
      simp only [← Nat.card_coe_set_eq]
      rw [← Nat.card_sigma]
      exact Nat.card_congr
        { toFun := fun x => ⟨x.1.idx, x.1.val, x.2⟩
          invFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    obtain ⟨j, hj⟩ : ∃ j, {x : M | RelMap sizedGraph.size ![x]}.ncard ≤
        {v : M | (⟨j, v⟩ : Copies J M) ∈ S}.ncard := by
      by_contra h
      simp only [not_exists, not_le] at h
      have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := J)) fun j _ => h j
      rw [← hsum, hS, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
        at hlt
      exact lt_irrefl _ hlt
    obtain ⟨t, hts, ht⟩ := Set.exists_subset_card_eq hj
    refine ⟨t, ht, fun x hx y hy hxy hadj => ?_⟩
    refine hind (hts hx) (hts hy) (fun h => hxy (congrArg Copies.val h)) ?_
    exact (Copies.relMap_copies_two _ _ _).2 ⟨rfl, hadj⟩
  · rintro ⟨s, hs, hind⟩
    refine ⟨{x | x.val ∈ s},
      ((Copies.ncard_set_val (J := J) (N := M) s).trans (congrArg _ hs)).trans hsize.symm,
      fun x hx y hy hxy hadj => ?_⟩
    obtain ⟨hidx, hadj⟩ := (Copies.relMap_copies_two _ _ _).1 hadj
    refine hind hx hy (fun h => hxy ?_) hadj
    obtain ⟨i, a⟩ := x
    obtain ⟨j, b⟩ := y
    simp_all

/-- Independent set is invariant under any finite positive number of disjoint copies. -/
theorem copyInvariant_IndependentSet : CopyInvariant IndependentSet.{w} :=
  fun _ _ _ _ _ _ => independentSet_copies_iff

end sizedGraph

/-! ### The occurrence graph -/

namespace cnf

/-- No order-free first-order interpretation reduces SAT to independent set on all finite
structures: a singleton empty clause is unsatisfiable, but every interpreted singleton is an
independent-set yes-instance. -/
theorem not_reduces_SAT_IndependentSet : ¬Reduces SAT.{w} sizedGraph.IndependentSet.{w} := by
  rintro ⟨ι, _, I, hI⟩
  let : cnf.Structure PUnit.{w + 1} := { RelMap := fun _ _ => False }
  have : Subsingleton (I.Model PUnit.{w + 1}) :=
    ⟨fun x y => Interpretation.Model.ext (Subsingleton.elim _ _)⟩
  have : Finite (Bundled.of (c := cnf.Structure) PUnit.{w + 1}) :=
    inferInstanceAs (Finite PUnit.{w + 1})
  have hsat := (hI (Bundled.of PUnit.{w + 1})).2
    (sizedGraph.mem_IndependentSet_of_subsingleton (M := I.Model PUnit.{w + 1}))
  obtain ⟨A, hA⟩ := hsat
  obtain ⟨x, ⟨h, _⟩ | ⟨h, _⟩⟩ := hA PUnit.unit <;> exact h

open TaggedInterpretation

/-- The kinds of vertices of the occurrence graph: the occurrences of literals of each polarity,
and the vertices of the target size. -/
inductive OccurrenceTag : Type
  /-- The occurrences of literals of polarity `b`. -/
  | occ (b : Bool)
  /-- The vertices counting the clauses. -/
  | sizeV
  deriving DecidableEq

/-- There are finitely many vertex tags in `OccurrenceTag`. -/
instance : Finite OccurrenceTag := by
  refine Finite.of_injective (β := Option Bool)
    (fun | .occ b => some b | .sizeV => none) ?_
  intro a b h
  cases a <;> cases b <;> simp_all

/-- The coordinates of the vertices: the clause and the variable of an occurrence, and the clause
of a size vertex. -/
abbrev OccurrenceTag.Coord : OccurrenceTag → Type
  | .occ _ => Fin 2
  | .sizeV => Fin 1

/-- Every vertex tag in `OccurrenceTag` has a finite coordinate type. -/
instance instFiniteOccurrenceTagCoord : ∀ t : OccurrenceTag, Finite t.Coord
  | .occ _ => inferInstanceAs (Finite (Fin 2))
  | .sizeV => inferInstanceAs (Finite (Fin 1))

/-- The edges from each kind of vertex: an occurrence is joined to the occurrences in its clause
and to the occurrences of the complementary literal, and a size vertex to every vertex. -/
def occurrenceEdges : (t : OccurrenceTag) →
    List (Template cnf OccurrenceTag.Coord t)
  | .occ b => [⟨.occ b, ⊤, ![some 0, none]⟩, ⟨.occ (!b), ⊤, ![some 0, none]⟩,
      ⟨.occ (!b), ⊤, ![none, some 1]⟩]
  | .sizeV => [⟨.sizeV, ⊤, fun _ => none⟩, ⟨.occ true, ⊤, fun _ => none⟩,
      ⟨.occ false, ⊤, fun _ => none⟩]

/-- The formula of the edges between vertices of kinds `t` and `w`. -/
noncomputable def occurrenceAdj (t w : OccurrenceTag) :
    cnf.Formula (t.Coord ⊕ w.Coord) :=
  Template.listFormula (occurrenceEdges t) w

/-- **The occurrence graph** of a CNF structure, with the size vertices as target size. -/
noncomputable def independentSetInterpretation :
    TaggedInterpretation cnf sizedGraph OccurrenceTag OccurrenceTag.Coord where
  domain
    | .occ b => (lit b).formula₂ (.var 0) (.var 1)
    | .sizeV => ⊤
  rel R := match R with
    | .adj => binaryRel occurrenceAdj
    | .size => fun ts => if ts 0 = .sizeV then ⊤ else ⊥

variable {M : Type w} [cnf.Structure M]

/-- An edge from `a` to `c` given by a template of the kind of `a`. -/
private def OccEdge (a c : independentSetInterpretation.Model M) : Prop :=
  ∃ τ ∈ occurrenceEdges a.1, τ.Holds a.2.1 c.toSigma

private theorem relMap_adj_iff (a c : independentSetInterpretation.Model M) :
    RelMap sizedGraph.adj ![a, c] ↔ OccEdge a c := by
  rw [relMap_binaryRel (F := occurrenceAdj) (fun _ => rfl), occurrenceAdj,
    Template.realize_listFormula]
  rfl

private theorem relMap_size_iff (a : independentSetInterpretation.Model M) :
    RelMap sizedGraph.size ![a] ↔ a.1 = .sizeV := by
  rw [relMap_model]
  change (if a.1 = OccurrenceTag.sizeV then ⊤ else ⊥ : cnf.Formula _).Realize _ ↔ _
  split_ifs with h <;> simp [h]

/-- The occurrence of the literal `l` in the clause `c`. -/
private def occVertex (c : M) (l : Bool × M) (hl : l ∈ literals c) :
    independentSetInterpretation.Model M :=
  ⟨.occ l.1, ![c, l.2], by
    change ((lit l.1).formula₂ (.var 0) (.var 1)).Realize _
    simpa [mem_literals] using hl⟩

/-- The size vertex of the clause `c`. -/
private def sizeVertex (c : M) : independentSetInterpretation.Model M :=
  ⟨.sizeV, ![c], formula_realize_top⟩

private theorem occEdge_sizeVertex (c : M) (a : independentSetInterpretation.Model M) :
    OccEdge (sizeVertex c) a := by
  obtain ⟨t, d, hd⟩ := a
  cases t with
  | sizeV => exact ⟨_, List.mem_cons_self, formula_realize_top, d, rfl, fun _ _ h => by cases h⟩
  | occ b =>
    cases b
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        formula_realize_top, d, rfl, fun _ _ h => by cases h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, formula_realize_top, d, rfl,
        fun _ _ h => by cases h⟩

/-- The clause of a vertex. -/
private def vertexClause : independentSetInterpretation.Model M → M
  | ⟨.occ _, d, _⟩ => d 0
  | ⟨.sizeV, d, _⟩ => d 0

/-- Two occurrences in the same clause are adjacent. -/
private theorem occEdge_of_clause_eq {b b' : Bool} {d d' : Fin 2 → M} {hd hd'} (h : d 0 = d' 0) :
    OccEdge (⟨.occ b, d, hd⟩ : independentSetInterpretation.Model M) ⟨.occ b', d', hd'⟩ := by
  by_cases hb : b' = b
  · subst hb
    exact ⟨_, List.mem_cons_self, formula_realize_top, d', rfl, fun j i hj => by
      fin_cases j
      · cases hj; exact h.symm
      · cases hj⟩
  · have hb' : b' = !b := by cases b <;> cases b' <;> simp_all
    subst hb'
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, formula_realize_top, d', rfl,
      fun j i hj => by
        fin_cases j
        · cases hj; exact h.symm
        · cases hj⟩

/-- Occurrences of complementary literals are adjacent. -/
private theorem occEdge_of_complementary {b : Bool} {d d' : Fin 2 → M} {hd hd'} (h : d 1 = d' 1) :
    OccEdge (⟨.occ b, d, hd⟩ : independentSetInterpretation.Model M) ⟨.occ (!b), d', hd'⟩ :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
    formula_realize_top, d', rfl, fun j i hj => by
      fin_cases j
      · cases hj
      · cases hj; exact h.symm⟩

/-- The edges between occurrences join occurrences in the same clause or of complementary
literals. -/
private theorem occEdge_cases {b b' : Bool} {d d' : Fin 2 → M} {hd hd'}
    (h : OccEdge (⟨.occ b, d, hd⟩ : independentSetInterpretation.Model M) ⟨.occ b', d', hd'⟩) :
    d' 0 = d 0 ∨ (b' = !b ∧ d' 1 = d 1) := by
  obtain ⟨τ, hτ, -, y, hy, hc⟩ := h
  simp only [occurrenceEdges, List.mem_cons, List.not_mem_nil, or_false] at hτ
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨-, h⟩ := Sigma.mk.inj_iff.1 hy
    cases eq_of_heq h
    exact .inl (hc 0 0 rfl)
  · obtain ⟨-, h⟩ := Sigma.mk.inj_iff.1 hy
    cases eq_of_heq h
    exact .inl (hc 0 0 rfl)
  · obtain ⟨h₁, h⟩ := Sigma.mk.inj_iff.1 hy
    cases eq_of_heq h
    exact .inr ⟨OccurrenceTag.occ.inj h₁, hc 1 1 rfl⟩

private theorem ncard_size :
    {x : independentSetInterpretation.Model M | RelMap sizedGraph.size ![x]}.ncard =
      Nat.card M := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun x => vertexClause x.1
      invFun := fun c => ⟨sizeVertex c, (relMap_size_iff _).2 rfl⟩
      left_inv := fun ⟨⟨t, d, hd⟩, hx⟩ => ?_
      right_inv := fun _ => rfl }
  have ht : t = .sizeV := (relMap_size_iff _).1 hx
  subst ht
  refine Subtype.ext (Model.ext_toSigma (Sigma.ext rfl (heq_of_eq (funext fun (i : Fin 1) => ?_))))
  obtain rfl : i = 0 := Subsingleton.elim _ _
  rfl

/-- **Correctness of the occurrence graph**: on a CNF structure with two distinct elements, the
occurrence graph has an independent set of the target size exactly when the structure is
satisfiable. -/
theorem mem_independentSet_iff_satisfiable [Finite M] [Nontrivial M] :
    (Bundled.of (independentSetInterpretation.Model M) : Bundled.{w} sizedGraph.Structure) ∈
      sizedGraph.IndependentSet ↔ Satisfiable M := by
  rw [sizedGraph.mem_IndependentSet]
  change (∃ s : Set (independentSetInterpretation.Model M), _ ∧ _) ↔ _
  constructor
  · rintro ⟨s, hs, hind⟩
    have hs : s.ncard = Nat.card M := hs.trans ncard_size
    have hind : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬OccEdge a b :=
      fun a ha b hb hab h => hind ha hb hab ((relMap_adj_iff a b).2 h)
    -- every vertex of `s` is an occurrence
    have hocc : ∀ a ∈ s, a.1 ≠ .sizeV := by
      rintro ⟨t, d, hd⟩ ha (rfl : t = _)
      have h2 : 1 < s.ncard := by
        rw [hs]
        exact Finite.one_lt_card
      obtain ⟨a', ha', hne⟩ := Set.exists_ne_of_one_lt_ncard h2 ⟨.sizeV, d, hd⟩
      have hsv : (⟨.sizeV, d, hd⟩ : independentSetInterpretation.Model M) = sizeVertex (d 0) :=
        Model.ext_toSigma (Sigma.ext rfl (heq_of_eq (funext fun (i : Fin 1) => by
          obtain rfl : i = 0 := Subsingleton.elim _ _; rfl)))
      exact hind ha ha' hne.symm (hsv ▸ occEdge_sizeVertex (d 0) a')
    -- each clause has exactly one vertex in `s`
    have hinj : Function.Injective fun a : s => vertexClause a.1 := by
      rintro ⟨⟨t, d, hd⟩, ha⟩ ⟨⟨t', d', hd'⟩, ha'⟩ h
      by_contra hne
      have hne' : (⟨t, d, hd⟩ : independentSetInterpretation.Model M) ≠ ⟨t', d', hd'⟩ :=
        fun h => hne (Subtype.ext h)
      cases t with
      | sizeV => exact hocc _ ha rfl
      | occ b =>
        cases t' with
        | sizeV => exact hocc _ ha' rfl
        | occ b' => exact hind ha ha' hne' (occEdge_of_clause_eq h)
    have hbij := hinj.bijective_of_nat_card_le (by rw [Nat.card_coe_set_eq, hs])
    refine ⟨fun x => ∃ a ∈ s, ∃ d hd, a = (⟨.occ true, d, hd⟩ : _) ∧ d 1 = x,
      (satisfies_iff _).2 fun c => ?_⟩
    obtain ⟨⟨⟨t, d, hd⟩, ha⟩, hac⟩ := hbij.2 c
    cases t with
    | sizeV => exact (hocc _ ha rfl).elim
    | occ b =>
      have hl : (b, d 1) ∈ literals c := by
        rw [← hac]
        exact Formula.realize_rel₂.1 hd
      refine ⟨(b, d 1), hl, ?_⟩
      cases b
      · refine iff_of_false ?_ Bool.false_ne_true
        rintro ⟨a', ha', d', hd', rfl, hd1⟩
        exact hind ha ha' (fun h => absurd (congrArg Sigma.fst h) (by simp))
          (occEdge_of_complementary hd1.symm)
      · exact iff_of_true ⟨_, ha, d, hd, rfl, rfl⟩ rfl
  · rintro ⟨A, hA⟩
    choose l hl htrue using (satisfies_iff A).1 hA
    let f : M → independentSetInterpretation.Model M := fun c => occVertex c (l c) (hl c)
    have hf : Function.Injective f := fun c c' h => by
      have := congrArg vertexClause h
      exact this
    refine ⟨Set.range f, ?_, ?_⟩
    · refine Eq.trans ?_ ncard_size.symm
      rw [← Set.image_univ, Set.ncard_image_of_injective _ hf, Set.ncard_univ]
    · rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩ hne h
      rcases occEdge_cases ((relMap_adj_iff _ _).1 h) with h | ⟨hb, hx⟩
      · change c' = c at h
        exact hne (h ▸ rfl)
      · change (l c').2 = (l c).2 at hx
        have h₁ := htrue c
        have h₂ := htrue c'
        rw [hx, hb] at h₂
        cases (l c).1 <;> simp_all

/-- **SAT reduces to independent set by an order-free interpretation on nontrivial structures**,
using Karp's occurrence graph [Karp1972]. -/
theorem reducesNontrivial_SAT_IndependentSet :
    ReducesNontrivial SAT.{w} sizedGraph.IndependentSet.{w} :=
  .of_tagged sizedGraph.isoClosed_IndependentSet sizedGraph.copyInvariant_IndependentSet
    independentSetInterpretation
    fun _ _ _ => mem_independentSet_iff_satisfiable.symm

end cnf

end Cslib.Logic.FO
