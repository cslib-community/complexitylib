/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Problems.CNF
public import Complexity.Logics.FirstOrder.Problems.Coloring
import Complexity.Tactic.FirstOrder
import Mathlib.Tactic.FinCases

/-!
# The order-free first-order interpretation from 3COL to 3SAT

The reductions in this module use order-free first-order interpretations. Input structures have
no built-in order or numeric predicates; these are variants of the standard ordered setting.

Three-colorability is a constraint satisfaction problem, and its constraints are clauses of at
most three literals: a graph is three-colorable exactly when the 3-CNF formula with a variable
`x(v, c)` for each vertex `v` and color `c`, a clause `x(v, 0) ∨ x(v, 1) ∨ x(v, 2)` for each vertex
and a clause `¬x(u, c) ∨ ¬x(v, c)` for each edge `(u, v)` and color `c` is satisfiable.
A loop at `v` gives the clauses `¬x(v, c)`, making the formula unsatisfiable, as the loop makes
the graph uncolorable. This construction is a tagged
interpretation (`Cslib.Logic.FO.graph.cnfInterpretation`), so 3COL, with loops allowed, is
order-free reducible to 3SAT (`Cslib.Logic.FO.graph.reduces_ThreeColorable_ThreeSAT`); with the
converse `Cslib.Logic.FO.cnf.reduces_ThreeSAT_ThreeColorable`, the two classes are order-free
interreducible.

## Main definitions

* `Cslib.Logic.FO.graph.ColoringClauseTag`, `Cslib.Logic.FO.graph.ColoringClauseTag.Coord`,
  `Cslib.Logic.FO.graph.coloringClauseTemplates`: the element tags, coordinates, and literal
  templates of the 3-CNF encoding of three-colorability.
* `Cslib.Logic.FO.graph.cnfInterpretation`, `Cslib.Logic.FO.graph.cnfSubsingleton`: the 3-CNF
  structure of the colorings of a graph, as a tagged interpretation and on subsingletons.

## Main results

* `Cslib.Logic.FO.graph.satisfiable_cnfInterpretation_iff`: the structure is satisfiable exactly
  when the graph is three-colorable, and `Cslib.Logic.FO.graph.isThreeCNF_cnfInterpretation`: it is
  a 3-CNF structure.
* `Cslib.Logic.FO.graph.reduces_ThreeColorable_ThreeSAT`: **3COL is order-free reducible to
  3SAT.**

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
-/

@[expose] public section

universe w

namespace Cslib.Logic.FO.graph

open FirstOrder Language Structure CategoryTheory TaggedInterpretation cnf

/-- The kinds of elements of the CNF structure of the colorings of a graph: the variables
`x(v, c)`, the clauses saying that a vertex has a color, and the clauses saying that the two ends
of an edge do not both have the color `c`. -/
inductive ColoringClauseTag : Type
  /-- The variables `x(v, c)`: the vertex `v` has the color `c`. -/
  | var (c : Fin 3)
  /-- The clauses `x(v, 0) ∨ x(v, 1) ∨ x(v, 2)`. -/
  | vertex
  /-- The clauses `¬x(u, c) ∨ ¬x(v, c)` of the edges `(u, v)`. -/
  | edge (c : Fin 3)

/-- The kinds of elements, as a sum type. -/
private def ColoringClauseTag.toSum : ColoringClauseTag → Fin 3 ⊕ Unit ⊕ Fin 3
  | .var c => .inl c
  | .vertex => .inr (.inl ())
  | .edge c => .inr (.inr c)

/-- There are finitely many element tags in `ColoringClauseTag`. -/
instance : Finite ColoringClauseTag := by
  refine Finite.of_injective ColoringClauseTag.toSum ?_
  intro a b h
  cases a <;> cases b <;> simp_all [ColoringClauseTag.toSum]

/-- The coordinates of the elements: the vertex of a variable or of a vertex clause, and the two
ends of the edge of an edge clause. -/
abbrev ColoringClauseTag.Coord : ColoringClauseTag → Type
  | .var _ => Fin 1
  | .vertex => Fin 1
  | .edge _ => Fin 2

/-- Every element tag in `ColoringClauseTag` has a finite coordinate type. -/
instance instFiniteColoringClauseTagCoord : ∀ t : ColoringClauseTag, Finite t.Coord
  | .var _ => inferInstanceAs (Finite (Fin 1))
  | .vertex => inferInstanceAs (Finite (Fin 1))
  | .edge _ => inferInstanceAs (Finite (Fin 2))

/-- The templates of the literals of each polarity. A variable names the tautology `x ∨ ¬x`. -/
def coloringClauseTemplates : (t : ColoringClauseTag) → Bool →
    List (Template Language.graph ColoringClauseTag.Coord t)
  | .var c, _ => [⟨.var c, ⊤, some⟩]
  | .vertex, true => [⟨.var 0, ⊤, some⟩, ⟨.var 1, ⊤, some⟩, ⟨.var 2, ⊤, some⟩]
  | .vertex, false => []
  | .edge _, true => []
  | .edge c, false => [⟨.var c, ⊤, fun _ => some 0⟩, ⟨.var c, ⊤, fun _ => some 1⟩]

/-- **The CNF structure of the colorings of a graph**, a tagged interpretation. -/
noncomputable def cnfInterpretation :
    TaggedInterpretation Language.graph cnf ColoringClauseTag ColoringClauseTag.Coord where
  domain
    | .edge _ => adj.formula₂ (.var 0) (.var 1)
    | _ => ⊤
  rel R := match R with
    | .pos => binaryRel fun t w => Template.listFormula (coloringClauseTemplates t true) w
    | .neg => binaryRel fun t w => Template.listFormula (coloringClauseTemplates t false) w

private theorem cnfInterpretation_rel_lit (b : Bool) (ts : Fin 2 → ColoringClauseTag) :
    cnfInterpretation.rel (lit b) ts =
      binaryRel (fun t w => Template.listFormula (coloringClauseTemplates t b) w) ts := by
  cases b <;> rfl

variable {M : Type*} [Language.graph.Structure M]

/-- The variable `x(v, c)`. -/
private def varElt (c : Fin 3) (v : M) : cnfInterpretation.Model M :=
  ⟨.var c, fun _ => v, formula_realize_top⟩

private theorem clauseSatisfied_iff' (A : cnfInterpretation.Model M → Prop)
    (e : cnfInterpretation.Model M) :
    ClauseSatisfied A e ↔
      (∃ τ ∈ coloringClauseTemplates e.1 true, τ.guard.Realize e.2.1 ∧
        ∃ y hy, τ.Compat e.2.1 y ∧ A ⟨τ.target, y, hy⟩) ∨
      (∃ τ ∈ coloringClauseTemplates e.1 false, τ.guard.Realize e.2.1 ∧
        ∃ y hy, τ.Compat e.2.1 y ∧ ¬A ⟨τ.target, y, hy⟩) :=
  clauseSatisfied_iff_of_templates cnfInterpretation_rel_lit A e

/-- Every vertex has a color under a satisfying assignment. -/
private theorem exists_color {A : cnfInterpretation.Model M → Prop} (hA : Satisfies A) (v : M) :
    ∃ c, A (varElt c v) := by
  rcases (clauseSatisfied_iff' A ⟨.vertex, fun _ => v, formula_realize_top⟩).1 (hA _) with
    ⟨τ, hτ, -, y, hy, hc, ha⟩ | ⟨τ, hτ, -⟩
  · simp only [coloringClauseTemplates, List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl | rfl
    · obtain rfl : y = fun _ => v := funext fun j => hc j j rfl
      exact ⟨0, ha⟩
    · obtain rfl : y = fun _ => v := funext fun j => hc j j rfl
      exact ⟨1, ha⟩
    · obtain rfl : y = fun _ => v := funext fun j => hc j j rfl
      exact ⟨2, ha⟩
  · simp [coloringClauseTemplates] at hτ

/-- The assignment of a coloring: `x(v, c)` is true when `v` has the color `c`. -/
private def coloringAssignment (f : M → Fin 3) : cnfInterpretation.Model M → Prop
  | ⟨.var c, d, _⟩ => f (d 0) = c
  | _ => False

/-- **The CNF structure of the colorings of a graph is satisfiable exactly when the graph is
three-colorable.** -/
theorem satisfiable_cnfInterpretation_iff :
    Satisfiable (cnfInterpretation.Model M) ↔ Colorable 3 M := by
  constructor
  · rintro ⟨A, hA⟩
    choose f hf using exists_color hA
    refine ⟨f, fun u v huv hfuv => ?_⟩
    have hd : (cnfInterpretation.domain (.edge (f u))).Realize ![u, v] := by
      change (adj.formula₂ (.var 0) (.var 1)).Realize _
      simpa using huv
    rcases (clauseSatisfied_iff' A ⟨.edge (f u), ![u, v], hd⟩).1 (hA _) with
      ⟨τ, hτ, -⟩ | ⟨τ, hτ, -, y, hy, hc, ha⟩
    · simp [coloringClauseTemplates] at hτ
    · simp only [coloringClauseTemplates, List.mem_cons, List.not_mem_nil, or_false] at hτ
      rcases hτ with rfl | rfl
      · have hy' : y = fun _ => u := funext fun j => hc j 0 rfl
        subst hy'
        exact ha (hf u)
      · have hy' : y = fun _ => v := funext fun j => hc j 1 rfl
        subst hy'
        exact ha (hfuv ▸ hf v)
  · rintro ⟨f, hf⟩
    refine ⟨coloringAssignment f, fun ⟨t, d, hd⟩ => ?_⟩
    refine (clauseSatisfied_iff' _ _).2 ?_
    cases t with
    | var c =>
      by_cases h : f (d 0) = c
      · exact .inl ⟨_, List.mem_singleton.2 rfl, formula_realize_top, d, hd,
          fun j i hj => by cases Option.some.inj hj; rfl, h⟩
      · exact .inr ⟨_, List.mem_singleton.2 rfl, formula_realize_top, d, hd,
          fun j i hj => by cases Option.some.inj hj; rfl, h⟩
    | vertex =>
      refine .inl ⟨⟨.var (f (d 0)), ⊤, some⟩, ?_, formula_realize_top, d, formula_realize_top,
        fun j i hj => by cases Option.some.inj hj; rfl, rfl⟩
      simp only [coloringClauseTemplates, List.mem_cons, List.not_mem_nil, or_false]
      generalize f (d 0) = c
      fin_cases c <;> simp
    | edge c =>
      have huv : RelMap adj ![d 0, d 1] := Formula.realize_rel₂.1 hd
      by_cases h : f (d 0) = c
      · refine .inr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, formula_realize_top,
          fun _ => d 1, formula_realize_top, fun j i hj => by cases Option.some.inj hj; rfl, ?_⟩
        change ¬f (d 1) = c
        exact fun h' => hf _ _ huv (h.trans h'.symm)
      · exact .inr ⟨_, List.mem_cons_self, formula_realize_top, fun _ => d 0,
          formula_realize_top, fun j i hj => by cases Option.some.inj hj; rfl, h⟩

private theorem encard_le_three_of_subset {α : Type*} {s : Set α} {a b c : α}
    (h : s ⊆ {a, b, c}) : s.encard ≤ 3 := by
  refine (Set.encard_le_encard h).trans ?_
  refine (Set.encard_insert_le _ _).trans ?_
  have := Set.encard_insert_le ({c} : Set α) b
  rw [Set.encard_singleton] at this
  calc ({b, c} : Set α).encard + 1 ≤ 1 + 1 + 1 := by gcongr
    _ = 3 := by norm_num

/-- **The CNF structure of the colorings of a graph is a 3-CNF structure.** -/
theorem isThreeCNF_cnfInterpretation : IsThreeCNF (cnfInterpretation.Model M) := by
  rintro ⟨t, d, hd⟩
  have hlit (l : Bool × cnfInterpretation.Model M) (hl : l ∈ literals (⟨t, d, hd⟩ : _)) :
      ∃ τ ∈ coloringClauseTemplates t l.1, ∃ y, l.2.toSigma = ⟨τ.target, y⟩ ∧ τ.Compat d y := by
    obtain ⟨τ, hτ, -, y, hy, hc⟩ := (relMap_lit_of_templates cnfInterpretation_rel_lit l.1 _ _).1 hl
    exact ⟨τ, hτ, y, hy, hc⟩
  cases t with
  | var c =>
    refine encard_le_three_of_subset (a := (true, ⟨.var c, d, hd⟩)) (b := (false, ⟨.var c, d, hd⟩))
      (c := (false, ⟨.var c, d, hd⟩)) fun ⟨b, e⟩ hl => ?_
    obtain ⟨τ, hτ, y, hy, hc⟩ := hlit _ hl
    obtain rfl := List.mem_singleton.1 hτ
    have he : e = ⟨.var c, d, hd⟩ := Model.ext_toSigma (hy.trans (by
      congr 1
      exact funext fun j => hc j j rfl))
    subst he
    cases b <;> simp
  | vertex =>
    refine encard_le_three_of_subset (a := (true, varElt 0 (d 0))) (b := (true, varElt 1 (d 0)))
      (c := (true, varElt 2 (d 0))) fun ⟨b, e⟩ hl => ?_
    obtain ⟨τ, hτ, y, hy, hc⟩ := hlit _ hl
    cases b
    · simp [coloringClauseTemplates] at hτ
    · simp only [coloringClauseTemplates, List.mem_cons, List.not_mem_nil, or_false] at hτ
      rcases hτ with rfl | rfl | rfl
      · obtain rfl : y = fun _ => d 0 :=
          funext fun j => (hc j j rfl).trans (congrArg d (Subsingleton.elim _ _))
        exact .inl (Prod.ext rfl (Model.ext_toSigma hy))
      · obtain rfl : y = fun _ => d 0 :=
          funext fun j => (hc j j rfl).trans (congrArg d (Subsingleton.elim _ _))
        exact .inr (.inl (Prod.ext rfl (Model.ext_toSigma hy)))
      · obtain rfl : y = fun _ => d 0 :=
          funext fun j => (hc j j rfl).trans (congrArg d (Subsingleton.elim _ _))
        exact .inr (.inr (Prod.ext rfl (Model.ext_toSigma hy)))
  | edge c =>
    refine encard_le_three_of_subset (a := (false, varElt c (d 0))) (b := (false, varElt c (d 1)))
      (c := (false, varElt c (d 1))) fun ⟨b, e⟩ hl => ?_
    obtain ⟨τ, hτ, y, hy, hc⟩ := hlit _ hl
    cases b
    · simp only [coloringClauseTemplates, List.mem_cons, List.not_mem_nil, or_false] at hτ
      rcases hτ with rfl | rfl
      · have hy' : y = fun _ => d 0 := funext fun j => hc j 0 rfl
        subst hy'
        exact .inl (Prod.ext rfl (Model.ext_toSigma hy))
      · have hy' : y = fun _ => d 1 := funext fun j => hc j 1 rfl
        subst hy'
        exact .inr (.inl (Prod.ext rfl (Model.ext_toSigma hy)))
    · simp [coloringClauseTemplates] at hτ

/-! ### Structures with at most one element -/

/-- On a graph with at most one vertex: a single clause, the clause `x` without a loop and the
empty clause with a loop. -/
def cnfSubsingleton : Interpretation Language.graph cnf Unit where
  domain := ⊤
  rel R := match R with
    | .pos => ∼(adj.formula₂ (.var (0, ())) (.var (0, ())))
    | .neg => ⊥

private theorem threeSat_cnfSubsingleton_iff [Subsingleton M] [Nonempty M] :
    (IsThreeCNF (cnfSubsingleton.Model M) ∧ Satisfiable (cnfSubsingleton.Model M)) ↔
      Colorable 3 M := by
  obtain ⟨v⟩ := ‹Nonempty M›
  have hpos (e e' : cnfSubsingleton.Model M) :
      RelMap cnf.pos ![e, e'] ↔ ¬RelMap adj ![v, v] := by
    fo_simp [Subsingleton.elim (e.1 ()) v]
  have hneg (e e' : cnfSubsingleton.Model M) : ¬RelMap cnf.neg ![e, e'] := id
  have : Subsingleton (cnfSubsingleton.Model M) :=
    ⟨fun x y => Interpretation.Model.ext (Subsingleton.elim _ _)⟩
  rw [and_iff_right (isThreeCNF_of_subsingleton (M := cnfSubsingleton.Model M))]
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨y, ⟨h, -⟩ | ⟨h, -⟩⟩ := hA ⟨fun _ => v, formula_realize_top⟩
    · exact ⟨fun _ => 0, fun x y hxy => absurd (by rwa [Subsingleton.elim x v,
        Subsingleton.elim y v] at hxy) ((hpos _ _).1 h)⟩
    · exact (hneg _ _ h).elim
  · rintro ⟨f, hf⟩
    have hv : ¬RelMap adj ![v, v] := fun h => hf v v h rfl
    exact ⟨fun _ => True, fun e => ⟨e, .inl ⟨(hpos _ _).2 hv, trivial⟩⟩⟩

/-- **3COL reduces to 3SAT by an order-free first-order interpretation.** -/
theorem reduces_ThreeColorable_ThreeSAT : Reduces ThreeColorable.{w} ThreeSAT.{w} := by
  refine Reduces.of_tagged isoClosed_ThreeSAT copyInvariant_ThreeSAT cnfInterpretation
    cnfSubsingleton (fun M _ _ => ⟨fun h => ⟨isThreeCNF_cnfInterpretation,
      satisfiable_cnfInterpretation_iff.2 h⟩, fun h => satisfiable_cnfInterpretation_iff.1 h.2⟩)
    (fun M _ hM => ?_)
  rcases isEmpty_or_nonempty M with hM' | hM'
  · have : IsEmpty (cnfSubsingleton.Model M) := ⟨fun x => isEmptyElim (x.1 ())⟩
    exact iff_of_true colorable_of_isEmpty
      ⟨isThreeCNF_of_isEmpty (M := cnfSubsingleton.Model M),
        satisfiable_of_isEmpty (M := cnfSubsingleton.Model M)⟩
  · exact threeSat_cnfSubsingleton_iff.symm

end Cslib.Logic.FO.graph
