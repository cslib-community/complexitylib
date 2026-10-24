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
# The order-free first-order interpretation from 3SAT to 3COL

The reductions in this module use order-free first-order interpretations. Input structures have
no built-in order or numeric predicates; these are variants of the standard ordered setting.

The palette, variable and clause gadget reduction from 3SAT to three-colorability, a standard
exercise [Sipser, Chapter 7][Sipser2013] (three-colorability is NP-complete
[Garey and Johnson][GareyJohnson1979]), is first-order on CNF structures
(`Cslib.Logic.FO.cnf.reduces_ThreeSAT_ThreeColorable`). From a 3-CNF structure it builds a palette
triangle `T`, `F`, `B`, two literal vertices `x` and `¬x` for each variable, joined to each other
and to `B`, and for each clause a gadget of six vertices, two chained OR gates whose output is
joined to `F` and `B`. A clause with at most three literals has no canonical order, so there is a
gadget for every triple of its literals that lists all of them; each such gadget forces the clause.
The construction is a tagged interpretation, the tags being the kinds of vertices. Inputs that are
not 3-CNF structures, or that have an empty clause, are mapped to graphs with a loop.

The target is the class `graph.ThreeColorable` of three-colorable graph structures, loops allowed.
On the members of 3SAT the graph is symmetric and loopless, so the same interpretation reduces
3SAT to classical three-colorability of simple graphs
(`Cslib.Logic.FO.cnf.reduces_ThreeSAT_SimpleThreeColorable`). The machine-level reduction, on
encoded formulas and graphs, is `Cslib.Complexity.SAT.toThreeColoring`.

## Main definitions

* `Cslib.Logic.FO.cnf.orGate`, `Cslib.Logic.FO.cnf.gadgetColor`,
  `Cslib.Logic.FO.cnf.GadgetProper`: the OR-gate coloring and properness condition for the
  six-vertex clause gadget.
* `Cslib.Logic.FO.cnf.ColoringTag`, `Cslib.Logic.FO.cnf.ColoringTag.Coord`,
  `Cslib.Logic.FO.cnf.GadgetDomain`, `Cslib.Logic.FO.cnf.gadgetDomain`,
  `Cslib.Logic.FO.cnf.badSentence`, `Cslib.Logic.FO.cnf.coloringEdges`,
  `Cslib.Logic.FO.cnf.coloringAdj`: the vertex tags, coordinates, gadget domain, and edge templates
  of the reduction graph.
* `Cslib.Logic.FO.cnf.coloringInterpretation`, `Cslib.Logic.FO.cnf.coloringSubsingleton`: the graph
  built from a CNF structure, as a tagged interpretation and on subsingletons.

## Main results

* `Cslib.Logic.FO.cnf.colorable_coloringInterpretation_iff`: the graph built from a CNF
  structure is three-colorable exactly when the structure is a satisfiable 3-CNF structure.
* `Cslib.Logic.FO.cnf.reduces_ThreeSAT_ThreeColorable`,
  `Cslib.Logic.FO.cnf.reduces_ThreeSAT_SimpleThreeColorable`: **3SAT is order-free reducible to
  3COL**, with loops allowed or on simple graphs.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe w

namespace Cslib.Logic.FO

open FirstOrder Language Structure CategoryTheory

namespace cnf

open TaggedInterpretation

/-! ### The clause gadget -/

/-- An OR gate on colors, with true `0`, false `1` and base `2`: the colors of the vertices
adjacent to the two inputs and of the output. -/
def orGate (u v : Fin 3) : Fin 3 × Fin 3 × Fin 3 :=
  if u = 0 then (1, 2, 0) else if v = 0 then (2, 1, 0) else (0, 2, 1)

/-- The coloring of the six vertices of the clause gadget for inputs colored `u`, `v`, `w`. -/
def gadgetColor (u v w : Fin 3) : Fin 6 → Fin 3 :=
  ![(orGate u v).1, (orGate u v).2.1, (orGate u v).2.2, (orGate (orGate u v).2.2 w).1,
    (orGate (orGate u v).2.2 w).2.1, (orGate (orGate u v).2.2 w).2.2]

/-- The edges of the clause gadget with inputs `u`, `v`, `w` and palette `t`, `f`, `b` are
properly colored by `g`: vertices `0, 1, 2` and `3, 4, 5` are triangles, `0` is joined to `u`,
`1` to `v`, `2` to `3`, `4` to `w`, and `5` to `f` and `b`. -/
abbrev GadgetProper (u v w : Fin 3) (g : Fin 6 → Fin 3) (f b : Fin 3) : Prop :=
  g 0 ≠ u ∧ g 1 ≠ v ∧ g 0 ≠ g 1 ∧ g 0 ≠ g 2 ∧ g 1 ≠ g 2 ∧ g 2 ≠ g 3 ∧ g 4 ≠ w ∧ g 3 ≠ g 4 ∧
    g 3 ≠ g 5 ∧ g 4 ≠ g 5 ∧ g 5 ≠ f ∧ g 5 ≠ b

/-- With true `0`, false `1` and base `2`, the gadget is properly colored when some input is
true. -/
private theorem gadgetProper_gadgetColor :
    ∀ u v w : Fin 3, u ≠ 2 → v ≠ 2 → w ≠ 2 → (u = 0 ∨ v = 0 ∨ w = 0) →
      GadgetProper u v w (gadgetColor u v w) 1 2 := by
  decide

private theorem fin_three_eq_of_ne :
    ∀ x y z w : Fin 3, x ≠ w → y ≠ w → x ≠ y → z ≠ x → z ≠ y → z = w := by
  intro x y z w
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases w <;> decide

private theorem fin_three_eq {x y z w : Fin 3} (hx : x ≠ w) (hy : y ≠ w) (hxy : x ≠ y) (hzx : z ≠ x)
    (hzy : z ≠ y) : z = w :=
  fin_three_eq_of_ne x y z w hx hy hxy hzx hzy

/-- **The gadget forces the clause**: in a proper coloring with palette `t`, `f`, `b`, some input
of the gadget has the color `t` of true, if all inputs are colored `t` or `f`. -/
private theorem gadget_forces {t f b u v w : Fin 3} {g : Fin 6 → Fin 3} (hu : u = t ∨ u = f)
    (hv : v = t ∨ v = f) (hw : w = t ∨ w = f) (h : GadgetProper u v w g f b) :
    u = t ∨ v = t ∨ w = t := by
  by_contra hne
  simp only [not_or] at hne
  rw [hu.resolve_left hne.1, hv.resolve_left hne.2.1, hw.resolve_left hne.2.2] at h
  obtain ⟨h0, h1, h01, h02, h12, h23, h4, h34, h35, h45, h5f, -⟩ := h
  have hg2 : g 2 = f := fin_three_eq h0 h1 h01 (Ne.symm h02) (Ne.symm h12)
  exact h5f (fin_three_eq (hg2 ▸ h23.symm) h4 h34 (Ne.symm h35) (Ne.symm h45))

/-! ### The graph of a CNF structure -/

/-- The kinds of vertices of the graph built from a CNF structure: the palette `T`, `F`, `B`,
the literal vertices of each polarity, and the vertices of the clause gadgets, for each pattern of
polarities of the three literals of the gadget. -/
inductive ColoringTag : Type
  /-- The palette vertex of true. -/
  | trueV
  /-- The palette vertex of false. -/
  | falseV
  /-- The palette vertex joined to all literals. -/
  | baseV
  /-- The literal vertices of a polarity. -/
  | lit (p : Bool)
  /-- The vertex `g` of the gadgets of a pattern of polarities. -/
  | gadget (g : Fin 6) (ps : Fin 3 → Bool)

/-- The kinds of vertices, as a sum type. -/
private def ColoringTag.toSum : ColoringTag → Fin 3 ⊕ Bool ⊕ (Fin 6 × (Fin 3 → Bool))
  | .trueV => .inl 0
  | .falseV => .inl 1
  | .baseV => .inl 2
  | .lit p => .inr (.inl p)
  | .gadget g ps => .inr (.inr (g, ps))

/-- There are finitely many vertex tags in `ColoringTag`. -/
instance : Finite ColoringTag := by
  refine Finite.of_injective ColoringTag.toSum ?_
  intro a b h
  cases a <;> cases b <;> simp_all [ColoringTag.toSum]

/-- The coordinates of the vertices: none for the palette, the variable of a literal vertex, and
the clause and the three literal variables of a gadget vertex. -/
abbrev ColoringTag.Coord : ColoringTag → Type
  | .trueV => Fin 0
  | .falseV => Fin 0
  | .baseV => Fin 0
  | .lit _ => Fin 1
  | .gadget _ _ => Fin 4

/-- Every vertex tag in `ColoringTag` has a finite coordinate type. -/
instance instFiniteColoringTagCoord : ∀ u : ColoringTag, Finite u.Coord
  | .trueV | .falseV | .baseV => inferInstanceAs (Finite (Fin 0))
  | .lit _ => inferInstanceAs (Finite (Fin 1))
  | .gadget _ _ => inferInstanceAs (Finite (Fin 4))

variable {M : Type*} [cnf.Structure M]

/-- A gadget with coordinates `d` lists the literals `(ps i, d (i + 1))` of the clause `d 0`, and
all of them. -/
def GadgetDomain (ps : Fin 3 → Bool) (d : Fin 4 → M) : Prop :=
  (∀ i : Fin 3, (ps i, d i.succ) ∈ literals (d 0)) ∧
    ∀ l ∈ literals (d 0), ∃ i : Fin 3, (ps i, d i.succ) = l

/-- The domain formula of the gadgets of a pattern of polarities. -/
noncomputable def gadgetDomain (ps : Fin 3 → Bool) : cnf.Formula (Fin 4) :=
  Formula.iInf (fun i : Fin 3 => (lit (ps i)).formula₂ (.var 0) (.var i.succ)) ⊓
    Formula.iAlls Unit (Formula.iInf fun p : Bool =>
      (lit p).formula₂ (.var (.inl 0)) (.var (.inr ())) ⟹
        Formula.iSup fun i : Fin 3 =>
          if ps i = p then varEq (.inr ()) (.inl i.succ) else ⊥)

private theorem realize_gadgetDomain (ps : Fin 3 → Bool) (d : Fin 4 → M) :
    (gadgetDomain ps).Realize d ↔ GadgetDomain ps d := by
  simp only [gadgetDomain, Formula.realize_inf, Formula.realize_iInf, Formula.realize_rel₂,
    Term.realize_var, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_iSup,
    Sum.elim_inl, Sum.elim_inr, GadgetDomain]
  refine and_congr Iff.rfl ⟨fun h ⟨p, y⟩ hl => ?_, fun h e p hp => ?_⟩
  · obtain ⟨i, hi⟩ := h (fun _ => y) p hl
    refine ⟨i, ?_⟩
    split_ifs at hi with hpi
    · exact Prod.ext hpi ((realize_varEq _ _ _).1 hi).symm
    · exact hi.elim
  · obtain ⟨i, hi⟩ := h (p, e ()) hp
    refine ⟨i, ?_⟩
    split_ifs with hpi
    · exact (realize_varEq _ _ _).2 (congrArg Prod.snd hi).symm
    · exact hpi (congrArg Prod.fst hi)

/-- The sentence saying that the structure is not a 3-CNF structure with nonempty clauses. -/
noncomputable def badSentence : cnf.Sentence :=
  ∼(threeCNFSentence ⊓ nonemptyClausesSentence)

private theorem realize_badSentence :
    M ⊨ badSentence ↔ ¬(IsThreeCNF M ∧ ∀ c : M, (literals c).Nonempty) := by
  rw [badSentence, Sentence.realize_not, Sentence.realize_inf, realize_threeCNFSentence,
    realize_nonemptyClausesSentence]

/-- The edges of the graph, from each kind of vertex: the palette triangle, with a loop at `T`
on bad inputs, the literal vertices joined to `B` and `x` joined to `¬x`, and the gadgets. -/
noncomputable def coloringEdges : (u : ColoringTag) →
    List (Template cnf ColoringTag.Coord u)
  | .trueV => [⟨.falseV, ⊤, Fin.elim0⟩, ⟨.baseV, ⊤, Fin.elim0⟩,
      ⟨.trueV, badSentence.relabel Empty.elim, Fin.elim0⟩]
  | .falseV => [⟨.baseV, ⊤, Fin.elim0⟩]
  | .baseV => []
  | .lit true => [⟨.lit false, ⊤, some⟩, ⟨.baseV, ⊤, Fin.elim0⟩]
  | .lit false => [⟨.baseV, ⊤, Fin.elim0⟩]
  | .gadget 0 ps => [⟨.lit (ps 0), ⊤, fun _ => some 1⟩, ⟨.gadget 1 ps, ⊤, some⟩,
      ⟨.gadget 2 ps, ⊤, some⟩]
  | .gadget 1 ps => [⟨.lit (ps 1), ⊤, fun _ => some 2⟩, ⟨.gadget 2 ps, ⊤, some⟩]
  | .gadget 2 ps => [⟨.gadget 3 ps, ⊤, some⟩]
  | .gadget 3 ps => [⟨.gadget 4 ps, ⊤, some⟩, ⟨.gadget 5 ps, ⊤, some⟩]
  | .gadget 4 ps => [⟨.lit (ps 2), ⊤, fun _ => some 3⟩, ⟨.gadget 5 ps, ⊤, some⟩]
  | .gadget 5 _ => [⟨.falseV, ⊤, Fin.elim0⟩, ⟨.baseV, ⊤, Fin.elim0⟩]

/-- The formula of the edges between vertices of kinds `u` and `w`, in both directions. -/
noncomputable def coloringAdj (u w : ColoringTag) :
    cnf.Formula (u.Coord ⊕ w.Coord) :=
  Template.listFormula (coloringEdges u) w ⊔
    (Template.listFormula (coloringEdges w) u).relabel Sum.swap

/-- **The graph of a CNF structure**, a tagged interpretation: the edges are those of
`coloringEdges`, in both directions. -/
noncomputable def coloringInterpretation :
    TaggedInterpretation cnf Language.graph ColoringTag ColoringTag.Coord where
  domain
    | .gadget _ ps => gadgetDomain ps
    | _ => ⊤
  rel R := match R with
    | .adj => binaryRel coloringAdj

/-- An edge from `a` to `c` given by a template of the kind of `a`. -/
private def Edge (a c : coloringInterpretation.Model M) : Prop :=
  ∃ τ ∈ coloringEdges a.1, τ.Holds a.2.1 c.toSigma

private theorem relMap_adj_iff (a c : coloringInterpretation.Model M) :
    RelMap adj ![a, c] ↔ Edge a c ∨ Edge c a := by
  rw [relMap_binaryRel (F := coloringAdj) (fun _ => rfl), coloringAdj, Formula.realize_sup,
    Template.realize_listFormula, Formula.realize_relabel, Sum.elim_swap,
    Template.realize_listFormula]
  rfl

private theorem colorable_iff_edge :
    graph.Colorable 3 (coloringInterpretation.Model M) ↔
      ∃ f : coloringInterpretation.Model M → Fin 3, ∀ a c, Edge a c → f a ≠ f c := by
  refine ⟨fun ⟨f, hf⟩ => ⟨f, fun a c h => hf a c ((relMap_adj_iff a c).2 (.inl h))⟩,
    fun ⟨f, hf⟩ => ⟨f, fun a c h => ?_⟩⟩
  rcases (relMap_adj_iff a c).1 h with h | h
  · exact hf a c h
  · exact (hf c a h).symm

/-! ### Correctness -/

section Correctness

/-- The palette vertex of true. -/
private def trueVertex : coloringInterpretation.Model M :=
  ⟨.trueV, Fin.elim0, formula_realize_top⟩

/-- The palette vertex of false. -/
private def falseVertex : coloringInterpretation.Model M :=
  ⟨.falseV, Fin.elim0, formula_realize_top⟩

/-- The palette vertex joined to all literals. -/
private def baseVertex : coloringInterpretation.Model M :=
  ⟨.baseV, Fin.elim0, formula_realize_top⟩

/-- The literal vertex of polarity `p` of the variable `x`. -/
private def litVertex (p : Bool) (x : M) : coloringInterpretation.Model M :=
  ⟨.lit p, fun _ => x, formula_realize_top⟩

open scoped Classical in
/-- The color of a literal under an assignment: `0` when it is true and `1` when it is false. -/
private noncomputable def litColor (A : M → Prop) (p : Bool) (x : M) : Fin 3 :=
  if (A x ↔ p = true) then 0 else 1

omit [cnf.Structure M] in
private theorem litColor_ne_two (A : M → Prop) (p : Bool) (x : M) : litColor A p x ≠ 2 := by
  unfold litColor
  split_ifs <;> decide

omit [cnf.Structure M] in
private theorem litColor_true_ne_false (A : M → Prop) (x : M) :
    litColor A true x ≠ litColor A false x := by
  unfold litColor
  by_cases h : A x <;> simp [h]

/-- The coloring of the graph given by an assignment: true `0`, false `1`, base `2`, a literal
by its truth value and a gadget by `gadgetColor`. -/
private noncomputable def colorOf (A : M → Prop) : (Σ u : ColoringTag, u.Coord → M) → Fin 3
  | ⟨.trueV, _⟩ => 0
  | ⟨.falseV, _⟩ => 1
  | ⟨.baseV, _⟩ => 2
  | ⟨.lit p, y⟩ => litColor A p (y 0)
  | ⟨.gadget g ps, d⟩ =>
    gadgetColor (litColor A (ps 0) (d 1)) (litColor A (ps 1) (d 2)) (litColor A (ps 2) (d 3)) g

/-- Under a satisfying assignment some input of every gadget is true. -/
private theorem exists_litColor_eq_zero {A : M → Prop} (hA : Satisfies A) {ps : Fin 3 → Bool}
    {d : Fin 4 → M} (hd : GadgetDomain ps d) :
    litColor A (ps 0) (d 1) = 0 ∨ litColor A (ps 1) (d 2) = 0 ∨ litColor A (ps 2) (d 3) = 0 := by
  obtain ⟨l, hl, hA⟩ := (satisfies_iff A).1 hA (d 0)
  obtain ⟨i, rfl⟩ := hd.2 l hl
  have h : litColor A (ps i) (d i.succ) = 0 := by
    unfold litColor
    split_ifs with h
    · rfl
    · exact absurd hA h
  fin_cases i
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)

private theorem gadgetDomain_of_realize {g : Fin 6} {ps : Fin 3 → Bool} {d : Fin 4 → M}
    (hd : (coloringInterpretation.domain (.gadget g ps)).Realize d) : GadgetDomain ps d :=
  (realize_gadgetDomain ps d).1 hd

omit [cnf.Structure M] in
private theorem colorOf_ne_of_comp_some {A : M → Prop} {c : Fin 3} {w : ColoringTag}
    {x y : w.Coord → M} (hcomp : ∀ j i : w.Coord, some j = some i → y j = x i)
    (hne : c ≠ colorOf A ⟨w, x⟩) : c ≠ colorOf A ⟨w, y⟩ :=
  (funext fun j => hcomp j j rfl : y = x) ▸ hne

omit [cnf.Structure M] in
private theorem colorOf_ne_lit_of_comp {A : M → Prop} {α : Type} {c : Fin 3} {p : Bool} {i : α}
    {x : α → M} {y : Fin 1 → M} (hcomp : ∀ (_ : Fin 1) (i' : α), some i = some i' → y ‹_› = x i')
    (hne : c ≠ litColor A p (x i)) : c ≠ colorOf A ⟨.lit p, y⟩ := by
  have hy : y 0 = x i := hcomp 0 i rfl
  change c ≠ litColor A p (y 0)
  rw [hy]
  exact hne

/-- **A satisfying assignment colors the graph**: the coloring `colorOf` is proper on every
edge. -/
private theorem colorOf_ne_of_edge {A : M → Prop} (hA : Satisfies A) (hgood : ¬M ⊨ badSentence)
    {a c : coloringInterpretation.Model M} (h : Edge a c) :
    colorOf A a.toSigma ≠ colorOf A c.toSigma := by
  obtain ⟨u, x, hx⟩ := a
  obtain ⟨τ, hτ, hg, y, hc, hcomp⟩ := h
  rw [hc]
  change colorOf A ⟨u, x⟩ ≠ colorOf A ⟨τ.target, y⟩
  cases u with
  | trueV =>
    simp only [coloringEdges, List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl | rfl
    · exact (by decide : (0 : Fin 3) ≠ 1)
    · exact (by decide : (0 : Fin 3) ≠ 2)
    · exact absurd ((congrArg (Formula.Realize badSentence) (Subsingleton.elim _ default)).mp
        (Formula.realize_relabel.1 hg)) hgood
  | falseV =>
    simp only [coloringEdges, List.mem_cons, List.not_mem_nil, or_false] at hτ
    subst hτ
    exact (by decide : (1 : Fin 3) ≠ 2)
  | baseV => simp [coloringEdges] at hτ
  | lit p =>
    cases p
    · simp only [coloringEdges, List.mem_cons, List.not_mem_nil, or_false] at hτ
      subst hτ
      exact litColor_ne_two A false (x 0)
    · simp only [coloringEdges, List.mem_cons, List.not_mem_nil, or_false] at hτ
      rcases hτ with rfl | rfl
      · exact colorOf_ne_of_comp_some hcomp (litColor_true_ne_false A (x 0))
      · exact litColor_ne_two A true (x 0)
  | gadget g ps =>
    have hd := gadgetDomain_of_realize hx
    have hP := gadgetProper_gadgetColor _ _ _ (litColor_ne_two A (ps 0) (x 1))
      (litColor_ne_two A (ps 1) (x 2)) (litColor_ne_two A (ps 2) (x 3))
      (exists_litColor_eq_zero hA hd)
    obtain ⟨h0, h1, h01, h02, h12, h23, h4, h34, h35, h45, h5f, h5b⟩ := hP
    fin_cases g <;> simp only [coloringEdges, List.mem_cons, List.not_mem_nil, or_false] at hτ
    · rcases hτ with rfl | rfl | rfl
      · exact colorOf_ne_lit_of_comp hcomp h0
      · exact colorOf_ne_of_comp_some hcomp h01
      · exact colorOf_ne_of_comp_some hcomp h02
    · rcases hτ with rfl | rfl
      · exact colorOf_ne_lit_of_comp hcomp h1
      · exact colorOf_ne_of_comp_some hcomp h12
    · subst hτ
      exact colorOf_ne_of_comp_some hcomp h23
    · rcases hτ with rfl | rfl
      · exact colorOf_ne_of_comp_some hcomp h34
      · exact colorOf_ne_of_comp_some hcomp h35
    · rcases hτ with rfl | rfl
      · exact colorOf_ne_lit_of_comp hcomp h4
      · exact colorOf_ne_of_comp_some hcomp h45
    · rcases hτ with rfl | rfl
      · exact h5f
      · exact h5b

/-- A clause with between one and three literals is listed by some triple of its literals. -/
private theorem exists_triple_of_encard_le_three {α : Type*} {S : Set α} (hne : S.Nonempty)
    (h3 : S.encard ≤ 3) : ∃ l : Fin 3 → α, (∀ i, l i ∈ S) ∧ ∀ m ∈ S, ∃ i, l i = m := by
  have hfin : S.Finite := Set.finite_of_encard_le_coe h3
  have hn : S.encard = S.ncard := hfin.cast_ncard_eq.symm
  have h0 : S.ncard ≠ 0 := (Set.ncard_pos hfin).2 hne |>.ne'
  have h3' : S.ncard ≤ 3 := by
    have := hn ▸ h3
    exact_mod_cast this
  obtain h | h | h : S.ncard = 1 ∨ S.ncard = 2 ∨ S.ncard = 3 := by omega
  · obtain ⟨a, rfl⟩ := Set.encard_eq_one.1 (by rw [hn, h]; rfl)
    exact ⟨![a, a, a], fun i => by fin_cases i <;> rfl, fun m hm => ⟨0, by simpa using hm.symm⟩⟩
  · obtain ⟨a, b, -, rfl⟩ := Set.encard_eq_two.1 (by rw [hn, h]; rfl)
    refine ⟨![a, b, b], fun i => by fin_cases i <;> simp, fun m hm => ?_⟩
    rcases hm with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · obtain ⟨a, b, e, -, -, -, rfl⟩ := Set.encard_eq_three.1 (by rw [hn, h]; rfl)
    refine ⟨![a, b, e], fun i => by fin_cases i <;> simp, fun m hm => ?_⟩
    rcases hm with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- **A three-coloring gives a satisfying assignment**: the clauses of the structure are those of
a satisfiable 3-CNF structure. -/
private theorem satisfies_of_colorable {f : coloringInterpretation.Model M → Fin 3}
    (hf : ∀ a c, Edge a c → f a ≠ f c) : IsThreeCNF M ∧ Satisfiable M := by
  have hTF : f trueVertex ≠ f falseVertex :=
    hf _ _ ⟨_, List.mem_cons_self, formula_realize_top, _, rfl, fun j => j.elim0⟩
  have hTB : f trueVertex ≠ f baseVertex :=
    hf _ _ ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, formula_realize_top, _, rfl,
      fun j => j.elim0⟩
  have hFB : f falseVertex ≠ f baseVertex :=
    hf _ _ ⟨_, List.mem_cons_self, formula_realize_top, _, rfl, fun j => j.elim0⟩
  have hgood : ¬M ⊨ badSentence := fun hbad => hf trueVertex trueVertex
    ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      Formula.realize_relabel.2
        ((congrArg (Formula.Realize badSentence) (Subsingleton.elim _ default)).mpr hbad),
      _, rfl, fun j => j.elim0⟩ rfl
  obtain ⟨h3, hne⟩ := not_not.1 ((not_congr realize_badSentence).1 hgood)
  have hlitB (p : Bool) (x : M) : f (litVertex p x) ≠ f baseVertex := by
    cases p
    · exact hf _ _ ⟨_, List.mem_cons_self, formula_realize_top, _, rfl, fun j => j.elim0⟩
    · exact hf _ _ ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, formula_realize_top, _, rfl,
        fun j => j.elim0⟩
  have hlit (p : Bool) (x : M) :
      f (litVertex p x) = f trueVertex ∨ f (litVertex p x) = f falseVertex := by
    by_contra h
    simp only [not_or] at h
    exact hlitB p x (fin_three_eq hTB hFB hTF h.1 h.2)
  have hneg (x : M) : f (litVertex true x) ≠ f (litVertex false x) :=
    hf _ _ ⟨_, List.mem_cons_self, formula_realize_top, _, rfl,
      fun j i hj => by cases Option.some.inj hj; rfl⟩
  refine ⟨h3, fun x => f (litVertex true x) = f trueVertex, (satisfies_iff _).2 fun c => ?_⟩
  obtain ⟨l, hl, hsurj⟩ := exists_triple_of_encard_le_three (hne c) (h3 c)
  let ps : Fin 3 → Bool := fun i => (l i).1
  let d : Fin 4 → M := ![c, (l 0).2, (l 1).2, (l 2).2]
  have hd : GadgetDomain ps d := by
    refine ⟨fun i => ?_, fun m hm => ?_⟩
    · fin_cases i <;> exact hl _
    · obtain ⟨i, rfl⟩ := hsurj m hm
      refine ⟨i, ?_⟩
      fin_cases i <;> rfl
  have hdom (g : Fin 6) : (coloringInterpretation.domain (.gadget g ps)).Realize d :=
    (realize_gadgetDomain ps d).2 hd
  let G : Fin 6 → coloringInterpretation.Model M := fun g => ⟨.gadget g ps, d, hdom g⟩
  have hP : GadgetProper (f (litVertex (ps 0) (d 1))) (f (litVertex (ps 1) (d 2)))
      (f (litVertex (ps 2) (d 3))) (fun g => f (G g)) (f falseVertex) (f baseVertex) := by
    refine ⟨hf (G 0) _ ⟨_, List.mem_cons_self, formula_realize_top, _, rfl, fun j i hj => ?_⟩,
      hf (G 1) _ ⟨_, List.mem_cons_self, formula_realize_top, _, rfl, fun j i hj => ?_⟩,
      hf (G 0) (G 1) ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, formula_realize_top, _, rfl,
        fun j i hj => ?_⟩,
      hf (G 0) (G 2) ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        formula_realize_top, _, rfl, fun j i hj => ?_⟩,
      hf (G 1) (G 2) ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, formula_realize_top, _, rfl,
        fun j i hj => ?_⟩,
      hf (G 2) (G 3) ⟨_, List.mem_cons_self, formula_realize_top, _, rfl, fun j i hj => ?_⟩,
      hf (G 4) _ ⟨_, List.mem_cons_self, formula_realize_top, _, rfl, fun j i hj => ?_⟩,
      hf (G 3) (G 4) ⟨_, List.mem_cons_self, formula_realize_top, _, rfl, fun j i hj => ?_⟩,
      hf (G 3) (G 5) ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, formula_realize_top, _, rfl,
        fun j i hj => ?_⟩,
      hf (G 4) (G 5) ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, formula_realize_top, _, rfl,
        fun j i hj => ?_⟩,
      hf (G 5) _ ⟨_, List.mem_cons_self, formula_realize_top, _, rfl, fun j => j.elim0⟩,
      hf (G 5) _ ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, formula_realize_top, _, rfl,
        fun j => j.elim0⟩⟩ <;>
    cases Option.some.inj hj <;> rfl
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, f (litVertex (ps i) (d i.succ)) = f trueVertex := by
    rcases gadget_forces (hlit _ _) (hlit _ _) (hlit _ _) hP with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  have hli : l i = (ps i, d i.succ) := by fin_cases i <;> rfl
  refine ⟨l i, hl i, ?_⟩
  rw [hli]
  change f (litVertex true (d i.succ)) = f trueVertex ↔ ps i = true
  cases hp : ps i
  · rw [hp] at hi
    exact iff_of_false (fun h => hneg _ (h.trans hi.symm)) Bool.false_ne_true
  · rw [hp] at hi
    exact iff_of_true hi rfl

/-- **The graph of a CNF structure is three-colorable exactly when the structure is a satisfiable
3-CNF structure.** -/
theorem colorable_coloringInterpretation_iff :
    graph.Colorable 3 (coloringInterpretation.Model M) ↔ IsThreeCNF M ∧ Satisfiable M := by
  rw [colorable_iff_edge]
  constructor
  · rintro ⟨f, hf⟩
    exact satisfies_of_colorable hf
  · rintro ⟨h3, A, hA⟩
    have hgood : ¬M ⊨ badSentence := fun h =>
      realize_badSentence.1 h ⟨h3, Satisfiable.literals_nonempty ⟨A, hA⟩⟩
    exact ⟨fun a => colorOf A a.toSigma, fun a c h => colorOf_ne_of_edge hA hgood h⟩

/-- Without bad clauses, no vertex is joined to itself. -/
private theorem not_edge_self (hgood : ¬M ⊨ badSentence) (a : coloringInterpretation.Model M) :
    ¬Edge a a := by
  obtain ⟨u, x, hx⟩ := a
  rintro ⟨τ, hτ, hg, y, hc, -⟩
  have ht : u = τ.target := congrArg Sigma.fst hc
  cases u with
  | trueV =>
    simp only [coloringEdges, List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl | rfl
    · simp at ht
    · simp at ht
    · exact hgood ((congrArg (Formula.Realize badSentence) (Subsingleton.elim _ default)).mp
        (Formula.realize_relabel.1 hg))
  | falseV =>
    simp only [coloringEdges, List.mem_cons, List.not_mem_nil, or_false] at hτ
    subst hτ
    simp at ht
  | baseV => simp [coloringEdges] at hτ
  | lit p =>
    cases p
    · simp only [coloringEdges, List.mem_cons, List.not_mem_nil, or_false] at hτ
      subst hτ
      simp at ht
    · simp only [coloringEdges, List.mem_cons, List.not_mem_nil, or_false] at hτ
      rcases hτ with rfl | rfl <;> simp at ht
  | gadget g ps =>
    fin_cases g <;> simp only [coloringEdges, List.mem_cons, List.not_mem_nil, or_false] at hτ
    · rcases hτ with rfl | rfl | rfl <;> simp at ht
    · rcases hτ with rfl | rfl <;> simp at ht
    · subst hτ
      simp at ht
    · rcases hτ with rfl | rfl <;> simp at ht
    · rcases hτ with rfl | rfl <;> simp at ht
    · rcases hτ with rfl | rfl <;> simp at ht

/-- On a 3-CNF structure without empty clauses, the graph is a simple graph. -/
theorem simpleGraph_coloringInterpretation (h3 : IsThreeCNF M)
    (hne : ∀ c : M, (literals c).Nonempty) :
    coloringInterpretation.Model M ⊨ Theory.simpleGraph := by
  have hgood : ¬M ⊨ badSentence := fun h => realize_badSentence.1 h ⟨h3, hne⟩
  rw [Theory.simpleGraph_model_iff]
  refine ⟨⟨fun a h => ?_⟩, ⟨fun a c h => ?_⟩⟩
  · rcases (relMap_adj_iff a a).1 h with h | h <;> exact not_edge_self hgood a h
  · exact (relMap_adj_iff c a).2 ((relMap_adj_iff a c).1 h).symm

end Correctness

/-! ### Structures with at most one element -/

section Subsingleton

/-- On a structure with at most one element: a single vertex, with a loop when its clause is
empty. -/
def coloringSubsingleton : Interpretation cnf Language.graph Unit where
  domain := ⊤
  rel R := match R with
    | .adj => ∼(cnf.pos.formula₂ (.var (0, ())) (.var (0, ())) ⊔
        cnf.neg.formula₂ (.var (0, ())) (.var (0, ())))

private theorem coloringSubsingleton_rel_adj :
    coloringSubsingleton.rel adj = ∼(cnf.pos.formula₂ (.var (0, ())) (.var (0, ())) ⊔
      cnf.neg.formula₂ (.var (0, ())) (.var (0, ()))) :=
  rfl

private theorem colorable_coloringSubsingleton_iff [Subsingleton M] [Nonempty M] :
    graph.Colorable 3 (coloringSubsingleton.Model M) ↔ IsThreeCNF M ∧ Satisfiable M := by
  obtain ⟨e⟩ := ‹Nonempty M›
  have hv (v : coloringSubsingleton.Model M) : v.1 () = e := Subsingleton.elim _ _
  have hadj (v w : coloringSubsingleton.Model M) :
      RelMap adj ![v, w] ↔ ¬(RelMap cnf.pos ![e, e] ∨ RelMap cnf.neg ![e, e]) := by
    fo_simp [hv]
  have hsat : Satisfiable M ↔ RelMap cnf.pos ![e, e] ∨ RelMap cnf.neg ![e, e] := by
    constructor
    · rintro ⟨A, hA⟩
      obtain ⟨x, ⟨h, -⟩ | ⟨h, -⟩⟩ := hA e
      · exact .inl (Subsingleton.elim x e ▸ h)
      · exact .inr (Subsingleton.elim x e ▸ h)
    · rintro (h | h)
      · exact ⟨fun _ => True, fun c => ⟨e, .inl ⟨Subsingleton.elim e c ▸ h, trivial⟩⟩⟩
      · exact ⟨fun _ => False, fun c => ⟨e, .inr ⟨Subsingleton.elim e c ▸ h, id⟩⟩⟩
  rw [and_iff_right isThreeCNF_of_subsingleton]
  constructor
  · rintro ⟨f, hf⟩
    by_contra h
    let v : coloringSubsingleton.Model M := ⟨fun _ => e, formula_realize_top⟩
    exact hf v v ((hadj v v).2 (fun h' => h (hsat.2 h'))) rfl
  · intro h
    exact ⟨fun _ => 0, fun v w hvw => absurd (hsat.1 h) ((hadj v w).1 hvw)⟩

/-- On a satisfiable structure with at most one element, the graph has no edge. -/
private theorem simpleGraph_coloringSubsingleton [Subsingleton M] [Nonempty M] (h : Satisfiable M) :
    coloringSubsingleton.Model M ⊨ Theory.simpleGraph := by
  obtain ⟨e⟩ := ‹Nonempty M›
  have hno (v w : coloringSubsingleton.Model M) : ¬RelMap adj ![v, w] := by
    fo_simp [Subsingleton.elim (v.1 ()) e]
    obtain ⟨A, hA⟩ := h
    obtain ⟨x, ⟨hx, -⟩ | ⟨hx, -⟩⟩ := hA e
    · exact .inl (Subsingleton.elim x e ▸ hx)
    · exact .inr (Subsingleton.elim x e ▸ hx)
  rw [Theory.simpleGraph_model_iff]
  exact ⟨⟨fun a h => hno a a h⟩, ⟨fun a c h => (hno a c h).elim⟩⟩

end Subsingleton

/-- **3SAT is order-free reducible to 3COL**, by the palette, variable and clause gadget
construction [Sipser, Chapter 7][Sipser2013], [Immerman, Chapter 7][Immerman1999]. -/
theorem reduces_ThreeSAT_ThreeColorable : Reduces ThreeSAT.{w} graph.ThreeColorable.{w} := by
  refine Reduces.of_tagged graph.isoClosed_ThreeColorable graph.copyInvariant_ThreeColorable
    coloringInterpretation coloringSubsingleton
    (fun M _ _ => colorable_coloringInterpretation_iff.symm) (fun M _ hM => ?_)
  rcases isEmpty_or_nonempty M with hM' | hM'
  · have : IsEmpty (coloringSubsingleton.Model M) := ⟨fun x => isEmptyElim (x.1 ())⟩
    exact iff_of_true ⟨isThreeCNF_of_isEmpty, satisfiable_of_isEmpty⟩
      (graph.colorable_of_isEmpty (M := coloringSubsingleton.Model M))
  · exact colorable_coloringSubsingleton_iff.symm

/-- **3SAT is order-free reducible to classical 3COL**, three-colorability of simple graphs: on
the members of 3SAT the graph of the reduction is symmetric and loopless. -/
theorem reduces_ThreeSAT_SimpleThreeColorable :
    Reduces ThreeSAT.{w} graph.SimpleThreeColorable.{w} := by
  refine Reduces.of_tagged graph.isoClosed_SimpleThreeColorable
    graph.copyInvariant_SimpleThreeColorable coloringInterpretation coloringSubsingleton
    (fun M _ _ => ⟨fun h => ⟨simpleGraph_coloringInterpretation h.1 h.2.literals_nonempty,
      colorable_coloringInterpretation_iff.2 h⟩,
      fun h => colorable_coloringInterpretation_iff.1 h.2⟩) (fun M _ hM => ?_)
  rcases isEmpty_or_nonempty M with hM' | hM'
  · have : IsEmpty (coloringSubsingleton.Model M) := ⟨fun x => isEmptyElim (x.1 ())⟩
    refine iff_of_true ⟨isThreeCNF_of_isEmpty, satisfiable_of_isEmpty⟩ ⟨?_,
      graph.colorable_of_isEmpty (M := coloringSubsingleton.Model M)⟩
    rw [Theory.simpleGraph_model_iff]
    exact ⟨⟨fun a => (this.false a).elim⟩, ⟨fun a => (this.false a).elim⟩⟩
  · exact ⟨fun h => ⟨simpleGraph_coloringSubsingleton h.2,
      colorable_coloringSubsingleton_iff.2 h⟩, fun h => colorable_coloringSubsingleton_iff.1 h.2⟩

end cnf

end Cslib.Logic.FO
