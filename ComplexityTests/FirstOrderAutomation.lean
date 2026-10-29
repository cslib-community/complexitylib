/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.FirstOrder.Problems.SizedGraph
import Complexity.Logics.FirstOrder.Projection.Graph
import Complexity.Logics.FirstOrder.Subformula
import Complexity.Tactic.FirstOrder

/-!
# Tests for first-order automation

Exercise `fo_qf`, `fo_simp` and `fo_reduction` on formulas, interpretations, projections and
reductions, including their documented failure modes: quantified formulas are not
quantifier-free, bare relation constructors block `simp`, and a domain formula that may fail
leaves the semantic goal about the interpreted structure. The classes of independent sets and
cliques are shown nonvacuous and distinct on a two-vertex structure. The closure properties of
`subformulas` are checked on the sentence saying that a graph has no loops.
-/

namespace ComplexityTests.FirstOrderAutomation

open FirstOrder Language Structure CategoryTheory Cslib.Logic Cslib.Logic.FO sizedGraph

/-! ### `fo_qf` -/

section QF

variable {L : Language} (R : L.Relations 2) (S : L.Relations 1)

example : (∼(rel₂ R (0 : Fin 2) 1) ⊔ varEq 0 1 ⇔ rel₁ S 0 ⊓ ⊤ : L.Formula (Fin 2)).IsQF := by
  fo_qf

example :
    (Formula.iInf fun i : Fin 3 => (rel₂ R i 0).relabel Fin.succ : L.Formula (Fin 4)).IsQF := by
  fo_qf

example : (le R (0 : Fin 2) 1 ⟹ lt R 1 0 : L.Formula (Fin 2)).IsQF := by
  fo_qf

example {φ : L.Formula (Fin 1)} (hφ : φ.IsQF) : (atVar φ (2 : Fin 3) ⊓ ∼(atVar φ 0)).IsQF := by
  fo_qf

example {L' : Language} [L'.IsRelational] {I : Interpretation L L' (Fin 2)} (hI : I.IsQF)
    {φ : L'.Formula (Fin 3)} (hφ : φ.IsQF) :
    (I.onFormula φ ⊓ I.domain.relabel fun i => (0, i)).IsQF := by
  fo_qf

example [L.IsRelational] : ((Interpretation.id L).comp (Interpretation.id L)).IsQF := by
  fo_qf

example {L' : Language} {I : Interpretation L L' (Fin 2)} (hI : I.IsQF) {n : ℕ}
    (R' : L'.Relations n) : (I.rel R' ⟹ ∼(I.rel R')).IsQF := by
  fo_qf

example {N N' L' : Language} {I : Projection N N' L L' (Fin 2)} (hI : I.IsQF) {n : ℕ}
    (R' : L'.Relations n) : ((I.rel R').not.relabel id).IsQF ∧ I.numeric.IsQF := by
  exact ⟨by fo_qf, by fo_qf⟩

/-- Without a hypothesis, an abstract interpretation is not known to be quantifier-free. -/
example {L' : Language} (_I : Interpretation L L' (Fin 2)) : True := by
  fail_if_success have : _I.IsQF := by fo_qf
  trivial

/-- A quantified formula is not quantifier-free, and `fo_qf` fails on it. -/
example : ¬ (∀' R.boundedFormula₂ &0 &0 : L.Sentence).IsQF := by
  fail_if_success have : (∀' R.boundedFormula₂ &0 &0 : L.Sentence).IsQF := by fo_qf
  exact BoundedFormula.not_all_isQF _

end QF

/-- Concrete interpretations are split by relation symbol and unfolded, and closure under
isomorphism is registered in the same rule set. -/
example (N : Language) :
    complementEdges.IsQF ∧
    (complementEdges.comp complementSize).IsQF ∧
    (Projection.offDiagonalComplement N).toInterpretation.IsQF ∧
    ((Projection.offDiagonalComplement Language.empty).comp
      (Projection.offDiagonalComplement Language.empty)).IsQF ∧
    IsoClosed Clique.{0} :=
  ⟨by fo_qf, by fo_qf, by fo_qf, by fo_qf, by fo_iso_closed⟩

/-- Restrict a structure to the elements of its size relation. -/
def restrictToSize : Interpretation sizedGraph sizedGraph Unit where
  domain := rel₁ sizedGraph.size ()
  rel
    | .adj => rel₂ sizedGraph.adj (0, ()) (1, ())
    | .size => rel₁ sizedGraph.size (0, ())

/-- A two-dimensional interpretation on ordered pairs of vertices. -/
def pairs : Interpretation sizedGraph sizedGraph (Fin 2) where
  domain := ⊤
  rel
    | .adj => rel₂ sizedGraph.adj (0, 0) (1, 0) ⊓ rel₂ sizedGraph.adj (0, 1) (1, 1)
    | .size => rel₁ sizedGraph.size (0, 0) ⊓ rel₁ sizedGraph.size (0, 1)

/-! ### `fo_simp` -/

section Simp

variable {M : Type*} [sizedGraph.Structure M]

example (x : Fin 2 → M) :
    (∼(rel₂ sizedGraph.adj 0 1) ⊓ varEq 0 1 ⊔ rel₁ sizedGraph.size 1 :
      sizedGraph.Formula (Fin 2)).Realize x ↔
      ¬ RelMap sizedGraph.adj ![x 0, x 1] ∧ x 0 = x 1 ∨ RelMap sizedGraph.size ![x 1] := by
  fo_simp

example (x y : M) :
    (complementEdges.unitStructure M).RelMap sizedGraph.adj ![x, y] ↔
      ¬ RelMap sizedGraph.adj ![x, y] ∧ x ≠ y := by
  fo_simp

example (x : complementSize.Model M) :
    RelMap sizedGraph.size ![x] ↔ ¬ RelMap sizedGraph.size ![x.1 ()] := by
  fo_simp

example (x y : M) (h : (complementSize.unitStructure M).RelMap sizedGraph.adj ![x, y]) :
    RelMap sizedGraph.adj ![x, y] := by
  fo_simp at h
  exact h

/-- The relations of a composite are those of the iterated interpretation. -/
example (x y : (complementEdges.comp complementSize).Model M) :
    RelMap sizedGraph.adj ![x, y] ↔
      ¬ RelMap sizedGraph.adj ![x.1 ((), ()), y.1 ((), ())] ∧ x.1 ((), ()) ≠ y.1 ((), ()) := by
  fo_simp

/-- The domain and relation formulas of a composite interpretation simplify directly. -/
example (x : Unit × Unit → M) :
    (complementEdges.comp complementSize).domain.Realize x := by
  fo_simp

example (x : Fin 2 × (Unit × Unit) → M) :
    ((complementEdges.comp complementSize).rel sizedGraph.adj).Realize x ↔
      ¬ RelMap sizedGraph.adj ![x (0, ((), ())), x (1, ((), ()))] ∧
        x (0, ((), ())) ≠ x (1, ((), ())) := by
  fo_simp

example (x y : Unit × Unit → M) :
    ((complementEdges.comp complementSize).tupleStructure M).RelMap sizedGraph.adj ![x, y] ↔
      ¬ RelMap sizedGraph.adj ![x ((), ()), y ((), ())] ∧ x ((), ()) ≠ y ((), ()) := by
  fo_simp

/-- A composite with a restricted inner domain simplifies to the inner domain and relation
propositions. -/
example (x : Unit × Unit → M) :
    (complementEdges.comp restrictToSize).domain.Realize x ↔
      RelMap sizedGraph.size ![x ((), ())] := by
  fo_simp

example (x y : (complementEdges.comp restrictToSize).Model M) :
    RelMap sizedGraph.adj ![x, y] ↔
      ¬ RelMap sizedGraph.adj ![x.1 ((), ()), y.1 ((), ())] ∧ x.1 ((), ()) ≠ y.1 ((), ()) := by
  fo_simp

/-- Higher-dimensional interpretations simplify on the full tuple domain. -/
example (x y : Fin 2 → M) :
    (pairs.tupleStructure M).RelMap sizedGraph.adj ![x, y] ↔
      RelMap sizedGraph.adj ![x 0, y 0] ∧ RelMap sizedGraph.adj ![x 1, y 1] := by
  fo_simp

example (x : Fin 2 → M) :
    (pairs.tupleStructure M).RelMap sizedGraph.size ![x] ↔
      RelMap sizedGraph.size ![x 0] ∧ RelMap sizedGraph.size ![x 1] := by
  fo_simp

/-- The input relations of a composite projection simplify on formulas, numeric models and full
tuple domains. -/
example (N : Language) [N.IsRelational] {G : Type*} [N.Structure G] [Language.graph.Structure G]
    (x : Fin 2 × (Unit × Unit) → G) :
    (((Projection.offDiagonalComplement N).comp (Projection.offDiagonalComplement N)).rel
      Language.adj).toFormula.Realize x ↔
      x (0, ((), ())) ≠ x (1, ((), ())) ∧
        ¬(x (0, ((), ())) ≠ x (1, ((), ())) ∧
          ¬RelMap Language.adj (fun i => x (i, ((), ())))) := by
  fo_simp

example (N : Language) [N.IsRelational] {G : Type*} [N.Structure G] [Language.graph.Structure G]
    (x y : ((Projection.offDiagonalComplement N).comp
      (Projection.offDiagonalComplement N)).numeric.Model G) :
    (((Projection.offDiagonalComplement N).comp
      (Projection.offDiagonalComplement N)).inputStructure G).RelMap Language.adj ![x, y] ↔
      x.1 ((), ()) ≠ y.1 ((), ()) ∧
        ¬(x.1 ((), ()) ≠ y.1 ((), ()) ∧
          ¬RelMap Language.adj (fun i => (![x, y] i).1 ((), ()))) := by
  fo_simp

example (N : Language) [N.IsRelational] {G : Type*} [N.Structure G] [Language.graph.Structure G]
    (x y : Unit × Unit → G) :
    (((Projection.offDiagonalComplement N).comp
      (Projection.offDiagonalComplement N)).tupleInputStructure G).RelMap Language.adj ![x, y] ↔
      x ((), ()) ≠ y ((), ()) ∧
        ¬(x ((), ()) ≠ y ((), ()) ∧
          ¬RelMap Language.adj (fun i => (![x, y] i) ((), ()))) := by
  fo_simp

/-- A bare constructor inside a formula is well typed only after unfolding the language, and
`fo_simp` makes no progress on it; the abbreviation `sizedGraph.adj` is rewritten. -/
example (x : Fin 2 → M) :
    (rel₂ (L := sizedGraph) .adj (0 : Fin 2) 1).Realize x ↔
      RelMap sizedGraph.adj ![x 0, x 1] := by
  fail_if_success fo_simp
  exact realize_rel₂ x _ 0 1

end Simp

/-! ### `fo_reduction` -/

/-- A first-order reduction which is not required to be quantifier-free. -/
example : Reduces IndependentSet.{0} Clique.{0} := by
  fo_reduction complementEdges [mem_IndependentSet, mem_Clique]
  exact fun _ _ => exists_congr fun _ => and_congr_right fun _ =>
    ⟨fun h _ hx _ hy hxy => ⟨h hx hy hxy, hxy⟩, fun h _ hx _ hy hxy => (h hx hy hxy).1⟩

/-- A reduction through a composite of two concrete interpretations, proved directly by
`fo_reduction` via `QFReduces.of_tupleStructure`. -/
example : QFReduces Clique.{0} VertexCover.{0} := by
  fo_reduction (complementSize.comp complementEdges) [mem_Clique, mem_VertexCover]
  intro M _
  let e : (Unit × Unit → M) ≃ M :=
    { toFun := fun f => f ((), ())
      invFun := fun x _ => x
      left_inv := fun f => funext fun ⟨(), ()⟩ => rfl
      right_inv := fun _ => rfl }
  have hcard (s : Set (Unit × Unit → M)) : s.ncard = (e '' s).ncard :=
    (Set.ncard_image_of_injective s e.injective).symm
  have hsize : {x : Unit × Unit → M | ¬RelMap sizedGraph.size ![x ((), ())]}.ncard =
      ({x : M | RelMap sizedGraph.size ![x]}ᶜ : Set M).ncard := by
    rw [hcard]
    congr 1
    ext x
    exact ⟨fun ⟨f, hf, hfx⟩ => hfx ▸ hf, fun hx => ⟨e.symm x, hx, rfl⟩⟩
  refine ⟨fun ⟨s, hs, hcl⟩ => ?_, fun ⟨t, ht, hcov⟩ => ?_⟩
  · refine ⟨e.symm '' sᶜ, ?_, fun x y hxy ⟨hnadj, _⟩ => ?_⟩
    · rw [Set.ncard_image_of_injective _ e.symm.injective, hsize]
      have := Set.ncard_add_ncard_compl s
      have := Set.ncard_add_ncard_compl {x : M | RelMap sizedGraph.size ![x]}
      omega
    · by_contra hc
      simp only [Set.mem_image, Equiv.symm_apply_eq, exists_eq_right, Set.mem_compl_iff,
        not_or, not_not] at hc
      exact hnadj (hcl hc.1 hc.2 (e.injective.ne hxy))
  · refine ⟨(e '' t)ᶜ, ?_, fun x hx y hy hxy => ?_⟩
    · have ht' : (e '' t).ncard = ({x : M | RelMap sizedGraph.size ![x]}ᶜ : Set M).ncard := by
        rw [← hcard, ht, hsize]
      have := Set.ncard_add_ncard_compl (e '' t)
      have := Set.ncard_add_ncard_compl {x : M | RelMap sizedGraph.size ![x]}
      omega
    · by_contra hnadj
      rcases hcov (e.symm x) (e.symm y) (e.symm.injective.ne hxy) ⟨hnadj, hxy⟩ with h | h
      · exact hx ⟨e.symm x, h, rfl⟩
      · exact hy ⟨e.symm y, h, rfl⟩

/-- All structures of the vocabulary `sizedGraph`. -/
abbrev allStructures : Set (Bundled.{0} sizedGraph.Structure) := Set.univ

/-- When the domain formula need not hold, the semantic goal is about the interpreted structure,
even though the target class is closed under isomorphism. -/
example (_hK : IsoClosed allStructures) : QFReduces allStructures allStructures := by
  fo_reduction restrictToSize
  guard_target =ₛ ∀ (M : Bundled.{0} sizedGraph.Structure) [Finite M], M ∈ allStructures ↔
    Bundled.of (c := sizedGraph.Structure) (restrictToSize.Model M) ∈ allStructures
  exact fun _ _ => Iff.rfl

/-- A composite with a restricted inner domain likewise leaves the semantic goal on `Model`. -/
example (_hK : IsoClosed allStructures) : QFReduces allStructures allStructures := by
  fo_reduction (complementEdges.comp restrictToSize)
  guard_target =ₛ ∀ (M : Bundled.{0} sizedGraph.Structure) [Finite M], M ∈ allStructures ↔
    Bundled.of (c := sizedGraph.Structure)
      ((complementEdges.comp restrictToSize).Model M) ∈ allStructures
  exact fun _ _ => Iff.rfl

/-- A two-dimensional interpretation whose domain formula always holds reduces the semantic goal to
the full tuple domain `Fin 2 → M`. -/
example (_hK : IsoClosed allStructures) : QFReduces allStructures allStructures := by
  fo_reduction pairs
  guard_target =ₛ ∀ (M : Bundled.{0} sizedGraph.Structure) [Finite M], M ∈ allStructures ↔
    (⟨Fin 2 → M, pairs.tupleStructure M⟩ : Bundled.{0} sizedGraph.Structure) ∈ allStructures
  exact fun _ _ => Iff.rfl

/-- An interpretation with a quantified relation: the edges of the complete graph on the
vertices with a neighbour. -/
noncomputable def hasNeighbour : Interpretation sizedGraph sizedGraph Unit where
  domain := ⊤
  rel
    | .adj => Formula.iExs (Fin 1) (rel₂ sizedGraph.adj (.inl (0, ())) (.inr 0))
    | .size => rel₁ sizedGraph.size (0, ())

/-- A quantified interpretation gives a first-order reduction; for a quantifier-free reduction
its quantifier-freeness is left open, both alone and in a composite. -/
example (_hK : IsoClosed allStructures) : Reduces allStructures allStructures := by
  fail_if_success
    have : QFReduces allStructures allStructures := by
      fo_reduction hasNeighbour [allStructures, Set.mem_univ]
  fail_if_success
    have : QFReduces allStructures allStructures := by
      fo_reduction (hasNeighbour.comp complementEdges) [allStructures, Set.mem_univ]
  fo_reduction (hasNeighbour.comp complementEdges) [allStructures, Set.mem_univ]

/-- Errors in the simp lemmas passed to `fo_reduction` are reported. -/
example : QFReduces IndependentSet.{0} Clique.{0} := by
  fail_if_success fo_reduction complementEdges [mem_IndependentSetTYPO]
  exact qfReduces_IndependentSet_Clique

/--
error: fo_reduction: expected `FO.Reduces K K'` or `FO.QFReduces K K'` through this interpretation
⊢ IsoClosed Clique
-/
#guard_msgs in
example : IsoClosed Clique.{0} := by
  fo_reduction complementEdges

/-! ### Nonvacuity of the classes -/

/-- Two vertices, adjacent exactly when `edge` holds, and in the size relation exactly when
`inSize` holds. -/
@[instance_reducible]
def twoVertices (edge inSize : Prop) : sizedGraph.Structure (Fin 2) where
  RelMap
    | .adj, x => edge ∧ x 0 ≠ x 1
    | .size, _ => inSize

private theorem eq_univ_of_ncard_eq {s : Set (Fin 2)}
    (h : s.ncard = (Set.univ : Set (Fin 2)).ncard) : s = Set.univ :=
  Set.eq_of_subset_of_ncard_le (Set.subset_univ s) h.ge

/-- Without the edge, both vertices form an independent set but not a clique. -/
example : Bundled.mk (Fin 2) (twoVertices False True) ∈ IndependentSet.{0} ∧
    Bundled.mk (Fin 2) (twoVertices False True) ∉ Clique.{0} := by
  let _ := twoVertices False True
  refine ⟨⟨Set.univ, rfl, fun _ _ _ _ _ h => h.1⟩, fun ⟨s, hs, hcl⟩ => ?_⟩
  rw [eq_univ_of_ncard_eq hs] at hcl
  exact (hcl (Set.mem_univ 0) (Set.mem_univ 1) (by decide)).1

/-- With the edge, both vertices form a clique but not an independent set. -/
example : Bundled.mk (Fin 2) (twoVertices True True) ∈ Clique.{0} ∧
    Bundled.mk (Fin 2) (twoVertices True True) ∉ IndependentSet.{0} := by
  let _ := twoVertices True True
  refine ⟨⟨Set.univ, rfl, fun _ _ _ _ h => ⟨trivial, by simpa using h⟩⟩, fun ⟨s, hs, hind⟩ => ?_⟩
  rw [eq_univ_of_ncard_eq hs] at hind
  exact hind (Set.mem_univ 0) (Set.mem_univ 1) (by decide) ⟨trivial, by decide⟩

/-- With an empty size relation, the empty set covers the graph without edges but not the edge. -/
example : Bundled.mk (Fin 2) (twoVertices False False) ∈ VertexCover.{0} ∧
    Bundled.mk (Fin 2) (twoVertices True False) ∉ VertexCover.{0} := by
  refine ⟨⟨∅, rfl, fun _ _ _ h => h.1.elim⟩, fun ⟨s, hs, hcov⟩ => ?_⟩
  rw [(Set.ncard_eq_zero (Set.toFinite s)).1 (hs.trans (Set.ncard_empty _))] at hcov
  simpa using hcov 0 1 (by decide) ⟨trivial, by decide⟩

/-! ### Axioms -/

/--
info: 'Cslib.Logic.FO.Interpretation.tupleModelEquiv' depends on axioms: [Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Interpretation.tupleModelEquiv

/--
info: 'Cslib.Logic.FO.Projection.tupleModelEquiv' depends on axioms: [Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Projection.tupleModelEquiv


/-! ### Subformulas -/

section Subformulas

/-- `∀ x, ¬ x ~ x`: a graph has no loops. -/
private def noLoops : Language.graph.Sentence := ∀' ∼(adj.boundedFormula₂ &0 &0)

/-- Finiteness of `subformulas noLoops`, and membership of the body of the quantifier, its atom,
and `⊥`. -/
example :
    (subformulas noLoops).Finite ∧
    ⟨1, ∼(adj.boundedFormula₂ &0 &0)⟩ ∈ subformulas noLoops ∧
    ⟨1, adj.boundedFormula₂ &0 &0⟩ ∈ subformulas noLoops ∧
    ⟨1, ⊥⟩ ∈ subformulas noLoops :=
  ⟨finite_subformulas _,
    mem_subformulas_of_all (self_mem_subformulas _),
    mem_subformulas_of_imp_left (mem_subformulas_of_all (self_mem_subformulas _)),
    mem_subformulas_of_imp_right (mem_subformulas_of_all (self_mem_subformulas _))⟩

end Subformulas

end ComplexityTests.FirstOrderAutomation
