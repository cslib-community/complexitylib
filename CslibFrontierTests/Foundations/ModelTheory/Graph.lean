/-
Copyright (c) 2026 Samuel Schlesinger, Rishik Pavani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Rishik Pavani
-/

import CslibFrontier.Foundations.ModelTheory.Graph
import Mathlib.Data.Fin.Rev

/-!
# Tests for graph maps as maps of `Language.graph`-structures

The path `0 — 1 — 2` on `Fin 3` is isomorphic to itself by reversal `i ↦ 2 - i`. The formula
"`x` is adjacent to some vertex", with one free variable `x`, transfers along the reversal, and the
graph isomorphism survives the round trip through `Language.graph`-equivalences.
-/

namespace CslibFrontierTests.ModelTheoryGraph

open FirstOrder Language

/-- The path `0 — 1 — 2`. -/
def path3 : SimpleGraph (Fin 3) := SimpleGraph.fromRel fun i j => i.val + 1 = j.val

instance : DecidableRel path3.Adj := fun i j => by
  unfold path3; infer_instance

/-- Reversal `i ↦ 2 - i` is an automorphism of the path. -/
def reverse : path3 ≃g path3 where
  toEquiv := Fin.revPerm
  map_rel_iff' {a b} := by revert a b; decide

/-- "`x` is adjacent to some vertex": the free variable `x` is `Sum.inl ()`, the bound one is
`&0`. -/
def hasNeighbour : Language.graph.Formula Unit :=
  ∃' adj.boundedFormula₂ (Term.var (Sum.inl ())) (&0)

/-- Realizing `hasNeighbour` at `v` means `v` has a neighbour. -/
theorem realize_hasNeighbour {V : Type*} (G : SimpleGraph V) (v : Unit → V) :
    (letI := G.structure; hasNeighbour.Realize v) ↔ ∃ w, G.Adj (v ()) w := by
  let := G.structure
  simp only [Formula.Realize, hasNeighbour, BoundedFormula.realize_ex,
    BoundedFormula.realize_rel₂, Term.realize_var, Sum.elim_inl]
  rfl

/-- The free-variable formula transfers along the explicit isomorphism: the image `2` of the
endpoint `0` has a neighbour because `0` does. -/
example : (letI := path3.structure; hasNeighbour.Realize (reverse ∘ fun _ => (0 : Fin 3))) := by
  rw [reverse.realize_formula_iff, realize_hasNeighbour]
  exact ⟨1, by decide⟩

/-- The reversal sends the assignment `x ↦ 0` to `x ↦ 2`. -/
example : (reverse ∘ fun _ : Unit => (0 : Fin 3)) = fun _ => 2 := rfl

/-- Round trip through `Language.graph`-equivalences. -/
example : SimpleGraph.Iso.ofLanguageEquiv reverse.toLanguageEquiv = reverse := by simp

/-- The language equivalence acts as the isomorphism. -/
example : (letI := path3.structure; reverse.toLanguageEquiv 0) = 2 := by
  simp only [SimpleGraph.Iso.coe_toLanguageEquiv]
  rfl

/-- Round trip through `Language.graph`-embeddings. -/
example : SimpleGraph.Embedding.ofLanguageEmbedding reverse.toEmbedding.toLanguageEmbedding =
    reverse.toEmbedding := by
  simp

end CslibFrontierTests.ModelTheoryGraph
