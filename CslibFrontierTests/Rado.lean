/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Rado

/-!
# Tests for the Rado graph

Concrete adjacencies and a concrete extension witness in the Rado graph; the transfer theorem
applied to the sentence "there is a triangle", which holds in the Rado graph on the vertices
`0, 1, 3`, so `G(n, 1/2)` has a triangle with probability tending to `1`; and the uniqueness,
universality and self-complementarity theorems applied to concrete graphs.
-/

namespace CslibFrontierTests.Rado

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.graph
open SimpleGraph (radoGraph radoGraph_adj)

/-! ### Concrete adjacencies -/

/-- `0` is bit `0` of `1`. -/
example : radoGraph.Adj 0 1 := by
  rw [radoGraph_adj]
  decide

/-- `2 = 0b10` has bit `0` clear, and `0` has no set bits. -/
example : ¬radoGraph.Adj 0 2 := by
  rw [radoGraph_adj]
  decide

/-- Adjacency is decidable, so small cases are checked by `decide` directly. -/
example : radoGraph.Adj 1 2 ∧ radoGraph.Adj 0 3 ∧ radoGraph.Adj 1 3 ∧ ¬radoGraph.Adj 2 3 := by
  decide

/-- `5 = 0b101` witnesses the extension of `A = {0}`, `B = {1}`: it is adjacent to `0` and not to
`1`. -/
example : radoGraph.Adj 5 0 ∧ ¬radoGraph.Adj 5 1 := by
  decide

/-! ### The transfer theorem on a concrete sentence -/

/-- The sentence "there is a triangle". -/
noncomputable def hasTriangle : Language.graph.Sentence :=
  closeEx (Fin 3)
    (rel₂ adj (0 : Fin 3) 1 ⊓ rel₂ adj (1 : Fin 3) 2 ⊓ rel₂ adj (0 : Fin 3) 2)

/-- The Rado graph has the triangle `0, 1, 3`, so `G(n, 1/2)` has a triangle with probability
tending to `1`. -/
example : Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G hasTriangle)
    Filter.atTop (nhds 1) := by
  rw [tendsto_randomGraphProb_one_iff_radoGraph]
  let := radoGraph.structure
  change Sentence.Realize ℕ hasTriangle
  rw [hasTriangle, realize_closeEx]
  refine ⟨![0, 1, 3], ?_⟩
  simp only [Formula.realize_inf, realize_rel₂]
  exact ⟨⟨(by decide : radoGraph.Adj 0 1), (by decide : radoGraph.Adj 1 3)⟩,
    (by decide : radoGraph.Adj 0 3)⟩

/-- The Rado graph satisfies every extension axiom, so no extension axiom holds almost never. -/
example (k : ℕ) (s : Fin k → Bool) :
    ¬Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G (extensionAxiom k s))
      Filter.atTop (nhds 0) := by
  rw [tendsto_randomGraphProb_zero_iff_radoGraph, not_not]
  exact satisfies_extensionAxiom_radoGraph k s

/-! ### Uniqueness, universality and self-complementarity -/

/-- The infinite complete graph is an induced subgraph of the Rado graph. -/
example : Nonempty ((⊤ : SimpleGraph ℕ) ↪g radoGraph) :=
  nonempty_embedding_radoGraph ⊤

/-- Every finite graph, for example the empty graph on `Fin 5`, is an induced subgraph of the Rado
graph. -/
example : Nonempty ((⊥ : SimpleGraph (Fin 5)) ↪g radoGraph) :=
  nonempty_embedding_radoGraph ⊥

/-- The complement of the Rado graph is again the Rado graph. -/
example : Nonempty (radoGraphᶜ ≃g radoGraph) :=
  nonempty_compl_iso_radoGraph

/-- The uniqueness theorem applies to the complement of the Rado graph through the finite-set form
of the extension property. -/
example : Nonempty (radoGraphᶜ ≃g radoGraph) := by
  refine nonempty_iso_radoGraph _ ((satisfies_extensionAxiom_iff_exists_adj _).2 ?_)
  intro A B hAB
  obtain ⟨z, hzA, hzB, hA, hB⟩ := SimpleGraph.radoGraph_exists_adj hAB.symm
  refine ⟨z, hzB, hzA, fun a ha => ?_, fun b hb h => ?_⟩
  · exact (SimpleGraph.compl_adj _ _ _).2 ⟨fun h => hzB (h ▸ ha), hB a ha⟩
  · exact ((SimpleGraph.compl_adj _ _ _).1 h).2 (hA b hb)

end CslibFrontierTests.Rado
