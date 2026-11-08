/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.FirstOrder.ZeroOneLaw

/-!
# Tests for the 0-1 law for first-order logic on graphs

Exact probabilities in small random graphs; an extension axiom holding in the triangle and
failing in the empty graph on two vertices; every finite graph violates some extension axiom, so
the limit statement `tendsto_randomGraphProb_extensionAxiom` is not a statement about every
graph; the transfer theorem applied to the sentence "there are no edges", which the theory of the
random graph refutes, so its probability tends to `0`; and non-definability of an odd number of
vertices, derived from the even case.
-/

namespace ComplexityTests.ZeroOneLaw

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.graph

/-! ### Exact probabilities -/

/-- In `G(2, 1/2)` the only potential edge is present with probability exactly `1/2`. -/
example : randomGraphProb 2 (fun G => G.Adj 0 1) = 1 / 2 :=
  randomGraphProb_adj (by decide)

/-- In `G(3, 1/2)` the number of edges is even with probability exactly `1/2`. -/
example : randomGraphProb 3 SimpleGraph.EvenEdges = 1 / 2 :=
  randomGraphProb_evenEdges (by norm_num)

/-! ### Extension axioms on concrete graphs -/

/-- The triangle satisfies the extension axiom "every vertex has a neighbour". -/
example : Satisfies (⊤ : SimpleGraph (Fin 3)) (extensionAxiom 1 fun _ => true) := by
  rw [satisfies_extensionAxiom_iff]
  intro x _
  refine ⟨x 0 + 1, fun i => ?_, fun i => ?_⟩ <;> obtain rfl := Subsingleton.elim i 0
  · simp
  · simp

/-- The empty graph on two vertices violates the extension axiom "every vertex has a
neighbour". -/
example : ¬Satisfies (⊥ : SimpleGraph (Fin 2)) (extensionAxiom 1 fun _ => true) := by
  rw [satisfies_extensionAxiom_iff]
  intro h
  obtain ⟨z, -, hz⟩ := h (fun _ => 0) (fun i j _ => Subsingleton.elim i j)
  exact (SimpleGraph.bot_adj _ _).1 ((hz 0).2 rfl)

/-- Every graph on `n` vertices violates the `n`-variable extension axiom: no vertex lies outside
the tuple listing all vertices. -/
example (n : ℕ) (G : SimpleGraph (Fin n)) : ¬Satisfies G (extensionAxiom n fun _ => false) := by
  rw [satisfies_extensionAxiom_iff]
  intro h
  obtain ⟨z, hz, -⟩ := h id Function.injective_id
  exact hz z rfl

/-! ### The transfer theorem on a concrete sentence -/

/-- The sentence "there are no edges". -/
noncomputable def noEdges : Language.graph.Sentence :=
  closeAll (Fin 2) ∼(rel₂ adj (0 : Fin 2) 1)

/-- The theory of the random graph refutes "there are no edges", so the probability that
`G(n, 1/2)` has no edges tends to `0`. -/
example : Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G noEdges)
    Filter.atTop (nhds 0) := by
  rw [tendsto_randomGraphProb_zero_iff, Theory.models_sentence_iff]
  intro M
  have hM := model_randomGraphTheory_iff.1 M.is_model
  have : Infinite M := infinite_of_hasExtension hM.2
  obtain ⟨a⟩ := Infinite.nonempty M
  obtain ⟨z, -, hz⟩ := hM.2 1 (fun _ => true) (fun _ => a) (fun i j _ => Subsingleton.elim i j)
  rw [Sentence.realize_not, noEdges, realize_closeAll]
  intro h
  have := h ![z, a]
  simp only [Formula.realize_not, realize_rel₂] at this
  exact this ((hz 0).2 rfl)

/-! ### Non-definability -/

/-- An odd number of vertices is not first-order definable either: the negation of a defining
sentence would define an even number of vertices. -/
example : ¬∃ φ : Language.graph.Sentence, ∀ᶠ n in Filter.atTop,
    ∀ G : SimpleGraph (Fin n), Satisfies G φ ↔ ¬Even n := by
  rintro ⟨φ, hφ⟩
  refine not_exists_sentence_even_card ⟨φ.not, hφ.mono fun n hn G => ?_⟩
  rw [satisfies_not, hn G, not_not]

end ComplexityTests.ZeroOneLaw
