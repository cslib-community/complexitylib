/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.AssignmentTester
public import CslibFrontier.Computability.PCP.GenericComposition
import Mathlib.Tactic.Linarith

/-!
# Composition: alphabet reduction

The powering step of Dinur's proof of the PCP theorem amplifies the value of a constraint graph at
the cost of an enormous, though constant, alphabet. **Composition** [Dinur, Section 3.3][Dinur2005]
brings the alphabet back to a fixed one, losing a constant factor of the value that does not depend
on the alphabet being reduced: that independence is what lets powering win.

Composition replaces every edge `e` of a constraint graph `G` over a finite alphabet `α` by the
Hadamard assignment tester of its constraint (`PCP.hadamardTester`), on the labels in `α`
themselves. The testers of all the edges share the tables of the vertices: the composed proof
holds, for every vertex, a table that is supposedly the long code of its label, and for every edge,
the linear and quadratic tables of its tester. The composed test
(`ConstraintGraph.composeTest`) runs the tester of a uniformly random edge on the tables of the ends
of that edge and on its own tables, and the composed constraint graph `G.compose` is the constraint
graph of that test (`LocalTest.toConstraintGraph`). Its alphabet `Bool × (HadamardTester.Query →
Bool)` has `2 ^ 18` symbols, whatever `α` is.

A labelling satisfying `G` gives the honest composed proof, which the composed test passes on every
random string (`ConstraintGraph.satisfiable_compose`). Conversely, a labelling of the composed graph
is decoded to a labelling of `G` by reading at every vertex the label whose long code is within
relative distance `1/4` of its table (`ConstraintGraph.decodeLabelling`). If the decoded labelling
violates an edge of `G`, the tester of that edge rejects with probability at least `1/28`: otherwise
its soundness would give labels satisfying the edge, with long codes within `1/4` of the tables of
its ends, which the decoding must return. So the composed test rejects with probability at least
`1/28` times the proportion of the edges of `G` that the decoded labelling violates, and since it
makes `17` queries, the composed graph has value at least `1/476` times that of `G`
(`ConstraintGraph.le_unsatVal_compose`). The number of edges is multiplied by a constant depending
only on `|α|` (`ConstraintGraph.card_edges_compose`).

## Main definitions

* `Cslib.PCP.ConstraintGraph.decodeLabel`: the label whose long code is close to a table.
* `Cslib.PCP.ConstraintGraph.composeTest`: the composed test of a constraint graph.
* `Cslib.PCP.ConstraintGraph.compose`: the composed constraint graph.
* `Cslib.PCP.ConstraintGraph.composeProof`: the honest composed proof of a labelling.
* `Cslib.PCP.ConstraintGraph.decodeLabelling`: the labelling decoded from a composed proof.

## Main results

* `Cslib.PCP.ConstraintGraph.satisfiable_compose`, `Cslib.PCP.ConstraintGraph.unsatVal_compose_le`:
  completeness of composition.
* `Cslib.PCP.ConstraintGraph.one_div_le_one_sub_acceptProb_of_not_satisfies`: the tester of an edge
  violated by the decoded labelling rejects.
* `Cslib.PCP.ConstraintGraph.unsatFrac_decodeLabelling_le`,
  `Cslib.PCP.ConstraintGraph.le_unsatVal_compose`: soundness of composition.
* `Cslib.PCP.ConstraintGraph.satisfiable_compose_iff`: composition preserves satisfiability.
* `Cslib.PCP.ConstraintGraph.card_edges_compose`, `Cslib.PCP.ConstraintGraph.card_vertices_compose`,
  `Cslib.PCP.ConstraintGraph.card_alphabet_compose`: the size of the composed graph.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Cslib.PCP

open BitString HadamardTester

namespace HadamardTester

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The Hadamard tester as data for binary-constraint composition. Its distance-soundness theorem
remains separate; composition needs only rejection on a violated decoded constraint. -/
noncomputable def assignmentTester :
    AssignmentTester α (α → Bool) (LinPos α ⊕ QuadPos α) (Rand α) Query Bool where
  test := hadamardTester
  encode := longCode
  auxiliary _ σ p := honestProof σ (.inr p)

/-- The Hadamard construction has perfect completeness in the generic composition interface. -/
theorem isComplete_assignmentTester : (assignmentTester (α := α)).IsComplete :=
  fun hσ ω => passes_honestProof hσ ω

end HadamardTester

namespace ConstraintGraph

variable {V E α : Type*}

/-- The positions of a composed proof, for vertices `V`, edges `E` and labels in `α`: the bit
`inl (v, r)` of the table of the vertex `v` at `r`, and the bit `inr (e, y)` of the tables of the
tester of the edge `e` at the position `y` of its linear or quadratic table. -/
abbrev ComposePos (V E α : Type*) : Type _ :=
  AssignmentTester.ComposePos V E (α → Bool) (HadamardTester.LinPos α ⊕ HadamardTester.QuadPos α)

/-- The positions of a composed proof are finitely many. -/
instance [Fintype V] [Fintype E] [Fintype α] [DecidableEq α] : Fintype (ComposePos V E α) :=
  inferInstanceAs (Fintype (_ ⊕ _))

/-! ### Decoding the long code -/

section Decode

variable [Fintype α] [DecidableEq α] [Nonempty α]

open Classical in
/-- The label decoded from a table `T`: the label whose long code is within relative distance `1/4`
of `T`, if there is one (it is then unique, `decodeLabel_eq`), and an arbitrary label otherwise. -/
noncomputable def decodeLabel (T : (α → Bool) → Bool) : α :=
  if h : ∃ a : α, (hammingDist T (longCode a) : ℝ) / 2 ^ Fintype.card α < 1 / 4
  then h.choose else Classical.arbitrary α

/-- **Unique decoding**: a table within relative distance `1/4` of the long code of a label decodes
to that label. -/
private theorem decodeLabel_eq {T : (α → Bool) → Bool} {a : α}
    (h : (hammingDist T (longCode a) : ℝ) / 2 ^ Fintype.card α < 1 / 4) :
    decodeLabel T = a := by
  have hex : ∃ a : α, (hammingDist T (longCode a) : ℝ) / 2 ^ Fintype.card α < 1 / 4 := ⟨a, h⟩
  rw [decodeLabel, dite_eq_left hex]
  exact eq_of_hammingDist_longCode_lt hex.choose_spec h

end Decode

end ConstraintGraph

namespace HadamardTester

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- A violated constraint on the uniquely decoded input tables is rejected with probability at
least `1/28`. This is the soundness contract required by generic composition. -/
theorem sound_assignmentTester :
    (assignmentTester (α := α)).Sound ConstraintGraph.decodeLabel (1 / 28) := by
  intro C π h
  by_contra! hρ
  change 1 - (hadamardTester C).acceptProb π < 1 / 28 at hρ
  obtain ⟨τ, hτ, hd⟩ := exists_inputDist_le_of_le_acceptProb (C := C) (π := π) hρ (by linarith)
  have hdec (b : Fin 2) : ConstraintGraph.decodeLabel (fun r => π (.inl (b, r))) = τ b :=
    ConstraintGraph.decodeLabel_eq
      ((hammingDist_inputTable_div_le π τ b).trans_lt (by linarith))
  exact h (by rw [hdec, hdec]; exact hτ)

end HadamardTester

namespace ConstraintGraph

variable {V E α : Type*} (G : ConstraintGraph V E α)

/-! ### The composed constraint graph -/

variable [Fintype α] [DecidableEq α]

/-- Where the tester of the edge `e` reads in a composed proof: the table of its end `b` is the
table of the vertex `G.ends e b`, and its linear and quadratic tables are those of `e`. -/
def testerPos (e : E) : Pos α → ComposePos V E α :=
  AssignmentTester.testerPos G e

/-- The **composed test** [Dinur, Section 3.3][Dinur2005]: on a uniformly random edge `e`, run the
Hadamard assignment tester of the constraint of `e` on the tables of the ends of `e` and the tables
of its tester. -/
noncomputable def composeTest : LocalTest (ComposePos V E α) (E × Rand α) Query Bool :=
  LocalTest.mix fun e ↦ (hadamardTester (G.rel e)).map (G.testerPos e)

/-- The **composed constraint graph** [Dinur, Section 3.3][Dinur2005]: the constraint graph of the
composed test, over the alphabet `Bool × (HadamardTester.Query → Bool)`, which does not depend on
`α`. -/
noncomputable def compose :
    ConstraintGraph (ComposePos V E α ⊕ E × Rand α) ((E × Rand α) × Query)
      (Bool × (Query → Bool)) :=
  G.composeTest.toConstraintGraph

/-! ### Completeness -/

/-- The **honest composed proof** of a labelling `σ` of `G`: the long code of the label of every
vertex as its table, and the honest proof of the labels of its ends as the tables of the tester of
every edge. -/
noncomputable def composeProof (σ : V → α) : ComposePos V E α → Bool :=
  assignmentTester.composeProof G σ

/-- The tester of the edge `e` reads in the honest composed proof the honest proof of the labels of
the ends of `e`. -/
theorem composeProof_comp_testerPos (σ : V → α) (e : E) :
    G.composeProof σ ∘ G.testerPos e = honestProof fun b ↦ σ (G.ends e b) :=
  assignmentTester.composeProof_comp_testerPos G σ e

/-- The composed test passes the honest composed proof of `σ` on every random string of the edges
satisfied by `σ`. -/
theorem passes_composeTest_composeProof {σ : V → α} {e : E} (he : G.Satisfies σ e)
    (ω : Rand α) : G.composeTest.Passes (G.composeProof σ) (e, ω) :=
  AssignmentTester.passes_composeTest_composeProof isComplete_assignmentTester G he ω

/-- **Completeness of composition** [Dinur, Lemma 3.6][Dinur2005]: if `G` is satisfiable, so is
the composed graph. -/
theorem satisfiable_compose (h : G.Satisfiable) : G.compose.Satisfiable :=
  AssignmentTester.satisfiable_compose isComplete_assignmentTester h

/-- The labelling of the composed graph by the honest composed proof of `σ` violates at most the
proportion of the edges of `G` that `σ` violates. -/
theorem unsatFrac_compose_labellingOf_le [Fintype E] (σ : V → α) (γ : Bool) :
    G.compose.unsatFrac (G.composeTest.labellingOf (G.composeProof σ) γ) ≤ G.unsatFrac σ :=
  AssignmentTester.unsatFrac_compose_labellingOf_le isComplete_assignmentTester G σ γ

/-- **Completeness of composition**, quantitatively: composition does not increase the value. -/
theorem unsatVal_compose_le [Fintype E] [Nonempty α] : G.compose.unsatVal ≤ G.unsatVal :=
  AssignmentTester.unsatVal_compose_le isComplete_assignmentTester G

/-! ### Soundness -/

section Soundness

variable [Nonempty α]

/-- The labelling of `G` decoded from a composed proof `π`: every vertex gets the label decoded from
its table. -/
noncomputable def decodeLabelling (π : ComposePos V E α → Bool) (v : V) : α :=
  AssignmentTester.decodeLabelling decodeLabel π v

/-- **A violated edge makes its tester reject**: if the labelling decoded from a composed proof `π`
violates the edge `e`, the tester of `e` rejects `π` with probability at least `1/28`. -/
theorem one_div_le_one_sub_acceptProb_of_not_satisfies
    {π : ComposePos V E α → Bool} {e : E} (he : ¬ G.Satisfies (decodeLabelling π) e) :
    1 / 28 ≤ 1 - (hadamardTester (G.rel e)).acceptProb (π ∘ G.testerPos e) :=
  sound_assignmentTester (G.rel e) (π ∘ G.testerPos e) he

/-- **Soundness of composition**, for a labelling: every labelling `A` of the composed graph
violates a proportion of the edges at least `1/476` times the proportion of the edges of `G`
violated by the labelling decoded from it. -/
theorem unsatFrac_decodeLabelling_le [Fintype E]
    (A : ComposePos V E α ⊕ E × Rand α → Bool × (Query → Bool)) :
    G.unsatFrac (decodeLabelling (LocalTest.proofOf A)) ≤ 476 * G.compose.unsatFrac A := by
  have h := AssignmentTester.mul_unsatFrac_decodeLabelling_le sound_assignmentTester G A
  change (1 / 28 : ℝ) * G.unsatFrac (decodeLabelling (LocalTest.proofOf A)) ≤
    17 * G.compose.unsatFrac A at h
  linarith

/-- **Soundness of composition** [Dinur, Lemma 3.6][Dinur2005]: composition divides the value of a
constraint graph by at most `476`, whatever its alphabet. -/
theorem le_unsatVal_compose [Fintype E] : G.unsatVal / 476 ≤ G.compose.unsatVal := by
  have h := AssignmentTester.le_unsatVal_compose sound_assignmentTester (by norm_num) G
  norm_num only [card_query, Nat.cast_ofNat] at h
  exact h

/-- **Composition preserves satisfiability.** -/
theorem satisfiable_compose_iff [Finite E] : G.compose.Satisfiable ↔ G.Satisfiable :=
  AssignmentTester.satisfiable_compose_iff isComplete_assignmentTester sound_assignmentTester
    (by norm_num) G

end Soundness

/-! ### Size -/

/-- **The size of the composed graph**: every edge of `G` gives `17 · 2 ^ (20 k² + 15 k + 3)` edges,
where `k = |α|`, a constant depending only on the alphabet. -/
theorem card_edges_compose [Fintype E] :
    Fintype.card ((E × Rand α) × Query) =
      17 * 2 ^ (20 * Fintype.card α ^ 2 + 15 * Fintype.card α + 3) * Fintype.card E := by
  rw [Fintype.card_prod, Fintype.card_prod, card_rand, card_query]
  ring

/-- The composed graph has a vertex for each position of the table of every vertex of `G`, and for
each position of the tables of the tester of every edge and each random string of that tester. -/
theorem card_vertices_compose [Fintype V] [Fintype E] :
    Fintype.card (ComposePos V E α ⊕ E × Rand α) =
      2 ^ Fintype.card α * Fintype.card V + (2 ^ (2 * Fintype.card α) +
        2 ^ (4 * Fintype.card α ^ 2) + 2 ^ (20 * Fintype.card α ^ 2 + 15 * Fintype.card α + 3)) *
        Fintype.card E := by
  rw [Fintype.card_sum, Fintype.card_prod E, card_rand]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  ring

/-- The alphabet of the composed graph has `2 ^ 18` symbols. -/
theorem card_alphabet_compose : Fintype.card (Bool × (Query → Bool)) = 2 ^ 18 := by
  rw [Fintype.card_prod, Fintype.card_fun, card_query, Fintype.card_bool]
  norm_num

end ConstraintGraph

end Cslib.PCP
