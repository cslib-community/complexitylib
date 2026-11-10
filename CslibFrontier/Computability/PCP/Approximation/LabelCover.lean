/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction
public import CslibFrontier.Computability.PCP.Encoded.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pi

/-!
# Label Cover and the Unique Games Conjecture

Both problems are binary constraint satisfaction problems on executable constraint graphs
(`Cslib.PCP.Encoded.Graph`), whose edges carry the table of a function.

* **Label Cover** [Arora and Barak, Chapter 22][AroraBarak09]: a bipartite graph whose edges go
  from a left vertex, labelled in `β`, to a right vertex, labelled in `γ`, each carrying a
  projection `π : β → γ`. An edge is satisfied when `π` maps the label of its left end to the
  label of its right end. Left and right vertices are numbered separately: each number carries a
  pair of labels, of which a left end reads the first and a right end the second
  (`satisfies_toGraph_projectionEval_iff`), so a labelling of the numbers is exactly a labelling
  of the left vertices together with one of the right vertices.
* **Unique Games** [Khot2002]: a constraint graph, not necessarily bipartite, whose edges carry
  bijections `π : α → α`; an edge from `u` to `v` is satisfied when `π` maps the label of `u` to
  the label of `v`. Instances with a non-bijective table are outside the promise.

The value of an instance is the largest proportion of its edges that a labelling satisfies, and
`GapLabelCover β γ c s` and `GapUniqueGames α c s` are the gap problems separating value at least
`c` from value at most `s`.

**The Unique Games Conjecture** [Khot2002] says that for all `ε, δ > 0` there is a number `L` of
labels for which `GapUniqueGames (Fin L) (1 - ε) δ` is NP-hard. It is stated here as the
proposition `UniqueGamesConjecture`, for the parameters with `δ < 1 - ε`: for the others the two
thresholds do not separate the instances, and `GapUniqueGames` has no no-instances. The library
states the conjecture and does not prove it.

## Main definitions

* `Cslib.Complexity.projectionEval`, `Cslib.Complexity.GapLabelCover`: Label Cover.
* `Cslib.Complexity.permutationEval`, `Cslib.Complexity.IsUniqueGame`,
  `Cslib.Complexity.GapUniqueGames`: Unique Games.
* `Cslib.Complexity.UniqueGamesConjecture`: the conjecture, as a proposition.

## Main results

* `Cslib.Complexity.satisfies_toGraph_projectionEval_iff`,
  `Cslib.Complexity.satisfiable_toGraph_projectionEval_iff`: a labelling of a Label Cover instance
  is a labelling of its left vertices together with one of its right vertices.
* `Cslib.Complexity.UniqueGamesConjecture.npHard_of_le`: the conjecture yields NP-hardness for every
  weaker gap.

## References

* [S. Khot, *On the power of unique 2-prover 1-round games*][Khot2002]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 22][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

/-! ### Label Cover -/

section LabelCover

variable {β γ : Type} [DecidableEq γ]

/-- The **projection constraint** `π` on the pairs of labels `x` of the left end and `y` of the
right end of an edge: it holds when `π x.1 = y.2`. -/
def projectionEval (π : β → γ) (x y : β × γ) : Bool :=
  decide (π x.1 = y.2)

/-- A labelling satisfies an edge of a Label Cover instance when the projection maps the first
label of its left end to the second label of its right end. -/
theorem satisfies_toGraph_projectionEval_iff (g : Graph (β → γ)) (σ : ℕ → β × γ)
    (i : Fin g.edges.length) :
    (g.toGraph projectionEval).Satisfies σ i ↔
      (g.edges.get i).constraint (σ (g.edges.get i).src).1 = (σ (g.edges.get i).dst).2 := by
  simp [ConstraintGraph.Satisfies, Graph.toGraph, projectionEval]

/-- **A Label Cover instance is satisfiable exactly when some labelling `ℓ` of its left vertices
and `r` of its right vertices satisfies every projection.** -/
theorem satisfiable_toGraph_projectionEval_iff (g : Graph (β → γ)) :
    (g.toGraph projectionEval).Satisfiable ↔
      ∃ (ℓ : ℕ → β) (r : ℕ → γ), ∀ d ∈ g.edges, d.constraint (ℓ d.src) = r d.dst := by
  simp only [ConstraintGraph.Satisfiable, ConstraintGraph.Satisfies, Graph.toGraph,
    projectionEval, decide_eq_true_eq]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨fun v => (σ v).1, fun v => (σ v).2, fun d hd => ?_⟩
    obtain ⟨i, rfl⟩ := List.get_of_mem hd
    exact hσ i
  · rintro ⟨ℓ, r, h⟩
    exact ⟨fun v => (ℓ v, r v), fun i => h _ (List.get_mem _ _)⟩

/-- The gap problem of **Label Cover** with left labels `β` and right labels `γ`, completeness
`c` and soundness `s`. Each edge goes from a left vertex `src` to a right vertex `dst` and carries
the table of a projection `β → γ`. The value of an instance is the largest proportion of the
edges that labellings of the left and the right vertices satisfy. The yes-instances have value at
least `c`, the no-instances value at most `s`. -/
noncomputable def GapLabelCover (β γ : Type) [DecidableEq γ] (c s : ℝ) :
    PromiseProblem (Graph (β → γ)) :=
  PromiseProblem.gapMax (fun g => 1 - (g.toGraph projectionEval).unsatVal) (fun _ => c)
    (fun _ => s)

end LabelCover

/-! ### Unique Games -/

section UniqueGames

variable {α : Type} [DecidableEq α]

/-- The constraint of a function `π` on the labels `a` of the first end and `b` of the second end
of an edge: it holds when `π a = b`. -/
def permutationEval (π : α → α) (a b : α) : Bool :=
  decide (π a = b)

/-- A **unique game**: the table on every edge is a bijection. -/
def IsUniqueGame (g : Graph (α → α)) : Prop :=
  ∀ d ∈ g.edges, Function.Bijective d.constraint

/-- The gap problem of **Unique Games** with labels `α`, completeness `c` and soundness `s`. The
instances are unique games: constraint graphs whose edges carry bijections `π : α → α`, an edge
from `u` to `v` being satisfied when `π` maps the label of `u` to that of `v`. The value of an
instance is the largest proportion of the edges that a labelling satisfies. The yes-instances have
value at least `c`, the no-instances value at most `s`. -/
noncomputable def GapUniqueGames (α : Type) [DecidableEq α] (c s : ℝ) :
    PromiseProblem (Graph (α → α)) :=
  (PromiseProblem.gapMax (fun g => 1 - (g.toGraph permutationEval).unsatVal) (fun _ => c)
    (fun _ => s)).restrict {g | IsUniqueGame g}

/-- Weakening the gap of `GapUniqueGames` enlarges its promise. -/
theorem GapUniqueGames_mono {c c' s s' : ℝ} (hc : c' ≤ c) (hs : s ≤ s') (hsc : s' < c') :
    (GapUniqueGames α c s).yes ⊆ (GapUniqueGames α c' s').yes ∧
      (GapUniqueGames α c s).no ⊆ (GapUniqueGames α c' s').no :=
  ⟨fun _ ⟨hg, hu⟩ => ⟨hc.trans hg, hu⟩, fun _ ⟨⟨hg, _⟩, hu⟩ => ⟨⟨hg.trans hs, hsc⟩, hu⟩⟩

end UniqueGames

/-- **The Unique Games Conjecture** [Khot2002]: for all `ε, δ > 0` with `δ < 1 - ε`, there is a
number `L` of labels such that distinguishing unique games on the labels `Fin L` of value at least
`1 - ε` from those of value at most `δ` is NP-hard. Instances are encoded by their vertex counts and
edge lists, with constraint tables listing ranks of labels. The constraint graphs need not be
bipartite. This is a conjecture, stated and not assumed. -/
def UniqueGamesConjecture : Prop :=
  ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 - ε → ∃ L : ℕ,
    PromiseProblem.NPHard (Graph.encoding (encPi (encFinEnum (Fin L))))
      (GapUniqueGames (Fin L) (1 - ε) δ)

/-- Under the Unique Games Conjecture, for every `ε, δ > 0` with `δ < 1 - ε` there is a number `L`
of labels such that every weaker gap problem on `Fin L`, with completeness at most `1 - ε` and
soundness at least `δ`, is NP-hard. -/
theorem UniqueGamesConjecture.npHard_of_le (h : UniqueGamesConjecture) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hεδ : δ < 1 - ε) : ∃ L : ℕ, ∀ c s : ℝ, c ≤ 1 - ε → δ ≤ s → s < c →
      PromiseProblem.NPHard (Graph.encoding (encPi (encFinEnum (Fin L))))
        (GapUniqueGames (Fin L) c s) := by
  obtain ⟨L, hL⟩ := h ε δ hε hδ hεδ
  exact ⟨L, fun c s hc hs hsc => hL.mono (GapUniqueGames_mono hc hs hsc).1
    (GapUniqueGames_mono hc hs hsc).2⟩

end Cslib.Complexity
