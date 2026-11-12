/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Coloring
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Complexity.Problems.Graph.VertexColors
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Chromatic number

`ChromaticNumber` is Karp's problem CHROMATIC NUMBER [Karp1972]: given a graph `G` and a number
`k`, the declared vertices of `G` can be colored with `k` colors so that adjacent vertices get
different colors. It is `KColoring k` with the number of colors moved into the instance
(`Cslib.Complexity.ChromaticNumberInstance`, encoded by `Cslib.Complexity.encChromaticNumber`). The
graph of the declared vertices has chromatic number at most `k` in the sense of
`SimpleGraph.chromaticNumber` (`Cslib.Complexity.mem_ChromaticNumber_iff_chromaticNumber_le`).
Equivalently, by Mathlib's `SimpleGraph.partitionable_iff_colorable`, that graph is partitioned
into at most `k` independent sets (`SimpleGraph.Partitionable`).

`NP` membership uses a list of colors as the witness, the color of a vertex being the entry at its
first occurrence among the declared vertices (`Cslib.Complexity.colorOf`). Since `k` is written in
binary, a coloring of a member is first replaced by one with colors below the number of declared
vertices, so that witnesses have length polynomial in the instance: when `k` exceeds the number of
declared vertices, every vertex is colored by its position.

Karp proves hardness by a reduction from SATISFIABILITY WITH AT MOST 3 LITERALS PER CLAUSE. Here
`ChromaticNumber` is `NP`-hard because the `NP`-hard `ThreeColoring` is the instances with three
colors (`Cslib.Complexity.polyTimeReducible_KColoring_ChromaticNumber`).

## Main definitions

* `Cslib.Complexity.ChromaticNumberInstance`: instance `(graph, colors)` of Chromatic Number.
* `Cslib.Complexity.encChromaticNumber`: polynomial-time encoding of
  `ChromaticNumberInstance`.
* `Cslib.Complexity.ChromaticNumber`: graphs with a number of colors that suffices.

## Main results

* `Cslib.Complexity.mem_ChromaticNumber_iff_chromaticNumber_le`: membership bounds the chromatic
  number of the graph of the declared vertices.
* `Cslib.Complexity.ChromaticNumber.mem_NP`: `ChromaticNumber ∈ NP encChromaticNumber`.
* `Cslib.Complexity.polyTimeReducible_KColoring_ChromaticNumber`,
  `Cslib.Complexity.ChromaticNumber_npHard`, `Cslib.Complexity.ChromaticNumber_npComplete`:
  `ChromaticNumber` is `NP`-complete.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- An instance `(graph, colors)` of **Chromatic Number**. -/
@[ext]
structure ChromaticNumberInstance where
  /-- The graph to be colored. -/
  graph : Graph
  /-- The maximum number of colors allowed. -/
  colors : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Encoding of `ChromaticNumberInstance` as a pair `(graph, colors)`. -/
enc_structure encChromaticNumber : ChromaticNumberInstance where
  graph : encGraph,
  colors : encNat

attribute [fun_prop] encChromaticNumber_graph_polyTime encChromaticNumber_colors_polyTime
  encChromaticNumber_mk_polyTime

/-- **Chromatic number** [Karp1972]: the graphs whose declared vertices can be colored with the
given number of colors so that adjacent vertices get different colors. Unlike `KColoring k`, the
number of colors is part of the instance. -/
@[expose]
def ChromaticNumber : Set ChromaticNumberInstance := {x | x.graph ∈ KColoring x.colors}

/-- Membership in `ChromaticNumber` is membership in `KColoring` with the given number of
colors. -/
@[simp]
theorem mem_ChromaticNumber_iff {G : Graph} {k : ℕ} :
    (⟨G, k⟩ : ChromaticNumberInstance) ∈ ChromaticNumber ↔ G ∈ KColoring k :=
  Iff.rfl

/-- Membership in `ChromaticNumber` bounds the chromatic number of the graph induced on the
declared vertices (`SimpleGraph.chromaticNumber`). -/
theorem mem_ChromaticNumber_iff_chromaticNumber_le {G : Graph} {k : ℕ} :
    (⟨G, k⟩ : ChromaticNumberInstance) ∈ ChromaticNumber ↔ G.induced.chromaticNumber ≤ k :=
  SimpleGraph.chromaticNumber_le_iff_colorable.symm

namespace ChromaticNumber

/-- The check of a list of colors: every declared vertex gets a color below the bound, and
adjacent declared vertices get different colors. -/
private def check (x : ChromaticNumberInstance × List ℕ) : Bool :=
  x.1.graph.vertices.all fun u => decide (colorOf x.1.graph x.2 u < x.1.colors) &&
    x.1.graph.vertices.all fun v =>
      !(x.1.graph.adjBool u v && decide (colorOf x.1.graph x.2 u = colorOf x.1.graph x.2 v))

private theorem computableInPolyTime_check :
    ComputableInPolyTime check (encPair encChromaticNumber (encList encNat)) encBool := by
  unfold check
  fun_prop

private theorem check_iff (x : ChromaticNumberInstance × List ℕ) :
    check x = true ↔ (∀ v ∈ x.1.graph.vertices, colorOf x.1.graph x.2 v < x.1.colors) ∧
      ∀ u ∈ x.1.graph.vertices, ∀ v ∈ x.1.graph.vertices, x.1.graph.toSimpleGraph.Adj u v →
        colorOf x.1.graph x.2 u ≠ colorOf x.1.graph x.2 v := by
  simp only [check, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, Graph.adjBool_eq_false_iff, decide_eq_false_iff_not]
  constructor
  · intro h
    exact ⟨fun v hv => (h v hv).1, fun u hu v hv huv =>
      ((h u hu).2 v hv).resolve_left (not_not.2 huv)⟩
  · rintro ⟨hlt, hadj⟩ u hu
    refine ⟨hlt u hu, fun v hv => ?_⟩
    by_cases huv : x.1.graph.toSimpleGraph.Adj u v
    · exact Or.inr (hadj u hu v hv huv)
    · exact Or.inl huv

/-- `ChromaticNumber` belongs to `NP`, with a list of colors as the witness. Colors are taken
below the number of declared vertices, so witnesses stay polynomial although the number of colors
is written in binary. -/
theorem mem_NP : ChromaticNumber ∈ NP encChromaticNumber := by
  have hcert : ∀ (G : Graph) (k : ℕ), (⟨G, k⟩ : ChromaticNumberInstance) ∈ ChromaticNumber →
      ∃ g : ℕ → ℕ, (∀ v ∈ G.vertices, g v ≤ G.vertices.length) ∧
        check (⟨G, k⟩, G.vertices.map g) = true := by
    intro G k h
    obtain ⟨c, hc, hadj⟩ := mem_KColoring_iff.1 h
    refine ⟨fun v => if k ≤ G.vertices.length then c v else G.vertices.idxOf v, fun v hv => ?_,
      (check_iff _).2 ⟨fun v hv => ?_, fun u hu v hv huv => ?_⟩⟩
    · split
      · exact (hc v hv).le.trans ‹_›
      · exact (List.idxOf_lt_length_iff.2 hv).le
    · rw [colorOf_map hv]
      split
      · exact hc v hv
      · exact (List.idxOf_lt_length_iff.2 hv).trans (Nat.lt_of_not_le ‹_›)
    · rw [colorOf_map hu, colorOf_map hv]
      split
      · exact hadj u hu v hv huv
      · exact fun heq => huv.ne ((List.idxOf_inj hu).1 heq)
  refine mem_NP_of_colorOf ChromaticNumberInstance.graph computableInPolyTime_check
    (fun ⟨G, k⟩ => by
      rw [encChromaticNumber_apply]
      exact G.length_vertices_le_encGraph.trans (length_le_encPair_left _ _ (G, k)))
    (fun ⟨G, k⟩ cs h => ?_) (fun ⟨G, k⟩ h => hcert G k h)
  obtain ⟨hlt, hadj⟩ := (check_iff (⟨G, k⟩, cs)).1 h
  exact mem_KColoring_iff.2 ⟨colorOf G cs, hlt, hadj⟩

end ChromaticNumber

/-- `KColoring k` reduces to `ChromaticNumber` in polynomial time, by attaching the number of
colors `k` to the graph. -/
theorem polyTimeReducible_KColoring_ChromaticNumber (k : ℕ) :
    PolyTimeReducible encGraph encChromaticNumber (KColoring k) ChromaticNumber :=
  ⟨fun G => ⟨G, k⟩, by fun_prop, fun _ => Iff.rfl⟩

/-- `ChromaticNumber` is `NP`-hard, already for three colors. -/
theorem ChromaticNumber_npHard : NPHard encChromaticNumber ChromaticNumber :=
  ThreeColoring_npHard.trans (polyTimeReducible_KColoring_ChromaticNumber 3)

/-- **Chromatic number is NP-complete**, with the number of colors in binary [Karp1972]. -/
theorem ChromaticNumber_npComplete : NPComplete encChromaticNumber ChromaticNumber :=
  ⟨ChromaticNumber.mem_NP, ChromaticNumber_npHard⟩

end Cslib.Complexity
