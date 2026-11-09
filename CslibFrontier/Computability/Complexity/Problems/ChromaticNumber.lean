/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Coloring
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Problems.Graph.VertexColors
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.List.GetD

/-!
# Chromatic number

`ChromaticNumber` is Karp's problem CHROMATIC NUMBER [Karp1972]: given a graph `G` and a number
`k`, the declared vertices of `G` can be colored with `k` colors so that adjacent vertices get
different colors. It is `KColoring k` with the number of colors moved into the instance, which is
encoded with the graph (`encGraph`) and `k` in binary (`encNat`). The graph of the declared
vertices has chromatic number at most `k` in the sense of `SimpleGraph.chromaticNumber`
(`Cslib.Complexity.mem_ChromaticNumber_iff_chromaticNumber_le`). Equivalently, by Mathlib's
`SimpleGraph.partitionable_iff_colorable`, that graph is partitioned into at most `k`
independent sets (`SimpleGraph.Partitionable`).

`NP` membership uses a list of colors as the witness, the color of a vertex being the entry at its
first occurrence among the declared vertices (`Cslib.Complexity.colorOf`). Since `k` is written in
binary, a coloring of a member is first replaced by one with colors below the number of declared
vertices, so that witnesses have length polynomial in the instance: when `k` exceeds the number of
declared vertices, every vertex is colored by its position.

Karp proves hardness by a reduction from SATISFIABILITY WITH AT MOST 3 LITERALS PER CLAUSE. Here
`ChromaticNumber` is `NP`-hard because the `NP`-hard `ThreeColoring` is the instances with three
colors (`Cslib.Complexity.polyTimeReducible_KColoring_ChromaticNumber`).

## Main definitions

* `Cslib.Complexity.ChromaticNumber`: graphs with a number of colors that suffices.

## Main results

* `Cslib.Complexity.mem_ChromaticNumber_iff_chromaticNumber_le`: membership bounds the chromatic
  number of the graph of the declared vertices.
* `Cslib.Complexity.ChromaticNumber.mem_NP`: `ChromaticNumber ∈ NP (encPair encGraph encNat)`.
* `Cslib.Complexity.polyTimeReducible_KColoring_ChromaticNumber`,
  `Cslib.Complexity.ChromaticNumber_npHard`, `Cslib.Complexity.ChromaticNumber_npComplete`:
  `ChromaticNumber` is `NP`-complete.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **Chromatic number** [Karp1972]: the graphs whose declared vertices can be colored with the
given number of colors so that adjacent vertices get different colors. Unlike `KColoring k`, the
number of colors is part of the instance. -/
@[expose]
def ChromaticNumber : Set (Graph × ℕ) := {x | x.1 ∈ KColoring x.2}

/-- Membership in `ChromaticNumber` is membership in `KColoring` with the given number of
colors. -/
@[simp]
theorem mem_ChromaticNumber_iff {G : Graph} {k : ℕ} :
    (G, k) ∈ ChromaticNumber ↔ G ∈ KColoring k :=
  Iff.rfl

/-- Membership in `ChromaticNumber` bounds the chromatic number of the graph induced on the
declared vertices (`SimpleGraph.chromaticNumber`). -/
theorem mem_ChromaticNumber_iff_chromaticNumber_le {G : Graph} {k : ℕ} :
    (G, k) ∈ ChromaticNumber ↔ G.induced.chromaticNumber ≤ k :=
  SimpleGraph.chromaticNumber_le_iff_colorable.symm

namespace ChromaticNumber

/-- The check of a list of colors: every declared vertex gets a color below the bound, and
adjacent declared vertices get different colors. -/
private def check (x : (Graph × ℕ) × List ℕ) : Bool :=
  x.1.1.1.all fun u => decide (colorOf x.1.1 x.2 u < x.1.2) &&
    x.1.1.1.all fun v =>
      !(x.1.1.adjBool u v && decide (colorOf x.1.1 x.2 u = colorOf x.1.1 x.2 v))

private theorem computableInPolyTime_check :
    ComputableInPolyTime check (encPair (encPair encGraph encNat) (encList encNat)) encBool := by
  have hV : ComputableInPolyTime (fun x : (Graph × ℕ) × List ℕ => x.1.1.1)
      (encPair (encPair encGraph encNat) (encList encNat)) (encList encNat) := by
    unfold encGraph
    fun_prop
  have hk : ComputableInPolyTime (fun x : (Graph × ℕ) × List ℕ => x.1.2)
      (encPair (encPair encGraph encNat) (encList encNat)) encNat := by
    fun_prop
  have hc : ComputableInPolyTime (fun x : (Graph × ℕ) × List ℕ => x.2)
      (encPair (encPair encGraph encNat) (encList encNat)) (encList encNat) := by
    fun_prop
  have hG : ComputableInPolyTime (fun x : (Graph × ℕ) × List ℕ => x.1.1)
      (encPair (encPair encGraph encNat) (encList encNat)) encGraph := by
    fun_prop
  unfold check
  fun_prop

private theorem check_iff (x : (Graph × ℕ) × List ℕ) :
    check x = true ↔ (∀ v ∈ x.1.1.1, colorOf x.1.1 x.2 v < x.1.2) ∧
      ∀ u ∈ x.1.1.1, ∀ v ∈ x.1.1.1, x.1.1.toSimpleGraph.Adj u v →
        colorOf x.1.1 x.2 u ≠ colorOf x.1.1 x.2 v := by
  simp only [check, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, Graph.adjBool_eq_false_iff, decide_eq_false_iff_not]
  constructor
  · intro h
    exact ⟨fun v hv => (h v hv).1, fun u hu v hv huv =>
      ((h u hu).2 v hv).resolve_left (not_not.2 huv)⟩
  · rintro ⟨hlt, hadj⟩ u hu
    refine ⟨hlt u hu, fun v hv => ?_⟩
    by_cases huv : x.1.1.toSimpleGraph.Adj u v
    · exact Or.inr (hadj u hu v hv huv)
    · exact Or.inl huv

/-- The colors of the declared vertices under a coloring `c` with `k` colors, or their positions
when `k` exceeds the number of declared vertices. -/
private def witness (G : Graph) (k : ℕ) (c : ℕ → ℕ) : List ℕ :=
  if k ≤ G.1.length then G.1.map c else List.range G.1.length

private theorem colorOf_witness {G : Graph} {k : ℕ} {c : ℕ → ℕ} {v : ℕ} (hv : v ∈ G.1) :
    colorOf G (witness G k c) v = if k ≤ G.1.length then c v else G.1.idxOf v := by
  have hlt : G.1.idxOf v < G.1.length := List.idxOf_lt_length_iff.2 hv
  unfold witness
  split
  · exact colorOf_map hv
  · rw [colorOf, List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_range]

/-- `ChromaticNumber` belongs to `NP`, with a list of colors as the witness. Colors are taken
below the number of declared vertices, so witnesses stay polynomial although the number of colors
is written in binary. -/
theorem mem_NP : ChromaticNumber ∈ NP (encPair encGraph encNat) := by
  have hset : ChromaticNumber = {x | ∃ c : List ℕ, (∀ v ∈ x.1.1, colorOf x.1 c v < x.2) ∧
      ∀ u ∈ x.1.1, ∀ v ∈ x.1.1, x.1.toSimpleGraph.Adj u v →
        colorOf x.1 c u ≠ colorOf x.1 c v} := by
    ext ⟨G, k⟩
    rw [mem_ChromaticNumber_iff, mem_KColoring_iff]
    constructor
    · rintro ⟨c, hc, hadj⟩
      refine ⟨G.1.map c, fun v hv => ?_, fun u hu v hv huv => ?_⟩
      · rw [colorOf_map hv]
        exact hc v hv
      · rw [colorOf_map hu, colorOf_map hv]
        exact hadj u hu v hv huv
    · rintro ⟨c, hc, hadj⟩
      exact ⟨colorOf G c, hc, hadj⟩
  rw [hset]
  refine mem_NP_of_witness (p := 2 * Polynomial.X ^ 2 + Polynomial.X) (.list .nat)
    computableInPolyTime_check (fun x c => check_iff (x, c)) ?_
  rintro ⟨G, k⟩ c ⟨hc, hadj⟩
  refine ⟨witness G k (colorOf G c), ⟨fun v hv => ?_, fun u hu v hv huv => ?_⟩, ?_⟩
  · rw [colorOf_witness hv]
    split
    · exact hc v hv
    · have := List.idxOf_lt_length_iff.2 hv
      omega
  · rw [colorOf_witness hu, colorOf_witness hv]
    split
    · exact hadj u hu v hv huv
    · exact fun h => huv.ne ((List.idxOf_inj hu).1 h)
  · have hN : G.1.length ≤ (encPair encGraph encNat (G, k)).length :=
      G.length_vertices_le_encGraph.trans (length_le_encPair_left _ _ (G, k))
    have hentry : ∀ a ∈ witness G k (colorOf G c),
        (encNat a).length ≤ (encPair encGraph encNat (G, k)).length := by
      intro a ha
      refine (length_encNat_le_self a).trans (le_trans ?_ hN)
      unfold witness at ha
      split at ha
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ha
        exact (hc v hv).le.trans ‹_›
      · exact (List.mem_range.1 ha).le
    have hlen : (witness G k (colorOf G c)).length ≤
        (encPair encGraph encNat (G, k)).length := by
      unfold witness
      split <;> simpa using hN
    have h := length_encList_le encNat _ hentry
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    nlinarith

end ChromaticNumber

/-- `KColoring k` reduces to `ChromaticNumber` in polynomial time, by attaching the number of
colors `k` to the graph. -/
theorem polyTimeReducible_KColoring_ChromaticNumber (k : ℕ) :
    PolyTimeReducible encGraph (encPair encGraph encNat) (KColoring k) ChromaticNumber :=
  ⟨fun G => (G, k), by fun_prop, fun _ => Iff.rfl⟩

/-- `ChromaticNumber` is `NP`-hard, already for three colors. -/
theorem ChromaticNumber_npHard : NPHard (encPair encGraph encNat) ChromaticNumber :=
  ThreeColoring_npHard.trans (polyTimeReducible_KColoring_ChromaticNumber 3)

/-- **Chromatic number is NP-complete**, with the number of colors in binary [Karp1972]. -/
theorem ChromaticNumber_npComplete : NPComplete (encPair encGraph encNat) ChromaticNumber :=
  ⟨ChromaticNumber.mem_NP, ChromaticNumber_npHard⟩

end Cslib.Complexity
