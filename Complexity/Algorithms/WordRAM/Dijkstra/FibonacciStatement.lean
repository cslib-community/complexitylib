/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.HeapStatement

/-!
# Dijkstra's algorithm on the word RAM with a Fibonacci heap: statements

This file states what a single-source shortest-path program on the word RAM must satisfy to
achieve the Fredman–Tarjan running-time bound of Dijkstra's algorithm with a Fibonacci heap
[Dijkstra][Dijkstra1959] [Fredman and Tarjan][FredmanTarjan1987]
[Cormen et al., Chapter 19 and Section 24.3][CLRS2009].

Because memory past the input starts at `0`, the priority-queue and distance arrays require only
`O(1)` fresh initialization, and the algorithm extracts at most `min n (m + 1)` reachable vertices
from the source. We therefore state both:

* `Cslib.Algorithms.WordRAM.Dijkstra.FibonacciSpec`: the sharper reachable-vertex bound
  `steps + 1 ≤ K (m + min(n, m + 1) (⌊log₂ n⌋ + 1))`;
* `Cslib.Algorithms.WordRAM.Dijkstra.FibonacciLinearSpec` and
  `Cslib.Algorithms.WordRAM.Dijkstra.FibonacciStatement`: the textbook bound
  `steps + 1 ≤ K (m + n (⌊log₂ n⌋ + 1))`, derived immediately from `FibonacciSpec`.

Both bounds use the exact same word-size hypothesis
`Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))` as
`Cslib.Algorithms.WordRAM.Dijkstra.LogLinearSpec`.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.FibonacciSpec`: a flat program computes every distance from
  the source within `K (m + min(n, m + 1) (⌊log₂ n⌋ + 1))` instructions.
* `Cslib.Algorithms.WordRAM.Dijkstra.FibonacciLinearSpec`: textbook `K (m + n (⌊log₂ n⌋ + 1))`
  program specification.
* `Cslib.Algorithms.WordRAM.Dijkstra.FibonacciSpecStatement`: some program meets `FibonacciSpec`.
* `Cslib.Algorithms.WordRAM.Dijkstra.FibonacciStatement`: some program meets `FibonacciLinearSpec`.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.FibonacciSpec.toLinearSpec`: `FibonacciSpec` implies
  `FibonacciLinearSpec` with the same constant `K`.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [M. L. Fredman and R. E. Tarjan, *Fibonacci heaps and their uses in improved network optimization
  algorithms*][FredmanTarjan1987], Section 4 (pp. 609–610).
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 24.3 (p. 662).
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM

/-- **Shortest paths in `O(m + min(n, m + 1) (⌊log₂ n⌋ + 1))` time.** At every word size `w` that
holds `8 (n + m + 2) (W + 2)`, where `m` is the number of edges and `W` the largest weight, the
flat program `p`, started on the input words of an adjacency-list instance, halts within
`K (m + min(n, m + 1) (⌊log₂ n⌋ + 1))` instructions, the final `halt` included, and its memory
then holds at `G.outAddr v` the encoded distance from the source to `v`, for every vertex `v`. -/
def FibonacciSpec {r : ℕ} (p : Program .exact r) (K : ℕ) : Prop :=
  ∀ (G : ListInstance) (w : ℕ), Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) →
    ∃ t steps, Runs w p (.init G.encode) t steps ∧ (∃ v, step w p t = .halt v) ∧
      steps + 1 ≤ K * (G.m + min G.n (G.m + 1) * (Nat.log 2 G.n + 1)) ∧
      ∀ v : Fin G.n, t.data.mem (G.outAddr v) = encodeDist (G.dist G.source v)

/-- **Shortest paths in `O(m + n (⌊log₂ n⌋ + 1))` time.** Textbook Fredman–Tarjan running-time
specification for a flat word-RAM program `p` over the exact basis. -/
def FibonacciLinearSpec {r : ℕ} (p : Program .exact r) (K : ℕ) : Prop :=
  ∀ (G : ListInstance) (w : ℕ), Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) →
    ∃ t steps, Runs w p (.init G.encode) t steps ∧ (∃ v, step w p t = .halt v) ∧
      steps + 1 ≤ K * (G.m + G.n * (Nat.log 2 G.n + 1)) ∧
      ∀ v : Fin G.n, t.data.mem (G.outAddr v) = encodeDist (G.dist G.source v)

/-- The sharper reachable-vertex specification `FibonacciSpec` implies the textbook specification
`FibonacciLinearSpec` with the same constant `K`. -/
theorem FibonacciSpec.toLinearSpec {r K : ℕ} {p : Program .exact r} (h : FibonacciSpec p K) :
    FibonacciLinearSpec p K := by
  intro G w hw
  obtain ⟨t, steps, hr, hh, hle, hd⟩ := h G w hw
  refine ⟨t, steps, hr, hh, hle.trans (Nat.mul_le_mul_left K ?_), hd⟩
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right (Nat.log 2 G.n + 1) (Nat.min_le_left G.n (G.m + 1))) G.m

/-- **Reachable-vertex Fibonacci-heap Dijkstra theorem (statement).** Some word-RAM program over
the exact basis meets `FibonacciSpec`. -/
def FibonacciSpecStatement : Prop :=
  ∃ r, ∃ p : Program .exact r, ∃ K, FibonacciSpec p K

/-- **Fibonacci-heap Dijkstra main theorem (statement).** Some word-RAM program over the exact
basis computes all shortest-path distances from the source of a weighted directed graph with `n`
vertices and `m` edges, given by adjacency lists, within `O(m + n (⌊log₂ n⌋ + 1))` instructions. -/
def FibonacciStatement : Prop :=
  ∃ r, ∃ p : Program .exact r, ∃ K, FibonacciLinearSpec p K

end Cslib.Algorithms.WordRAM.Dijkstra
