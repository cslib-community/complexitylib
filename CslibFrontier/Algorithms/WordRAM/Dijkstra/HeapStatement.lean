/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Dijkstra.ListInstance
public import CslibFrontier.Computability.WordRAM.Time

/-!
# Dijkstra's algorithm on the word RAM with adjacency lists: statements

This file states, without proof, what a single-source shortest-path program on the word RAM
must satisfy to run in `O((m + 1) log n)` time on a graph with `n` vertices and `m` edges, the
bound of Dijkstra's algorithm with a binary heap [Dijkstra][Dijkstra1959]
[Cormen et al., Section 24.3][CLRS2009]. The bound has no `n` term: memory past the input starts
at `0`, so the per-vertex arrays need no initialization, and the offsets give the adjacency list
of any vertex directly, so the program touches only the vertices it reaches.

An instance is an adjacency-list instance `Cslib.Algorithms.Dijkstra.ListInstance`, and its
distance is `Cslib.Algorithms.Dijkstra.ListInstance.dist`; both are machine-free. This file adds
the input words and the output convention. The program reads the input words `n`, the source,
the `n + 1` offsets of the adjacency lists in the edge array, and the edges in order, each as two
words, its target and its weight. When it halts, the `n` memory cells just past the input hold
the distances from the source, with `0` for an unreachable vertex and `d + 1` for distance `d`
(`Cslib.Algorithms.WordRAM.Dijkstra.encodeDist`).

## Main definitions

* `Cslib.Algorithms.Dijkstra.ListInstance.encode`: the input words of an instance.
* `Cslib.Algorithms.Dijkstra.ListInstance.outAddr`: the output address of a vertex.
* `Cslib.Algorithms.WordRAM.Dijkstra.encodeDist`: a distance as a word.
* `Cslib.Algorithms.WordRAM.Dijkstra.decodeDist`: the distance a word encodes.
* `Cslib.Algorithms.WordRAM.Dijkstra.LogLinearSpec`: a flat program computes every distance from
  the source within `K (m + 1) (⌊log₂ n⌋ + 1)` instructions.
* `Cslib.Algorithms.WordRAM.Dijkstra.LogLinearStatement`: some program meets `LogLinearSpec`.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.decodeDist_encodeDist`: decoding inverts the encoding of
  distances.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Dijkstra.ListInstance

variable (G : ListInstance)

/-- The offset of the adjacency list of vertex `u` in the edge array: the number of edges out of
the vertices below `u`. The offset of `n` is the number `m` of edges. -/
def offset (u : ℕ) : ℕ :=
  (((List.finRange G.n).take u).map fun x => (G.adj x).length).sum

/-- The input words: `n`, the source, the offsets of the vertices `0, …, n`, and then the edges of
the lists `adj 0, …, adj (n - 1)` in order, each as its target and its weight. Edge `j` in this
order has its target at word `n + 3 + 2 j` and its weight at word `n + 4 + 2 j`, and the edges
out of `u` are those with `offset u ≤ j < offset (u + 1)`. -/
def encode : List ℕ :=
  G.n :: (G.source : ℕ) ::
    ((List.range (G.n + 1)).map G.offset ++
      (List.finRange G.n).flatMap fun u => (G.adj u).flatMap fun e => [(e.1 : ℕ), e.2])

/-- The output address of vertex `v`: the `n` cells just past the input, which has `n + 2 m + 3`
words and so ends at address `n + 2 m + 3`. -/
def outAddr (v : Fin G.n) : ℕ := G.n + 2 * G.m + 4 + v

end Cslib.Algorithms.Dijkstra.ListInstance

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM Cslib.Algorithms.Dijkstra

/-- A distance as a word: `0` for an unreachable vertex and `d + 1` for distance `d`. -/
def encodeDist (d : ℕ∞) : ℕ := if d = ⊤ then 0 else d.toNat + 1

/-- The distance a word encodes: `⊤` for `0` and `d` for `d + 1`. -/
def decodeDist (x : ℕ) : ℕ∞ := if x = 0 then ⊤ else ((x - 1 : ℕ) : ℕ∞)

@[simp]
theorem encodeDist_decodeDist (x : ℕ) : encodeDist (decodeDist x) = x := by
  cases x with
  | zero => simp [decodeDist, encodeDist]
  | succ x => simp [decodeDist, encodeDist]

/-- Decoding inverts the encoding of distances: a distance word decodes to its distance. -/
@[simp]
theorem decodeDist_encodeDist (d : ℕ∞) : decodeDist (encodeDist d) = d := by
  induction d using ENat.recTopCoe with
  | top => simp [decodeDist, encodeDist]
  | coe d => simp [decodeDist, encodeDist]

/-- **Shortest paths in `O((m + 1) log n)` time.** At every word size `w` that holds
`8 (n + m + 2) (W + 2)`, where `m` is the number of edges and `W` the largest weight, the flat
program `p`, started on the input words of an adjacency-list instance, halts within
`K (m + 1) (⌊log₂ n⌋ + 1)` instructions, the final `halt` included, and its memory then holds at
`G.outAddr v` the encoded distance from the source to `v`, for every vertex `v`. The register
value returned by `halt` is not part of the result. -/
def LogLinearSpec {r : ℕ} (p : Program .exact r) (K : ℕ) : Prop :=
  ∀ (G : ListInstance) (w : ℕ), Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) →
    ∃ t steps, Runs w p (.init G.encode) t steps ∧ (∃ v, step w p t = .halt v) ∧
      steps + 1 ≤ K * (G.m + 1) * (Nat.log 2 G.n + 1) ∧
      ∀ v : Fin G.n, t.data.mem (G.outAddr v) = encodeDist (G.dist G.source v)

/-- **Log-linear main theorem (statement).** Some word-RAM program over the exact basis computes
all shortest-path distances from the source of a weighted directed graph with `n` vertices and
`m` edges, given by adjacency lists, within `O((m + 1) log n)` instructions. -/
def LogLinearStatement : Prop :=
  ∃ r, ∃ p : Program .exact r, ∃ K, LogLinearSpec p K

end Cslib.Algorithms.WordRAM.Dijkstra
