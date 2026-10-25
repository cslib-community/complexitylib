/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.HeapStatement
public import Complexity.Algorithms.WordRAM.Dijkstra.ExactNotation

/-!
# Dijkstra's algorithm with a binary heap: the program

This file writes Dijkstra's algorithm [Dijkstra][Dijkstra1959] [Cormen et al., Section
24.3][CLRS2009] on adjacency lists as a structured word-RAM program over the exact basis
`Cslib.WordRAM.Basis.exact` and 27 registers, with a binary min-heap [Cormen et al., Chapter
6][CLRS2009] that supports decrease-key through an array of positions.

The program reads the input of `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.encode`: `n` at
address `1`, the source at address `2`, the offset of vertex `u` at address `u + 3`, and edge `j`
as its target at address `n + 4 + 2 j` and its weight at the next address. With `m` the number of
edges and `Db = n + 2 m + 4` the first address past the input, it keeps three arrays:

* the distance words `D v` at `Db + v`, which are the output cells: `0` for an undiscovered
  vertex and `d + 1` for tentative distance `d`;
* the heap `H i` at `Db + n + i` for the positions `1 ≤ i ≤ sz`, ordered by the keys `D (H i)`;
* the positions `P v` at `Db + 2 n + 1 + v`: the position of `v` in the heap, and `0` when `v` is
  not in it.

Memory past the input starts at `0`, so every vertex starts undiscovered and out of the heap, and
the arrays need no initialization. A vertex is visited once it has left the heap: its distance
word is nonzero and its position is `0`.

Each round extracts the root `u` of the heap and scans the edges out of `u`. An edge to an
undiscovered vertex inserts it with its new key; an edge that lowers the key of a vertex in the
heap moves it up. The rounds stop when the heap is empty.

On the exact basis a subtraction below zero or a division by zero faults. The program divides
only by the constant `2`, and subtracts only `1` from the heap size, which is positive then.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.siftUp`, `Cslib.Algorithms.WordRAM.Dijkstra.siftDown`: the
  two heap repairs.
* `Cslib.Algorithms.WordRAM.Dijkstra.extractMin`: removal of the root of the heap.
* `Cslib.Algorithms.WordRAM.Dijkstra.pushNew`: insertion of a newly discovered vertex into the
  heap.
* `Cslib.Algorithms.WordRAM.Dijkstra.relaxEdges`: the scan of the edges out of a vertex.
* `Cslib.Algorithms.WordRAM.Dijkstra.heapDijkstra`: Dijkstra's algorithm with a binary heap.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM

/-! ### Register names -/

namespace HeapReg

/-- The constant `0`. -/
abbrev zero : Fin 27 := 0
/-- The constant `1`. -/
abbrev one : Fin 27 := 1
/-- The constant `2`. -/
abbrev two : Fin 27 := 2
/-- The constant `3`. -/
abbrev three : Fin 27 := 3
/-- The number `n` of vertices. -/
abbrev n : Fin 27 := 4
/-- The address `n + 4` of the first edge. -/
abbrev eb : Fin 27 := 5
/-- The base `Db` of the distance words. -/
abbrev db : Fin 27 := 6
/-- The base `Db + n` of the heap. -/
abbrev hb : Fin 27 := 7
/-- The base `Db + 2 n + 1` of the positions. -/
abbrev pb : Fin 27 := 8
/-- The size of the heap. -/
abbrev sz : Fin 27 := 9
/-- The vertex of the current round. -/
abbrev u : Fin 27 := 10
/-- The distance word of `u`. -/
abbrev best : Fin 27 := 11
/-- The index of the current edge. -/
abbrev j : Fin 27 := 12
/-- The index past the last edge out of `u`. -/
abbrev jend : Fin 27 := 13
/-- The target of the current edge. -/
abbrev tv : Fin 27 := 14
/-- The weight of the current edge. -/
abbrev tc : Fin 27 := 15
/-- The candidate distance word through the current edge. -/
abbrev cand : Fin 27 := 16
/-- The distance word of the target. -/
abbrev dv : Fin 27 := 17
/-- The heap position being repaired. -/
abbrev k : Fin 27 := 18
/-- The parent or the chosen child of position `k`. -/
abbrev p : Fin 27 := 19
/-- The vertex at position `k`. -/
abbrev vk : Fin 27 := 20
/-- The vertex at position `p`. -/
abbrev vp : Fin 27 := 21
/-- The key of `vk`. -/
abbrev dk : Fin 27 := 22
/-- The key of `vp`. -/
abbrev dp : Fin 27 := 23
/-- A scratch register, mostly for addresses. -/
abbrev t : Fin 27 := 24
/-- The heap size plus one, during a sift-down. -/
abbrev szp : Fin 27 := 25
/-- The left child `2 k` of position `k`, during a sift-down. -/
abbrev l : Fin 27 := 26

end HeapReg

open HeapReg

/-- Swap the heap entries at positions `k` and `p`, which hold the vertices `vk` and `vp`, and
update their positions. -/
def swapCode : Code .exact 27 := ram_exact[
  t ← hb + k; *t ← vp;
  t ← hb + p; *t ← vk;
  t ← pb + vp; *t ← k;
  t ← pb + vk; *t ← p ]

/-- One step of the sift-up: swap position `k` with its parent if the parent has the larger key,
and otherwise stop by setting `k` to `1`. -/
def siftUpBody : Code .exact 27 := ram_exact[
  p ← k / two;
  t ← hb + k; vk ← *t; t ← db + vk; dk ← *t;
  t ← hb + p; vp ← *t; t ← db + vp; dp ← *t;
  if dk < dp then [ ⟪swapCode⟫; k ← p ] else [ k ← one ] ]

/-- **Sift-up** from position `k`. -/
def siftUp : Code .exact 27 := ram_exact[ while one < k do [ ⟪siftUpBody⟫ ] ]

/-- The first half of a sift-down step: put the child of least key of position `k`, among the
left child `l` and the right child `l + 1` if it is in the heap, in `p`, its vertex in `vp` and
its key in `dp`. -/
def siftDownChoose : Code .exact 27 := ram_exact[
  p ← l;
  t ← hb + l; vp ← *t; t ← db + vp; dp ← *t;
  t ← l + one;
  if t < szp then [
    t ← hb + t; vk ← *t; t ← db + vk; dk ← *t;
    if dk < dp then [ p ← l + one; vp ← vk; dp ← dk ] else [ p ← p ] ] else [ p ← p ] ]

/-- The second half of a sift-down step: swap position `k` with the position `p` chosen by
`siftDownChoose` and move to it if its key `dp` is smaller, and otherwise stop by setting `l` to
`szp`. -/
def siftDownSink : Code .exact 27 := ram_exact[
  t ← hb + k; vk ← *t; t ← db + vk; dk ← *t;
  if dp < dk then [ ⟪swapCode⟫; k ← p; l ← k + k ] else [ l ← szp ] ]

/-- One step of the sift-down: swap position `k` with its child of least key if that key is
smaller, and otherwise stop by setting `l` to `szp`. -/
def siftDownBody : Code .exact 27 := ram_exact[ ⟪siftDownChoose⟫; ⟪siftDownSink⟫ ]

/-- **Sift-down** from position `k`. -/
def siftDown : Code .exact 27 := ram_exact[
  l ← k + k; szp ← sz + one;
  while l < szp do [ ⟪siftDownBody⟫ ] ]

/-- **Extract-min**: remove the root `u` of the heap, with distance word `best`, move the last
entry to the root and sift it down. -/
def extractMin : Code .exact 27 := ram_exact[
  t ← hb + one; u ← *t;
  t ← db + u; best ← *t;
  t ← pb + u; *t ← zero;
  t ← hb + sz; vk ← *t;
  sz ← sz - one;
  if zero < sz then [
    t ← hb + one; *t ← vk;
    t ← pb + vk; *t ← one;
    k ← one; ⟪siftDown⟫ ] else [ k ← k ] ]

/-- **Insert** the vertex `tv`, whose distance word is already set, as a new last entry, and sift
it up. -/
def pushNew : Code .exact 27 := ram_exact[
  sz ← sz + one;
  t ← hb + sz; *t ← tv;
  t ← pb + tv; *t ← sz;
  k ← sz; ⟪siftUp⟫ ]

/-- Relax edge `j` out of `u`: read its target `tv` and weight `tc`, and if `best + tc` improves
the distance word of `tv`, store it and insert `tv` into the heap or move it up (decrease-key). -/
def edgeBody : Code .exact 27 := ram_exact[
  t ← j + j; t ← t + eb; tv ← *t; t ← t + one; tc ← *t; j ← j + one;
  cand ← best + tc;
  t ← db + tv; dv ← *t;
  if dv = zero then [ *t ← cand; ⟪pushNew⟫ ] else [
    if cand < dv then [ *t ← cand; t ← pb + tv; k ← *t; ⟪siftUp⟫ ] else [ t ← t ] ] ]

/-- The scan of the edges `j, …, jend - 1`. -/
def relaxEdges : Code .exact 27 := ram_exact[ while j < jend do [ ⟪edgeBody⟫ ] ]

/-- One round: extract the root `u` of the heap and relax the edges out of it, which are those
between its offset, at address `u + 3`, and the next offset. -/
def heapRound : Code .exact 27 := ram_exact[
  ⟪extractMin⟫;
  t ← u + three; j ← *t;
  t ← t + one; jend ← *t;
  ⟪relaxEdges⟫ ]

/-- The setup: load the constants and `n`, compute the array bases from `n` and the number `m`
of edges, which is the offset at address `n + 3`, give the source the distance word `1` and make
it the only heap entry. -/
def heapSetup : Code .exact 27 := ram_exact[
  one ← #1; two ← #2; three ← #3;
  t ← #1; n ← *t;
  t ← #2; u ← *t;
  t ← n + three; t ← *t;
  db ← t + t; db ← db + n; db ← db + three; db ← db + one;
  eb ← n + three; eb ← eb + one;
  hb ← db + n; pb ← hb + n; pb ← pb + one;
  t ← db + u; *t ← one;
  t ← hb + one; *t ← u;
  t ← pb + u; *t ← one;
  sz ← one ]

/-- **Dijkstra's algorithm with a binary heap**, on adjacency lists. -/
def heapDijkstra : Code .exact 27 := ram_exact[ ⟪heapSetup⟫; while zero < sz do [ ⟪heapRound⟫ ] ]

end Cslib.Algorithms.WordRAM.Dijkstra

end
