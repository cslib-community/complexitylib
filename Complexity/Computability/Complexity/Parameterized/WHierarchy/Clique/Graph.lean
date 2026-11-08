/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Unbounded.Certificate
public import Complexity.Computability.Complexity.Parameterized.WHierarchy
public import Complexity.Computability.Complexity.Parameterized.WHierarchy.Clique.Bracket
public import Complexity.Computability.Complexity.Problems.Clique.OfAdj
public import Complexity.Foundations.Data.List.ListsUpTo

/-!
# The graph of a circuit of weft one

This file builds, from a circuit of weft at most `1` and depth at most `d` and a weight `k`, a
graph and a clique size (`WCS.toClique`), and shows that the graph has a clique of that size
exactly when the circuit has a satisfying input with `k` ones (`WCS.toClique_mem_Clique_iff`).
This is the graph construction behind the `W[1]`-hardness of `Clique`
[Cygan et al., Chapter 13][CyganEtAl2015] [DowneyFellows1999], in a form adapted to the
certificates of `Cslib.Circuits.Boolean.Unbounded.WeftOne`.

Write `n` for the number of inputs and `kk = min (n + 1) k`. The vertices are of two kinds.

* A *certificate*: at most `2 ^ d` wire-value claims that are valid for the output
  (`WeftOne.claimsValid`).
* A *bracket*: at most `2 ^ (d + 1)` pairs `(j, s)` with `j < kk` and `s < n`, read as "the
  `j`-th selected input is `s`" (`WCS.ToClique.know`).

A certificate is adjacent to a bracket when Kleene evaluation from the partial input that the
bracket describes refutes no check of a claim. Two brackets are adjacent when they are consistent
(`WCS.ToClique.consistent`) and have different lists of indices. The clique size is one more than
the number of lists of at most `2 ^ (d + 1)` indices below `kk`.

A satisfying input with `k` ones gives a clique: its correct certificate, and the correct bracket
of every list of indices. Conversely, a clique of that size has one certificate and one bracket
for each list of indices. The brackets of the one-index lists select `k` increasing positions,
and every check of a claim is at small depth, so it is determined by at most `2 ^ d` inputs
(`WeftOne.exists_determining`), which the bracket of some list of at most `2 ^ (d + 1)` indices
describes (`WCS.ToClique.exists_cover`). The certificate is adjacent to that bracket, so the check
holds on the selected input, which therefore satisfies the circuit.

## Main definitions

* `Cslib.Complexity.WCS.ToClique.vertices`, `Cslib.Complexity.WCS.ToClique.vadj`: the vertices
  and adjacency of the graph.
* `Cslib.Complexity.WCS.toClique`: the graph and clique size of a circuit and a weight.

## Main results

* `Cslib.Complexity.WCS.toClique_mem_Clique_iff`: the graph has a clique of the size exactly
  when the circuit has a satisfying input with `k` ones.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Chapter 13][CyganEtAl2015]
* [R. G. Downey, M. R. Fellows, *Parameterized Complexity*][DowneyFellows1999]
-/

@[expose] public section

namespace Cslib.Complexity.WCS

open Circuits Circuits.Boolean Circuits.Boolean.Unbounded

namespace ToClique

/-! ### The construction -/

/-- The wire-value pairs of the wires of a gate list with `L` gates from `n` inputs. -/
def claimUniverse (n L : ℕ) : List (ℕ × Bool) :=
  (List.range (n + L)).flatMap fun w => [(w, true), (w, false)]

/-- The certificates: lists of at most `2 ^ d` wire-value pairs that are valid for output `o`. -/
def certs (d n : ℕ) (gates : List (Unbounded.Op × List ℕ)) (o : ℕ) : List (List (ℕ × Bool)) :=
  ((claimUniverse n gates.length).listsUpTo (2 ^ d)).filter (WeftOne.claimsValid d n gates o)

/-- The index-position pairs: `(j, s)` with `j < kk` and `s < n`. -/
def pairs (n kk : ℕ) : List (ℕ × ℕ) :=
  (List.range kk).flatMap fun j => (List.range n).map (j, ·)

/-- The brackets: lists of at most `2 ^ (d + 1)` index-position pairs. -/
def brackets (d n kk : ℕ) : List (List (ℕ × ℕ)) :=
  (pairs n kk).listsUpTo (2 ^ (d + 1))

/-- The index lists: lists of at most `2 ^ (d + 1)` indices below `kk`. -/
def classes (d kk : ℕ) : List (List ℕ) :=
  (List.range kk).listsUpTo (2 ^ (d + 1))

/-- The partial input that a bracket describes. -/
def knowList (n kk : ℕ) (P : List (ℕ × ℕ)) : List (Option Bool) :=
  (List.range n).map (know kk P)

/-- A bracket refutes a list of claims when Kleene evaluation from the partial input it describes
finds a check of a claim false. -/
def refutes (n kk : ℕ) (gates : List (Unbounded.Op × List ℕ)) (cl : List (ℕ × Bool))
    (P : List (ℕ × ℕ)) : Bool :=
  (cl.flatMap (WeftOne.claimChecks n gates)).any fun e =>
    (kleeneEval (knowList n kk P) gates).getD e.1 none == some (!e.2)

/-- A vertex: a list of claims tagged `true`, or a bracket tagged `false`. -/
abbrev Vertex : Type := Bool × (List (ℕ × Bool) × List (ℕ × ℕ))

/-- The vertices: the certificates, then the brackets. -/
def vertices (d n kk : ℕ) (gates : List (Unbounded.Op × List ℕ)) (o : ℕ) : List Vertex :=
  (certs d n gates o).map (fun cl => (true, cl, [])) ++
    (brackets d n kk).map (fun P => (false, [], P))

/-- Adjacency: a certificate and a bracket that does not refute it, or two consistent brackets
with different lists of indices. -/
def vadj (n kk : ℕ) (gates : List (Unbounded.Op × List ℕ)) (v w : Vertex) : Bool :=
  if v.1 then !w.1 && !refutes n kk gates v.2.1 w.2.2
  else !w.1 && (v.2.2.map Prod.fst != w.2.2.map Prod.fst) && consistent v.2.2 w.2.2

/-- The graph of a gate list from `n` inputs with output `o`, for depth `d` and weight `k`. -/
def graph (d n : ℕ) (gates : List (Unbounded.Op × List ℕ)) (o k : ℕ) : Graph :=
  Graph.ofAdj (vertices d n (min (n + 1) k) gates o) (vadj n (min (n + 1) k) gates)

/-- The clique size for depth `d`, `n` inputs and weight `k`. -/
def size (d n k : ℕ) : ℕ :=
  (classes d (min (n + 1) k)).length + 1

end ToClique

open ToClique

/-- **The graph of a circuit of weft one and a weight**, with its clique size. -/
def toClique {d : ℕ} (x : WeftCircuit 1 d × ℕ) : Graph × ℕ :=
  (graph d x.1.1.1 x.1.1.2.code.1 (x.1.1.2.outputs 0).toNat x.2, size d x.1.1.1 x.2)

end Cslib.Complexity.WCS
