/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.BipartiteMatching
public import Cslib.Computability.Languages.Slice
import Mathlib.Data.List.GetD

/-!
# Bipartite perfect matching as a language

A word `w : List Bool` of length `n * n` is read as the adjacency matrix of a subgraph of the
complete bipartite graph `K_{n,n}`, row by row: the left vertex `u` and the right vertex `v` are
adjacent when bit `v + n * u` of `w` is one (`Cslib.Complexity.BipartitePerfectMatching.graph`).
This is the numbering `finProdFinEquiv` used by the monotone circuit lower bound for perfect
matching, so the slice of the language at length `n * n` is exactly the Boolean function
`Cslib.Circuits.bipartitePerfectMatching n`
(`Cslib.Complexity.BipartitePerfectMatching.slice_mul_self`). Words whose length is not a square
are rejected. Every slice is monotone (`Cslib.Complexity.BipartitePerfectMatching.monotone_slice`):
adding edges keeps a perfect matching, and the slices at non-square lengths are constant.

## Main definitions

* `Cslib.Complexity.BipartitePerfectMatching.adj`,
  `Cslib.Complexity.BipartitePerfectMatching.graph`: the adjacency matrix and the bipartite graph
  of a word.
* `Cslib.Complexity.BipartitePerfectMatching`: the words that encode a bipartite graph with a
  perfect matching.

## Main results

* `Cslib.Complexity.BipartitePerfectMatching.slice_mul_self`: the slice at length `n * n` is
  `Cslib.Circuits.bipartitePerfectMatching n`.
* `Cslib.Complexity.BipartitePerfectMatching.monotone_slice`: every slice is monotone.

## References

* [A. A. Razborov, *Lower bounds on monotone complexity of the logical permanent*][Razborov1985a]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

public section

namespace Cslib.Complexity

namespace BipartitePerfectMatching

/-- Entry `(u, v)` of the `n × n` matrix stored row by row in the word `w`: bit `v + n * u` of `w`,
read as zero when `w` is too short. -/
@[expose] def adj (w : List Bool) (n u v : ℕ) : Bool := w.getD (v + n * u) false

/-- The bipartite graph on `n` left and `n` right vertices read from the word `w`: the left vertex
`u` and the right vertex `v` are adjacent when bit `v + n * u` of `w` is one (`adj`). -/
@[expose] def graph (w : List Bool) (n : ℕ) : Fin n × Fin n → Bool :=
  fun e => adj w n e.1 e.2

end BipartitePerfectMatching

/-- **Bipartite perfect matching**: the words of square length `n * n` whose row-major `n × n`
adjacency matrix (`BipartitePerfectMatching.graph`) has a perfect matching. -/
@[expose] def BipartitePerfectMatching : Language Bool :=
  {w | ∃ n, n * n = w.length ∧
    Circuits.BipartiteMatching.HasPerfectMatching (BipartitePerfectMatching.graph w n)}

namespace BipartitePerfectMatching

/-- Membership unfolds to a square length `n * n` and a perfect matching in `graph w n`. -/
theorem mem_iff {w : List Bool} :
    w ∈ BipartitePerfectMatching ↔ ∃ n, n * n = w.length ∧
      Circuits.BipartiteMatching.HasPerfectMatching (graph w n) :=
  Iff.rfl

/-- On a word of length `n * n`, `graph` is the graph `Cslib.Circuits.BipartiteMatching.graph` of
the corresponding bit string. -/
theorem graph_ofFn {n : ℕ} (x : Fin (n * n) → Bool) :
    graph (List.ofFn x) n = Circuits.BipartiteMatching.graph x := by
  funext e
  have he : e.2.val + n * e.1.val < n * n := (finProdFinEquiv e).isLt
  rw [graph, adj, Circuits.BipartiteMatching.graph, List.getD_eq_getElem _ _ (by simpa using he),
    List.getElem_ofFn]
  rfl

/-- A word of length `n * n` is in the language exactly when its graph on `n + n` vertices has a
perfect matching. -/
theorem mem_iff_of_length_eq {w : List Bool} {n : ℕ} (hw : w.length = n * n) :
    w ∈ BipartitePerfectMatching ↔ Circuits.BipartiteMatching.HasPerfectMatching (graph w n) := by
  refine ⟨fun ⟨m, hm, h⟩ => ?_, fun h => ⟨n, hw.symm, h⟩⟩
  obtain rfl : m = n := Nat.mul_self_inj.mp (hm.trans hw)
  exact h

/-- **The slice at length `n * n` is perfect matching** in subgraphs of `K_{n,n}`, numbered as in
the monotone lower bound. -/
theorem slice_mul_self (n : ℕ) :
    BipartitePerfectMatching.slice (n * n) = Circuits.bipartitePerfectMatching n := by
  funext x
  rw [Bool.eq_iff_iff, Language.slice_eq_true_iff,
    mem_iff_of_length_eq (List.length_ofFn (f := x)), graph_ofFn,
    Circuits.bipartitePerfectMatching_eq_true_iff]

/-- At a length that is not a square, the slice is constantly false. -/
theorem slice_eq_false_of_ne {m : ℕ} (hm : ∀ n, n * n ≠ m) (x : Fin m → Bool) :
    BipartitePerfectMatching.slice m x = false := by
  rw [Bool.eq_false_iff, ne_eq, Language.slice_eq_true_iff, mem_iff]
  rintro ⟨n, hn, -⟩
  exact hm n (hn.trans (List.length_ofFn (f := x)))

/-- **Every slice is monotone**: adding edges keeps a perfect matching, and the slices at
non-square lengths are constant. -/
theorem monotone_slice (m : ℕ) : Monotone (BipartitePerfectMatching.slice m) := by
  by_cases hm : ∃ n, n * n = m
  · obtain ⟨n, rfl⟩ := hm
    rw [slice_mul_self]
    exact Circuits.monotone_bipartitePerfectMatching
  · intro x y _
    rw [slice_eq_false_of_ne (fun n hn => hm ⟨n, hn⟩) x]
    exact Bool.false_le _

end BipartitePerfectMatching

end Cslib.Complexity
