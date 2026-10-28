/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.NP.Closure
import Complexity.Computability.Complexity.Problems.Hamiltonian
import Complexity.Tactic.PolyTime

/-!
# Hamiltonian path and cycle tests

Concrete, boundary, and `fun_prop` checks for the verifiers of `DirHamPath`,
`DirHamCycle`, `HamPath` and `HamCycle`.
-/

namespace ComplexityTests.NPCompleteGraphs.Hamiltonian

open Cslib.Complexity Turing.MultiTapeTM

/-! ### Headline complexity class results -/

example : DirHamPath ∩ HamPath ∈ NP (encPair encGraph (encPair encNat encNat)) :=
  inter_mem_NP DirHamPath.mem_NP HamPath.mem_NP

example : DirHamCycle ∪ HamCycle ∈ NP encGraph :=
  union_mem_NP DirHamCycle.mem_NP HamCycle.mem_NP

-- Certificates are quadratic in the encoded instance: every positive instance has a witness of
-- length `len ^ 2`.
example {x : Graph × ℕ × ℕ} (hx : x ∈ DirHamPath) :
    ∃ w : List Bool,
      w.length = (encPair encGraph (encPair encNat encNat) x).length ^ 2 ∧
        DirHamPath.verifier (x, w) = true := by
  simpa using (DirHamPath.isVerifier x).mp hx

example {G : Graph} (hG : G ∈ HamCycle) :
    ∃ w : List Bool,
      w.length = (encGraph G).length ^ 2 ∧ HamCycle.verifier (G, w) = true := by
  simpa using (HamCycle.isVerifier G).mp hG

/-! ### Compositional `fun_prop` synthesis -/

example : ComputableInPolyTime DirHamPath.verifier
    (encPair (encPair encGraph (encPair encNat encNat)) encBits) encBool := by
  fun_prop

example : ComputableInPolyTime DirHamCycle.verifier (encPair encGraph encBits) encBool := by
  fun_prop

example : ComputableInPolyTime HamPath.verifier
    (encPair (encPair encGraph (encPair encNat encNat)) encBits) encBool := by
  fun_prop

example : ComputableInPolyTime HamCycle.verifier (encPair encGraph encBits) encBool := by
  fun_prop

example : ComputableInPolyTime (fun x : List ℕ × List Bool => Graph.decodeVertexList x.1 x.2)
    (encPair (encList encNat) encBits) (encList encNat) := by
  fun_prop

/-! ### Decoding certificates -/

-- A certificate naming the list `p` of vertices of `V`: one block of `V.length` bits for each
-- entry of `p`, whose number of set bits is the first position of the entry in `V`.
private def certificate (V p : List ℕ) : List Bool :=
  p.flatMap fun v => (List.range V.length).map fun c => decide (c < V.idxOf v)

example : Graph.decodeVertexList [3, 5, 7] (certificate [3, 5, 7] [7, 3, 5]) = [7, 3, 5] := rfl

-- One block for each distinct vertex; trailing bits are ignored.
example : Graph.decodeVertexList [3, 5, 3] (certificate [3, 5, 3] [5, 3] ++ [true, true]) =
    [5, 3] := rfl

-- Decoding is total: missing bits read as `false`, and a block with all bits set names the
-- fallback vertex `0`.
example : Graph.decodeVertexList [3, 5, 7] [] = [3, 3, 3] := rfl
example : Graph.decodeVertexList [3, 5] [true, true, false, true] = [0, 5] := rfl

-- The executable list tests.
example : Graph.enumeratesBool [3, 5, 3] [5, 3] = true := rfl
example : Graph.enumeratesBool [3, 5, 3] [5, 3, 5] = false := rfl
example : Graph.enumeratesBool [3, 5] [5, 3, 0] = false := rfl
example : Graph.enumeratesBool [3, 5] [5] = false := rfl
example : Graph.chainBool (fun u v => decide (v = u + 1)) [2, 3, 4] = true := rfl
example : Graph.chainBool (fun u v => decide (v = u + 1)) [2, 4] = false := rfl
example : Graph.cycleChainBool (fun u v => decide (v = u + 1)) [2, 3, 4] = false := rfl
example : Graph.cycleChainBool (fun u v => decide (v % 3 = (u + 1) % 3)) [2, 3, 4] = true := rfl
example : Graph.cycleChainBool (fun _ _ => false) [] = true := rfl
example : Graph.cycleChainBool (fun u v => decide (u = v)) [7] = true := rfl

/-! ### Directed Hamiltonian paths -/

private def dpath : Graph := ([0, 1, 2], [(0, 1), (1, 2)])

example : DirHamPath.verifier ((dpath, 0, 2), certificate dpath.1 [0, 1, 2]) = true := rfl
-- Arcs are directed.
example : DirHamPath.verifier ((dpath, 2, 0), certificate dpath.1 [2, 1, 0]) = false := rfl
-- Wrong endpoints, a repeated vertex, and a missing arc are rejected.
example : DirHamPath.verifier ((dpath, 0, 1), certificate dpath.1 [0, 1, 2]) = false := rfl
example : DirHamPath.verifier ((dpath, 0, 2), certificate dpath.1 [0, 1, 1]) = false := rfl
example : DirHamPath.verifier ((dpath, 1, 2), certificate dpath.1 [1, 0, 2]) = false := rfl

example : (dpath, 0, 2) ∈ DirHamPath :=
  ⟨[0, 1, 2], by decide, fun v => by simp [dpath], rfl, rfl, by simp [dpath]⟩

-- An undeclared endpoint is rejected.
example : DirHamPath.verifier ((dpath, 0, 9), certificate dpath.1 [0, 1, 2]) = false := rfl

example : (dpath, 0, 9) ∉ DirHamPath := by
  rintro ⟨p, -, hmem, -, ht, -⟩
  have := (hmem 9).1 (List.mem_of_getLast? ht)
  simp [dpath] at this

-- `s = t` on a one-vertex graph is accepted.
example : DirHamPath.verifier (((([5], []), 5, 5)), [false]) = true := rfl

example : (([5], []), 5, 5) ∈ DirHamPath :=
  ⟨[5], by decide, fun v => by simp, rfl, rfl, by simp⟩

-- The empty graph has no Hamiltonian path.
example : DirHamPath.verifier ((([], []), 0, 0), []) = false := rfl

example : (([], []), 0, 0) ∉ DirHamPath := by
  rintro ⟨p, -, hmem, hs, -⟩
  have := (hmem 0).1 (List.mem_of_head? hs)
  simp at this

-- Duplicate vertex entries count once.
example : DirHamPath.verifier ((([0, 1, 0], [(0, 1)]), 0, 1), certificate [0, 1, 0] [0, 1]) =
    true := rfl

-- Arcs with an undeclared endpoint are never used.
private def detour : Graph := ([0, 1], [(0, 7), (7, 1)])

example : DirHamPath.verifier ((detour, 0, 1), certificate detour.1 [0, 1]) = false := rfl

example : (detour, 0, 1) ∉ DirHamPath := by
  rintro ⟨p, hnd, hmem, hs, ht, hch⟩
  have hlen := ((List.perm_ext_iff_of_nodup hnd (by decide : [0, 1].Nodup)).2 hmem).length_eq
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hlen
  simp only [List.head?_cons, Option.some.injEq] at hs
  simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at ht
  subst hs ht
  simp [detour] at hch

/-! ### Directed Hamiltonian cycles -/

private def dtriangle : Graph := ([0, 1, 2], [(0, 1), (1, 2), (2, 0)])

example : DirHamCycle.verifier (dtriangle, certificate dtriangle.1 [0, 1, 2]) = true := rfl
example : DirHamCycle.verifier (dtriangle, certificate dtriangle.1 [1, 2, 0]) = true := rfl
example : DirHamCycle.verifier (dtriangle, certificate dtriangle.1 [0, 2, 1]) = false := rfl
-- The closing arc is checked: the path graph has no Hamiltonian cycle.
example : DirHamCycle.verifier (dpath, certificate dpath.1 [0, 1, 2]) = false := rfl

-- Two vertices need arcs in both directions.
example : DirHamCycle.verifier (([0, 1], [(0, 1), (1, 0)]), certificate [0, 1] [0, 1]) = true :=
  rfl
example : DirHamCycle.verifier (([0, 1], [(0, 1)]), certificate [0, 1] [0, 1]) = false := rfl

-- A single vertex with a self-loop has a directed Hamiltonian cycle; without it, it has none.
example : DirHamCycle.verifier (([0], [(0, 0)]), [false]) = true := rfl
example : DirHamCycle.verifier (([0], []), [false]) = false := rfl

example : ([0], [(0, 0)]) ∈ DirHamCycle :=
  ⟨[0], by decide, fun v => by simp, by simp, by simp⟩

-- The empty graph has no directed Hamiltonian cycle.
example : DirHamCycle.verifier (([], []), []) = false := rfl

example : ([], []) ∉ DirHamCycle := by
  rintro ⟨p, -, hmem, hne, -⟩
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil p hne
  simpa using (hmem a).1 ha

/-! ### Undirected Hamiltonian paths -/

example : HamPath.verifier ((dpath, 0, 2), certificate dpath.1 [0, 1, 2]) = true := rfl
-- Edges are undirected.
example : HamPath.verifier ((dpath, 2, 0), certificate dpath.1 [2, 1, 0]) = true := rfl
example : HamPath.verifier ((dpath, 1, 2), certificate dpath.1 [1, 0, 2]) = false := rfl

example : (dpath, 2, 0) ∈ HamPath := by
  rw [mem_HamPath_iff]
  refine ⟨[2, 1, 0], by decide, fun _ => (by decide : [2, 1, 0].Perm dpath.1).mem_iff, rfl, rfl, ?_⟩
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
  exact ⟨(Graph.adjBool_eq_true_iff _ _ _).1 rfl, (Graph.adjBool_eq_true_iff _ _ _).1 rfl⟩

-- An undeclared endpoint is rejected.
example : HamPath.verifier ((dpath, 9, 2), certificate dpath.1 [0, 1, 2]) = false := rfl

example : (dpath, 9, 2) ∉ HamPath := by
  rintro ⟨hs, -⟩
  simp [dpath] at hs

-- `s = t` on a one-vertex graph is accepted.
example : HamPath.verifier (((([5], []), 5, 5)), [false]) = true := rfl

example : (([5], []), 5, 5) ∈ HamPath := by
  rw [mem_HamPath_iff]
  exact ⟨[5], by decide, fun v => by simp, rfl, rfl, by simp⟩

-- The empty graph has no Hamiltonian path.
example : HamPath.verifier ((([], []), 0, 0), []) = false := rfl

example : (([], []), 0, 0) ∉ HamPath := by
  rintro ⟨hs, -⟩
  simp at hs

-- Duplicate vertex entries count once.
example : HamPath.verifier ((([0, 1, 0], [(1, 0)]), 0, 1), certificate [0, 1, 0] [0, 1]) = true :=
  rfl

-- Edges with an undeclared endpoint are never used.
example : HamPath.verifier ((detour, 0, 1), certificate detour.1 [0, 1]) = false := rfl

example : (detour, 0, 1) ∉ HamPath := by
  rw [mem_HamPath_iff]
  rintro ⟨p, hnd, hmem, hs, ht, hch⟩
  have hlen := ((List.perm_ext_iff_of_nodup hnd (by decide : [0, 1].Nodup)).2 hmem).length_eq
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hlen
  simp only [List.head?_cons, Option.some.injEq] at hs
  simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at ht
  subst hs ht
  rw [List.isChain_pair, ← Graph.adjBool_eq_true_iff] at hch
  exact absurd hch (by decide)

/-! ### Undirected Hamiltonian cycles -/

example : HamCycle.verifier (dtriangle, certificate dtriangle.1 [0, 1, 2]) = true := rfl
-- Edges are undirected.
example : HamCycle.verifier (dtriangle, certificate dtriangle.1 [0, 2, 1]) = true := rfl
-- The path graph has a Hamiltonian path but no Hamiltonian cycle.
example : HamCycle.verifier (dpath, certificate dpath.1 [0, 1, 2]) = false := rfl

example : dtriangle ∈ HamCycle := by
  rw [mem_HamCycle_iff]
  refine ⟨[0, 1, 2], by decide, fun v => by simp [dtriangle], le_rfl, ?_⟩
  rw [← Graph.cycleChainBool_eq_true_iff (Graph.adjBool_eq_true_iff dtriangle)]
  rfl

-- A Hamiltonian cycle needs three vertices: one or two vertices never suffice, even with a
-- self-loop or with edges in both directions.
example : HamCycle.verifier (([0], [(0, 0)]), [false]) = false := rfl
example : HamCycle.verifier (([0, 1], [(0, 1), (1, 0)]), certificate [0, 1] [0, 1]) = false := rfl

example : ([0], [(0, 0)]) ∉ HamCycle := by
  rw [mem_HamCycle_iff]
  rintro ⟨p, hnd, hmem, hlen, -⟩
  have := ((List.perm_ext_iff_of_nodup hnd (by decide : [0].Nodup)).2 hmem).length_eq
  simp only [List.length_singleton] at this
  omega

-- The empty graph has no Hamiltonian cycle.
example : HamCycle.verifier (([], []), []) = false := rfl

example : ([], []) ∉ HamCycle := by
  rw [mem_HamCycle_iff]
  rintro ⟨p, -, hmem, hlen, -⟩
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil p (List.ne_nil_of_length_pos (by omega))
  simpa using (hmem a).1 ha

-- Duplicate vertex entries count once.
example : HamCycle.verifier (([0, 1, 2, 0], [(0, 1), (1, 2), (2, 0)]),
    certificate [0, 1, 2, 0] [0, 1, 2]) = true := rfl

end ComplexityTests.NPCompleteGraphs.Hamiltonian
