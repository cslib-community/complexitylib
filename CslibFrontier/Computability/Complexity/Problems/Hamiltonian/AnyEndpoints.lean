/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Hamiltonian.Directed
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Directed Hamiltonian paths between unspecified endpoints

`DirHamPathAny` is the set of directed graphs that have a Hamiltonian path, with no endpoints
given: the language dHAMPATH of [Arora and Barak, draft, Theorem 2.18][AroraBarak07], whose
instances are graphs alone. `DirHamPath` instead fixes the start and the end vertex.

**Empty-graph convention.** A Hamiltonian path is a *nonempty* list of the declared vertices, so a
graph without declared vertices is not in `DirHamPathAny`
(`DirHamPathAny.notMem_of_vertices_eq_nil`). Equivalently, `G ∈ DirHamPathAny` exactly when `G`
has a Hamiltonian path between some vertices `s` and `t` (`mem_DirHamPathAny_iff`). The reduction
below produces graphs with at least two vertices, so it does not depend on this convention.

**The reduction** `DirHamPath.toAny` shifts every vertex label by two and adds a source `0` with
the single arc `0 → s + 2` and a sink `1` with the single arc `t + 2 → 1`. No arc enters `0` and
no arc leaves `1`, so a Hamiltonian path of the new graph starts at `0`, ends at `1`, and in
between is a shifted Hamiltonian path of the old graph from `s` to `t`
(`DirHamPath.toAny_mem_iff`). Shifting rather than picking fresh labels keeps the reduction a
simple list map, and also handles arcs of the old graph with undeclared endpoints.

## Main definitions

* `Cslib.Complexity.DirHamPathAny`: graphs with a Hamiltonian path.
* `Cslib.Complexity.DirHamPath.toAny`: the reduction from `DirHamPath`.
* `Cslib.Complexity.DirHamPathAny.verifier`: its verifier.

## Main results

* `Cslib.Complexity.mem_DirHamPathAny_iff`: some endpoints exist.
* `Cslib.Complexity.DirHamPath.toAny_mem_iff`,
  `Cslib.Complexity.DirHamPath.computableInPolyTime_toAny`,
  `Cslib.Complexity.polyTimeReducible_DirHamPath_DirHamPathAny`: the reduction.
* `Cslib.Complexity.DirHamPathAny.mem_NP`, `Cslib.Complexity.DirHamPathAny_npHard`,
  `Cslib.Complexity.DirHamPathAny_npComplete`: `DirHamPathAny` is `NP`-complete.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft 2007][AroraBarak07]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-- The directed graphs with a Hamiltonian path between some vertices: a nonempty list of every
declared vertex exactly once whose consecutive vertices are joined by arcs
[Arora and Barak, draft, Theorem 2.18][AroraBarak07]. Graphs without declared vertices are not
members. -/
def DirHamPathAny : Set Graph :=
  {G | ∃ p : List ℕ, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ G.vertices) ∧ p ≠ [] ∧
    p.IsChain fun u v => (u, v) ∈ G.edges}

/-- A graph is in `DirHamPathAny` exactly when it has a Hamiltonian path between some vertices. -/
theorem mem_DirHamPathAny_iff {G : Graph} :
    G ∈ DirHamPathAny ↔ ∃ s t p, G.IsDirHamPath s t p := by
  constructor
  · rintro ⟨p, hnd, hcov, hne, hch⟩
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨a, _, _, hnd, hcov, rfl, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hch⟩
  · rintro ⟨s, t, p, hnd, hcov, hs, -, hch⟩
    exact ⟨p, hnd, hcov, by rintro rfl; simp at hs, hch⟩

namespace DirHamPathAny

/-- **Empty-graph convention**: a graph without declared vertices has no Hamiltonian path. -/
theorem notMem_of_vertices_eq_nil {G : Graph} (h : G.vertices = []) : G ∉ DirHamPathAny := by
  rintro ⟨p, -, hcov, hne, -⟩
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil p hne
  simpa [h] using (hcov v).1 hv

/-- The verifier for `DirHamPathAny`: decode a list of vertices from the certificate
(`Graph.decodeVertexList`) and check that it is nonempty, lists every declared vertex exactly
once, and that consecutive vertices are joined by arcs. -/
def verifier : Graph × List Bool → Bool :=
  Graph.verifyOrdering (fun G => G.vertices) fun G p =>
    decide (p ≠ []) && Graph.chainBool G.arcBool p

/-- `DirHamPathAny.verifier` verifies `DirHamPathAny` with certificates of length `n ^ 2` for
graphs of encoded length `n`. -/
theorem isVerifier : IsVerifier encGraph (Polynomial.X ^ 2) verifier DirHamPathAny :=
  Graph.isVerifier_verifyOrdering
    (P := fun (G : Graph) p => p ≠ [] ∧ p.IsChain fun u v => (u, v) ∈ G.edges)
    Graph.length_vertices_le_encGraph fun G p => by
      simp only [Bool.and_eq_true, decide_eq_true_eq,
        Graph.chainBool_eq_true_iff (Graph.arcBool_eq_true_iff G)]

/-- The `DirHamPathAny` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encGraph encBits) encBool := by
  have hproj : ComputableInPolyTime
      (fun q : ((Graph × List ℕ) × ℕ) × ℕ => ((q.1.1.1, q.1.2), q.2))
      (encPair (encPair (encPair encGraph (encList encNat)) encNat) encNat)
      (encPair (encPair encGraph encNat) encNat) := by
    fun_prop
  refine Graph.computableInPolyTime_verifyOrdering (by unfold encGraph; fun_prop)
    (bool_and' ?_ (Graph.computableInPolyTime_chainBool
      (Graph.computableInPolyTime_arcBool.comp hproj) (snd _ _)))
  simpa only [Function.comp_def, _root_.decide_not] using
    bool_not.comp ((snd _ _).decide_eq' (const []))

/-- `DirHamPathAny` belongs to `NP`. -/
theorem mem_NP : DirHamPathAny ∈ NP encGraph :=
  ⟨_, verifier, computableInPolyTime_verifier, isVerifier⟩

end DirHamPathAny

/-! ### The reduction from `DirHamPath` -/

/-- An element of a chain other than its first has a predecessor related to it. -/
private theorem exists_rel_of_mem_tail {R : ℕ → ℕ → Prop} :
    ∀ {p : List ℕ}, p.IsChain R → ∀ {x}, x ∈ p.tail → ∃ y, R y x
  | [], _, _, hx => by simp at hx
  | [_], _, _, hx => by simp at hx
  | a :: b :: l, h, x, hx => by
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨a, h.1⟩
    · exact exists_rel_of_mem_tail h.2 hx

/-- An element of a chain other than its last has a successor related to it. -/
private theorem exists_rel_of_mem_dropLast {R : ℕ → ℕ → Prop} {p : List ℕ} (h : p.IsChain R)
    {x : ℕ} (hx : x ∈ p.dropLast) : ∃ y, R x y := by
  have h' : p.reverse.IsChain (flip R) := List.isChain_reverse.mpr h
  rw [← List.mem_reverse, ← List.tail_reverse] at hx
  exact exists_rel_of_mem_tail h' hx

namespace DirHamPath

/-- The reduction from `DirHamPath` to `DirHamPathAny`: shift every vertex by two, and add a source
`0` with an arc to `s + 2` and a sink `1` with an arc from `t + 2`. -/
def toAny (x : PathInstance) : Graph :=
  ⟨0 :: 1 :: x.graph.vertices.map (· + 2),
    (0, x.source + 2) :: (x.target + 2, 1) :: x.graph.edges.map fun e => (e.1 + 2, e.2 + 2)⟩

private theorem mem_toAny_vertices {x : PathInstance} {v : ℕ} :
    v ∈ (toAny x).vertices ↔ v = 0 ∨ v = 1 ∨ ∃ w ∈ x.graph.vertices, w + 2 = v := by
  simp [toAny]

private theorem mem_toAny_edges {x : PathInstance} {u v : ℕ} :
    (u, v) ∈ (toAny x).edges ↔ (u = 0 ∧ v = x.source + 2) ∨ (u = x.target + 2 ∧ v = 1) ∨
      ∃ a b, (a, b) ∈ x.graph.edges ∧ a + 2 = u ∧ b + 2 = v := by
  simp [toAny]

/-- An arc of `toAny x` between shifted vertices is a shifted arc of `x.graph`. -/
private theorem shifted_edge {x : PathInstance} {a b : ℕ}
    (h : (a + 2, b + 2) ∈ (toAny x).edges) : (a, b) ∈ x.graph.edges := by
  rw [mem_toAny_edges] at h
  rcases h with ⟨h, -⟩ | ⟨-, h⟩ | ⟨a', b', h, ha, hb⟩
  · omega
  · omega
  · obtain rfl : a' = a := by omega
    obtain rfl : b' = b := by omega
    exact h

private theorem shift_injective : Function.Injective (· + 2 : ℕ → ℕ) :=
  fun _ _ h => by simpa using h

/-- **Correctness of `DirHamPath.toAny`.** -/
theorem toAny_mem_iff (x : PathInstance) : toAny x ∈ DirHamPathAny ↔ x ∈ DirHamPath := by
  constructor
  · rintro ⟨p, hnd, hcov, -, hch⟩
    -- no arc enters `0`, so `0` comes first
    have h0 : 0 ∉ p.tail := fun h => by
      obtain ⟨y, hy⟩ := exists_rel_of_mem_tail hch h
      rw [mem_toAny_edges] at hy
      omega
    -- no arc leaves `1`, so `1` comes last
    have h1 : 1 ∉ p.dropLast := fun h => by
      obtain ⟨y, hy⟩ := exists_rel_of_mem_dropLast hch h
      rw [mem_toAny_edges] at hy
      omega
    obtain ⟨r, rfl⟩ : ∃ r, p = 0 :: r := by
      cases p with
      | nil => simpa using (hcov 0).2 (by simp [toAny])
      | cons a r =>
        rcases List.mem_cons.mp ((hcov 0).2 (by simp [toAny])) with h | h
        · exact ⟨r, by rw [h]⟩
        · exact absurd h h0
    have hr : r ≠ [] := by
      rintro rfl
      simpa [toAny] using (hcov 1).2 (by simp [toAny])
    obtain ⟨m, rfl⟩ : ∃ m, r = m ++ [1] := by
      refine ⟨r.dropLast, ?_⟩
      have h1r : 1 ∈ r := by
        rcases List.mem_cons.mp ((hcov 1).2 (by simp [toAny])) with h | h
        · omega
        · exact h
      conv_lhs => rw [← List.dropLast_append_getLast hr]
      congr 2
      by_contra hne
      rw [← List.dropLast_append_getLast hr, List.mem_append, List.mem_singleton] at h1r
      rcases h1r with h | h
      · exact h1 (by rw [List.dropLast_cons_of_ne_nil hr]; exact List.mem_cons_of_mem _ h)
      · exact hne h.symm
    -- the vertices in between are shifted
    have hnd' := hnd
    rw [List.nodup_cons, List.mem_append, not_or, List.nodup_append] at hnd'
    have hm2 : ∀ v ∈ m, 2 ≤ v := fun v hv => by
      have hv0 : v ≠ 0 := by rintro rfl; exact hnd'.1.1 hv
      have hv1 : v ≠ 1 := by rintro rfl; exact hnd'.2.2.2 1 hv 1 (by simp) rfl
      omega
    obtain ⟨q, rfl⟩ : ∃ q, m = q.map (· + 2) :=
      ⟨m.map (· - 2), by
        rw [List.map_map]
        conv_lhs => rw [← List.map_id m]
        exact List.map_congr_left fun v hv => by
          change v = v - 2 + 2
          have := hm2 v hv
          omega⟩
    have hq : q ≠ [] := by
      rintro rfl
      have := hch
      simp only [List.map_nil, List.nil_append, List.isChain_cons_cons, mem_toAny_edges] at this
      omega
    have hchm := hch
    rw [← List.singleton_append, ← List.append_assoc, List.isChain_append, List.isChain_append]
      at hchm
    obtain ⟨⟨-, hmid, hfirst⟩, -, hlast⟩ := hchm
    refine ⟨q, (List.nodup_map_iff shift_injective).mp hnd'.2.1, fun v => ?_, ?_, ?_, ?_⟩
    · have := hcov (v + 2)
      simp only [List.mem_cons, List.mem_append, List.mem_map,
        mem_toAny_vertices, shift_injective.eq_iff, exists_eq_right] at this
      simpa [show v + 2 ≠ 0 by omega, show v + 2 ≠ 1 by omega, shift_injective.eq_iff] using this
    · obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hq
      have := hfirst 0 (by simp) (a + 2) (by simp)
      rw [mem_toAny_edges] at this
      simp only [List.head?_cons, Option.some.injEq]
      rcases this with ⟨-, h⟩ | ⟨h, -⟩ | ⟨_, _, -, h, -⟩ <;> omega
    · have := hlast (q.getLast hq + 2)
        (by
          rw [Option.mem_def, List.getLast?_append_of_ne_nil _ (by simpa using hq),
            List.getLast?_map, List.getLast?_eq_some_getLast hq]
          rfl) 1 (by simp)
      rw [mem_toAny_edges] at this
      rw [List.getLast?_eq_some_getLast hq, Option.some.injEq]
      rcases this with ⟨h, -⟩ | ⟨h, -⟩ | ⟨_, _, -, -, h⟩ <;> omega
    · rw [List.isChain_map] at hmid
      exact hmid.imp fun a b h => shifted_edge h
  · rintro ⟨q, hnd, hcov, hs, ht, hch⟩
    have hq : q ≠ [] := by rintro rfl; simp at hs
    refine ⟨0 :: (q.map (· + 2) ++ [1]), ?_, fun v => ?_, List.cons_ne_nil _ _, ?_⟩
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr
        ⟨(List.nodup_map_iff shift_injective).mpr hnd, List.nodup_singleton _, ?_⟩⟩
      · rw [List.mem_append, List.mem_singleton, List.mem_map]
        rintro (⟨_, _, h⟩ | h) <;> omega
      · intro a ha b hb
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
        rw [List.mem_singleton] at hb
        omega
    · rw [mem_toAny_vertices]
      simp only [List.mem_cons, List.mem_append, List.mem_map, hcov, List.not_mem_nil, or_false]
      exact or_congr_right or_comm
    · obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hq
      simp only [List.head?_cons, Option.some.injEq] at hs
      subst hs
      rw [← List.singleton_append, ← List.append_assoc, List.isChain_append, List.isChain_append]
      refine ⟨⟨List.isChain_singleton _, ?_, ?_⟩, List.isChain_singleton _, ?_⟩
      · rw [List.isChain_map]
        refine hch.imp fun u v h => ?_
        rw [mem_toAny_edges]
        exact Or.inr (Or.inr ⟨u, v, h, rfl, rfl⟩)
      · intro u hu v hv
        simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hu
        simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hv
        rw [← hu, ← hv, mem_toAny_edges]
        exact Or.inl ⟨rfl, rfl⟩
      · intro u hu v hv
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hv
        rw [List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_map, ht] at hu
        simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hu
        rw [← hu, ← hv, mem_toAny_edges]
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- The reduction `DirHamPath.toAny` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toAny :
    ComputableInPolyTime toAny encPathInstance encGraph := by
  have hadd : ComputableInPolyTime (· + 2 : ℕ → ℕ) encNat encNat :=
    binary_add' .id' (const 2)
  unfold toAny
  fun_prop

end DirHamPath

/-- `DirHamPath` reduces to `DirHamPathAny` in polynomial time via `DirHamPath.toAny`. -/
theorem polyTimeReducible_DirHamPath_DirHamPathAny :
    PolyTimeReducible encPathInstance encGraph DirHamPath DirHamPathAny :=
  ⟨DirHamPath.toAny, DirHamPath.computableInPolyTime_toAny,
    fun x => (DirHamPath.toAny_mem_iff x).symm⟩

/-- `DirHamPathAny` is `NP`-hard. -/
theorem DirHamPathAny_npHard : NPHard encGraph DirHamPathAny :=
  DirHamPath_npHard.trans polyTimeReducible_DirHamPath_DirHamPathAny

/-- **Directed Hamiltonian path, without given endpoints, is `NP`-complete**
[Arora and Barak, draft, Theorem 2.18][AroraBarak07]. -/
theorem DirHamPathAny_npComplete : NPComplete encGraph DirHamPathAny :=
  ⟨DirHamPathAny.mem_NP, DirHamPathAny_npHard⟩

end Cslib.Complexity
