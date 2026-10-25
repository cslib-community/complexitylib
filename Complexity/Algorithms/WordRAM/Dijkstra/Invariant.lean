/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.Statement

/-!
# Dijkstra's algorithm: the invariant

This file proves the graph theory behind Dijkstra's algorithm [Dijkstra][Dijkstra1959]
[Cormen et al., Section 24.3][CLRS2009], independently of the machine. The algorithm keeps a set
`S` of visited vertices and a tentative distance `D v` for every vertex, and
`Cslib.Algorithms.WordRAM.Dijkstra.Instance.Inv` states what it maintains: `D` bounds the
distance from above, is exact on `S`, and is already relaxed along every edge out of `S`.

The key step (`Cslib.Algorithms.WordRAM.Dijkstra.Instance.Inv.step`) is the classical cut
argument: on every path from the source to an unvisited vertex, either the source is unvisited,
with tentative distance `0`, or the path has an edge from `S` to an unvisited vertex. Either way
its weight is at least the least tentative distance outside `S`. Hence an unvisited
vertex of least finite tentative distance has the exact distance, and relaxing its edges keeps
the invariant with that vertex visited.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.decodeDist`: the distance a word encodes.
* `Cslib.Algorithms.WordRAM.Dijkstra.Instance.relax`: relaxation of the edges out of a vertex.
* `Cslib.Algorithms.WordRAM.Dijkstra.Instance.Inv`: the invariant of Dijkstra's algorithm.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.decodeDist_encodeDist`: decoding inverts the encoding of
  distances.
* `Cslib.Algorithms.WordRAM.Dijkstra.decodeDist_le`: decoding preserves order between nonzero
  words.
* `Cslib.Algorithms.WordRAM.Dijkstra.Instance.le_maxWeight`: every edge weight is at most the
  largest one.
* `Cslib.Algorithms.WordRAM.Dijkstra.Instance.dist_le_edge`: the distance to the head of an edge
  is at most the distance to its tail plus its weight.
* `Cslib.Algorithms.WordRAM.Dijkstra.Instance.Inv.init`: the invariant holds initially.
* `Cslib.Algorithms.WordRAM.Dijkstra.Instance.Inv.step`: visiting an unvisited vertex of least
  finite tentative distance and relaxing its edges keeps the invariant.
* `Cslib.Algorithms.WordRAM.Dijkstra.Instance.Inv.eq_dist`: once every unvisited vertex has
  infinite tentative distance, the tentative distances are the distances.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

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

/-- A nonzero distance word decodes to a finite distance. -/
theorem decodeDist_ne_top {b : ℕ} (hb : b ≠ 0) : decodeDist b ≠ ⊤ := by
  simp [decodeDist, hb]

/-- Decoding preserves order between nonzero distance words. -/
theorem decodeDist_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a ≤ b) :
    decodeDist a ≤ decodeDist b := by
  simp only [decodeDist, ha, hb, ite_false]
  exact_mod_cast Nat.sub_le_sub_right h 1

namespace Instance

variable (I : Instance)

/-- Every edge weight is at most the largest one. -/
theorem le_maxWeight {u v : Fin I.n} {c : ℕ} (h : I.weight u v = some c) : c ≤ I.maxWeight := by
  have hle := Finset.le_sup (f := fun uv : Fin I.n × Fin I.n =>
    (I.weight uv.1 uv.2).getD 0) (Finset.mem_univ (u, v))
  simpa only [h, Option.getD_some, maxWeight] using hle

/-- Relaxation of the edges out of `u`: the tentative distance of `v` becomes at most that of `u`
plus the weight of the edge from `u` to `v`, if there is one. -/
noncomputable def relax (D : Fin I.n → ℕ∞) (u v : Fin I.n) : ℕ∞ :=
  match I.weight u v with
  | none => D v
  | some c => min (D v) (D u + c)

/-- **The invariant of Dijkstra's algorithm**, for the visited set `S` and the tentative
distances `D`. -/
structure Inv (S : Finset (Fin I.n)) (D : Fin I.n → ℕ∞) : Prop where
  /-- The source has tentative distance `0`. -/
  source : D I.source = 0
  /-- Tentative distances bound the distances from above. -/
  dist_le : ∀ v, I.dist I.source v ≤ D v
  /-- Tentative distances are exact on visited vertices. -/
  eq_of_mem : ∀ v ∈ S, D v = I.dist I.source v
  /-- Every edge from a visited vertex to an unvisited one is relaxed. -/
  relaxed : ∀ a ∈ S, ∀ b ∉ S, ∀ c, I.weight a b = some c → D b ≤ D a + c
  /-- Finite tentative distances are at most `|S|` times the largest weight. -/
  bound : ∀ v, D v ≠ ⊤ → D v ≤ ((S.card * I.maxWeight : ℕ) : ℕ∞)

/-- A distance is at most the weight of any path between its endpoints. -/
private theorem dist_le_addWeight {a b : I.Vertex} (p : Quiver.Path a b) :
    I.dist a b ≤ p.addWeight I.arrowWeight :=
  iInf_le _ p

/-- Extending a path by an edge bounds the distance to the new endpoint. -/
theorem dist_le_edge {a b : Fin I.n} {c : ℕ} (he : I.weight a b = some c) :
    I.dist I.source b ≤ I.dist I.source a + c := by
  change I.dist I.source b ≤
    (⨅ p : Quiver.Path (V := I.Vertex) I.source a, p.addWeight I.arrowWeight) + c
  rw [ENat.iInf_add]
  apply le_iInf
  intro p
  let e : Quiver.Hom (V := I.Vertex) a b := ⟨c, he⟩
  exact (I.dist_le_addWeight (p.cons e)).trans_eq
    (Quiver.Path.addWeight_cons (V := I.Vertex) I.arrowWeight p e)

/-- Relaxation never increases a tentative distance. -/
private theorem relax_le (D : Fin I.n → ℕ∞) (u v : Fin I.n) :
    I.relax D u v ≤ D v := by
  cases he : I.weight u v with
  | none => simp [relax, he]
  | some c => simpa only [relax, he] using min_le_left (D v) (D u + c)

/-- Every path to an unvisited vertex bounds an unvisited tentative distance from above. -/
private theorem Inv.cut {S : Finset (Fin I.n)} {D : Fin I.n → ℕ∞} (h : I.Inv S D)
    {v : I.Vertex} (p : Quiver.Path (V := I.Vertex) I.source v) (hv : v ∉ S) :
    ∃ x ∉ S, D x ≤ p.addWeight I.arrowWeight := by
  induction p with
  | nil =>
    refine ⟨I.source, hv, ?_⟩
    exact h.source.le.trans_eq (Quiver.Path.addWeight_nil (V := I.Vertex) I.arrowWeight _).symm
  | @cons b v p e ih =>
    rw [Quiver.Path.addWeight_cons (V := I.Vertex) I.arrowWeight p e]
    by_cases hb : b ∈ S
    · refine ⟨v, hv, ?_⟩
      calc
        D v ≤ D b + (e : {c : ℕ // I.weight b v = some c}).1 :=
          h.relaxed b hb v hv _ e.property
        _ = I.dist I.source b + I.arrowWeight e := by rw [h.eq_of_mem b hb]; rfl
        _ ≤ p.addWeight I.arrowWeight + I.arrowWeight e :=
          add_le_add (I.dist_le_addWeight p) le_rfl
    · obtain ⟨x, hx, hxp⟩ := ih hb
      refine ⟨x, hx, ?_⟩
      exact hxp.trans (le_add_right le_rfl)

/-- The invariant holds with no vertex visited, the source at tentative distance `0` and every
other vertex at `⊤`. -/
theorem Inv.init : I.Inv ∅ (Function.update (fun _ => ⊤) I.source 0) := by
  classical
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v = I.source
    · subst v
      simp [I.dist_self]
    · simp [Function.update_of_ne hv]
  · simp
  · simp
  · intro v hv
    by_cases heq : v = I.source
    · subst v
      simp
    · simp [Function.update_of_ne heq] at hv

/-- **Dijkstra's step.** Visiting an unvisited vertex `u` of least finite tentative distance and
relaxing its edges keeps the invariant. -/
theorem Inv.step {S : Finset (Fin I.n)} {D : Fin I.n → ℕ∞} (h : I.Inv S D) {u : Fin I.n}
    (hu : u ∉ S) (hmin : ∀ v ∉ S, D u ≤ D v) (hfin : D u ≠ ⊤) :
    I.Inv (insert u S) (I.relax D u) := by
  classical
  have hexact : D u = I.dist I.source u := by
    apply le_antisymm _ (h.dist_le u)
    apply le_iInf
    intro p
    obtain ⟨x, hx, hxp⟩ := h.cut I p hu
    exact (hmin x hx).trans hxp
  have hlower (v) : I.dist I.source v ≤ I.relax D u v := by
    cases he : I.weight u v with
    | none => simpa only [relax, he] using h.dist_le v
    | some c =>
      simp only [relax, he]
      exact le_min (h.dist_le v) (hexact ▸ I.dist_le_edge he)
  have hold (a) (ha : a ∈ S) : I.relax D u a = D a := by
    apply le_antisymm (I.relax_le D u a)
    rw [h.eq_of_mem a ha]
    exact hlower a
  have hself : I.relax D u u = D u := by
    apply le_antisymm (I.relax_le D u u)
    rw [hexact]
    exact hlower u
  have hcard : S.card * I.maxWeight ≤ (insert u S).card * I.maxWeight :=
    Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.subset_insert _ _))
  refine ⟨?_, hlower, ?_, ?_, ?_⟩
  · exact le_antisymm ((I.relax_le D u I.source).trans h.source.le) zero_le
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hself.trans hexact
    · exact (hold a ha).trans (h.eq_of_mem a ha)
  · intro a ha b hb c he
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rw [hself]
      simp only [relax, he]
      exact min_le_right _ _
    · rw [hold a ha]
      exact (I.relax_le D u b).trans
        (h.relaxed a ha b (fun hbS => hb (Finset.mem_insert_of_mem hbS)) c he)
  · intro v hv
    by_cases hd : D v = ⊤
    · cases he : I.weight u v with
      | none => simp [relax, he, hd] at hv
      | some c =>
        have hc : (c : ℕ∞) ≤ (I.maxWeight : ℕ∞) := by
          exact_mod_cast I.le_maxWeight he
        calc
          I.relax D u v ≤ D u + c := by simp [relax, he]
          _ ≤ ((S.card * I.maxWeight : ℕ) : ℕ∞) + I.maxWeight :=
            add_le_add (h.bound u hfin) hc
          _ = (((insert u S).card * I.maxWeight : ℕ) : ℕ∞) := by
            rw [Finset.card_insert_of_notMem hu, Nat.add_mul, Nat.one_mul, Nat.cast_add]
    · exact (I.relax_le D u v).trans ((h.bound v hd).trans (by exact_mod_cast hcard))

/-- **Termination.** Once every unvisited vertex has infinite tentative distance, the tentative
distances are the distances. -/
theorem Inv.eq_dist {S : Finset (Fin I.n)} {D : Fin I.n → ℕ∞} (h : I.Inv S D)
    (hdone : ∀ v ∉ S, D v = ⊤) (v : Fin I.n) : D v = I.dist I.source v := by
  by_cases hv : v ∈ S
  · exact h.eq_of_mem v hv
  · rw [hdone v hv]
    apply le_antisymm _ le_top
    apply le_iInf
    intro p
    obtain ⟨x, hx, hxp⟩ := h.cut I p hv
    rw [hdone x hx] at hxp
    exact hxp

end Instance

end Cslib.Algorithms.WordRAM.Dijkstra

end
