/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Hamiltonian
public import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Complexity.Problems.Hamiltonian.Directed
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# From directed to undirected Hamiltonian paths and cycles

Splitting every vertex of a directed graph into three reduces directed Hamiltonian cycles and paths
to undirected ones: for cycles this is Karp's reduction [Karp1972], for paths a variant of
[Sipser, Theorem 7.55][Sipser2013]. In `Graph.split G`, every declared vertex `v` of `G` becomes a
path `in(v) - mid(v) - out(v)` (`Graph.splitVertex G v r` for `r = 0, 1, 2`), and every arc
`(u, v)` of `G` becomes an edge `out(u) - in(v)`. A middle vertex is adjacent only to the two other
vertices of its gadget, so an undirected Hamiltonian path from `in(s)` to `out(t)` traverses every
gadget from its entry to its exit, and the order of the gadgets is a directed Hamiltonian path from
`s` to `t`; an undirected Hamiltonian cycle, read in a suitable direction, likewise traverses every
gadget from its entry to its exit. Unlike Sipser's construction, the gadgets of `s` and `t` keep
all three vertices, which treats the endpoints uniformly and covers `s = t`.

Vertices of the split graph are numbered by first occurrence in the vertex list, so repeated vertex
entries share one gadget. An undeclared vertex gets labels that no declared vertex has: arcs with an
undeclared endpoint become edges with an undeclared endpoint, which the undirected problems ignore,
and an undeclared `s` or `t` makes both path instances negative. A self-loop `(v, v)` becomes the
edge `out(v) - in(v)`, so a single vertex with a self-loop, which is a directed Hamiltonian cycle,
becomes a triangle.

## Main definitions

* `Cslib.Complexity.Graph.splitVertex`, `Cslib.Complexity.Graph.split`.
* `Cslib.Complexity.DirHamPath.toHamPath`.

## Main results

* `Cslib.Complexity.Graph.split_mem_HamPath_iff`,
  `Cslib.Complexity.DirHamPath.toHamPath_mem_iff`:
  `(G.split, G.splitVertex s 0, G.splitVertex t 2) ∈ HamPath ↔ (G, s, t) ∈ DirHamPath`.
* `Cslib.Complexity.Graph.split_mem_HamCycle_iff`: `G.split ∈ HamCycle ↔ G ∈ DirHamCycle`.
* `Cslib.Complexity.Graph.computableInPolyTime_split`,
  `Cslib.Complexity.DirHamPath.computableInPolyTime_toHamPath`: both reductions are
  polynomial-time.
* `Cslib.Complexity.polyTimeReducible_DirHamPath_HamPath`,
  `Cslib.Complexity.polyTimeReducible_DirHamCycle_HamCycle`.
* `Cslib.Complexity.HamPath_npHard`, `Cslib.Complexity.HamPath_npComplete`,
  `Cslib.Complexity.HamCycle_npHard`, `Cslib.Complexity.HamCycle_npComplete`: the undirected
  problems are `NP`-complete.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

namespace Graph

/-- Vertex `r` of the gadget of `v` in `Graph.split G`: `r = 0` is `in(v)`, `r = 1` is `mid(v)`
and `r = 2` is `out(v)`. Vertices are numbered by their first occurrence in `G.1`, so an
undeclared vertex gets the number `G.1.length`, which no declared vertex has. -/
def splitVertex (G : Graph) (v r : ℕ) : ℕ := Nat.pair (G.1.idxOf v) r

/-- The vertex-splitting graph of a directed graph `G`: every declared vertex `v` becomes a path
`in(v) - mid(v) - out(v)`, and every arc `(u, v)` becomes an edge `out(u) - in(v)`. -/
def split (G : Graph) : Graph :=
  (G.1.flatMap fun v => [G.splitVertex v 0, G.splitVertex v 1, G.splitVertex v 2],
    G.1.flatMap (fun v => [(G.splitVertex v 0, G.splitVertex v 1),
      (G.splitVertex v 1, G.splitVertex v 2)]) ++
    G.2.map fun e => (G.splitVertex e.1 2, G.splitVertex e.2 0))

/-- Gadget vertices are equal exactly when their vertices have the same first occurrence and their
positions in the gadget agree. -/
theorem splitVertex_eq_splitVertex_iff {G : Graph} {u v r r' : ℕ} :
    G.splitVertex u r = G.splitVertex v r' ↔ G.1.idxOf u = G.1.idxOf v ∧ r = r' :=
  Nat.pair_eq_pair

private theorem eq_of_idxOf_eq {G : Graph} {u v : ℕ} (hv : v ∈ G.1)
    (h : G.1.idxOf u = G.1.idxOf v) : u = v :=
  ((List.idxOf_inj hv).1 h.symm).symm

/-- Gadget vertices of a declared vertex determine the vertex and the position in the gadget. -/
theorem splitVertex_eq_splitVertex_iff_of_mem {G : Graph} {u v r r' : ℕ} (hv : v ∈ G.1) :
    G.splitVertex u r = G.splitVertex v r' ↔ u = v ∧ r = r' := by
  rw [splitVertex_eq_splitVertex_iff]
  exact ⟨fun h => ⟨eq_of_idxOf_eq hv h.1, h.2⟩, fun h => ⟨h.1 ▸ rfl, h.2⟩⟩

private theorem mem_triple {G : Graph} {v x : ℕ} :
    x ∈ [G.splitVertex v 0, G.splitVertex v 1, G.splitVertex v 2] ↔
      ∃ r < 3, x = G.splitVertex v r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, by omega, rfl⟩, ⟨1, by omega, rfl⟩, ⟨2, by omega, rfl⟩]
  · rintro ⟨r, hr, rfl⟩
    obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]

/-- The split graph lists three vertices for each declared vertex. -/
theorem length_split_fst (G : Graph) : G.split.1.length = 3 * G.1.length := by
  simp [split, List.length_flatMap, mul_comm]

/-- The split graph lists two edges for each declared vertex and one for each arc. -/
theorem length_split_snd (G : Graph) : G.split.2.length = 2 * G.1.length + G.2.length := by
  simp [split, List.length_flatMap, mul_comm]

/-- The declared vertices of the split graph are the gadget vertices of declared vertices. -/
theorem mem_split_fst_iff {G : Graph} {x : ℕ} :
    x ∈ G.split.1 ↔ ∃ v ∈ G.1, ∃ r < 3, x = G.splitVertex v r := by
  simp only [split, List.mem_flatMap, mem_triple]

/-- A gadget vertex is a declared vertex of the split graph exactly when its vertex is declared
and its position is `0`, `1` or `2`. -/
theorem splitVertex_mem_split_fst_iff {G : Graph} {v r : ℕ} :
    G.splitVertex v r ∈ G.split.1 ↔ v ∈ G.1 ∧ r < 3 := by
  rw [mem_split_fst_iff]
  constructor
  · rintro ⟨w, hw, r', hr', h⟩
    obtain ⟨rfl, rfl⟩ := (splitVertex_eq_splitVertex_iff_of_mem hw).1 h
    exact ⟨hw, hr'⟩
  · rintro ⟨hv, hr⟩
    exact ⟨v, hv, r, hr, rfl⟩

/-! ### Adjacency in the split graph -/

private theorem mem_split_snd_iff {G : Graph} {a b : ℕ} :
    (a, b) ∈ G.split.2 ↔ (∃ v ∈ G.1, (a = G.splitVertex v 0 ∧ b = G.splitVertex v 1) ∨
      (a = G.splitVertex v 1 ∧ b = G.splitVertex v 2)) ∨
      ∃ e ∈ G.2, a = G.splitVertex e.1 2 ∧ b = G.splitVertex e.2 0 := by
  simp only [split, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, Prod.mk.injEq]
  refine or_congr Iff.rfl (exists_congr fun e => and_congr_right fun _ => ?_)
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩, fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩⟩

private theorem adj_split_iff {G : Graph} {a b : ℕ} :
    G.split.toSimpleGraph.Adj a b ↔ a ≠ b ∧ ((a, b) ∈ G.split.2 ∨ (b, a) ∈ G.split.2) :=
  toSimpleGraph_adj

private theorem adj_in_mid {G : Graph} {v : ℕ} (hv : v ∈ G.1) :
    G.split.toSimpleGraph.Adj (G.splitVertex v 0) (G.splitVertex v 1) := by
  refine adj_split_iff.2 ⟨fun h => ?_, Or.inl (mem_split_snd_iff.2 (Or.inl ⟨v, hv, ?_⟩))⟩
  · simp [splitVertex_eq_splitVertex_iff] at h
  · exact Or.inl ⟨rfl, rfl⟩

private theorem adj_mid_out {G : Graph} {v : ℕ} (hv : v ∈ G.1) :
    G.split.toSimpleGraph.Adj (G.splitVertex v 1) (G.splitVertex v 2) := by
  refine adj_split_iff.2 ⟨fun h => ?_, Or.inl (mem_split_snd_iff.2 (Or.inl ⟨v, hv, ?_⟩))⟩
  · simp [splitVertex_eq_splitVertex_iff] at h
  · exact Or.inr ⟨rfl, rfl⟩

/-- Between declared vertices, an exit is adjacent to an entry exactly along an arc. -/
private theorem adj_out_in_iff {G : Graph} {u v : ℕ} (hu : u ∈ G.1) (hv : v ∈ G.1) :
    G.split.toSimpleGraph.Adj (G.splitVertex u 2) (G.splitVertex v 0) ↔ (u, v) ∈ G.2 := by
  rw [adj_split_iff, mem_split_snd_iff, mem_split_snd_iff]
  simp only [splitVertex_eq_splitVertex_iff]
  constructor
  · rintro ⟨-, (⟨w, -, h | h⟩ | ⟨e, he, h₁, h₂⟩) | (⟨w, -, h | h⟩ | ⟨e, -, h₁, h₂⟩)⟩
    · omega
    · omega
    · obtain ⟨a, b⟩ := e
      obtain rfl := eq_of_idxOf_eq hu h₁.1.symm
      obtain rfl := eq_of_idxOf_eq hv h₂.1.symm
      exact he
    · omega
    · omega
    · omega
  · intro h
    refine ⟨by simp [splitVertex_eq_splitVertex_iff], Or.inl (Or.inr ⟨(u, v), h, ?_, ?_⟩)⟩ <;>
      exact ⟨rfl, trivial⟩

/-- A middle vertex is adjacent only to the two other vertices of its gadget. -/
private theorem eq_of_adj_mid {G : Graph} {v x : ℕ}
    (h : G.split.toSimpleGraph.Adj (G.splitVertex v 1) x) :
    x = G.splitVertex v 0 ∨ x = G.splitVertex v 2 := by
  rw [adj_split_iff, mem_split_snd_iff, mem_split_snd_iff] at h
  rcases h with ⟨-, (⟨w, -, ⟨h₁, rfl⟩ | ⟨h₁, rfl⟩⟩ | ⟨e, -, h₁, rfl⟩) |
    (⟨w, -, ⟨rfl, h₁⟩ | ⟨rfl, h₁⟩⟩ | ⟨e, -, rfl, h₁⟩)⟩ <;>
    simp only [splitVertex_eq_splitVertex_iff] at h₁ ⊢
  · omega
  · exact Or.inr ⟨h₁.1.symm, trivial⟩
  · omega
  · exact Or.inl ⟨h₁.1.symm, trivial⟩
  · omega
  · omega

/-- An exit vertex of a declared vertex is adjacent only to its middle vertex and to entries of
its out-neighbours. -/
private theorem eq_of_adj_out {G : Graph} {v x : ℕ} (hv : v ∈ G.1)
    (h : G.split.toSimpleGraph.Adj (G.splitVertex v 2) x) :
    x = G.splitVertex v 1 ∨ ∃ w, (v, w) ∈ G.2 ∧ x = G.splitVertex w 0 := by
  rw [adj_split_iff, mem_split_snd_iff, mem_split_snd_iff] at h
  rcases h with ⟨-, (⟨w, -, ⟨h₁, rfl⟩ | ⟨h₁, rfl⟩⟩ | ⟨e, he, h₁, rfl⟩) |
    (⟨w, -, ⟨rfl, h₁⟩ | ⟨rfl, h₁⟩⟩ | ⟨e, -, rfl, h₁⟩)⟩ <;>
    simp only [splitVertex_eq_splitVertex_iff] at h₁
  · omega
  · omega
  · obtain ⟨a, b⟩ := e
    obtain rfl := eq_of_idxOf_eq hv h₁.1.symm
    exact Or.inr ⟨b, he, rfl⟩
  · omega
  · exact Or.inl (splitVertex_eq_splitVertex_iff.2 ⟨h₁.1.symm, rfl⟩)
  · omega

/-! ### Sequences of gadgets -/

/-- The gadgets of the vertices of `p`, in order. -/
private def gadgets (G : Graph) (p : List ℕ) : List ℕ :=
  p.flatMap fun v => [G.splitVertex v 0, G.splitVertex v 1, G.splitVertex v 2]

private theorem split_fst (G : Graph) : G.split.1 = gadgets G G.1 := rfl

private theorem gadgets_nil (G : Graph) : gadgets G [] = [] := rfl

private theorem gadgets_cons (G : Graph) (v : ℕ) (p : List ℕ) :
    gadgets G (v :: p) =
      G.splitVertex v 0 :: G.splitVertex v 1 :: G.splitVertex v 2 :: gadgets G p := rfl

private theorem gadgets_append (G : Graph) (p p' : List ℕ) :
    gadgets G (p ++ p') = gadgets G p ++ gadgets G p' :=
  List.flatMap_append

private theorem mem_gadgets {G : Graph} {p : List ℕ} {x : ℕ} :
    x ∈ gadgets G p ↔ ∃ v ∈ p, ∃ r < 3, x = G.splitVertex v r := by
  simp only [gadgets, List.mem_flatMap, mem_triple]

private theorem length_gadgets (G : Graph) (p : List ℕ) : (gadgets G p).length = 3 * p.length := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [gadgets_cons, List.length_cons, List.length_cons, List.length_cons, ih, List.length_cons]
    omega

private theorem head?_gadgets (G : Graph) (p : List ℕ) :
    (gadgets G p).head? = p.head?.map (G.splitVertex · 0) := by
  cases p <;> rfl

private theorem getLast?_gadgets (G : Graph) (p : List ℕ) :
    (gadgets G p).getLast? = p.getLast?.map (G.splitVertex · 2) := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p v _ =>
    rw [gadgets_append, gadgets_cons, gadgets_nil, List.getLast?_append, List.getLast?_append]
    simp

/-- The gadgets of distinct declared vertices are disjoint. -/
private theorem nodup_gadgets_iff {G : Graph} {p : List ℕ} (hp : ∀ v ∈ p, v ∈ G.1) :
    (gadgets G p).Nodup ↔ p.Nodup := by
  rw [gadgets, List.nodup_flatMap]
  constructor
  · rintro ⟨-, h⟩
    refine h.imp fun {a b} hab => ?_
    rintro rfl
    exact hab (List.mem_cons_self ..) (List.mem_cons_self ..)
  · intro h
    refine ⟨fun v _ => ?_, h.imp_of_mem fun {a b} _ hb hab x hxa hxb => ?_⟩
    · simp [splitVertex_eq_splitVertex_iff]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxa hxb
      apply hab
      rcases hxa with rfl | rfl | rfl <;> rcases hxb with h | h | h <;>
        exact ((splitVertex_eq_splitVertex_iff_of_mem (hp b hb)).1 h).1

private theorem mem_gadgets_iff_of_forall_mem_iff {G : Graph} {p : List ℕ}
    (hp : ∀ v, v ∈ p ↔ v ∈ G.1) (x : ℕ) : x ∈ gadgets G p ↔ x ∈ G.split.1 := by
  simp only [split_fst, mem_gadgets, hp]

private theorem forall_mem_iff_of_mem_gadgets_iff {G : Graph} {p : List ℕ}
    (hp : ∀ v ∈ p, v ∈ G.1) (hcov : ∀ x, x ∈ gadgets G p ↔ x ∈ G.split.1) (v : ℕ) :
    v ∈ p ↔ v ∈ G.1 := by
  refine ⟨hp v, fun hv => ?_⟩
  obtain ⟨w, hw, r, -, h⟩ :=
    mem_gadgets.1 ((hcov _).2 (splitVertex_mem_split_fst_iff.2 ⟨hv, (by omega : 1 < 3)⟩))
  rw [((splitVertex_eq_splitVertex_iff_of_mem (hp w hw)).1 h).1]
  exact hw

/-- Along declared vertices, a chain of gadgets is a directed walk. -/
private theorem isChain_gadgets_iff {G : Graph} {p : List ℕ} (hp : ∀ v ∈ p, v ∈ G.1) :
    (gadgets G p).IsChain G.split.toSimpleGraph.Adj ↔ p.IsChain fun u v => (u, v) ∈ G.2 := by
  induction p with
  | nil => simp [gadgets_nil]
  | cons a p ih =>
    have ha := hp a (List.mem_cons_self ..)
    have hp' : ∀ v ∈ p, v ∈ G.1 := fun v hv => hp v (List.mem_cons_of_mem _ hv)
    have h₃ : [G.splitVertex a 0, G.splitVertex a 1, G.splitVertex a 2].IsChain
        G.split.toSimpleGraph.Adj :=
      List.isChain_cons_cons.2 ⟨adj_in_mid ha, List.isChain_pair.2 (adj_mid_out ha)⟩
    have hhead : (∀ x ∈ [G.splitVertex a 0, G.splitVertex a 1, G.splitVertex a 2].getLast?,
        ∀ y ∈ p.head?.map (G.splitVertex · 0), G.split.toSimpleGraph.Adj x y) ↔
          ∀ y ∈ p.head?, (a, y) ∈ G.2 := by
      cases p with
      | nil => simp
      | cons b p => simp [adj_out_in_iff ha (hp' b (List.mem_cons_self ..))]
    rw [gadgets_cons, show ∀ l : List ℕ, G.splitVertex a 0 :: G.splitVertex a 1 ::
      G.splitVertex a 2 :: l = [G.splitVertex a 0, G.splitVertex a 1, G.splitVertex a 2] ++ l
      from fun _ => rfl, List.isChain_append, ih hp', head?_gadgets, hhead,
      List.isChain_cons (x := a)]
    exact ⟨fun ⟨_, h₁, h₂⟩ => ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ => ⟨h₃, h₂, h₁⟩⟩

/-- Along declared vertices, a closed chain of gadgets is a closed directed walk. -/
private theorem chain_gadgets_iff {G : Graph} {p : List ℕ} (hp : ∀ v ∈ p, v ∈ G.1) :
    (gadgets G p : Cycle ℕ).Chain G.split.toSimpleGraph.Adj ↔
      (p : Cycle ℕ).Chain fun u v => (u, v) ∈ G.2 := by
  cases p with
  | nil => rfl
  | cons a p =>
    have ha := hp a (List.mem_cons_self ..)
    have hp' : ∀ v ∈ a :: (p ++ [a]), v ∈ G.1 := by
      intro v hv
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | hv | rfl
      · exact ha
      · exact hp v (List.mem_cons_of_mem _ hv)
      · exact ha
    have e : gadgets G (a :: (p ++ [a])) = (G.splitVertex a 0 :: G.splitVertex a 1 ::
        G.splitVertex a 2 :: (gadgets G p ++ [G.splitVertex a 0])) ++
          [G.splitVertex a 1, G.splitVertex a 2] := by
      simp [gadgets_cons, gadgets_append, gadgets_nil]
    have hl : (G.splitVertex a 2 :: (gadgets G p ++ [G.splitVertex a 0])).getLast? =
        some (G.splitVertex a 0) := by
      rw [← List.cons_append, List.getLast?_concat]
    rw [gadgets_cons, Cycle.chain_coe_cons, Cycle.chain_coe_cons, ← isChain_gadgets_iff hp', e,
      List.isChain_append]
    simp [adj_mid_out ha, adj_in_mid ha, hl]

/-- A chain of the split graph without repetitions through declared vertices that starts at an
entry, does not end at a middle vertex, and contains the middle vertex of each entry it contains,
is a sequence of gadgets. -/
private theorem exists_eq_gadgets {G : Graph} (n : ℕ) : ∀ (l : List ℕ) (v : ℕ), l.length ≤ n →
    l.IsChain G.split.toSimpleGraph.Adj → l.Nodup → (∀ x ∈ l, x ∈ G.split.1) →
    l.head? = some (G.splitVertex v 0) → (∀ u, l.getLast? ≠ some (G.splitVertex u 1)) →
    (∀ u ∈ G.1, G.splitVertex u 0 ∈ l → G.splitVertex u 1 ∈ l) →
    ∃ p, (∀ u ∈ p, u ∈ G.1) ∧ l = gadgets G p := by
  induction n with
  | zero =>
    intro l v hlen _ _ _ hhead
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)] at hhead
    simp at hhead
  | succ n ih =>
    intro l v hlen hch hnd hdecl hhead hlast hmid
    obtain ⟨l₁, rfl⟩ := List.head?_eq_some_iff.1 hhead
    have hv : v ∈ G.1 := (splitVertex_mem_split_fst_iff.1 (hdecl _ (List.mem_cons_self ..))).1
    have hnd₀ : G.splitVertex v 0 ∉ l₁ := (List.nodup_cons.1 hnd).1
    have hnd₁ : l₁.Nodup := (List.nodup_cons.1 hnd).2
    have hch₁ : l₁.IsChain G.split.toSimpleGraph.Adj := hch.tail
    -- `mid(v)` lies in `l₁`, at some position `j`.
    have hm : G.splitVertex v 1 ∈ l₁ := by
      rcases List.mem_cons.1 (hmid v hv (List.mem_cons_self ..)) with h | h
      · simp [splitVertex_eq_splitVertex_iff] at h
      · exact h
    obtain ⟨j, hj, hjm⟩ := List.getElem_of_mem hm
    -- `mid(v)` is not the last vertex, and its successor is `out(v)`.
    have hj₁ : j + 1 < l₁.length := by
      by_contra h
      apply hlast v
      rw [List.getLast?_eq_getElem?, List.length_cons, Nat.add_sub_cancel,
        (by omega : l₁.length = j + 1), List.getElem?_cons_succ, List.getElem?_eq_getElem hj, hjm]
    have hsucc : l₁[j + 1] = G.splitVertex v 2 := by
      rcases eq_of_adj_mid (hjm ▸ hch₁.getElem j hj₁) with h | h
      · exact absurd (h ▸ List.getElem_mem hj₁) hnd₀
      · exact h
    -- The predecessor of `mid(v)` is `in(v)`, so `mid(v)` is the second vertex.
    have hj₀ : j = 0 := by
      rcases j with _ | i
      · rfl
      · rcases eq_of_adj_mid (hjm ▸ (hch₁.getElem i hj).symm) with h | h
        · exact absurd (h ▸ List.getElem_mem _) hnd₀
        · have := hnd₁.getElem_inj_iff.1 (h.trans hsucc.symm)
          omega
    subst hj₀
    obtain ⟨l₂, rfl⟩ : ∃ l₂, l₁ = G.splitVertex v 1 :: G.splitVertex v 2 :: l₂ := by
      rcases l₁ with _ | ⟨b, _ | ⟨c, l₂⟩⟩
      · simp at hj
      · simp at hj₁
      · exact ⟨l₂, by rw [← hjm, ← hsucc]; rfl⟩
    rcases l₂ with _ | ⟨x, l₃⟩
    · exact ⟨[v], by simpa using hv, rfl⟩
    -- The vertex after `out(v)` is the entry of an out-neighbour `w` of `v`.
    rcases eq_of_adj_out hv (List.isChain_cons_cons.1 hch₁.tail).1 with rfl | ⟨w, -, rfl⟩
    · simp at hnd₁
    have hmid' : ∀ u ∈ G.1, G.splitVertex u 0 ∈ G.splitVertex w 0 :: l₃ →
        G.splitVertex u 1 ∈ G.splitVertex w 0 :: l₃ := by
      intro u hu hu0
      rcases List.mem_append.1 (show G.splitVertex u 1 ∈
          [G.splitVertex v 0, G.splitVertex v 1, G.splitVertex v 2] ++ (G.splitVertex w 0 :: l₃)
          from hmid u hu (List.mem_append_right
            [G.splitVertex v 0, G.splitVertex v 1, G.splitVertex v 2] hu0)) with h | h
      · obtain ⟨r, -, h⟩ := mem_triple.1 h
        rw [splitVertex_eq_splitVertex_iff.2 ⟨(splitVertex_eq_splitVertex_iff.1 h).1, rfl⟩] at hu0
        exact absurd (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu0)) hnd₀
      · exact h
    obtain ⟨p, hp, hl⟩ := ih (G.splitVertex w 0 :: l₃) w
      (by simp only [List.length_cons] at hlen ⊢; omega) hch₁.tail.tail hnd₁.of_cons.of_cons
      (fun y hy => hdecl y (by simp [hy])) rfl
      (fun u => by simpa only [List.getLast?_cons_cons] using hlast u) hmid'
    exact ⟨v :: p, List.forall_mem_cons.2 ⟨hv, hp⟩, by rw [gadgets_cons, ← hl]⟩

/-- Reversing a closed chain of a symmetric relation gives a closed chain. -/
private theorem chain_reverse_coe {α : Type*} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a)
    (l : List α) : (l.reverse : Cycle α).Chain R ↔ (l : Cycle α).Chain R := by
  cases l with
  | nil => rfl
  | cons a l =>
    have hrot : (((a :: l).reverse : List α) : Cycle α) = (a :: l.reverse : List α) := by
      rw [Cycle.coe_eq_coe, List.reverse_cons]
      exact List.isRotated_append
    rw [hrot, Cycle.chain_coe_cons, Cycle.chain_coe_cons,
      show a :: (l.reverse ++ [a]) = (a :: (l ++ [a])).reverse by simp, List.isChain_reverse]
    exact List.IsChain.iff fun x y => ⟨hR y x, hR x y⟩

/-! ### Correctness of the reductions -/

/-- **Vertex splitting preserves Hamiltonian paths.** A directed graph has a Hamiltonian path from
`s` to `t` exactly when its split graph has an undirected Hamiltonian path from `in(s)` to
`out(t)`. -/
theorem split_mem_HamPath_iff (G : Graph) (s t : ℕ) :
    (G.split, G.splitVertex s 0, G.splitVertex t 2) ∈ HamPath ↔ (G, s, t) ∈ DirHamPath := by
  rw [mem_HamPath_iff]
  constructor
  · rintro ⟨q, hnd, hcov, hs, ht, hch⟩
    obtain ⟨p, hp, rfl⟩ := exists_eq_gadgets q.length q s le_rfl hch hnd
      (fun x hx => (hcov x).1 hx) hs
      (fun u h => by
        rw [ht, Option.some.injEq, splitVertex_eq_splitVertex_iff] at h
        omega)
      (fun u hu _ => (hcov _).2 (splitVertex_mem_split_fst_iff.2 ⟨hu, by omega⟩))
    refine ⟨p, (nodup_gadgets_iff hp).1 hnd, forall_mem_iff_of_mem_gadgets_iff hp hcov, ?_, ?_,
      (isChain_gadgets_iff hp).1 hch⟩
    · rw [head?_gadgets, Option.map_eq_some_iff] at hs
      obtain ⟨a, ha, h⟩ := hs
      rw [ha, ((splitVertex_eq_splitVertex_iff_of_mem (hp a (List.mem_of_head? ha))).1 h.symm).1]
    · rw [getLast?_gadgets, Option.map_eq_some_iff] at ht
      obtain ⟨b, hb, h⟩ := ht
      rw [hb, ((splitVertex_eq_splitVertex_iff_of_mem (hp b (List.mem_of_getLast? hb))).1
        h.symm).1]
  · rintro ⟨p, hnd, hcov, hs, ht, hch⟩
    have hp : ∀ v ∈ p, v ∈ G.1 := fun v hv => (hcov v).1 hv
    exact ⟨gadgets G p, (nodup_gadgets_iff hp).2 hnd, mem_gadgets_iff_of_forall_mem_iff hcov,
      by rw [head?_gadgets, hs]; rfl, by rw [getLast?_gadgets, ht]; rfl,
      (isChain_gadgets_iff hp).2 hch⟩

/-- **Vertex splitting preserves Hamiltonian cycles** [Karp1972]. A directed graph has a
Hamiltonian cycle exactly when its split graph has an undirected Hamiltonian cycle. -/
theorem split_mem_HamCycle_iff (G : Graph) : G.split ∈ HamCycle ↔ G ∈ DirHamCycle := by
  rw [mem_HamCycle_iff]
  constructor
  · rintro ⟨q, hnd, hcov, hlen, hch⟩
    obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos (by omega : 0 < q.length)
    obtain ⟨u, hu, -⟩ := mem_split_fst_iff.1 ((hcov x).1 hx)
    obtain ⟨A, B, rfl⟩ := List.append_of_mem
      ((hcov _).2 (splitVertex_mem_split_fst_iff.2 ⟨hu, (by omega : 0 < 3)⟩))
    -- Rotations and reversals preserve the hypotheses.
    have key : ∀ L : List ℕ, L ~r (A ++ G.splitVertex u 0 :: B) ∨
        L ~r (A ++ G.splitVertex u 0 :: B).reverse →
        L.Nodup ∧ (∀ x, x ∈ L ↔ x ∈ G.split.1) ∧ 3 ≤ L.length ∧
          (L : Cycle ℕ).Chain G.split.toSimpleGraph.Adj := by
      rintro L (h | h)
      · exact ⟨h.nodup_iff.2 hnd, fun x => h.mem_iff.trans (hcov x), h.perm.length_eq ▸ hlen,
          (Cycle.coe_eq_coe.2 h) ▸ hch⟩
      · refine ⟨h.nodup_iff.2 (List.nodup_reverse.2 hnd),
          fun x => h.mem_iff.trans (List.mem_reverse.trans (hcov x)), ?_, ?_⟩
        · rw [h.perm.length_eq, List.length_reverse]
          exact hlen
        · rw [Cycle.coe_eq_coe.2 h, chain_reverse_coe (fun _ _ h => h.symm)]
          exact hch
    -- Rotate to start at `in(u)`, and reverse if the cycle then ends at `mid(u)`.
    obtain ⟨L₁, hL, hlast⟩ : ∃ L₁ : List ℕ,
        ((G.splitVertex u 0 :: L₁) ~r (A ++ G.splitVertex u 0 :: B) ∨
          (G.splitVertex u 0 :: L₁) ~r (A ++ G.splitVertex u 0 :: B).reverse) ∧
        ((G.splitVertex u 0 :: L₁).getLast? ≠ some (G.splitVertex u 1) ∨
          ∃ L₂, L₁ = G.splitVertex u 1 :: L₂) := by
      have hrot : (G.splitVertex u 0 :: (B ++ A)) ~r (A ++ G.splitVertex u 0 :: B) :=
        (List.isRotated_append (l := A) (l' := G.splitVertex u 0 :: B)).symm
      by_cases h : (G.splitVertex u 0 :: (B ++ A)).getLast? = some (G.splitVertex u 1)
      · obtain ⟨M, hM⟩ := List.getLast?_eq_some_iff.1 h
        obtain ⟨M', rfl⟩ : ∃ M', M = G.splitVertex u 0 :: M' := by
          rcases M with _ | ⟨a, M'⟩
          · simp [splitVertex_eq_splitVertex_iff] at hM
          · simp only [List.cons_append, List.cons.injEq] at hM
            exact ⟨M', by rw [hM.1]⟩
        refine ⟨G.splitVertex u 1 :: M'.reverse, Or.inr ?_, Or.inr ⟨_, rfl⟩⟩
        have := hrot.reverse
        rw [hM] at this
        refine List.IsRotated.trans ?_ this
        simp only [List.cons_append, List.reverse_cons, List.reverse_append, List.reverse_nil,
          List.nil_append]
        exact List.isRotated_append (l := [G.splitVertex u 0])
          (l' := G.splitVertex u 1 :: M'.reverse)
      · exact ⟨B ++ A, Or.inl hrot, Or.inl h⟩
    obtain ⟨hndL, hcovL, hlenL, hchC⟩ := key _ hL
    have hchL := hchC
    rw [Cycle.chain_coe_cons, ← List.cons_append, List.isChain_append] at hchL
    obtain ⟨hchL, -, hclose⟩ := hchL
    -- The cycle does not end at a middle vertex.
    have hlast' : ∀ w, (G.splitVertex u 0 :: L₁).getLast? ≠ some (G.splitVertex w 1) := by
      intro w hw
      rcases eq_of_adj_mid (hclose _ hw _ rfl) with h | h
      · rw [splitVertex_eq_splitVertex_iff.2 ⟨(splitVertex_eq_splitVertex_iff.1 h).1.symm, rfl⟩]
          at hw
        rcases hlast with hlast | ⟨L₂, rfl⟩
        · exact hlast hw
        · obtain ⟨b, L₃, rfl⟩ := List.exists_cons_of_ne_nil (by rintro rfl; simp at hlenL :
            L₂ ≠ [])
          rw [List.getLast?_cons_cons, List.getLast?_cons_cons] at hw
          exact (List.nodup_cons.1 (List.nodup_cons.1 hndL).2).1 (List.mem_of_getLast? hw)
      · simp [splitVertex_eq_splitVertex_iff] at h
    obtain ⟨p, hp, hL⟩ := exists_eq_gadgets _ _ u le_rfl hchL hndL (fun x hx => (hcovL x).1 hx)
      rfl hlast' (fun w hw _ => (hcovL _).2 (splitVertex_mem_split_fst_iff.2 ⟨hw, by omega⟩))
    rw [hL] at hndL hcovL hchC
    refine ⟨p, (nodup_gadgets_iff hp).1 hndL, forall_mem_iff_of_mem_gadgets_iff hp hcovL, ?_,
      (chain_gadgets_iff hp).1 hchC⟩
    rintro rfl
    simp [gadgets_nil] at hL
  · rintro ⟨p, hnd, hcov, hne, hch⟩
    have hp : ∀ v ∈ p, v ∈ G.1 := fun v hv => (hcov v).1 hv
    refine ⟨gadgets G p, (nodup_gadgets_iff hp).2 hnd, mem_gadgets_iff_of_forall_mem_iff hcov, ?_,
      (chain_gadgets_iff hp).2 hch⟩
    rw [length_gadgets]
    have := List.length_pos_of_ne_nil hne
    omega

/-! ### Polynomial-time reductions -/

/-- Computing a gadget vertex is polynomial-time: the first-occurrence index is found in unary,
paired with the unary position in the gadget, and converted to binary. -/
private theorem computableInPolyTime_splitVertex :
    ComputableInPolyTime (fun p : Graph × ℕ × ℕ => p.1.splitVertex p.2.1 p.2.2)
      (encPair encGraph (encPair encNat encUnary)) encNat := by
  unfold splitVertex encGraph
  exact unary_to_binary.comp (by fun_prop)

/-- Splitting the vertices of a graph is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_split : ComputableInPolyTime split encGraph encGraph := by
  have hsv := computableInPolyTime_splitVertex
  unfold split
  unfold encGraph at hsv ⊢
  fun_prop

end Graph

namespace DirHamPath

/-- The reduction from `DirHamPath` to `HamPath`: split the vertices of the graph, and ask for a
path from the entry of `s` to the exit of `t`. -/
def toHamPath (x : Graph × ℕ × ℕ) : Graph × ℕ × ℕ :=
  (x.1.split, x.1.splitVertex x.2.1 0, x.1.splitVertex x.2.2 2)

/-- Correctness of `DirHamPath.toHamPath`. -/
theorem toHamPath_mem_iff (x : Graph × ℕ × ℕ) : toHamPath x ∈ HamPath ↔ x ∈ DirHamPath :=
  Graph.split_mem_HamPath_iff x.1 x.2.1 x.2.2

/-- The reduction `DirHamPath.toHamPath` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toHamPath :
    ComputableInPolyTime toHamPath (encPair encGraph (encPair encNat encNat))
      (encPair encGraph (encPair encNat encNat)) := by
  have hsv := Graph.computableInPolyTime_splitVertex
  unfold toHamPath
  fun_prop

end DirHamPath

/-- `DirHamPath` reduces to `HamPath` in polynomial time via `DirHamPath.toHamPath`. -/
theorem polyTimeReducible_DirHamPath_HamPath :
    PolyTimeReducible (encPair encGraph (encPair encNat encNat))
      (encPair encGraph (encPair encNat encNat)) DirHamPath HamPath :=
  ⟨DirHamPath.toHamPath, DirHamPath.computableInPolyTime_toHamPath,
    fun x => (DirHamPath.toHamPath_mem_iff x).symm⟩

/-- `DirHamCycle` reduces to `HamCycle` in polynomial time via `Graph.split`. -/
theorem polyTimeReducible_DirHamCycle_HamCycle :
    PolyTimeReducible encGraph encGraph DirHamCycle HamCycle :=
  ⟨Graph.split, Graph.computableInPolyTime_split,
    fun G => (Graph.split_mem_HamCycle_iff G).symm⟩

/-- `HamPath` is `NP`-hard. -/
theorem HamPath_npHard : NPHard (encPair encGraph (encPair encNat encNat)) HamPath :=
  DirHamPath_npHard.trans polyTimeReducible_DirHamPath_HamPath

/-- **`HamPath` is NP-complete** [Sipser, Theorem 7.55][Sipser2013]. -/
theorem HamPath_npComplete : NPComplete (encPair encGraph (encPair encNat encNat)) HamPath :=
  ⟨HamPath.mem_NP, HamPath_npHard⟩

/-- `HamCycle` is `NP`-hard. -/
theorem HamCycle_npHard : NPHard encGraph HamCycle :=
  DirHamCycle_npHard.trans polyTimeReducible_DirHamCycle_HamCycle

/-- **`HamCycle` is NP-complete** [Karp1972]. -/
theorem HamCycle_npComplete : NPComplete encGraph HamCycle :=
  ⟨HamCycle.mem_NP, HamCycle_npHard⟩

end Cslib.Complexity
