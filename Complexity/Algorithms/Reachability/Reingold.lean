/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.AffineTower
public import Complexity.Foundations.Combinatorics.Expander.Reingold
public import Complexity.Foundations.Combinatorics.Expander.SlotGraph
public import Complexity.Foundations.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum.Prime

/-!
# Undirected connectivity by short walks in an explicit graph

This is the combinatorial core of Reingold's theorem that undirected `s`–`t` connectivity is in
deterministic logarithmic space [Reingold, Theorem 4.1][Reingold2008]
[Arora and Barak, Section 21.4][AroraBarak09], with explicit constants. For a simple graph `G` on
`Fin n` and any `a` with `n ≤ 2 ^ a`:

1. the slot graph of `G` (`Cslib.RotationMap.slotGraph`, with the slots of a vertex in the
   cyclic order of `finRotate n`) is a `3`-regular multigraph on `Fin n × Fin n` with the
   connectivity of `G`; its labels are extended by self-loops to the `257 ^ 8` vertices of the base
   graph below, so that at least half of the edges at every vertex are self-loops
   (`Cslib.Reachability.Reingold.input`);
2. the base graph `Cslib.Reachability.Reingold.base` is the arithmetic zig-zag base graph over
   `ZMod 257` (`Cslib.RotationMap.affinePlaneTowerBase`), a `257 ^ 2`-regular multigraph on
   `257 ^ 8` vertices of spectral expansion at most `1 / 5`, computed by field arithmetic;
3. `depth a = 16 a + 524` steps of Reingold's transformation (`Cslib.RotationMap.reingold`) make
   every connected component an expander with `λ ≤ 4 / 5`, and walks of length
   `walkLength a = 4 (2 a + 65 depth a)` reach every vertex of a component.

So `t` is reachable from `s` exactly when some walk of length `walkLength a` in `graph G a` from
the vertex `start s a` over the slot `(s, s)` ends over a slot of `t`
(`Cslib.Reachability.Reingold.reachable_iff_exists_walk_of_le_two_pow`), and with `a = ⌈log₂ n⌉`
(`Cslib.Reachability.Reingold.reachable_iff_exists_walk`). Both the depth and the walk length are
`O(log n)`, and the graph has constant degree `257 ^ 8`, so the walks can be enumerated with
`O(log n)` bits.

The constants are far from optimal: they come from the gap growth `γ ↦ min (6 γ / 5) (1 / 5)` of a
step that squares once (`Cslib.RotationMap.min_le_one_sub_spectralExpansion_reingoldStep`), from
the initial gap `1 / (2 N² |B|²)` given by Cheeger's inequality, and from rounding `log₂ (6 / 5)`
and `log₂ (5 / 4)` down to `1 / 4`.

## Main definitions

* `Cslib.Reachability.Reingold.Label`, `Cslib.Reachability.Reingold.base`: the labels and the
  base graph.
* `Cslib.Reachability.Reingold.input`: the regular rotation map of a simple graph on `Fin n`.
* `Cslib.Reachability.Reingold.depth`, `Cslib.Reachability.Reingold.walkLength`: the number of
  steps of the transformation and the walk length.
* `Cslib.Reachability.Reingold.graph`, `Cslib.Reachability.Reingold.start`: the transformed graph
  and the start vertex over `s`.

## Main results

* `Cslib.Reachability.Reingold.spectralExpansion_base_le`: the base graph has `λ ≤ 1 / 5`.
* `Cslib.Reachability.Reingold.reachable_input_iff`: the regular rotation map has the
  connectivity of the simple graph.
* `Cslib.Reachability.Reingold.reachable_iff_exists_walk_of_le_two_pow`,
  `Cslib.Reachability.Reingold.reachable_iff_exists_walk`: undirected connectivity is decided by
  the walks of length `O(log n)` from one vertex of the constant-degree graph `graph G a`.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
-/

@[expose] public section

namespace Cslib.Reachability.Reingold

open RotationMap

/-- The labels of the graphs of Reingold's transformation: the `257 ^ 8` vertices of the base graph,
eight coordinates in `ZMod 257`. -/
abbrev Label : Type :=
  AffinePlaneTowerBaseVertex (ZMod 257)

/-- The labels of the base graph: pairs of elements of `ZMod 257`. -/
abbrev BaseLabel : Type :=
  ZMod 257 × ZMod 257

/-- The base graph of the transformation: the arithmetic zig-zag base graph over `ZMod 257`, a
`257 ^ 2`-regular multigraph on `257 ^ 8` vertices. -/
def base : RotationMap Label BaseLabel :=
  have : Fact (Nat.Prime 257) := ⟨by norm_num⟩
  affinePlaneTowerBase (ZMod 257)

/-- The vertices of the base graph name the pairs of pairs of its labels. -/
def baseEquiv : Label ≃ (Fin 2 → BaseLabel × BaseLabel) :=
  affinePlaneTowerBaseEquiv (ZMod 257)

/-- There are `257 ^ 8` labels. -/
theorem card_label : Fintype.card Label = 257 ^ 8 := by
  simp only [Label, AffinePlaneTowerBaseVertex, Fintype.card_prod, ZMod.card]
  norm_num

/-- **The base graph is a good expander**: its spectral expansion is at most `1 / 5`. -/
theorem spectralExpansion_base_le : base.spectralExpansion ≤ 1 / 5 := by
  have : Fact (Nat.Prime 257) := ⟨by norm_num⟩
  exact spectralExpansion_affinePlaneTowerBase_le_one_div_five (ZMod 257)
    (by rw [ZMod.card]; norm_num)

/-- The three labels of the slot graph, as labels of the base graph. -/
def slotLabel : SlotLabel ↪ Label where
  toFun
    | .inl () => ((((0, 0), (0, 0)), (0, 0)), (0, 0))
    | .inr ((), (), false) => ((((1, 0), (0, 0)), (0, 0)), (0, 0))
    | .inr ((), (), true) => ((((2, 0), (0, 0)), (0, 0)), (0, 0))
  inj' := Function.LeftInverse.injective
    (g := fun b ↦ if b.1.1.1.1 = 1 then .inr ((), (), false)
      else if b.1.1.1.1 = 2 then .inr ((), (), true) else .inl ())
    (by rintro (_ | ⟨_, _, _ | _⟩) <;> rfl)

section Input

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- The regular rotation map of a simple graph on `Fin n`: its slot graph, with the slots of a
vertex in the cyclic order of `finRotate n`, with self-loops added to reach the labels of the base
graph. -/
def input : RotationMap (Fin n × Fin n) Label :=
  (slotGraph G (finRotate n)).extendLabels slotLabel

/-- **The regular rotation map has the connectivity of the simple graph**: a slot `q` is reachable
from a slot `p` exactly when the vertex of `q` is reachable from the vertex of `p` in `G`. -/
theorem reachable_input_iff {p q : Fin n × Fin n} :
    (input G).toSimpleGraph.Reachable p q ↔ G.Reachable p.1 q.1 := by
  rw [input, toSimpleGraph_extendLabels]
  exact reachable_slotGraph_iff G _ Equiv.Perm.sameCycle_finRotate

/-- At least half of the edges at every vertex of the regular rotation map are self-loops. -/
theorem card_le_two_mul_edgeCount_input (v : Fin n × Fin n) :
    Fintype.card Label ≤ 2 * (input G).edgeCount v v :=
  (slotGraph G (finRotate n)).card_le_two_mul_edgeCount_extendLabels slotLabel
    (by rw [card_slotLabel, card_label]; norm_num) v

end Input

/-- The number of steps of the transformation for graphs on at most `2 ^ a` vertices:
`16 a + 524`. -/
def depth (a : ℕ) : ℕ :=
  16 * a + 524

/-- The length of the walks for graphs on at most `2 ^ a` vertices: `4 (2 a + 65 depth a)`. -/
def walkLength (a : ℕ) : ℕ :=
  4 * (2 * a + 65 * depth a)

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- **Reingold's graph** of a simple graph on `Fin n`: `depth a` steps of Reingold's transformation
applied to its regular rotation map, a `257 ^ 8`-regular multigraph. -/
def graph (a : ℕ) : RotationMap (IteratedProd (Fin n × Fin n) Label (depth a)) Label :=
  reingold base baseEquiv (input G) (depth a)

/-- The start vertex of the walks from `s`: the vertex `(⋯ ((s, s), 0) ⋯, 0)` of Reingold's graph,
over the slot `(s, s)`. -/
def start (s : Fin n) (a : ℕ) : IteratedProd (Fin n × Fin n) Label (depth a) :=
  IteratedProd.mk (s, s) 0 (depth a)

/-- The number of steps suffices: `2 |V|² |B|² 5 ^ ℓ ≤ 5 · 6 ^ ℓ` for the `n ^ 2` slots and the
`257 ^ 8` labels. -/
private theorem depth_bound {a : ℕ} (hn : n ≤ 2 ^ a) :
    2 * (n * n) ^ 2 * (257 ^ 8) ^ 2 * 5 ^ depth a ≤ 5 * 6 ^ depth a := by
  set m := 4 * a + 131
  have hℓ : depth a = 4 * m := by simp only [depth, m]; ring
  have h₁ : 2 * (n * n) ^ 2 * (257 ^ 8) ^ 2 ≤ 2 ^ m :=
    calc 2 * (n * n) ^ 2 * (257 ^ 8) ^ 2 ≤ 2 * (2 ^ a * 2 ^ a) ^ 2 * 2 ^ 130 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.mul_le_mul hn hn) 2))
            (by norm_num)
      _ = 2 ^ m := by simp only [m]; ring
  rw [hℓ, pow_mul, pow_mul]
  calc 2 * (n * n) ^ 2 * (257 ^ 8) ^ 2 * (5 ^ 4) ^ m ≤ 2 ^ m * (5 ^ 4) ^ m := by gcongr
    _ = 1250 ^ m := by rw [← mul_pow]; norm_num
    _ ≤ 1296 ^ m := Nat.pow_le_pow_left (by norm_num) m
    _ = (6 ^ 4) ^ m := by norm_num
    _ ≤ 5 * (6 ^ 4) ^ m := Nat.le_mul_of_pos_left _ (by norm_num)

/-- The walk length suffices: `|V| |B| ^ ℓ 4 ^ T ≤ 5 ^ T` for the `n ^ 2` slots and the `257 ^ 8`
labels. -/
private theorem length_bound {a : ℕ} (hn : n ≤ 2 ^ a) :
    n * n * (257 ^ 8) ^ depth a * 4 ^ walkLength a ≤ 5 ^ walkLength a := by
  rw [show walkLength a = 4 * (2 * a + 65 * depth a) from rfl]
  generalize depth a = ℓ
  set m := 2 * a + 65 * ℓ with hm
  have h₁ : n * n * (257 ^ 8) ^ ℓ ≤ 2 ^ m :=
    calc n * n * (257 ^ 8) ^ ℓ ≤ 2 ^ a * 2 ^ a * (2 ^ 65) ^ ℓ :=
          Nat.mul_le_mul (Nat.mul_le_mul hn hn) (Nat.pow_le_pow_left (by norm_num) _)
      _ = 2 ^ m := by
          rw [← pow_add, ← pow_mul, ← pow_add, hm]
          congr 1
          ring
  rw [pow_mul, pow_mul]
  calc n * n * (257 ^ 8) ^ ℓ * (4 ^ 4) ^ m ≤ 2 ^ m * (4 ^ 4) ^ m := by gcongr
    _ = 512 ^ m := by rw [← mul_pow]; norm_num
    _ ≤ 625 ^ m := Nat.pow_le_pow_left (by norm_num) m
    _ = (5 ^ 4) ^ m := by norm_num

/-- **Undirected connectivity by short walks in Reingold's graph**, the combinatorial part of the
proof of [Reingold, Theorem 4.1][Reingold2008] [Arora and Barak, Section 21.4][AroraBarak09]: for
a simple graph `G` on `Fin n` with `n ≤ 2 ^ a`, `t` is reachable from `s` exactly when some walk of
length `walkLength a` in the `257 ^ 8`-regular graph `graph G a` from `start s a` ends at a vertex
over a slot `(t, w)` of `t`. -/
theorem reachable_iff_exists_walk_of_le_two_pow {a : ℕ} (ha : n ≤ 2 ^ a) (s t : Fin n) :
    G.Reachable s t ↔ ∃ k : Fin (walkLength a) → Label,
      (((graph G a).pow (walkLength a)).neighbor (start s a) k).root.1 = t := by
  have hloop := card_le_two_mul_edgeCount_input G
  have hV : Fintype.card (Fin n × Fin n) = n * n := by
    rw [Fintype.card_prod, Fintype.card_fin]
  have hℓ : 2 * Fintype.card (Fin n × Fin n) ^ 2 * Fintype.card Label ^ 2 *
      5 ^ depth a ≤ 5 * 6 ^ depth a := by
    rw [hV, card_label]
    exact depth_bound ha
  have hT : Fintype.card (Fin n × Fin n) * Fintype.card Label ^ depth a *
      4 ^ walkLength a ≤ 5 ^ walkLength a := by
    rw [hV, card_label]
    exact length_bound ha
  have key := reachable_iff_exists_root_neighbor_pow_reingold base baseEquiv
    spectralExpansion_base_le (input G) hloop hℓ hT (s, s) (t, t) 0
  refine ⟨fun h ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · obtain ⟨k, hk⟩ := key.1 ((reachable_input_iff G).2 h)
    exact ⟨k, by rw [graph, start, hk]⟩
  · have h := reachable_root_neighbor_pow_reingold base baseEquiv (input G)
      (depth a) (walkLength a) (start s a) k
    rw [start, IteratedProd.root_mk] at h
    rw [← hk]
    exact (reachable_input_iff G).1 h

/-- **Undirected connectivity by short walks in Reingold's graph**, with `a = ⌈log₂ n⌉`: `t` is
reachable from `s` exactly when some walk of length `walkLength ⌈log₂ n⌉ = O(log n)` in the
`257 ^ 8`-regular graph `graph G ⌈log₂ n⌉` from `start s ⌈log₂ n⌉` ends over a slot of `t`. -/
theorem reachable_iff_exists_walk (s t : Fin n) :
    G.Reachable s t ↔ ∃ k : Fin (walkLength (Nat.clog 2 n)) → Label,
      (((graph G (Nat.clog 2 n)).pow (walkLength (Nat.clog 2 n))).neighbor
        (start s (Nat.clog 2 n)) k).root.1 = t :=
  reachable_iff_exists_walk_of_le_two_pow G (Nat.le_pow_clog (by norm_num) n) s t

end Cslib.Reachability.Reingold
