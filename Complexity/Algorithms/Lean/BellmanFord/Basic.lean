/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Combinatorics.Quiver.Path.Weight
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Order.Monoid.WithTop
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Complexity.Algorithms.Lean.TimeM.Loops
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring

/-!
# The Bellman–Ford algorithm

Single-source shortest paths with possibly negative edge weights, and detection of negative
cycles, by the Bellman–Ford algorithm [Bellman][Bellman1958] [Cormen et al., Section
24.1][CLRS2009].

## Model

A weighted directed graph is given by adjacency lists `adj : V → List (V × W)`: the entry
`(v, w) ∈ adj u` is an edge from `u` to `v` of weight `w`; parallel edges and self-loops are
allowed. Weights lie in a linearly ordered cancellative additive commutative monoid `W` (for
example `ℤ`, `ℚ` or `ℝ`), and estimates in `WithTop W`, with `⊤` for "no walk found yet". Walks
are paths (`Quiver.Path`) in the quiver `Cslib.Algorithms.Lean.BellmanFord.Vertex adj`, as for
Dijkstra's `Cslib.Algorithms.WordRAM.Dijkstra.Instance.dist`, and
`Cslib.Algorithms.Lean.BellmanFord.walkWeight` is the sum of the edge weights.

The algorithm is given a list `vs` of all the vertices (`hvs : ∀ v, v ∈ vs`). It starts from `0` at
the source and `⊤` elsewhere, relaxes every edge in `|vs| - 1` rounds, and then checks whether
some edge can still be relaxed.

## Main definitions

* `Cslib.Algorithms.Lean.BellmanFord.NegCycleReachable`: a closed walk of negative weight is
  reachable from the source.
* `Cslib.Algorithms.Lean.BellmanFord.IsShortestDist`: `d` is the least weight of a walk from `s` to
  `v`, and `⊤` when there is none.
* `Cslib.Algorithms.Lean.BellmanFord.bellmanFord`: the algorithm, returning the estimates, or
  `none` when an edge can still be relaxed.
* `Cslib.Algorithms.Lean.BellmanFord.bellmanFordM`: the algorithm in `TimeM`.

## Main results

* `Cslib.Algorithms.Lean.BellmanFord.bellmanFord_eq_none_iff`: Bellman–Ford returns `none` exactly
  when a negative cycle is reachable from the source.
* `Cslib.Algorithms.Lean.BellmanFord.isShortestDist_of_bellmanFord_eq_some`: otherwise every
  returned estimate is the shortest-path weight. Together these are [Cormen et al., Theorem
  24.4][CLRS2009] without the predecessor tree.
* `Cslib.Algorithms.Lean.BellmanFord.iterate_round_le_walkWeight`: after `k` rounds each estimate is
  at most the weight of every walk from the source with at most `k` edges (the path-relaxation
  argument of [Cormen et al., Lemma 24.2][CLRS2009]).
* `Cslib.Algorithms.Lean.BellmanFord.exists_walk_of_iterate_round_eq`: every finite estimate is the
  weight of a walk from the source.
* `Cslib.Algorithms.Lean.BellmanFord.exists_nodup_walk_le`: with no negative cycle reachable from
  the source, every walk from it can be shortened to one without repeated vertices.
* `Cslib.Algorithms.Lean.BellmanFord.time_bellmanFordM`,
  `Cslib.Algorithms.Lean.BellmanFord.time_bellmanFordM_of_nodup`: the cost is exactly
  `n + n (n + m)` for `n` listed vertices and `m` edges, that is `O(V E)` when `E ≥ V`.

## Cost model

`Cslib.Algorithms.Lean.BellmanFord.bellmanFordM` charges one unit per vertex to initialize, and in
each of the `|vs| - 1` rounds and in the final check one unit per vertex scanned and one per edge
relaxed or tested. Reading and updating an estimate and adding or comparing weights are counted
as constant-time steps, as on a machine with an array of estimates and unit-cost arithmetic.

## References

* [R. Bellman, *On a routing problem*][Bellman1958]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.BellmanFord

variable {V : Type*} {W : Type*}

section Defs

/-- The vertices of the weighted digraph `adj`, as a quiver: an arrow from `u` to `v` is a weight
`w` with `(v, w) ∈ adj u`. -/
def Vertex (_adj : V → List (V × W)) : Type _ := V

instance (adj : V → List (V × W)) : Quiver (Vertex adj) where
  Hom u v := {w : W // ((v : V), w) ∈ adj (u : V)}

/-- A walk in `adj` from `u` to `v`: a path in the quiver `Vertex adj`. -/
abbrev Walk (adj : V → List (V × W)) (u v : V) : Type _ := Quiver.Path (V := Vertex adj) u v

/-- Extend a walk by an edge. -/
def Walk.snoc {adj : V → List (V × W)} {u v x : V} (p : Walk adj u v) {w : W}
    (h : (x, w) ∈ adj v) : Walk adj u x :=
  Quiver.Path.cons (V := Vertex adj) p (⟨w, h⟩ : {w : W // (x, w) ∈ adj v})

/-- Induction on walks, with vertices in `V`. -/
@[elab_as_elim]
theorem Walk.induction {adj : V → List (V × W)} {u : V} {motive : ∀ v : V, Walk adj u v → Prop}
    (nil : motive u Quiver.Path.nil)
    (snoc : ∀ {v x : V} {w : W} (p : Walk adj u v) (h : (x, w) ∈ adj v), motive v p →
      motive x (p.snoc h))
    {v : V} (p : Walk adj u v) : motive v p := by
  induction p with
  | nil => exact nil
  | cons p e ih => exact snoc p e.2 ih

/-- The vertices visited by a walk, in order. -/
def Walk.support {adj : V → List (V × W)} {u v : V} (p : Walk adj u v) : List V :=
  Quiver.Path.vertices (V := Vertex adj) p

section Support

variable {adj : V → List (V × W)}

@[simp] theorem Walk.support_nil {u : V} : Walk.support (Quiver.Path.nil : Walk adj u u) = [u] :=
  rfl

@[simp] theorem Walk.support_snoc {u v x : V} (p : Walk adj u v) {w : W} (h : (x, w) ∈ adj v) :
    (p.snoc h).support = p.support.concat x :=
  Quiver.Path.vertices_cons _ _

theorem Walk.support_comp {u v x : V} (p : Walk adj u v) (q : Walk adj v x) :
    Walk.support (Quiver.Path.comp p q) = p.support.dropLast ++ q.support :=
  Quiver.Path.vertices_comp p q

@[simp] theorem Walk.dropLast_support_append {u v : V} (p : Walk adj u v) :
    p.support.dropLast ++ [v] = p.support :=
  Quiver.Path.dropLast_append_end_eq p

theorem Walk.start_mem_support {u v : V} (p : Walk adj u v) : u ∈ p.support :=
  Quiver.Path.start_mem_vertices p

theorem Walk.length_support {u v : V} (p : Walk adj u v) : p.support.length = p.length + 1 :=
  Quiver.Path.vertices_length p

/-- A walk through `x` splits at `x`. -/
theorem Walk.exists_eq_comp_of_mem_support {u v x : V} (p : Walk adj u v) (hx : x ∈ p.support) :
    ∃ (p₁ : Walk adj u x) (p₂ : Walk adj x v), p = Quiver.Path.comp p₁ p₂ :=
  Quiver.Path.exists_eq_comp_of_mem_vertices p hx

/-- A walk with no repeated vertex has fewer edges than there are vertices. -/
theorem Walk.length_lt_of_nodup {vs : List V} (hvs : ∀ v, v ∈ vs) {u v : V} (p : Walk adj u v)
    (hp : p.support.Nodup) : p.length < vs.length := by
  have h := (hp.subperm fun x _ => hvs x).length_le
  rw [Walk.length_support] at h
  omega

end Support

variable [AddMonoid W]

/-- The weight of a walk: the sum of the weights of its edges. -/
def walkWeight {adj : V → List (V × W)} {u v : V} (p : Walk adj u v) : W :=
  Quiver.Path.addWeight (V := Vertex adj)
    (fun {i j} (e : i ⟶ j) => (show {w : W // ((j : V), w) ∈ adj (i : V)} from e).1) p

@[simp] theorem walkWeight_nil {adj : V → List (V × W)} {u : V} :
    walkWeight (Quiver.Path.nil : Walk adj u u) = 0 :=
  Quiver.Path.addWeight_nil _ _

@[simp] theorem walkWeight_snoc {adj : V → List (V × W)} {u v x : V} (p : Walk adj u v) {w : W}
    (h : (x, w) ∈ adj v) : walkWeight (p.snoc h) = walkWeight p + w :=
  Quiver.Path.addWeight_cons _ _ _

@[simp] theorem walkWeight_comp {adj : V → List (V × W)} {u v x : V} (p : Walk adj u v)
    (q : Walk adj v x) : walkWeight (p.comp q) = walkWeight p + walkWeight q :=
  Quiver.Path.addWeight_comp _ p q

/-- A cycle of negative weight is reachable from `s`: some vertex `v` reachable from `s` lies on a
closed walk of negative weight. -/
def NegCycleReachable [Preorder W] (adj : V → List (V × W)) (s : V) : Prop :=
  ∃ v, Nonempty (Walk adj s v) ∧ ∃ c : Walk adj v v, walkWeight c < 0

/-- `d` is the **shortest-path weight** from `s` to `v`: the least weight of a walk from `s` to
`v`, and `⊤` when there is none. -/
def IsShortestDist [Preorder W] (adj : V → List (V × W)) (s v : V) (d : WithTop W) : Prop :=
  IsLeast (insert ⊤ (Set.range fun p : Walk adj s v => ((walkWeight p : W) : WithTop W))) d

end Defs

section Algorithm

variable [DecidableEq V] [AddCommMonoid W] [LinearOrder W]

/-- Relax the edge from `u` to `v` of weight `w`: lower the estimate of `v` to `d u + w` if that
is smaller. -/
def relax (d : V → WithTop W) (u v : V) (w : W) : V → WithTop W :=
  if d u + w < d v then Function.update d v (d u + w) else d

/-- One round of Bellman–Ford: relax every edge, scanning the vertices `vs` and their adjacency
lists in order. -/
def round (adj : V → List (V × W)) (vs : List V) (d : V → WithTop W) : V → WithTop W :=
  vs.foldl (fun d u => (adj u).foldl (fun d e => relax d u e.1 e.2) d) d

/-- The initial estimates: `0` at the source and `⊤` elsewhere. -/
def init (s : V) : V → WithTop W := Function.update (fun _ => ⊤) s 0

/-- The estimates after `|vs| - 1` rounds from the source `s`. -/
def distances (adj : V → List (V × W)) (vs : List V) (s : V) : V → WithTop W :=
  (round adj vs)^[vs.length - 1] (init s)

/-- Whether no edge can be relaxed further. -/
def check (adj : V → List (V × W)) (vs : List V) (d : V → WithTop W) : Bool :=
  vs.all fun u => (adj u).all fun e => d e.1 ≤ d u + e.2

/-- **The Bellman–Ford algorithm** from the source `s`: the estimates after `|vs| - 1` rounds if no
edge can be relaxed further, and `none` (a negative cycle) otherwise. -/
def bellmanFord (adj : V → List (V × W)) (vs : List V) (s : V) : Option (V → WithTop W) :=
  if check adj vs (distances adj vs s) then some (distances adj vs s) else none

section Proof

variable {adj : V → List (V × W)} {vs : List V} {s : V}

/-! ### Monotonicity and soundness -/

theorem relax_le (d : V → WithTop W) (u v : V) (w : W) : relax d u v w ≤ d := by
  intro x
  unfold relax
  split_ifs with h
  · rcases eq_or_ne x v with rfl | hx
    · simpa using h.le
    · simp [hx]
  · exact le_rfl

theorem relax_apply_le (d : V → WithTop W) (u v : V) (w : W) : relax d u v w v ≤ d u + w := by
  unfold relax
  split_ifs with h
  · simp
  · exact not_lt.1 h

private theorem scan_le (u : V) (l : List (V × W)) (d : V → WithTop W) :
    l.foldl (fun d e => relax d u e.1 e.2) d ≤ d :=
  List.foldlRecOn (motive := (· ≤ d)) l _ le_rfl fun _ hb e _ => (relax_le _ u e.1 e.2).trans hb

/-- A round only lowers the estimates. -/
theorem round_le (d : V → WithTop W) : round adj vs d ≤ d :=
  List.foldlRecOn (motive := (· ≤ d)) vs _ le_rfl fun _ hb u _ => (scan_le u (adj u) _).trans hb

theorem iterate_round_le (k : ℕ) (d : V → WithTop W) : (round adj vs)^[k] d ≤ d := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => rw [Function.iterate_succ_apply']; exact (round_le _).trans ih

omit [LinearOrder W] in
theorem init_self (s : V) : init (W := W) s s = 0 := by simp [init]

/-- Every finite estimate is the weight of a walk from `s`. -/
private def Sound (adj : V → List (V × W)) (s : V) (d : V → WithTop W) : Prop :=
  ∀ v (x : W), d v = x → ∃ p : Walk adj s v, walkWeight p = x

omit [LinearOrder W] in
private theorem sound_init : Sound adj s (init s) := by
  intro v x h
  rcases eq_or_ne v s with rfl | hv
  · rw [init_self] at h
    exact ⟨.nil, by rw [walkWeight_nil]; exact (WithTop.coe_eq_zero.1 h.symm).symm⟩
  · simp [init, hv] at h

private theorem sound_relax {d : V → WithTop W} (hd : Sound adj s d) {u v : V} {w : W}
    (huv : (v, w) ∈ adj u) : Sound adj s (relax d u v w) := by
  intro x y h
  unfold relax at h
  split_ifs at h with hlt
  · rcases eq_or_ne x v with hxv | hxv
    · subst hxv
      rw [Function.update_self] at h
      have hu : d u ≠ ⊤ := by
        rintro hu
        rw [hu, WithTop.top_add] at h
        exact WithTop.top_ne_coe h
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hu
      obtain ⟨p, hp⟩ := hd u a ha.symm
      refine ⟨p.snoc huv, ?_⟩
      rw [walkWeight_snoc, hp]
      rw [← ha, ← WithTop.coe_add] at h
      exact_mod_cast h
    · rw [Function.update_of_ne hxv] at h
      exact hd x y h
  · exact hd x y h

private theorem sound_scan {d : V → WithTop W} (hd : Sound adj s d) (u : V) :
    Sound adj s ((adj u).foldl (fun d e => relax d u e.1 e.2) d) :=
  List.foldlRecOn (motive := Sound adj s) (adj u) _ hd fun _ hb _ he => sound_relax hb he

private theorem sound_round {d : V → WithTop W} (hd : Sound adj s d) :
    Sound adj s (round adj vs d) :=
  List.foldlRecOn (motive := Sound adj s) vs _ hd fun _ hb u _ => sound_scan hb u

private theorem sound_iterate (k : ℕ) : Sound adj s ((round adj vs)^[k] (init s)) := by
  induction k with
  | zero => exact sound_init
  | succ k ih => rw [Function.iterate_succ_apply']; exact sound_round ih

/-- **Soundness**: every finite estimate after any number of rounds is the weight of a walk from
the source. -/
theorem exists_walk_of_iterate_round_eq (k : ℕ) {v : V} {x : W}
    (h : (round adj vs)^[k] (init s) v = x) : ∃ p : Walk adj s v, walkWeight p = x :=
  sound_iterate k v x h

omit [DecidableEq V] in
theorem check_iff (d : V → WithTop W) :
    check adj vs d = true ↔ ∀ u ∈ vs, ∀ v w, (v, w) ∈ adj u → d v ≤ d u + w := by
  simp [check]

/-! ### Upper bound -/

variable [IsOrderedCancelAddMonoid W]

private theorem scan_apply_le (u : V) {v : V} {w : W} :
    ∀ (l : List (V × W)), (v, w) ∈ l → ∀ (d : V → WithTop W) (c : WithTop W), d u ≤ c →
      l.foldl (fun d e => relax d u e.1 e.2) d v ≤ c + w
  | [], h, _, _, _ => by simp at h
  | e :: l, h, d, c, hc => by
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact (scan_le u l _ v).trans ((relax_apply_le d u v w).trans (add_le_add hc le_rfl))
    · exact scan_apply_le u l h _ c ((relax_le d u e.1 e.2 u).trans hc)

private theorem foldl_round_apply_le {u v : V} {w : W} (hv : (v, w) ∈ adj u) :
    ∀ (l : List V), u ∈ l → ∀ (d : V → WithTop W) (c : WithTop W), d u ≤ c →
      round adj l d v ≤ c + w
  | [], h, _, _, _ => by simp at h
  | x :: l, h, d, c, hc => by
    rw [round, List.foldl_cons]
    rcases List.mem_cons.1 h with hux | h
    · subst hux
      exact (round_le (adj := adj) (vs := l) _ v).trans (scan_apply_le u (adj u) hv d c hc)
    · exact foldl_round_apply_le hv l h _ c ((scan_le x (adj x) d u).trans hc)

/-- After a round, every edge `(u, v)` of weight `w` satisfies `d v ≤ d u + w` for the estimates
`d` before the round. -/
theorem round_apply_le {u : V} (hu : u ∈ vs) {v : V} {w : W} (hv : (v, w) ∈ adj u)
    (d : V → WithTop W) : round adj vs d v ≤ d u + w :=
  foldl_round_apply_le hv vs hu d (d u) le_rfl

/-- **Upper bound**: after `k` rounds the estimate of `v` is at most the weight of every walk from
`s` to `v` with at most `k` edges. -/
theorem iterate_round_le_walkWeight (hvs : ∀ v, v ∈ vs) {v : V} (p : Walk adj s v) (k : ℕ)
    (hk : p.length ≤ k) : (round adj vs)^[k] (init s) v ≤ walkWeight p := by
  induction p using Walk.induction generalizing k with
  | nil =>
    rw [walkWeight_nil, WithTop.coe_zero, ← init_self (W := W) s]
    exact iterate_round_le k (init s) s
  | @snoc b c w p hw ih =>
    cases k with
    | zero => exact absurd hk (Nat.not_succ_le_zero _)
    | succ k =>
      rw [Function.iterate_succ_apply', walkWeight_snoc, WithTop.coe_add]
      exact (round_apply_le (hvs _) hw _).trans
        (add_le_add (ih k (Nat.le_of_succ_le_succ hk)) le_rfl)

/-! ### Simple walks -/

omit [DecidableEq V] in
/-- With no negative cycle reachable from `s`, every walk from `s` can be shortened to a walk with
no repeated vertex. -/
theorem exists_nodup_walk_le (hneg : ¬ NegCycleReachable adj s) {v : V} (p : Walk adj s v) :
    ∃ q : Walk adj s v, q.support.Nodup ∧ walkWeight q ≤ walkWeight p := by
  induction p using Walk.induction with
  | nil => exact ⟨.nil, by rw [Walk.support_nil]; exact List.nodup_singleton _, le_rfl⟩
  | @snoc b c w p hw ih =>
    obtain ⟨q, hq, hqp⟩ := ih
    by_cases hc : c ∈ q.support
    · obtain ⟨q₁, q₂, rfl⟩ := Walk.exists_eq_comp_of_mem_support q hc
      have hcyc : 0 ≤ walkWeight (Walk.snoc q₂ hw) :=
        not_lt.1 fun h => hneg ⟨c, ⟨q₁⟩, Walk.snoc q₂ hw, h⟩
      refine ⟨q₁, ?_, ?_⟩
      · rw [Walk.support_comp] at hq
        refine hq.sublist ?_
        rw [← Walk.dropLast_support_append q₁]
        exact List.Sublist.append (by rw [Walk.dropLast_support_append])
          (List.singleton_sublist.2 (Walk.start_mem_support q₂))
      · rw [walkWeight_snoc] at hcyc
        rw [walkWeight_comp] at hqp
        rw [walkWeight_snoc]
        calc walkWeight q₁ ≤ walkWeight q₁ + (walkWeight q₂ + w) := le_add_of_nonneg_right hcyc
          _ = walkWeight q₁ + walkWeight q₂ + w := (add_assoc _ _ _).symm
          _ ≤ walkWeight p + w := add_le_add hqp le_rfl
    · refine ⟨Walk.snoc q hw, ?_, ?_⟩
      · rw [Walk.support_snoc]
        exact hq.concat hc
      · rw [walkWeight_snoc, walkWeight_snoc]
        exact add_le_add hqp le_rfl

/-! ### Correctness -/

omit [IsOrderedCancelAddMonoid W] in
theorem distances_self_le : distances adj vs s s ≤ 0 :=
  (iterate_round_le _ (init s) s).trans (init_self s).le

/-- **Upper bound**: with no negative cycle reachable from `s`, the estimates after `|vs| - 1`
rounds are at most the weight of every walk from `s`. -/
theorem distances_le_walkWeight (hvs : ∀ v, v ∈ vs) (hneg : ¬ NegCycleReachable adj s) {v : V}
    (p : Walk adj s v) : distances adj vs s v ≤ walkWeight p := by
  obtain ⟨q, hq, hqp⟩ := exists_nodup_walk_le hneg p
  have := Walk.length_lt_of_nodup hvs q hq
  exact (iterate_round_le_walkWeight hvs q _ (by omega)).trans (WithTop.coe_le_coe.2 hqp)

/-- With no negative cycle reachable from `s`, no edge can be relaxed after `|vs| - 1` rounds. -/
theorem check_distances (hvs : ∀ v, v ∈ vs) (hneg : ¬ NegCycleReachable adj s) :
    check adj vs (distances adj vs s) = true := by
  rw [check_iff]
  intro u _ v w huv
  by_cases hu : distances adj vs s u = ⊤
  · rw [hu, WithTop.top_add]
    exact le_top
  · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hu
    obtain ⟨p, hp⟩ := exists_walk_of_iterate_round_eq (vs.length - 1) ha.symm
    calc distances adj vs s v ≤ walkWeight (Walk.snoc p huv) := distances_le_walkWeight hvs hneg _
      _ = distances adj vs s u + w := by rw [walkWeight_snoc, hp, ← ha, WithTop.coe_add]

omit [DecidableEq V] in
/-- Estimates passing the check satisfy `d b ≤ d a + w(p)` along every walk `p` from `a` to `b`. -/
theorem le_add_walkWeight_of_check {d : V → WithTop W} (hd : check adj vs d = true)
    (hvs : ∀ v, v ∈ vs) {a b : V} (p : Walk adj a b) : d b ≤ d a + walkWeight p := by
  induction p using Walk.induction with
  | nil => rw [walkWeight_nil, WithTop.coe_zero, add_zero]
  | @snoc b c w p hw ih =>
    rw [walkWeight_snoc, WithTop.coe_add, ← add_assoc]
    exact ((check_iff d).1 hd b (hvs b) c w hw).trans (add_le_add ih le_rfl)

/-- If the check passes after `|vs| - 1` rounds, no negative cycle is reachable from `s`. -/
theorem not_negCycleReachable_of_check (hvs : ∀ v, v ∈ vs)
    (hd : check adj vs (distances adj vs s) = true) : ¬ NegCycleReachable adj s := by
  rintro ⟨v, ⟨p⟩, c, hc⟩
  have hv : distances adj vs s v ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (le_add_walkWeight_of_check hd hvs p)
    exact WithTop.add_ne_top.2 ⟨ne_top_of_le_ne_top WithTop.zero_ne_top distances_self_le,
      WithTop.coe_ne_top⟩
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hv
  have h := le_add_walkWeight_of_check hd hvs c
  rw [← ha, ← WithTop.coe_add, WithTop.coe_le_coe] at h
  exact absurd ((le_add_iff_nonneg_right a).1 h) (not_le.2 hc)

/-- **Negative-cycle detection**: Bellman–Ford reports `none` exactly when a cycle of negative
weight is reachable from the source. -/
theorem bellmanFord_eq_none_iff (hvs : ∀ v, v ∈ vs) :
    bellmanFord adj vs s = none ↔ NegCycleReachable adj s := by
  unfold bellmanFord
  split_ifs with h
  · simp only [false_iff]
    exact not_negCycleReachable_of_check hvs h
  · simp only [true_iff]
    by_contra hneg
    exact h (check_distances hvs hneg)

/-- **Shortest paths**: when Bellman–Ford returns estimates, each is the shortest-path weight from
the source. -/
theorem isShortestDist_of_bellmanFord_eq_some (hvs : ∀ v, v ∈ vs) {d : V → WithTop W}
    (h : bellmanFord adj vs s = some d) (v : V) : IsShortestDist adj s v (d v) := by
  unfold bellmanFord at h
  split_ifs at h with hd
  cases h
  refine ⟨?_, ?_⟩
  · by_cases hv : distances adj vs s v = ⊤
    · exact Or.inl hv
    · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hv
      obtain ⟨p, hp⟩ := exists_walk_of_iterate_round_eq (vs.length - 1) ha.symm
      exact Or.inr ⟨p, by simp only [hp, ha]⟩
  · rintro x (rfl | ⟨p, rfl⟩)
    · exact le_top
    · refine (le_add_walkWeight_of_check hd hvs p).trans ?_
      calc distances adj vs s s + walkWeight p ≤ 0 + walkWeight p :=
            add_le_add distances_self_le le_rfl
        _ = walkWeight p := zero_add _

/-- With no negative cycle reachable from `s`, Bellman–Ford returns the estimates after
`|vs| - 1` rounds. -/
theorem bellmanFord_eq_some (hvs : ∀ v, v ∈ vs) (hneg : ¬ NegCycleReachable adj s) :
    bellmanFord adj vs s = some (distances adj vs s) := by
  rw [bellmanFord, ite_eq_left_iff.2 fun h => absurd (check_distances hvs hneg) h]

end Proof

/-! ### Cost -/

section Cost

open TimeM

/-- `relax` in `TimeM`, charging one unit (a comparison and at most one update). -/
def relaxM (d : V → WithTop W) (u v : V) (w : W) : TimeM ℕ (V → WithTop W) := do
  ✓ return relax d u v w

/-- Relax the out-edges of `u` in `TimeM`, charging one unit for `u` and one per edge. -/
def scanM (adj : V → List (V × W)) (d : V → WithTop W) (u : V) : TimeM ℕ (V → WithTop W) := do
  ✓ (adj u).foldlM (fun d e => relaxM d u e.1 e.2) d

/-- `round` in `TimeM`. -/
def roundM (adj : V → List (V × W)) (vs : List V) (d : V → WithTop W) :
    TimeM ℕ (V → WithTop W) :=
  vs.foldlM (scanM adj) d

/-- `k` rounds in `TimeM`. -/
def roundsM (adj : V → List (V × W)) (vs : List V) : ℕ → (V → WithTop W) → TimeM ℕ (V → WithTop W)
  | 0, d => pure d
  | k + 1, d => do
    let d ← roundsM adj vs k d
    roundM adj vs d

/-- Test one edge in `TimeM`, charging one unit: keep `o` if the edge from `u` to `e.1` cannot
be relaxed, and give `none` otherwise. -/
def testM (d : V → WithTop W) (u : V) (o : Option (V → WithTop W)) (e : V × W) :
    TimeM ℕ (Option (V → WithTop W)) := do
  ✓ return bif decide (d e.1 ≤ d u + e.2) then o else none

/-- Test the out-edges of `u` in `TimeM`, charging one unit for `u` and one per edge. -/
def checkScanM (adj : V → List (V × W)) (d : V → WithTop W) (o : Option (V → WithTop W))
    (u : V) : TimeM ℕ (Option (V → WithTop W)) := do
  ✓ (adj u).foldlM (testM d u) o

/-- `check` in `TimeM`, charging one unit per vertex and one per edge (without short-circuiting):
`some d` if no edge can be relaxed, and `none` otherwise. -/
def checkM (adj : V → List (V × W)) (vs : List V) (d : V → WithTop W) :
    TimeM ℕ (Option (V → WithTop W)) :=
  vs.foldlM (checkScanM adj d) (some d)

/-- `init` in `TimeM`, charging one unit per vertex. -/
def initM (vs : List V) (s : V) : TimeM ℕ (V → WithTop W) := do
  ✓[vs.length] return init s

/-- **The Bellman–Ford algorithm** in `TimeM`. -/
def bellmanFordM (adj : V → List (V × W)) (vs : List V) (s : V) :
    TimeM ℕ (Option (V → WithTop W)) := do
  let d ← initM vs s
  let d ← roundsM adj vs (vs.length - 1) d
  checkM adj vs d

private theorem scanM_spec (adj : V → List (V × W)) (d : V → WithTop W) (u : V) :
    (scanM adj d u).ret = (adj u).foldl (fun d e => relax d u e.1 e.2) d ∧
      (scanM adj d u).time = 1 + (adj u).length := by
  refine ⟨by rw [scanM, TimeM.ret_bind, ret_foldlM]; rfl, ?_⟩
  rw [scanM, TimeM.time_bind, TimeM.time_tick, time_foldlM_eq_sum _ (fun _ => 1) (fun _ _ => rfl)]
  simp

theorem ret_roundM (adj : V → List (V × W)) (vs : List V) (d : V → WithTop W) :
    (roundM adj vs d).ret = round adj vs d := by
  rw [roundM, ret_foldlM, round]
  exact congrArg (fun f => vs.foldl f d) (funext₂ fun d u => (scanM_spec adj d u).1)

theorem time_roundM (adj : V → List (V × W)) (vs : List V) (d : V → WithTop W) :
    (roundM adj vs d).time = vs.length + (vs.map fun u => (adj u).length).sum := by
  rw [roundM, time_foldlM_eq_sum _ _ (fun d u => (scanM_spec adj d u).2), List.sum_map_add]
  simp

theorem ret_roundsM (adj : V → List (V × W)) (vs : List V) (k : ℕ) (d : V → WithTop W) :
    (roundsM adj vs k d).ret = (round adj vs)^[k] d := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [roundsM, TimeM.ret_bind, ret_roundM, ih, Function.iterate_succ_apply']

theorem time_roundsM (adj : V → List (V × W)) (vs : List V) (k : ℕ) (d : V → WithTop W) :
    (roundsM adj vs k d).time = k * (vs.length + (vs.map fun u => (adj u).length).sum) := by
  induction k with
  | zero => simp [roundsM]
  | succ k ih => rw [roundsM, TimeM.time_bind, time_roundM, ih, Nat.succ_mul]

omit [DecidableEq V] [AddCommMonoid W] [LinearOrder W] in
private theorem foldl_cond {α γ : Type*} (q : α → Bool) :
    ∀ (l : List α) (o : Option γ),
      l.foldl (fun o a => bif q a then o else none) o = bif l.all q then o else none
  | [], o => rfl
  | a :: l, o => by
    rw [List.foldl_cons, foldl_cond q l, List.all_cons]
    cases q a <;> cases l.all q <;> rfl

omit [DecidableEq V] in
private theorem checkScanM_spec (adj : V → List (V × W)) (d : V → WithTop W)
    (o : Option (V → WithTop W)) (u : V) :
    (checkScanM adj d o u).ret =
        (bif (adj u).all (fun e => decide (d e.1 ≤ d u + e.2)) then o else none) ∧
      (checkScanM adj d o u).time = 1 + (adj u).length := by
  refine ⟨?_, ?_⟩
  · rw [checkScanM, TimeM.ret_bind, ret_foldlM]
    exact foldl_cond (fun e : V × W => decide (d e.1 ≤ d u + e.2)) (adj u) o
  · rw [checkScanM, TimeM.time_bind, TimeM.time_tick,
      time_foldlM_eq_sum _ (fun _ => 1) (fun _ _ => rfl)]
    simp

omit [DecidableEq V] in
theorem ret_checkM (adj : V → List (V × W)) (vs : List V) (d : V → WithTop W) :
    (checkM adj vs d).ret = if check adj vs d then some d else none := by
  rw [checkM, ret_foldlM, funext₂ fun o u => (checkScanM_spec adj d o u).1, foldl_cond, check,
    cond_eq_ite]

omit [DecidableEq V] in
theorem time_checkM (adj : V → List (V × W)) (vs : List V) (d : V → WithTop W) :
    (checkM adj vs d).time = vs.length + (vs.map fun u => (adj u).length).sum := by
  rw [checkM, time_foldlM_eq_sum _ _ (fun o u => (checkScanM_spec adj d o u).2), List.sum_map_add]
  simp

/-- `bellmanFordM` computes `bellmanFord`. -/
theorem ret_bellmanFordM (adj : V → List (V × W)) (vs : List V) (s : V) :
    (bellmanFordM adj vs s).ret = bellmanFord adj vs s := by
  simp only [bellmanFordM, initM, TimeM.ret_bind, TimeM.ret_pure, ret_roundsM, ret_checkM,
    bellmanFord, distances]
  rfl

/-- **Cost of Bellman–Ford**: `n + n (n + m)` units for `n = |vs|` vertices and `m` adjacency-list
entries, that is, `O(V E)` for a graph with at least as many edges as vertices. -/
theorem time_bellmanFordM (adj : V → List (V × W)) (vs : List V) (s : V) :
    (bellmanFordM adj vs s).time =
      vs.length + vs.length * (vs.length + (vs.map fun u => (adj u).length).sum) := by
  simp only [bellmanFordM, initM, TimeM.time_bind, TimeM.time_tick, TimeM.ret_bind,
    TimeM.ret_pure, TimeM.time_pure, time_roundsM, time_checkM, add_zero]
  cases vs with
  | nil => simp
  | cons a l =>
    simp only [List.length_cons, Nat.add_sub_cancel]
    ring

/-- **Cost of Bellman–Ford on a finite graph**: from a duplicate-free list of all the vertices, the
cost is `|V| + |V| (|V| + |E|)` with `|E| = ∑ v, |adj v|`. -/
theorem time_bellmanFordM_of_nodup [Fintype V] {vs : List V} (hvs : ∀ v, v ∈ vs) (hnd : vs.Nodup)
    (adj : V → List (V × W)) (s : V) :
    (bellmanFordM adj vs s).time =
      Fintype.card V + Fintype.card V * (Fintype.card V + ∑ v, (adj v).length) := by
  have huniv : vs.toFinset = Finset.univ :=
    Finset.eq_univ_of_forall fun v => List.mem_toFinset.2 (hvs v)
  have hcard : vs.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup hnd, huniv, Finset.card_univ]
  rw [time_bellmanFordM, hcard, ← List.sum_toFinset _ hnd, huniv]

end Cost

end Algorithm

end Cslib.Algorithms.Lean.BellmanFord
