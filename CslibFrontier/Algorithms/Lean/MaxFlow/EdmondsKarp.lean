/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.Basic
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card

/-!
# Edmonds–Karp Shortest-Augmenting-Path Algorithm

Formalizes the **Edmonds–Karp algorithm** ([EdmondsKarp1972], Section 1, Theorem 1, pp. 249–253;
[CLRS2009], Section 26.2, Lemma 26.7 and Theorem 26.8, pp. 727–730): augmenting an integral network
flow along breadth-first (fewest-arc) residual `s`-`t` paths guarantees monotonic residual
shortest-path distances and terminates in strongly polynomial time independent of arc capacities.

## Mathematical and algorithmic overview

1. **Residual shortest-path distance (`Flow.resDist`):** for any finite vertex type `V`,
   `f.resDist v : ℕ` is the minimum arc length `< |V|` of a positive-residual-capacity walk from
   `N.s` to `v`, or `|V|` when `v` is unreachable.
2. **Distance monotonicity (`Flow.resDist_le_augmentByBottleneck`):** augmenting `f` along any
   shortest augmenting path `p` (`IsShortestAugmentingPath`) never decreases `resDist v` for any
   vertex `v` ([EdmondsKarp1972], p. 251; [CLRS2009], Lemma 26.7, pp. 727–728).
3. **Critical-arc bound (`Network.shortestAugmentingSeq_length_le`):** each directed residual pair
   `(u, v) ∈ N.symArcs` becomes a bottleneck critical arc at most `|V| / 2` times because
   `resDist u` increases by at least `2` between critical occurrences, bounding any sequence of
   shortest-path augmentations by `N.symArcs.card * (|V| / 2) ≤ |V| * N.posArcs.card`
   ([CLRS2009], Theorem 26.8, p. 729; compare [EdmondsKarp1972], Theorem 1, p. 251, which obtains
   `(|V|^3 - |V|) / 4` by combining source- and sink-distance monotonicity).
4. **Executable `TimeM` solver (`edmondsKarpM`, `edmondsKarpDenseM`):** over `Network (Fin n)` with
   candidate neighbor lists `adj : Fin n → List (Fin n)`, maintains an explicit `n × n` `Vector`
   matrix (`FlowMatrix N`) for `O(1)` flow lookups and arc-by-arc bottleneck updates, finishing in
   at most `(N.symArcs.card * (n / 2) + 2) * (adjSteps adj + 5 * n)` charged steps (`O(|V| |E|^2)`
   on sparse nonempty adjacency lists and `O(n^5)` on `defaultAdj n`).

## Cost model and limitations

* **Charged (`TimeM ℕ` ticks):**
  * `2 * n` ticks in `initFlowMatrixM` (`n` ticks to allocate an all-zero row of length `n` and `n`
    ticks to replicate that row reference across `n` vertices);
  * `n + adjSteps adj` ticks in `countAdjM` to compute sparse fuel `adjSteps adj * (n / 2)`
    without dense `Fin n × Fin n` enumeration;
  * per `bfsM` call (`adjSteps adj + 3 * n` ticks upper bound, `≥ n` ticks lower bound): `n` ticks
    for visited/path-table initialization (`replicateM`), `1` tick per popped frontier vertex
    (`≤ n`), `1` tick per candidate neighbor `v ∈ adj u` (`≤ adjSteps adj`), and either `p.length`
    ticks to reverse the found augmenting path (`≤ n`) or `n` ticks to extract the reachable cut
    (`extractFinsetM`);
  * per augmentation (`augmentFlowMatrixM`, `2 * (pathArcs p).length ≤ 2 * n` ticks): `1` tick per
    path arc to compute `δ ← bottleneckM` and `1` tick per path arc in `updateArcsMatM` to update
    the forward and reverse entries of `FlowMatrix N` using `δ`.
* **Abstract unit-cost primitives:** `Vector` indexing/update (`vget`, `vset`, `fget`, `fset`),
  `Finset.insert`, arithmetic on `ℕ`, and evaluating `N.cap u v` are treated as `O(1)` operations
  within each charged step; this models abstract RAM-style algorithmic steps in `TimeM ℕ`, not
  bit-level Turing-machine time or persistent-array reference-counting copy costs when shared zero
  rows are first mutated.

## Main definitions

* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.HasResWalkOfLen`, `Flow.resDist`,
  `Flow.IsShortestAugmentingPath`: residual walk lengths, capped shortest-path distances, and
  fewest-arc augmenting paths.
* `Cslib.Algorithms.Lean.MaxFlow.Network.symArcs`, `Network.posArcs`,
  `Network.IsShortestAugmentingSeq`: active directed residual pairs and shortest-augmentation
  traces.
* `Cslib.Algorithms.Lean.MaxFlow.AdjValid`, `adjSteps`, `defaultAdj`, `FlowMatrix`, `bfsM`,
  `Output`, `edmondsKarpM`, `edmondsKarpDenseM`: executable BFS and Edmonds–Karp solver in
  `TimeM ℕ`.

## Main results

* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.resDist_le_augmentByBottleneck`: shortest-path
  distance monotonicity.
* `Cslib.Algorithms.Lean.MaxFlow.Network.shortestAugmentingSeq_length_le` and
  `shortestAugmentingSeq_length_le_card_mul_posArcs`: polynomial augmentation bounds.
* `Cslib.Algorithms.Lean.MaxFlow.edmondsKarpM_correct` and `edmondsKarpM_time_le`: max-flow /
  min-cut certification and explicit `TimeM` step bound.

## References

* [J. Edmonds and R. M. Karp, *Theoretical Improvements in Algorithmic Efficiency for Network Flow
  Problems*][EdmondsKarp1972]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

open Cslib.Algorithms.Lean
open scoped TimeM

namespace Network

section DistanceAndCriticalArcs

variable {V : Type*} [Fintype V] (N : Network V)

/-- Active directed pairs `(u, v)` with `u ≠ v` that can ever carry positive residual capacity in
`N` (either `N.cap u v > 0` or `N.cap v u > 0`). -/
@[expose] def symArcs [DecidableEq V] : Finset (V × V) :=
  Finset.univ.filter fun e => e.1 ≠ e.2 ∧ 0 < N.cap e.1 e.2 + N.cap e.2 e.1

/-- Non-loop directed arcs `(u, v)` with positive capacity `N.cap u v > 0` in `N`. -/
@[expose] def posArcs [DecidableEq V] : Finset (V × V) :=
  Finset.univ.filter fun e => e.1 ≠ e.2 ∧ 0 < N.cap e.1 e.2

theorem card_symArcs_le_two_mul_posArcs [DecidableEq V] :
    N.symArcs.card ≤ 2 * N.posArcs.card := by
  have hsub : N.symArcs ⊆ N.posArcs ∪ N.posArcs.image Prod.swap := by
    intro ⟨u, v⟩ he
    simp only [symArcs, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases he with ⟨hne, hpos⟩
    rw [Finset.mem_union]
    by_cases huv : 0 < N.cap u v
    · left
      simp [posArcs, hne, huv]
    · right
      have hvu : 0 < N.cap v u := by omega
      rw [Finset.mem_image]
      exact ⟨(v, u), by simp [posArcs, hne.symm, hvu], rfl⟩
  calc
    N.symArcs.card ≤ (N.posArcs ∪ N.posArcs.image Prod.swap).card :=
      Finset.card_le_card hsub
    _ ≤ N.posArcs.card + (N.posArcs.image Prod.swap).card :=
      Finset.card_union_le _ _
    _ ≤ N.posArcs.card + N.posArcs.card :=
      Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * N.posArcs.card := by omega

theorem card_symArcs_le_card_sq [DecidableEq V] :
    N.symArcs.card ≤ Fintype.card V * Fintype.card V := by
  calc
    N.symArcs.card ≤ (Finset.univ : Finset (V × V)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card (V × V) := Finset.card_univ
    _ = Fintype.card V * Fintype.card V := Fintype.card_prod V V

namespace Flow

variable {N}

/-- Existence of a positive-residual-capacity walk of exact arc length `k` from `N.s` to `v`. -/
inductive HasResWalkOfLen (f : N.Flow) : V → ℕ → Prop
  | zero : HasResWalkOfLen f N.s 0
  | succ {u v : V} {k : ℕ} : HasResWalkOfLen f u k → 0 < f.resCap u v → HasResWalkOfLen f v (k + 1)

theorem HasResWalkOfLen.resReachable {f : N.Flow} {v : V} {k : ℕ}
    (h : f.HasResWalkOfLen v k) : f.ResReachable N.s v := by
  induction h with
  | zero => exact .refl
  | succ _ hstep ih => exact ih.tail hstep

private theorem hasResWalkOfLen_add (f : N.Flow) (q : List V) {u w : V} {k : ℕ}
    (hwalk : f.HasResWalkOfLen u k) (hu : q.head? = some u) (hw : q.getLast? = some w)
    (hq : ∀ e ∈ pathArcs q, 0 < f.resCap e.1 e.2) :
    f.HasResWalkOfLen w (k + (pathArcs q).length) := by
  induction q generalizing u k with
  | nil => simp at hu
  | cons x rest ih =>
    simp only [List.head?_cons, Option.some.injEq] at hu
    subst hu
    rcases rest with _ | ⟨y, rest'⟩
    · simp only [List.getLast?_singleton, Option.some.injEq] at hw
      subst hw
      simpa using hwalk
    · have hrec := ih (hwalk.succ (hq (x, y) List.mem_cons_self)) rfl (by simpa using hw)
        fun e he => hq e (List.mem_cons_of_mem _ he)
      simpa [Nat.add_assoc, Nat.add_comm] using hrec

theorem hasResWalkOfLen_of_walk (f : N.Flow) {p : List V} {v : V}
    (hs : p.head? = some N.s) (ht : p.getLast? = some v)
    (harcs : ∀ e ∈ pathArcs p, 0 < f.resCap e.1 e.2) :
    f.HasResWalkOfLen v (pathArcs p).length := by
  simpa using hasResWalkOfLen_add f p .zero hs ht harcs

theorem exists_hasResWalkOfLen_lt_card_of_resReachable (f : N.Flow) {v : V}
    (h : f.ResReachable N.s v) : ∃ k < Fintype.card V, f.HasResWalkOfLen v k := by
  classical
  have hwalk_ex : ∃ p : List V, p.head? = some N.s ∧ p.getLast? = some v ∧
      ∀ e ∈ pathArcs p, 0 < f.resCap e.1 e.2 := by
    induction h with
    | refl => exact ⟨[N.s], rfl, rfl, by simp⟩
    | @tail b c _ hstep ih =>
      obtain ⟨p, hhead, hlast, harcs⟩ := ih
      have hp_ne : p ≠ [] := by intro hnil; rw [hnil] at hhead; simp at hhead
      refine ⟨p ++ [c], ?_, by simp, ?_⟩
      · rw [List.head?_append_of_ne_nil p hp_ne]; exact hhead
      · intro e he
        rw [pathArcs_append_singleton hp_ne hlast, List.mem_append, List.mem_singleton] at he
        rcases he with he' | rfl
        · exact harcs e he'
        · exact hstep
  obtain ⟨p, hs, ht, harcs⟩ := hwalk_ex
  let q := loopErase p
  have hnodup : q.Nodup := nodup_loopErase p
  have hqs : q.head? = some N.s := (head?_loopErase p).trans hs
  have hqt : q.getLast? = some v := (getLast?_loopErase p).trans ht
  have hqarcs : ∀ e ∈ pathArcs q, 0 < f.resCap e.1 e.2 :=
    fun e he => harcs e (mem_pathArcs_loopErase he)
  have hq_ne : q ≠ [] := by intro hnil; rw [hnil] at hqs; simp at hqs
  have hlen_le : q.length ≤ Fintype.card V := hnodup.length_le_card
  have harc_len := length_pathArcs_add_one hq_ne
  refine ⟨(pathArcs q).length, by omega, f.hasResWalkOfLen_of_walk hqs hqt hqarcs⟩

/-- Residual shortest-path distance from `N.s` to `v`, capped at `Fintype.card V` when `v` is
unreachable. -/
noncomputable def resDist (f : N.Flow) (v : V) : ℕ :=
  open scoped Classical in
  if h : ∃ k, k < Fintype.card V ∧ f.HasResWalkOfLen v k then Nat.find h else Fintype.card V

theorem resDist_le_card (f : N.Flow) (v : V) : f.resDist v ≤ Fintype.card V := by
  classical
  unfold resDist
  split_ifs with h
  · exact Nat.le_of_lt (Nat.find_spec h).1
  · exact le_rfl

theorem resDist_lt_card_iff_resReachable (f : N.Flow) (v : V) :
    f.resDist v < Fintype.card V ↔ f.ResReachable N.s v := by
  classical
  constructor
  · intro hlt
    unfold resDist at hlt
    split_ifs at hlt with h
    · exact (Nat.find_spec h).2.resReachable
    · exact absurd hlt (Nat.lt_irrefl _)
  · intro hreach
    obtain ⟨k, hk, hwalk⟩ := f.exists_hasResWalkOfLen_lt_card_of_resReachable hreach
    have hex : ∃ m, m < Fintype.card V ∧ f.HasResWalkOfLen v m := ⟨k, hk, hwalk⟩
    unfold resDist
    simp only [hex, ↓reduceDIte]
    exact (Nat.find_spec hex).1

theorem hasResWalkOfLen_resDist (f : N.Flow) {v : V} (hlt : f.resDist v < Fintype.card V) :
    f.HasResWalkOfLen v (f.resDist v) := by
  classical
  unfold resDist at hlt ⊢
  split_ifs at hlt ⊢ with h
  · exact (Nat.find_spec h).2
  · exact absurd hlt (Nat.lt_irrefl _)

theorem resDist_le_of_hasResWalkOfLen (f : N.Flow) {v : V} {k : ℕ}
    (hwalk : f.HasResWalkOfLen v k) : f.resDist v ≤ k := by
  classical
  by_cases hk : k < Fintype.card V
  · have hex : ∃ m, m < Fintype.card V ∧ f.HasResWalkOfLen v m := ⟨k, hk, hwalk⟩
    unfold resDist
    simp only [hex, ↓reduceDIte]
    exact Nat.find_min' hex ⟨hk, hwalk⟩
  · exact le_trans (f.resDist_le_card v) (Nat.le_of_not_lt hk)

@[simp]
theorem resDist_source (f : N.Flow) : f.resDist N.s = 0 :=
  Nat.eq_zero_of_le_zero (f.resDist_le_of_hasResWalkOfLen .zero)

theorem eq_source_of_resDist_eq_zero (f : N.Flow) {v : V} (hv : f.resDist v = 0) : v = N.s := by
  have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.s⟩
  have hwalk := f.hasResWalkOfLen_resDist (v := v) (by omega)
  rw [hv] at hwalk
  cases hwalk
  rfl

/-- Residual shortest-path triangle inequality: positive residual capacity on `(u, v)` gives
`f.resDist v ≤ f.resDist u + 1` unconditionally (including when `u` is unreachable). -/
theorem resDist_le_add_one_of_pos_resCap (f : N.Flow) {u v : V} (hpos : 0 < f.resCap u v) :
    f.resDist v ≤ f.resDist u + 1 := by
  by_cases hlt : f.resDist u < Fintype.card V
  · exact f.resDist_le_of_hasResWalkOfLen ((f.hasResWalkOfLen_resDist hlt).succ hpos)
  · have hle := f.resDist_le_card v
    omega

theorem exists_pred_of_resDist_eq_succ (f : N.Flow) {v : V} {k : ℕ}
    (hk : k + 1 < Fintype.card V) (hv : f.resDist v = k + 1) :
    ∃ u : V, f.resDist u = k ∧ 0 < f.resCap u v := by
  have hwalk := f.hasResWalkOfLen_resDist (v := v) (by omega)
  rw [hv] at hwalk
  cases hwalk with
  | succ hprev hpos =>
    rename_i u
    have hle₁ : f.resDist u ≤ k := f.resDist_le_of_hasResWalkOfLen hprev
    have hle₂ : f.resDist v ≤ f.resDist u + 1 := f.resDist_le_add_one_of_pos_resCap hpos
    exact ⟨u, by omega, hpos⟩

theorem resDist_le_add_length_pathArcs (f : N.Flow) {q : List V} {u w : V}
    (hu : q.head? = some u) (hw : q.getLast? = some w)
    (hq : ∀ e ∈ pathArcs q, 0 < f.resCap e.1 e.2) :
    f.resDist w ≤ f.resDist u + (pathArcs q).length := by
  induction q generalizing u with
  | nil => simp at hu
  | cons x rest ih =>
    simp only [List.head?_cons, Option.some.injEq] at hu
    subst hu
    rcases rest with _ | ⟨y, rest'⟩
    · simp only [List.getLast?_singleton, Option.some.injEq] at hw
      subst hw
      simp
    · have hstep : f.resDist y ≤ f.resDist x + 1 :=
        f.resDist_le_add_one_of_pos_resCap (hq (x, y) List.mem_cons_self)
      have hrec := ih (u := y) rfl (by simpa using hw)
        (fun e he => hq e (List.mem_cons_of_mem _ he))
      simp only [pathArcs_cons_cons, List.length_cons]
      omega

/-- Every vertex on a positive-residual-capacity walk starting at `N.s` has `resDist` bounded by
the walk's arc length. -/
theorem resDist_mem_le_length_pathArcs (f : N.Flow) {p : List V}
    (hs : p.head? = some N.s) (harcs : ∀ e ∈ pathArcs p, 0 < f.resCap e.1 e.2)
    {x : V} (hx : x ∈ p) : f.resDist x ≤ (pathArcs p).length := by
  have hgen : ∀ q : List V, ∀ u : V,
      q.head? = some u → (∀ e ∈ pathArcs q, 0 < f.resCap e.1 e.2) →
      x ∈ q → f.resDist x ≤ f.resDist u + (pathArcs q).length := by
    intro q
    induction q with
    | nil => intro _ _ _ hmem; simp at hmem
    | cons a rest ih =>
      intro u hu hq hmem
      simp only [List.head?_cons, Option.some.injEq] at hu
      subst a
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · omega
      · rcases rest with _ | ⟨b, rest'⟩
        · simp at hmem'
        · have hstep : f.resDist b ≤ f.resDist u + 1 :=
            f.resDist_le_add_one_of_pos_resCap (hq (u, b) List.mem_cons_self)
          have hrec := ih b rfl (fun e he => hq e (List.mem_cons_of_mem _ he)) hmem'
          simp only [pathArcs_cons_cons, List.length_cons]
          omega
  simpa using hgen p N.s hs harcs hx

/-- A shortest augmenting path: a simple `s`-`t` augmenting path of minimum residual arc length
`f.resDist N.t`. -/
@[expose] def IsShortestAugmentingPath (f : N.Flow) (p : List V) : Prop :=
  f.IsAugmentingPath p ∧ (pathArcs p).length = f.resDist N.t

theorem IsShortestAugmentingPath.isAugmentingPath {f : N.Flow} {p : List V}
    (hp : f.IsShortestAugmentingPath p) : f.IsAugmentingPath p := hp.1

theorem IsShortestAugmentingPath.length_eq {f : N.Flow} {p : List V}
    (hp : f.IsShortestAugmentingPath p) : (pathArcs p).length = f.resDist N.t := hp.2

/-- Every consecutive arc `(u, v)` along a shortest augmenting path advances `f.resDist` by `1` and
satisfies `f.resDist v ≤ f.resDist N.t`. -/
theorem resDist_arc_of_isShortestAugmentingPath (f : N.Flow) {p : List V}
    (hp : f.IsShortestAugmentingPath p) {u v : V} (he : (u, v) ∈ pathArcs p) :
    f.resDist v = f.resDist u + 1 ∧ f.resDist v ≤ f.resDist N.t := by
  have haug := hp.isAugmentingPath
  have hlen := hp.length_eq
  have hgen : ∀ q : List V, ∀ x : V,
      q.head? = some x → q.getLast? = some N.t →
      (∀ a ∈ pathArcs q, 0 < f.resCap a.1 a.2) →
      f.resDist N.t = f.resDist x + (pathArcs q).length →
      (u, v) ∈ pathArcs q →
      f.resDist v = f.resDist u + 1 ∧ f.resDist v ≤ f.resDist N.t := by
    intro q
    induction q with
    | nil => intro _ _ _ _ _ hmem; simp at hmem
    | cons a rest ih =>
      intro x hx hqt hq hdists hmem
      simp only [List.head?_cons, Option.some.injEq] at hx
      subst hx
      rcases rest with _ | ⟨b, rest'⟩
      · simp at hmem
      · have hpos_ab : 0 < f.resCap a b := hq (a, b) List.mem_cons_self
        have hab_le : f.resDist b ≤ f.resDist a + 1 :=
          f.resDist_le_add_one_of_pos_resCap hpos_ab
        have htail_ar := fun e he => hq e (List.mem_cons_of_mem _ he)
        have hbt_le : f.resDist N.t ≤ f.resDist b + (pathArcs (b :: rest')).length :=
          f.resDist_le_add_length_pathArcs rfl (by simpa using hqt) htail_ar
        simp only [pathArcs_cons_cons, List.length_cons] at hdists
        have hab_eq : f.resDist b = f.resDist a + 1 := by omega
        have hbt_eq : f.resDist N.t = f.resDist b + (pathArcs (b :: rest')).length := by omega
        simp only [pathArcs_cons_cons, List.mem_cons, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | hmem'
        · exact ⟨hab_eq, by omega⟩
        · exact ih b rfl (by simpa using hqt) htail_ar hbt_eq hmem'
  exact hgen p N.s haug.head? haug.getLast? (fun e he => haug.pos_resCap he) (by simp [hlen]) he

/-- **Edmonds–Karp shortest-path distance monotonicity** ([EdmondsKarp1972], Section 1, p. 251;
[CLRS2009], Lemma 26.7, pp. 727–728): augmenting `f` along a shortest augmenting path `p` never
decreases `resDist v` for any vertex `v`. -/
private theorem resCap_augmentByBottleneck [DecidableEq V] (f : N.Flow) {p : List V}
    (hp : f.IsAugmentingPath p) (u w : V) :
    (f.augmentByBottleneck p hp).resCap u w =
      if (u, w) ∈ pathArcs p then f.resCap u w - f.bottleneck p
      else if (w, u) ∈ pathArcs p then f.resCap u w + f.bottleneck p
      else f.resCap u w :=
  f.resCap_augment hp.nodup hp.head? hp.getLast? (f.bottleneck p)
    (fun _ he => f.bottleneck_le_resCap he) u w

theorem resDist_le_augmentByBottleneck [DecidableEq V] (f : N.Flow) {p : List V}
    (hp : f.IsShortestAugmentingPath p) (v : V) :
    f.resDist v ≤ (f.augmentByBottleneck p hp.isAugmentingPath).resDist v := by
  have haug := hp.isAugmentingPath
  let f' := f.augmentByBottleneck p haug
  by_cases hlt : f'.resDist v < Fintype.card V
  · have hind : ∀ k < Fintype.card V, ∀ w : V, f'.resDist w = k → f.resDist w ≤ k := by
      intro k
      induction k with
      | zero =>
        intro _ w hw
        obtain rfl := f'.eq_source_of_resDist_eq_zero hw
        simp
      | succ k ih =>
        intro hk1 w hw
        obtain ⟨u, hu_dist, hpos'⟩ := f'.exists_pred_of_resDist_eq_succ hk1 hw
        have hu_le : f.resDist u ≤ k := ih (by omega) u hu_dist
        by_cases hpos : 0 < f.resCap u w
        · have := f.resDist_le_add_one_of_pos_resCap hpos
          omega
        · have hres' := f.resCap_augmentByBottleneck haug u w
          have hwu : (w, u) ∈ pathArcs p := by grind
          have := (f.resDist_arc_of_isShortestAugmentingPath hp hwu).1
          omega
    exact hind (f'.resDist v) hlt v rfl
  · exact le_trans (f.resDist_le_card v) (Nat.le_of_not_lt hlt)

end Flow

/-- A shortest-augmenting-path trace of length `T` on `N`: `flows 0, …, flows T` linked by shortest
augmenting paths `paths 0, …, paths (T - 1)`. -/
@[expose] def IsShortestAugmentingSeq [DecidableEq V] (T : ℕ) (flows : ℕ → N.Flow)
    (paths : ℕ → List V) : Prop :=
  ∀ t < T, ∃ hp : (flows t).IsShortestAugmentingPath (paths t),
    flows (t + 1) = (flows t).augmentByBottleneck (paths t) hp.isAugmentingPath

private theorem resDist_mono_of_seq [DecidableEq V] {T : ℕ} {flows : ℕ → N.Flow}
    {paths : ℕ → List V} (hseq : N.IsShortestAugmentingSeq T flows paths)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ T) (v : V) :
    (flows i).resDist v ≤ (flows j).resDist v := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    have hprev := ih (Nat.le_add_right i d) (by omega)
    obtain ⟨hp, hnext⟩ := hseq (i + d) (by omega)
    have hstep := (flows (i + d)).resDist_le_augmentByBottleneck hp v
    rw [← hnext] at hstep
    exact le_trans hprev hstep

private theorem exists_zero_to_pos_step {g : ℕ → ℕ} {a b : ℕ} (hab : a ≤ b)
    (ha : g a = 0) (hb : 0 < g b) :
    ∃ r, a ≤ r ∧ r < b ∧ g r < g (r + 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero =>
    rw [Nat.add_zero] at hb
    omega
  | succ d ih =>
    by_cases hpos : 0 < g (a + d)
    · obtain ⟨r, hr₁, hr₂, hlt⟩ := ih (Nat.le_add_right a d) hpos
      exact ⟨r, hr₁, by omega, hlt⟩
    · refine ⟨a + d, Nat.le_add_right a d, by omega, ?_⟩
      rw [← Nat.add_assoc] at hb
      omega

/-- **Edmonds–Karp polynomial augmentation bound** ([EdmondsKarp1972], Section 1, Theorem 1,
p. 251; [CLRS2009], Theorem 26.8, p. 729): when `N.s ≠ N.t`, every sequence of shortest-path
augmentations has length at most `N.symArcs.card * (Fintype.card V / 2)`. -/
theorem shortestAugmentingSeq_length_le [DecidableEq V] (hst : N.s ≠ N.t) {T : ℕ}
    {flows : ℕ → N.Flow} {paths : ℕ → List V}
    (hseq : N.IsShortestAugmentingSeq T flows paths) :
    T ≤ N.symArcs.card * (Fintype.card V / 2) := by
  let isCrit (t : Fin T) (e : V × V) : Bool :=
    decide (e ∈ pathArcs (paths t.1) ∧
      (flows t.1).resCap e.1 e.2 = (flows t.1).bottleneck (paths t.1))
  have hcover : ∀ t : Fin T, ∃ e ∈ N.symArcs, isCrit t e = true := by
    intro t
    obtain ⟨hp, _⟩ := hseq t.1 t.2
    have haug := hp.isAugmentingPath
    obtain ⟨e, he, hbot⟩ := (flows t.1).exists_mem_pathArcs_resCap_eq_bottleneck
      (pathArcs_ne_nil_of_head?_ne_getLast? hst haug.head? haug.getLast?)
    have hpos_res := haug.pos_resCap he
    have hcap_le := (flows t.1).resCap_le_cap_add_cap e.1 e.2
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ne_of_mem_pathArcs haug.nodup he, by omega⟩, decide_eq_true ⟨he, hbot⟩⟩
  have hcrit_card : ∀ e ∈ N.symArcs,
      (Finset.univ.filter fun t : Fin T => isCrit t e = true).card ≤ Fintype.card V / 2 := by
    rintro ⟨u, v⟩ _
    let S := Finset.univ.filter fun t : Fin T => isCrit t (u, v) = true
    have hmaps : ∀ t ∈ S, (flows t.1).resDist u / 2 ∈ Finset.range (Fintype.card V / 2) := by
      intro t ht
      obtain ⟨he, _⟩ := of_decide_eq_true (Finset.mem_filter.mp ht).2
      obtain ⟨hp, _⟩ := hseq t.1 t.2
      have := (flows t.1).resDist_arc_of_isShortestAugmentingPath hp he
      have hlt_t := ((flows t.1).resDist_lt_card_iff_resReachable N.t).mpr
        (((flows t.1).exists_augmentingPath_iff_resReachable).mp ⟨paths t.1, hp.isAugmentingPath⟩)
      rw [Finset.mem_range]
      omega
    have hgap : ∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁.1 < t₂.1 →
        (flows t₁.1).resDist u + 2 ≤ (flows t₂.1).resDist u := by
      intro t₁ ht₁ t₂ ht₂ hlt12
      obtain ⟨he₁, hbot₁⟩ := of_decide_eq_true (Finset.mem_filter.mp ht₁).2
      obtain ⟨he₂, _⟩ := of_decide_eq_true (Finset.mem_filter.mp ht₂).2
      obtain ⟨hp₁, hnext₁⟩ := hseq t₁.1 t₁.2
      obtain ⟨hp₂, _⟩ := hseq t₂.1 t₂.2
      have hdist₁ := ((flows t₁.1).resDist_arc_of_isShortestAugmentingPath hp₁ he₁).1
      have hzero₁ : (flows (t₁.1 + 1)).resCap u v = 0 := by
        rw [hnext₁, Flow.resCap_augmentByBottleneck]
        simp [he₁, hbot₁]
      have hpos₂ : 0 < (flows t₂.1).resCap u v := hp₂.isAugmentingPath.pos_resCap he₂
      obtain ⟨r, hr₁, hr₂, hinc⟩ :=
        exists_zero_to_pos_step (g := fun k => (flows k).resCap u v) (by omega) hzero₁ hpos₂
      obtain ⟨hpr, hnextr⟩ := hseq r (by omega)
      have hvu_r : (v, u) ∈ pathArcs (paths r) := by
        rw [hnextr, Flow.resCap_augmentByBottleneck] at hinc
        by_contra hnot
        split_ifs at hinc <;> omega
      have hdistr := ((flows r).resDist_arc_of_isShortestAugmentingPath hpr hvu_r).1
      have hmono₁ := N.resDist_mono_of_seq hseq (i := t₁.1) (j := r) (by omega) (by omega) v
      have hmono₂ := N.resDist_mono_of_seq hseq (i := r) (j := t₂.1) (by omega) (by omega) u
      omega
    have hinj : Set.InjOn (fun t : Fin T => (flows t.1).resDist u / 2) S := by
      intro t₁ ht₁ t₂ ht₂ heq
      dsimp only at heq
      rcases lt_trichotomy t₁.1 t₂.1 with hlt | heq' | hgt
      · have := hgap t₁ ht₁ t₂ ht₂ hlt; omega
      · exact Fin.ext heq'
      · have := hgap t₂ ht₂ t₁ ht₁ hgt; omega
    calc
      S.card ≤ (Finset.range (Fintype.card V / 2)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
      _ = Fintype.card V / 2 := Finset.card_range _
  have huniv_sub : (Finset.univ : Finset (Fin T)) ⊆
      N.symArcs.biUnion (fun e => Finset.univ.filter fun t : Fin T => isCrit t e = true) := by
    intro t _
    obtain ⟨e, he, hcrit⟩ := hcover t
    exact Finset.mem_biUnion.mpr ⟨e, he, by simp [hcrit]⟩
  calc
    T = (Finset.univ : Finset (Fin T)).card := by simp [Fintype.card_fin]
    _ ≤ (N.symArcs.biUnion
          (fun e => Finset.univ.filter fun t : Fin T => isCrit t e = true)).card :=
      Finset.card_le_card huniv_sub
    _ ≤ ∑ e ∈ N.symArcs, (Finset.univ.filter fun t : Fin T => isCrit t e = true).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ N.symArcs, (Fintype.card V / 2) :=
      Finset.sum_le_sum hcrit_card
    _ = N.symArcs.card * (Fintype.card V / 2) := by simp

/-- Sparse `|V| * |E|` corollary of `shortestAugmentingSeq_length_le` ([CLRS2009], Theorem 26.8,
p. 729): every shortest-path augmentation sequence has length at most
`Fintype.card V * N.posArcs.card`. -/
theorem shortestAugmentingSeq_length_le_card_mul_posArcs [DecidableEq V] (hst : N.s ≠ N.t)
    {T : ℕ} {flows : ℕ → N.Flow} {paths : ℕ → List V}
    (hseq : N.IsShortestAugmentingSeq T flows paths) :
    T ≤ Fintype.card V * N.posArcs.card := by
  have h1 := N.shortestAugmentingSeq_length_le hst hseq
  have h2 := N.card_symArcs_le_two_mul_posArcs
  have hdiv : 2 * (Fintype.card V / 2) ≤ Fintype.card V := Nat.mul_div_le (Fintype.card V) 2
  calc
    T ≤ N.symArcs.card * (Fintype.card V / 2) := h1
    _ ≤ (2 * N.posArcs.card) * (Fintype.card V / 2) := Nat.mul_le_mul_right _ h2
    _ = N.posArcs.card * (2 * (Fintype.card V / 2)) := by
      rw [Nat.mul_comm 2 N.posArcs.card, Nat.mul_assoc]
    _ ≤ N.posArcs.card * Fintype.card V := Nat.mul_le_mul_left _ hdiv
    _ = Fintype.card V * N.posArcs.card := Nat.mul_comm _ _

end DistanceAndCriticalArcs

end Network

/-! ### Executable BFS and Edmonds–Karp solver in `TimeM ℕ` over `Fin n` -/

section ExecutableFin

/-- Attach the definitional equality `x = m.ret` as an erased `Subtype` witness (`0` extra ticks).
-/
@[expose] def attachRet {T α : Type*} (m : TimeM T α) : TimeM T { x : α // x = m.ret } :=
  ⟨⟨m.ret, rfl⟩, m.time⟩

@[simp]
theorem attachRet_val {T α : Type*} (m : TimeM T α) : (attachRet m).ret.1 = m.ret := rfl

@[simp]
theorem attachRet_time {T α : Type*} (m : TimeM T α) : (attachRet m).time = m.time := rfl

/-- Total `Fin n`-indexed lookup on `Vector α n`. -/
@[expose] def vget {α : Type*} {n : ℕ} (tbl : Vector α n) (v : Fin n) : α := tbl[v.1]

/-- Total `Fin n`-indexed update on `Vector α n`. -/
@[expose] def vset {α : Type*} {n : ℕ} (tbl : Vector α n) (v : Fin n) (x : α) : Vector α n :=
  tbl.set v.1 x v.2

@[simp]
theorem vget_replicate {α : Type*} {n : ℕ} (a : α) (v : Fin n) :
    vget (Vector.replicate n a) v = a := by
  simp [vget]

@[simp]
theorem vget_vset_self {α : Type*} {n : ℕ} (tbl : Vector α n) (v : Fin n) (x : α) :
    vget (vset tbl v x) v = x := by
  simp [vget, vset]

theorem vget_vset_ne {α : Type*} {n : ℕ} (tbl : Vector α n) {u v : Fin n} (x : α) (h : u ≠ v) :
    vget (vset tbl u x) v = vget tbl v := by
  have hne : u.1 ≠ v.1 := Fin.val_ne_of_ne h
  simp [vget, vset, hne]

/-- Lookup entry `(u, v)` in an `n × n` `Vector` matrix. -/
@[expose] def fget {α : Type*} {n : ℕ} (mat : Vector (Vector α n) n) (u v : Fin n) : α :=
  vget (vget mat u) v

/-- Update entry `(u, v)` in an `n × n` `Vector` matrix. -/
@[expose] def fset {α : Type*} {n : ℕ} (mat : Vector (Vector α n) n) (u v : Fin n) (x : α) :
    Vector (Vector α n) n :=
  vset mat u (vset (vget mat u) v x)

@[simp]
theorem fget_fset_self {α : Type*} {n : ℕ} (mat : Vector (Vector α n) n) (u v : Fin n) (x : α) :
    fget (fset mat u v x) u v = x := by
  simp [fget, fset]

theorem fget_fset_ne {α : Type*} {n : ℕ} (mat : Vector (Vector α n) n) {a b u v : Fin n} (x : α)
    (hne : (a, b) ≠ (u, v)) :
    fget (fset mat a b x) u v = fget mat u v := by
  by_cases hau : a = u
  · subst hau
    have hbv : b ≠ v := fun h => hne (congrArg (Prod.mk a) h)
    simp [fget, fset, vget_vset_ne _ _ hbv]
  · simp [fget, fset, vget_vset_ne _ _ hau]

/-- Allocate `Vector.replicate m a` in `m` `TimeM` ticks (`1` tick per slot). -/
@[expose] def replicateM {α : Type*} : (m : ℕ) → α → TimeM ℕ (Vector α m)
  | 0, _ => pure #v[]
  | m + 1, a => do
    ✓
    let rest ← replicateM m a
    pure (rest.push a)

@[simp]
theorem replicateM_ret {α : Type*} (m : ℕ) (a : α) :
    (replicateM m a).ret = Vector.replicate m a := by
  induction m with
  | zero =>
    ext i hi
    exact False.elim (Nat.not_lt_zero i hi)
  | succ m ih =>
    simp only [replicateM, TimeM.ret_bind, TimeM.ret_pure, ih]
    ext i hi
    by_cases hlt : i < m
    · simp [Vector.getElem_push_lt hlt]
    · have heq : i = m := by omega
      subst heq
      simp

@[simp]
theorem replicateM_time {α : Type*} (m : ℕ) (a : α) :
    (replicateM m a).time = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [replicateM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih]
    omega

/-- Filter `vs` into a `Finset`, charging `1` tick per inspected element. -/
@[expose] def filterFinsetM {α : Type*} [DecidableEq α] (p : α → Bool) :
    List α → Finset α → TimeM ℕ (Finset α)
  | [], acc => pure acc
  | v :: vs, acc => do
    ✓
    let acc' := if p v then insert v acc else acc
    filterFinsetM p vs acc'

theorem mem_filterFinsetM_ret {α : Type*} [DecidableEq α] (p : α → Bool)
    (vs : List α) (acc : Finset α) (x : α) :
    x ∈ (filterFinsetM p vs acc).ret ↔ x ∈ acc ∨ (x ∈ vs ∧ p x = true) := by
  induction vs generalizing acc with
  | nil => simp [filterFinsetM]
  | cons v vs' ih =>
    simp only [filterFinsetM, TimeM.ret_bind, ih]
    split_ifs with hpv <;> grind

@[simp]
theorem filterFinsetM_time {α : Type*} [DecidableEq α] (p : α → Bool)
    (vs : List α) (acc : Finset α) :
    (filterFinsetM p vs acc).time = vs.length := by
  induction vs generalizing acc with
  | nil => rfl
  | cons _ vs' ih =>
    simp only [filterFinsetM, TimeM.time_bind, TimeM.time_tick, ih, List.length_cons]
    omega

/-- Scan all `n` vertices of `Fin n` into `Finset.univ.filter (fun v => p v = true)` in `n` ticks.
-/
@[expose] def extractFinsetM {n : ℕ} (p : Fin n → Bool) : TimeM ℕ (Finset (Fin n)) :=
  filterFinsetM p (List.finRange n) ∅

@[simp]
theorem extractFinsetM_ret {n : ℕ} (p : Fin n → Bool) :
    (extractFinsetM p).ret = Finset.univ.filter fun v => p v = true := by
  ext v
  simp [extractFinsetM, mem_filterFinsetM_ret, List.mem_finRange]

@[simp]
theorem extractFinsetM_time {n : ℕ} (p : Fin n → Bool) :
    (extractFinsetM p).time = n := by
  simp [extractFinsetM]

/-- Tail-recursive list reversal charging `1` tick per element. -/
@[expose] def reverseLoopM {α : Type*} : List α → List α → TimeM ℕ (List α)
  | [], acc => pure acc
  | x :: xs, acc => do
    ✓
    reverseLoopM xs (x :: acc)

/-- Reverse `xs` in `xs.length` `TimeM` ticks. -/
@[expose] def reverseM {α : Type*} (xs : List α) : TimeM ℕ (List α) :=
  reverseLoopM xs []

private theorem reverseLoopM_ret {α : Type*} (xs acc : List α) :
    (reverseLoopM xs acc).ret = xs.reverseAux acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs' ih => exact ih (x :: acc)

private theorem reverseLoopM_time {α : Type*} (xs acc : List α) :
    (reverseLoopM xs acc).time = xs.length := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs' ih =>
    simp only [reverseLoopM, TimeM.time_bind, TimeM.time_tick, ih (x :: acc), List.length_cons]
    omega

@[simp]
theorem reverseM_ret {α : Type*} (xs : List α) : (reverseM xs).ret = xs.reverse :=
  reverseLoopM_ret xs []

@[simp]
theorem reverseM_time {α : Type*} (xs : List α) : (reverseM xs).time = xs.length :=
  reverseLoopM_time xs []

/-- Fold residual-capacity minimum across arcs, charging `1` tick per arc. -/
@[expose] def foldMinArcsM {V : Type*} [Fintype V] {N : Network V} (f : N.Flow) :
    List (V × V) → ℕ → TimeM ℕ ℕ
  | [], acc => pure acc
  | e :: es, acc => do
    ✓
    foldMinArcsM f es (min acc (f.resCap e.1 e.2))

/-- Compute `f.bottleneck p` in `(pathArcs p).length` `TimeM` ticks. -/
@[expose] def bottleneckM {V : Type*} [Fintype V] {N : Network V} (f : N.Flow)
    (p : List V) : TimeM ℕ ℕ :=
  match pathArcs p with
  | [] => pure 0
  | e :: es => do
    ✓
    foldMinArcsM f es (f.resCap e.1 e.2)

private theorem foldMinArcsM_ret {V : Type*} [Fintype V] {N : Network V} (f : N.Flow)
    (es : List (V × V)) (acc : ℕ) :
    (foldMinArcsM f es acc).ret = es.foldl (fun m b => min m (f.resCap b.1 b.2)) acc := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es' ih => exact ih (min acc (f.resCap e.1 e.2))

private theorem foldMinArcsM_time {V : Type*} [Fintype V] {N : Network V} (f : N.Flow)
    (es : List (V × V)) (acc : ℕ) :
    (foldMinArcsM f es acc).time = es.length := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es' ih =>
    simp only [foldMinArcsM, TimeM.time_bind, TimeM.time_tick, ih, List.length_cons]
    omega

@[simp]
theorem bottleneckM_ret {V : Type*} [Fintype V] {N : Network V} (f : N.Flow) (p : List V) :
    (bottleneckM f p).ret = f.bottleneck p := by
  unfold bottleneckM Network.Flow.bottleneck
  rcases pathArcs p with _ | ⟨e, es⟩
  · rfl
  · exact foldMinArcsM_ret f es (f.resCap e.1 e.2)

@[simp]
theorem bottleneckM_time {V : Type*} [Fintype V] {N : Network V} (f : N.Flow) (p : List V) :
    (bottleneckM f p).time = (pathArcs p).length := by
  unfold bottleneckM
  rcases pathArcs p with _ | ⟨e, es⟩
  · rfl
  · simp only [TimeM.time_bind, TimeM.time_tick, foldMinArcsM_time, List.length_cons]
    omega

/-- Candidate neighbor lists `adj` cover `N` when every non-loop pair `(u, v)` with positive
capacity in either direction appears in `adj u`. -/
@[expose] def AdjValid {n : ℕ} (N : Network (Fin n)) (adj : Fin n → List (Fin n)) : Prop :=
  ∀ u v, u ≠ v → 0 < N.cap u v + N.cap v u → v ∈ adj u

instance instDecidableAdjValid {n : ℕ} (N : Network (Fin n))
    (adj : Fin n → List (Fin n)) : Decidable (AdjValid N adj) := by
  unfold AdjValid
  infer_instance

/-- Total length of all candidate neighbor lists (`2 * |E|` on sparse symmetric adjacency lists,
`n^2` on `defaultAdj n`). -/
@[expose] def adjSteps {n : ℕ} (adj : Fin n → List (Fin n)) : ℕ :=
  ∑ u : Fin n, (adj u).length

/-- Dense candidate neighbor list enumerating `List.finRange n` at every vertex. -/
@[expose] def defaultAdj (n : ℕ) : Fin n → List (Fin n) :=
  fun _ => List.finRange n

theorem adjValid_defaultAdj {n : ℕ} (N : Network (Fin n)) : AdjValid N (defaultAdj n) :=
  fun _ v _ _ => List.mem_finRange v

@[simp]
theorem adjSteps_defaultAdj (n : ℕ) : adjSteps (defaultAdj n) = n * n := by
  simp [adjSteps, defaultAdj, Fintype.card_fin]

private theorem finset_card_le_list_length {α : Type*} {s : Finset α} {l : List α}
    (h : ∀ x ∈ s, x ∈ l) : s.card ≤ l.length := by
  classical
  induction l generalizing s with
  | nil =>
    have hempty : s = ∅ := Finset.eq_empty_of_forall_notMem fun x hx => List.not_mem_nil (h x hx)
    simp [hempty]
  | cons a l' ih =>
    have herase : ∀ x ∈ s.erase a, x ∈ l' := by
      intro x hx
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hx
      rcases List.mem_cons.mp (h x hmem) with rfl | hx'
      · exact absurd rfl hne
      · exact hx'
    have hrec := ih herase
    by_cases ha : a ∈ s
    · have hadd := Finset.card_erase_add_one ha
      simp only [List.length_cons]
      omega
    · rw [Finset.erase_eq_of_notMem ha] at hrec
      simp only [List.length_cons]
      omega

/-- Under `AdjValid N adj`, every active residual pair `(u, v) ∈ N.symArcs` appears in `adj u`, so
`N.symArcs.card ≤ adjSteps adj`. -/
theorem card_symArcs_le_adjSteps {n : ℕ} {N : Network (Fin n)} {adj : Fin n → List (Fin n)}
    (hadj : AdjValid N adj) : N.symArcs.card ≤ adjSteps adj := by
  let S (u : Fin n) : Finset (Fin n) := Finset.univ.filter fun v => (u, v) ∈ N.symArcs
  have hcard_eq : N.symArcs.card = ∑ u : Fin n, (S u).card := by
    calc
      N.symArcs.card = ∑ _e ∈ N.symArcs, 1 := by simp
      _ = ∑ e : Fin n × Fin n, if e ∈ N.symArcs then 1 else 0 := by
        have hflt : Finset.univ.filter (fun e : Fin n × Fin n => e ∈ N.symArcs) = N.symArcs := by
          ext e; simp
        rw [← Finset.sum_filter, hflt]
      _ = ∑ u : Fin n, ∑ v : Fin n, if (u, v) ∈ N.symArcs then 1 else 0 := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
      _ = ∑ u : Fin n, (S u).card := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← Finset.sum_filter]
        simp [S]
  rw [hcard_eq]
  refine Finset.sum_le_sum fun u _ => finset_card_le_list_length fun v hv => ?_
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Network.symArcs] at hv
  exact hadj u v hv.1 hv.2

/-- Count elements of `xs`, charging `1` tick per element. -/
@[expose] def countListM {α : Type*} : List α → ℕ → TimeM ℕ ℕ
  | [], acc => pure acc
  | _ :: xs, acc => do
    ✓
    countListM xs (acc + 1)

private theorem countListM_ret {α : Type*} (xs : List α) (acc : ℕ) :
    (countListM xs acc).ret = acc + xs.length := by
  induction xs generalizing acc with
  | nil => simp [countListM]
  | cons _ xs' ih =>
    simp only [countListM, TimeM.ret_bind, ih, List.length_cons]
    omega

private theorem countListM_time {α : Type*} (xs : List α) (acc : ℕ) :
    (countListM xs acc).time = xs.length := by
  induction xs generalizing acc with
  | nil => rfl
  | cons _ xs' ih =>
    simp only [countListM, TimeM.time_bind, TimeM.time_tick, ih, List.length_cons]
    omega

/-- Count total neighbor entries across `us`, charging `1` tick per vertex and `1` tick per
neighbor entry. -/
@[expose] def countAdjLoopM {n : ℕ} (adj : Fin n → List (Fin n)) :
    List (Fin n) → ℕ → TimeM ℕ ℕ
  | [], acc => pure acc
  | u :: us, acc => do
    ✓
    let acc' ← countListM (adj u) acc
    countAdjLoopM adj us acc'

private theorem countAdjLoopM_ret {n : ℕ} (adj : Fin n → List (Fin n))
    (us : List (Fin n)) (acc : ℕ) :
    (countAdjLoopM adj us acc).ret = acc + (us.map fun u => (adj u).length).sum := by
  induction us generalizing acc with
  | nil => simp [countAdjLoopM]
  | cons u us' ih =>
    simp only [countAdjLoopM, TimeM.ret_bind, countListM_ret, ih, List.map_cons, List.sum_cons]
    omega

private theorem countAdjLoopM_time {n : ℕ} (adj : Fin n → List (Fin n))
    (us : List (Fin n)) (acc : ℕ) :
    (countAdjLoopM adj us acc).time = us.length + (us.map fun u => (adj u).length).sum := by
  induction us generalizing acc with
  | nil => simp [countAdjLoopM]
  | cons u us' ih =>
    simp only [countAdjLoopM, TimeM.time_bind, TimeM.time_tick, countListM_time, countListM_ret, ih,
      List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- Compute `adjSteps adj` in `n + adjSteps adj` `TimeM` ticks without `Fin n × Fin n` scans. -/
@[expose] def countAdjM {n : ℕ} (adj : Fin n → List (Fin n)) : TimeM ℕ ℕ :=
  countAdjLoopM adj (List.finRange n) 0

@[simp]
theorem countAdjM_ret {n : ℕ} (adj : Fin n → List (Fin n)) :
    (countAdjM adj).ret = adjSteps adj := by
  simp only [countAdjM, countAdjLoopM_ret, Nat.zero_add]
  unfold adjSteps Finset.sum
  simp [Finset.univ, Fintype.elems]

@[simp]
theorem countAdjM_time {n : ℕ} (adj : Fin n → List (Fin n)) :
    (countAdjM adj).time = n + adjSteps adj := by
  simp only [countAdjM, countAdjLoopM_time, List.length_finRange]
  unfold adjSteps Finset.sum
  simp [Finset.univ, Fintype.elems]

/-! #### Reversed-walk validity and executable BFS -/

/-- `rp` reverses to a simple positive-residual-capacity walk from `N.s` to `v`. -/
structure IsRevWalkTo {n : ℕ} {N : Network (Fin n)} (f : N.Flow)
    (v : Fin n) (rp : List (Fin n)) : Prop where
  nodup : rp.reverse.Nodup
  head? : rp.reverse.head? = some N.s
  getLast? : rp.reverse.getLast? = some v
  pos_resCap : ∀ e ∈ pathArcs rp.reverse, 0 < f.resCap e.1 e.2

theorem IsRevWalkTo.isAugmentingPath {n : ℕ} {N : Network (Fin n)} {f : N.Flow} {rp : List (Fin n)}
    (h : IsRevWalkTo f N.t rp) : f.IsAugmentingPath rp.reverse :=
  ⟨h.nodup, h.head?, h.getLast?, h.pos_resCap⟩

/-- Table-level structural invariant for `revPath`: every `some rp` entry is a valid reversed walk
whose vertices are all already marked in `revPath`. -/
structure TblValid {n : ℕ} {N : Network (Fin n)} (f : N.Flow)
    (tbl : Vector (Option (List (Fin n))) n) : Prop where
  walk : ∀ v rp, vget tbl v = some rp → IsRevWalkTo f v rp
  mem_isSome : ∀ v rp, vget tbl v = some rp → ∀ x ∈ rp.reverse, (vget tbl x).isSome = true

/-- Intermediate state of one BFS layer over `Fin n`, carrying an erased `TblValid` proof. -/
structure BfsState {n : ℕ} {N : Network (Fin n)} (f : N.Flow) where
  /-- Reversed shortest path `v :: … :: [s]` for each discovered vertex `v`, or `none`. -/
  revPath : Vector (Option (List (Fin n))) n
  /-- Newly discovered vertices in the current layer. -/
  frontier : List (Fin n)
  /-- Erased proof that every `some rp` in `revPath` reverses to a simple valid walk. -/
  tblValid : TblValid f revPath

/-- Result of a single BFS shortest-augmenting-path search for flow `f`. -/
structure BfsResult {n : ℕ} {N : Network (Fin n)} (f : N.Flow) where
  /-- Shortest residual `s`-`t` augmenting path when `t` is reachable, or `none`. -/
  augPath : Option (List (Fin n))
  /-- Erased proof that any returned `some p` is a valid augmenting path for `f`. -/
  augPath_valid : ∀ p, augPath = some p → f.IsAugmentingPath p
  /-- Residual-reachability cut (`f.reachableCut` when `augPath = none`). -/
  cut : Finset (Fin n)

theorem tblValid_init {n : ℕ} {N : Network (Fin n)} (f : N.Flow)
    (baseTbl : Vector (Option (List (Fin n))) n)
    (hbase : baseTbl = Vector.replicate n none) :
    TblValid f (vset baseTbl N.s (some [N.s])) := by
  subst hbase
  refine ⟨?_, ?_⟩
  · intro v rp hget
    by_cases hvs : v = N.s
    · subst hvs
      simp only [vget_vset_self, Option.some.injEq] at hget
      subst hget
      exact ⟨List.nodup_singleton N.s, rfl, rfl, by simp⟩
    · have hsv : N.s ≠ v := Ne.symm hvs
      simp [vget_vset_ne _ _ hsv] at hget
  · intro v rp hget x hx
    by_cases hvs : v = N.s
    · subst hvs
      simp only [vget_vset_self, Option.some.injEq] at hget
      subst hget
      simp only [List.reverse_singleton, List.mem_singleton] at hx
      subst hx
      simp
    · have hsv : N.s ≠ v := Ne.symm hvs
      simp [vget_vset_ne _ _ hsv] at hget

theorem tblValid_insert {n : ℕ} {N : Network (Fin n)} {f : N.Flow}
    {tbl : Vector (Option (List (Fin n))) n} (htbl : TblValid f tbl)
    {u v : Fin n} {rp_u : List (Fin n)}
    (hu_walk : IsRevWalkTo f u rp_u)
    (hu_mem : ∀ x ∈ rp_u.reverse, (vget tbl x).isSome = true)
    (hpos : 0 < f.resCap u v) (hnone : (vget tbl v).isNone = true) :
    TblValid f (vset tbl v (some (v :: rp_u))) ∧
      (∀ x ∈ rp_u.reverse, (vget (vset tbl v (some (v :: rp_u))) x).isSome = true) := by
  have hnone_eq : vget tbl v = none := Option.isNone_iff_eq_none.mp hnone
  have hpu_ne : rp_u.reverse ≠ [] := by
    intro hnil; have := hu_walk.head?; simp [hnil] at this
  have hv_walk : IsRevWalkTo f v (v :: rp_u) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [List.reverse_cons, List.nodup_append]
      have hv_notin : v ∉ rp_u.reverse := by grind
      exact ⟨hu_walk.nodup, List.nodup_singleton v, fun a ha b hb hab => by
        subst hab; rw [List.mem_singleton.mp hb] at ha; exact hv_notin ha⟩
    · simpa [List.reverse_cons, List.head?_append_of_ne_nil _ hpu_ne] using hu_walk.head?
    · simp [List.reverse_cons]
    · intro e he
      rw [List.reverse_cons, pathArcs_append_singleton hpu_ne hu_walk.getLast?,
        List.mem_append, List.mem_singleton] at he
      rcases he with he' | rfl
      · exact hu_walk.pos_resCap e he'
      · exact hpos
  have hisSome_mono : ∀ x, (vget tbl x).isSome = true →
      (vget (vset tbl v (some (v :: rp_u))) x).isSome = true := by
    intro x hx
    rcases eq_or_ne v x with rfl | hvx
    · simp
    · simp [vget_vset_ne _ _ hvx, hx]
  refine ⟨⟨?_, ?_⟩, fun x hx => hisSome_mono x (hu_mem x hx)⟩
  · intro w rp hget
    rcases eq_or_ne v w with rfl | hvw
    · simp only [vget_vset_self, Option.some.injEq] at hget
      exact hget ▸ hv_walk
    · exact htbl.walk w rp (by simpa [vget_vset_ne _ _ hvw] using hget)
  · intro w rp hget x hx
    rcases eq_or_ne v w with rfl | hvw
    · simp only [vget_vset_self, Option.some.injEq] at hget
      subst hget
      rw [List.reverse_cons, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx_u | rfl
      · exact hisSome_mono x (hu_mem x hx_u)
      · simp
    · exact hisSome_mono x
        (htbl.mem_isSome w rp (by simpa [vget_vset_ne _ _ hvw] using hget) x hx)

/-- Scan candidate neighbors `vs` of `u`, charging `1` tick per neighbor inspection. -/
@[expose] def scanNeighborsM {n : ℕ} {N : Network (Fin n)} (f : N.Flow)
    (u : Fin n) (rp_u : List (Fin n)) (hu_walk : IsRevWalkTo f u rp_u) :
    List (Fin n) → (st : BfsState f) →
    (∀ x ∈ rp_u.reverse, (vget st.revPath x).isSome = true) →
    TimeM ℕ (BfsState f)
  | [], st, _ => pure st
  | v :: vs, st, hu_mem => do
    ✓
    if hcond : (0 < f.resCap u v && (vget st.revPath v).isNone) = true then
      let hpos : 0 < f.resCap u v := of_decide_eq_true (Bool.and_eq_true_iff.mp hcond).1
      let hnone : (vget st.revPath v).isNone = true := (Bool.and_eq_true_iff.mp hcond).2
      let hins := tblValid_insert st.tblValid hu_walk hu_mem hpos hnone
      let st' : BfsState f :=
        { revPath := vset st.revPath v (some (v :: rp_u))
          frontier := v :: st.frontier
          tblValid := hins.1 }
      scanNeighborsM f u rp_u hu_walk vs st' hins.2
    else
      scanNeighborsM f u rp_u hu_walk vs st hu_mem

/-- Expand all vertices in `layer`, charging `1` tick per popped frontier vertex. -/
@[expose] def expandLayerM {n : ℕ} {N : Network (Fin n)} (f : N.Flow)
    (adj : Fin n → List (Fin n)) :
    List (Fin n) → BfsState f → TimeM ℕ (BfsState f)
  | [], st => pure st
  | u :: us, st => do
    ✓
    let st' ←
      match hget : vget st.revPath u with
      | none => pure st
      | some rp_u =>
        scanNeighborsM f u rp_u (st.tblValid.walk u rp_u hget) (adj u) st
          (st.tblValid.mem_isSome u rp_u hget)
    expandLayerM f adj us st'

/-- Run `k` BFS layer expansions from `(revPath, frontier)`. -/
@[expose] def bfsLoopM {n : ℕ} {N : Network (Fin n)} (f : N.Flow)
    (adj : Fin n → List (Fin n)) :
    ℕ → BfsState f → TimeM ℕ (BfsState f)
  | 0, st => pure st
  | k + 1, st => do
    let st' ← expandLayerM f adj st.frontier
      { revPath := st.revPath, frontier := [], tblValid := st.tblValid }
    bfsLoopM f adj k st'

/-- Breadth-first search for a shortest residual `s`-`t` augmenting path in `TimeM ℕ`. -/
@[expose] def bfsM {n : ℕ} (N : Network (Fin n)) (adj : Fin n → List (Fin n))
    (f : N.Flow) : TimeM ℕ (BfsResult f) := do
  let ⟨baseTbl, hbase⟩ ← attachRet (replicateM n (none : Option (List (Fin n))))
  let initSt : BfsState f :=
    { revPath := vset baseTbl N.s (some [N.s])
      frontier := [N.s]
      tblValid := tblValid_init f baseTbl (hbase.trans (replicateM_ret n none)) }
  let finalSt ← bfsLoopM f adj (n - 1) initSt
  match hget : vget finalSt.revPath N.t with
  | some rp_t =>
    let ⟨p, hp⟩ ← attachRet (reverseM rp_t)
    pure
      { augPath := some p
        augPath_valid := fun q hq => by
          injection hq with hq_eq
          subst hq_eq
          rw [hp, reverseM_ret]
          exact (finalSt.tblValid.walk N.t rp_t hget).isAugmentingPath
        cut := ∅ }
  | none =>
    let cut ← extractFinsetM fun v => (vget finalSt.revPath v).isSome
    pure
      { augPath := none
        augPath_valid := fun _ h => nomatch h
        cut := cut }

private structure ValidRevPath {n : ℕ} {N : Network (Fin n)} (f : N.Flow) (v : Fin n)
    (rp : List (Fin n)) : Prop extends IsRevWalkTo f v rp where
  length_eq : (pathArcs rp.reverse).length = f.resDist v

private structure LayerInv {n : ℕ} {N : Network (Fin n)} (f : N.Flow) (d : ℕ)
    (st : BfsState f) : Prop where
  frontier_nodup : st.frontier.Nodup
  mem_frontier : ∀ v, v ∈ st.frontier ↔ f.resDist v < n ∧ f.resDist v = d
  isSome_iff : ∀ v, (vget st.revPath v).isSome ↔ f.resDist v < n ∧ f.resDist v ≤ d
  valid_revPath : ∀ v rp, vget st.revPath v = some rp → ValidRevPath f v rp

private structure StepInv {n : ℕ} {N : Network (Fin n)} (f : N.Flow) (d : ℕ)
    (baseTbl : Vector (Option (List (Fin n))) n) (st : BfsState f) : Prop where
  frontier_nodup : st.frontier.Nodup
  mono_base : ∀ w rp, vget baseTbl w = some rp → vget st.revPath w = some rp
  mem_frontier : ∀ w, w ∈ st.frontier ↔ (vget baseTbl w).isNone ∧ (vget st.revPath w).isSome
  valid_entry : ∀ w rp, vget st.revPath w = some rp →
    ValidRevPath f w rp ∧ f.resDist w < n ∧ f.resDist w ≤ d + 1

private theorem scanNeighborsM_time {n : ℕ} {N : Network (Fin n)} (f : N.Flow)
    (u : Fin n) (rp_u : List (Fin n)) (hu_walk : IsRevWalkTo f u rp_u)
    (vs : List (Fin n)) (st : BfsState f)
    (hu_mem : ∀ x ∈ rp_u.reverse, (vget st.revPath x).isSome = true) :
    (scanNeighborsM f u rp_u hu_walk vs st hu_mem).time = vs.length := by
  induction vs generalizing st with
  | nil => rfl
  | cons v vs' ih =>
    simp only [scanNeighborsM]
    split_ifs with hcond
    · simp only [TimeM.time_bind, TimeM.time_tick, ih, List.length_cons]
      omega
    · simp only [TimeM.time_bind, TimeM.time_tick, ih, List.length_cons]
      omega

private theorem expandLayerM_time_le {n : ℕ} {N : Network (Fin n)} (f : N.Flow)
    (adj : Fin n → List (Fin n)) (us : List (Fin n)) (st : BfsState f) :
    (expandLayerM f adj us st).time ≤ (us.map fun u => 1 + (adj u).length).sum := by
  induction us generalizing st with
  | nil => simp [expandLayerM]
  | cons u us' ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [expandLayerM, TimeM.time_bind, TimeM.time_tick]
    dsimp only
    split
    · simp only [TimeM.time_bind, TimeM.ret_pure, TimeM.time_pure]
      have hrec := ih st
      omega
    · rename_i rp_u hget
      simp only [TimeM.time_bind, scanNeighborsM_time]
      have hrec := ih (scanNeighborsM f u rp_u (st.tblValid.walk u rp_u hget) (adj u) st
        (st.tblValid.mem_isSome u rp_u hget)).ret
      omega

private theorem scanNeighborsM_preserves {n : ℕ} {N : Network (Fin n)} {f : N.Flow} {d : ℕ}
    {baseTbl : Vector (Option (List (Fin n))) n}
    (hbase : ∀ v, (vget baseTbl v).isSome ↔ f.resDist v < n ∧ f.resDist v ≤ d)
    {u : Fin n} {rp_u : List (Fin n)} (hu_walk : IsRevWalkTo f u rp_u)
    (hu_valid : ValidRevPath f u rp_u) (hu_lt : f.resDist u < n) (hu_dist : f.resDist u = d)
    (vs : List (Fin n)) {st : BfsState f}
    (hu_mem : ∀ x ∈ rp_u.reverse, (vget st.revPath x).isSome = true)
    (hst : StepInv f d baseTbl st) :
    StepInv f d baseTbl (scanNeighborsM f u rp_u hu_walk vs st hu_mem).ret ∧
      (∀ w rp, vget st.revPath w = some rp →
        vget (scanNeighborsM f u rp_u hu_walk vs st hu_mem).ret.revPath w = some rp) ∧
      (∀ v ∈ vs, 0 < f.resCap u v →
        (vget (scanNeighborsM f u rp_u hu_walk vs st hu_mem).ret.revPath v).isSome = true) := by
  induction vs generalizing st with
  | nil => exact ⟨hst, fun _ _ h => h, by simp⟩
  | cons v vs' ih =>
    simp only [scanNeighborsM, TimeM.ret_bind]
    by_cases hcond : (0 < f.resCap u v && (vget st.revPath v).isNone) = true
    · simp only [hcond, ↓reduceDIte]
      obtain ⟨hpos', hnone⟩ := Bool.and_eq_true_iff.mp hcond
      have hpos : 0 < f.resCap u v := of_decide_eq_true hpos'
      have hnone_st : vget st.revPath v = none := Option.isNone_iff_eq_none.mp hnone
      have hnone_base : vget baseTbl v = none := by
        rcases hb : vget baseTbl v with _ | rp
        · rfl
        · have := hst.mono_base v rp hb; simp [hnone_st] at this
      have hv_not_front : v ∉ st.frontier := fun h => by
        have := (hst.mem_frontier v).mp h; simp [hnone_st] at this
      have hv_lt : f.resDist v < n := by
        have hu_reach := (f.resDist_lt_card_iff_resReachable u).mp
          (by simpa [Fintype.card_fin] using hu_lt)
        simpa [Fintype.card_fin] using
          (f.resDist_lt_card_iff_resReachable v).mpr (hu_reach.tail hpos)
      have hv_gt_d : ¬ f.resDist v ≤ d := fun hle => by
        have := (hbase v).mpr ⟨hv_lt, hle⟩; simp [hnone_base] at this
      have := f.resDist_le_add_one_of_pos_resCap hpos
      have hv_dist : f.resDist v = d + 1 := by omega
      let hins := tblValid_insert st.tblValid hu_walk hu_mem hpos hnone
      let st' : BfsState f :=
        { revPath := vset st.revPath v (some (v :: rp_u))
          frontier := v :: st.frontier
          tblValid := hins.1 }
      have hv_valid : ValidRevPath f v (v :: rp_u) := by
        have hpu_ne : rp_u.reverse ≠ [] := by
          intro hnil; have := hu_valid.head?; simp [hnil] at this
        have hlen_eq : (pathArcs (v :: rp_u).reverse).length = f.resDist v := by
          rw [List.reverse_cons, pathArcs_append_singleton hpu_ne hu_valid.getLast?,
            List.length_append, List.length_singleton, hu_valid.length_eq]
          omega
        exact ⟨hins.1.walk v (v :: rp_u) (by simp), hlen_eq⟩
      have hst' : StepInv f d baseTbl st' := by
        refine ⟨List.nodup_cons.mpr ⟨hv_not_front, hst.frontier_nodup⟩, ?_, ?_, ?_⟩
        · intro w rp hbw
          have hvw : v ≠ w := by rintro rfl; simp [hnone_base] at hbw
          simp only [st', vget_vset_ne _ _ hvw]
          exact hst.mono_base w rp hbw
        · intro w
          rcases eq_or_ne w v with rfl | hwv
          · simp [st', hnone_base]
          · simp only [st', List.mem_cons, hwv, false_or, vget_vset_ne _ _ hwv.symm]
            exact hst.mem_frontier w
        · intro w rp hw
          rcases eq_or_ne w v with rfl | hwv
          · simp only [st', vget_vset_self, Option.some.injEq] at hw
            subst hw
            exact ⟨hv_valid, hv_lt, by omega⟩
          · simp only [st', vget_vset_ne _ _ hwv.symm] at hw
            exact hst.valid_entry w rp hw
      obtain ⟨hfin, hmono', hcov'⟩ := ih hins.2 hst'
      refine ⟨hfin, ?_, ?_⟩
      · intro w rp hsw
        have hvw : v ≠ w := by rintro rfl; simp [hnone_st] at hsw
        exact hmono' w rp (by simpa [st', vget_vset_ne _ _ hvw] using hsw)
      · intro w hw hres_w
        rcases List.mem_cons.mp hw with hEq | hw'
        · have hv_some := hmono' v (v :: rp_u) (by simp [st'])
          rw [hEq, hv_some]
          rfl
        · exact hcov' w hw' hres_w
    · simp only [hcond]
      obtain ⟨hfin, hmono', hcov'⟩ := ih hu_mem hst
      refine ⟨hfin, hmono', fun w hw hres_w => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw'
      · have hnot_none : ¬ (vget st.revPath w).isNone = true := fun h => by
          have : (0 < f.resCap u w && (vget st.revPath w).isNone) = true :=
            Bool.and_eq_true_iff.mpr ⟨decide_eq_true hres_w, h⟩
          simp [hcond] at this
        have hsome : (vget st.revPath w).isSome = true := by
          cases h : vget st.revPath w <;> simp_all
        obtain ⟨rp_w, hrp_w⟩ := Option.isSome_iff_exists.mp hsome
        simp [hmono' w rp_w hrp_w]
      · exact hcov' w hw' hres_w

private theorem expandLayerM_preserves {n : ℕ} {N : Network (Fin n)} {f : N.Flow}
    {adj : Fin n → List (Fin n)} {d : ℕ}
    {baseSt : BfsState f} (hinv : LayerInv f d baseSt)
    (us : List (Fin n)) (hus : ∀ u ∈ us, u ∈ baseSt.frontier)
    {st : BfsState f} (hst : StepInv f d baseSt.revPath st) :
    StepInv f d baseSt.revPath (expandLayerM f adj us st).ret ∧
      (∀ w rp, vget st.revPath w = some rp →
        vget (expandLayerM f adj us st).ret.revPath w = some rp) ∧
      (∀ u ∈ us, ∀ v ∈ adj u, 0 < f.resCap u v →
        (vget (expandLayerM f adj us st).ret.revPath v).isSome = true) := by
  induction us generalizing st with
  | nil => exact ⟨hst, fun _ _ h => h, by simp⟩
  | cons u us' ih =>
    have hu_front : u ∈ baseSt.frontier := hus u List.mem_cons_self
    have hus' : ∀ x ∈ us', x ∈ baseSt.frontier := fun x hx => hus x (List.mem_cons_of_mem u hx)
    obtain ⟨hu_lt, hu_dist⟩ := (hinv.mem_frontier u).mp hu_front
    have hu_some_base : (vget baseSt.revPath u).isSome = true :=
      (hinv.isSome_iff u).mpr ⟨hu_lt, Nat.le_of_eq hu_dist⟩
    obtain ⟨rp_u, hrp_base⟩ := Option.isSome_iff_exists.mp hu_some_base
    have hrp_st : vget st.revPath u = some rp_u := hst.mono_base u rp_u hrp_base
    have hu_valid : ValidRevPath f u rp_u := hinv.valid_revPath u rp_u hrp_base
    simp only [expandLayerM, TimeM.ret_bind]
    split
    · rename_i hget_none
      rw [hrp_st] at hget_none
      simp at hget_none
    · rename_i rp_u' hget
      have hrp_eq : rp_u' = rp_u := Option.some.inj (hget.symm.trans hrp_st)
      subst rp_u'
      obtain ⟨hst_mid, hmono_mid, hcov_u⟩ :=
        scanNeighborsM_preserves hinv.isSome_iff (st.tblValid.walk u rp_u hget) hu_valid
          hu_lt hu_dist (adj u) (st.tblValid.mem_isSome u rp_u hget) hst
      obtain ⟨hst_end, hmono_end, hcov_us⟩ := ih hus' hst_mid
      refine ⟨hst_end, fun w rp hw => hmono_end w rp (hmono_mid w rp hw), ?_⟩
      intro x hx v hv hpos
      rcases List.mem_cons.mp hx with rfl | hx'
      · obtain ⟨rp_v, hrpv⟩ := Option.isSome_iff_exists.mp (hcov_u v hv hpos)
        simp only [TimeM.ret_bind]
        rw [hmono_end v rp_v hrpv]
        rfl
      · exact hcov_us x hx' v hv hpos

private theorem layerInv_step {n : ℕ} {N : Network (Fin n)} {f : N.Flow}
    {adj : Fin n → List (Fin n)} (hadj : AdjValid N adj) {d : ℕ}
    {baseSt : BfsState f} (hinv : LayerInv f d baseSt) :
    let st := (expandLayerM f adj baseSt.frontier
      { revPath := baseSt.revPath, frontier := [], tblValid := baseSt.tblValid }).ret
    LayerInv f (d + 1) st := by
  let st0 : BfsState f :=
    { revPath := baseSt.revPath, frontier := [], tblValid := baseSt.tblValid }
  have hst0 : StepInv f d baseSt.revPath st0 := by
    refine ⟨List.nodup_nil, fun _ _ h => h, fun w => by cases vget baseSt.revPath w <;> simp [st0],
      fun w rp hw => ?_⟩
    obtain ⟨hlt, _⟩ := (hinv.isSome_iff w).mp (by simp [st0] at hw; simp [hw])
    exact ⟨hinv.valid_revPath w rp hw, hlt, by omega⟩
  obtain ⟨hst, -, hcov⟩ := expandLayerM_preserves hinv baseSt.frontier (fun _ h => h) hst0
  dsimp only
  have hsome_iff : ∀ v : Fin n,
      (vget (expandLayerM f adj baseSt.frontier st0).ret.revPath v).isSome
        ↔ f.resDist v < n ∧ f.resDist v ≤ d + 1 := by
    intro v
    constructor
    · intro hs
      obtain ⟨rp, hrp⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨_, hlt, hle⟩ := hst.valid_entry v rp hrp
      exact ⟨hlt, hle⟩
    · rintro ⟨hlt, hle⟩
      by_cases hle_d : f.resDist v ≤ d
      · obtain ⟨rp, hrp⟩ := Option.isSome_iff_exists.mp ((hinv.isSome_iff v).mpr ⟨hlt, hle_d⟩)
        simp [hst.mono_base v rp hrp]
      · have hlt_card : d + 1 < Fintype.card (Fin n) := by grind [Fintype.card_fin]
        have heq_succ : f.resDist v = d + 1 := by omega
        obtain ⟨u, hu_dist, hpos⟩ := f.exists_pred_of_resDist_eq_succ hlt_card heq_succ
        have hu_front : u ∈ baseSt.frontier := (hinv.mem_frontier u).mpr ⟨by omega, hu_dist⟩
        have hcap_le := f.resCap_le_cap_add_cap u v
        exact hcov u hu_front v (hadj u v (by intro rfl; omega) (by omega)) hpos
  refine ⟨hst.frontier_nodup, fun v => ?_, hsome_iff, fun v rp hrp => (hst.valid_entry v rp hrp).1⟩
  rw [hst.mem_frontier v, hsome_iff v]
  have hbase : (vget baseSt.revPath v).isNone = true ↔ ¬ (f.resDist v < n ∧ f.resDist v ≤ d) := by
    rw [← hinv.isSome_iff v]
    cases vget baseSt.revPath v <;> simp
  rw [hbase]
  omega

private theorem layerInv_init {n : ℕ} {N : Network (Fin n)} (f : N.Flow)
    (baseTbl : Vector (Option (List (Fin n))) n)
    (hbase : baseTbl = Vector.replicate n none)
    (htbl : TblValid f (vset baseTbl N.s (some [N.s]))) :
    LayerInv f 0
      { revPath := vset baseTbl N.s (some [N.s])
        frontier := [N.s]
        tblValid := htbl } := by
  subst hbase
  have hn : 0 < n := Nat.zero_lt_of_lt N.s.isLt
  refine ⟨List.nodup_singleton N.s, ?_, ?_, ?_⟩
  · intro v
    simp only [List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨by simp [hn], f.resDist_source⟩
    · rintro ⟨_, h0⟩
      exact f.eq_source_of_resDist_eq_zero h0
  · intro v
    by_cases hvs : v = N.s
    · subst hvs
      simp [hn]
    · have hsv : N.s ≠ v := Ne.symm hvs
      simp only [vget_vset_ne _ _ hsv, vget_replicate, Option.isSome_none, Bool.false_eq_true,
        false_iff, not_and]
      intro _ hle
      exact hvs (f.eq_source_of_resDist_eq_zero (Nat.eq_zero_of_le_zero hle))
  · intro v rp hget
    by_cases hvs : v = N.s
    · subst hvs
      simp only [vget_vset_self, Option.some.injEq] at hget
      subst hget
      exact ⟨⟨List.nodup_singleton N.s, rfl, rfl, by simp⟩, by simp⟩
    · have hsv : N.s ≠ v := Ne.symm hvs
      simp [vget_vset_ne _ _ hsv] at hget

private theorem sum_map_le_filter_of_nodup {n : ℕ} (g : Fin n → ℕ) {l : List (Fin n)}
    (hl : l.Nodup) {P : Fin n → Prop} [DecidablePred P] (hP : ∀ u ∈ l, P u) :
    (l.map g).sum ≤ ∑ u ∈ Finset.univ.filter P, g u := by
  induction l generalizing P with
  | nil => simp
  | cons a l' ih =>
    obtain ⟨ha_not, hl'⟩ := List.nodup_cons.mp hl
    let P' : Fin n → Prop := fun u => P u ∧ u ≠ a
    have hP' : ∀ u ∈ l', P' u := by
      intro u hu
      exact ⟨hP u (List.mem_cons_of_mem a hu), fun h => ha_not (h ▸ hu)⟩
    have hrec := ih hl' hP'
    have ha_mem : a ∈ Finset.univ.filter P :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, hP a List.mem_cons_self⟩
    have hsub : Finset.univ.filter P' ⊆ (Finset.univ.filter P).erase a := by
      intro u hu
      simp only [P', Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact Finset.mem_erase.mpr ⟨hu.2, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu.1⟩⟩
    have hle_erase : ∑ u ∈ Finset.univ.filter P', g u ≤
        ∑ u ∈ (Finset.univ.filter P).erase a, g u :=
      Finset.sum_le_sum_of_subset hsub
    have hadd := Finset.add_sum_erase (Finset.univ.filter P) g ha_mem
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem bfsLoopM_spec {n : ℕ} {N : Network (Fin n)} {f : N.Flow}
    {adj : Fin n → List (Fin n)} (hadj : AdjValid N adj) :
    ∀ (k d : ℕ) (st : BfsState f),
      LayerInv f d st →
      LayerInv f (d + k) (bfsLoopM f adj k st).ret
  | 0, _, st, hinv => by simpa [bfsLoopM] using hinv
  | k + 1, d, st, hinv => by
    simp only [bfsLoopM, TimeM.ret_bind]
    have hstep := layerInv_step hadj hinv
    have hfin := bfsLoopM_spec hadj k (d + 1) _ hstep
    simpa [Nat.add_right_comm, Nat.add_assoc] using hfin

private theorem bfsLoopM_time_le_sum {n : ℕ} {N : Network (Fin n)} {f : N.Flow}
    {adj : Fin n → List (Fin n)} (hadj : AdjValid N adj) :
    ∀ (k d : ℕ) (st : BfsState f),
      LayerInv f d st →
      (bfsLoopM f adj k st).time ≤
        ∑ i ∈ Finset.range k,
          ∑ u ∈ Finset.univ.filter (fun u : Fin n => f.resDist u = d + i),
            (1 + (adj u).length)
  | 0, _, _, _ => by simp [bfsLoopM]
  | k + 1, d, st, hinv => by
    simp only [bfsLoopM, TimeM.time_bind]
    have hexp := expandLayerM_time_le f adj st.frontier
      { revPath := st.revPath, frontier := [], tblValid := st.tblValid }
    have hfront_sum :
        (st.frontier.map fun u => 1 + (adj u).length).sum ≤
          ∑ u ∈ Finset.univ.filter (fun u : Fin n => f.resDist u = d), (1 + (adj u).length) :=
      sum_map_le_filter_of_nodup (fun u => 1 + (adj u).length) hinv.frontier_nodup
        (fun u hu => ((hinv.mem_frontier u).mp hu).2)
    have hstep := layerInv_step hadj hinv
    have hrec := bfsLoopM_time_le_sum hadj k (d + 1) _ hstep
    rw [Finset.sum_range_succ']
    have hshift :
        (∑ x ∈ Finset.range k,
            ∑ u ∈ Finset.univ.filter (fun u : Fin n => f.resDist u = d + (x + 1)),
              (1 + (adj u).length)) =
          ∑ i ∈ Finset.range k,
            ∑ u ∈ Finset.univ.filter (fun u : Fin n => f.resDist u = (d + 1) + i),
              (1 + (adj u).length) :=
      Finset.sum_congr rfl fun i _ => by simp only [Nat.add_assoc, Nat.add_comm i 1]
    rw [hshift]
    simp only [Nat.add_zero]
    omega

private theorem sum_range_filter_resDist_le {n : ℕ} {N : Network (Fin n)} (f : N.Flow)
    (g : Fin n → ℕ) (k : ℕ) :
    (∑ i ∈ Finset.range k,
        ∑ u ∈ Finset.univ.filter (fun u : Fin n => f.resDist u = i), g u) ≤
      ∑ u : Fin n, g u := by
  have h1 :
      (∑ i ∈ Finset.range k,
          ∑ u ∈ Finset.univ.filter (fun u : Fin n => f.resDist u = i), g u) =
        ∑ i ∈ Finset.range k, ∑ u : Fin n, if f.resDist u = i then g u else 0 :=
    Finset.sum_congr rfl fun i _ => Finset.sum_filter _ _
  rw [h1, Finset.sum_comm]
  refine Finset.sum_le_sum fun u _ => ?_
  by_cases hmem : f.resDist u ∈ Finset.range k
  · rw [Finset.sum_eq_single (f.resDist u) (fun i _ hne => by simp [hne.symm])
      (fun h => absurd hmem h)]
    simp
  · rw [Finset.sum_eq_zero (fun i hi => by
      have hne : f.resDist u ≠ i := fun heq => hmem (heq ▸ hi)
      simp [hne])]
    omega

private theorem bfsM_loop_inv {n : ℕ} {N : Network (Fin n)} {adj : Fin n → List (Fin n)}
    (hadj : AdjValid N adj) (f : N.Flow) :
    let baseTbl := (replicateM n (none : Option (List (Fin n)))).ret
    let initSt : BfsState f :=
      { revPath := vset baseTbl N.s (some [N.s])
        frontier := [N.s]
        tblValid := tblValid_init f baseTbl (rfl.trans (replicateM_ret n none)) }
    LayerInv f (n - 1) (bfsLoopM f adj (n - 1) initSt).ret ∧
      (bfsLoopM f adj (n - 1) initSt).time ≤ n + adjSteps adj := by
  intro baseTbl initSt
  have hinit := layerInv_init f baseTbl (replicateM_ret n none) initSt.tblValid
  have hinv := bfsLoopM_spec hadj (n - 1) 0 initSt hinit
  rw [Nat.zero_add] at hinv
  refine ⟨hinv, ?_⟩
  have hsum := bfsLoopM_time_le_sum hadj (n - 1) 0 initSt hinit
  simp only [Nat.zero_add] at hsum
  have hub := sum_range_filter_resDist_le f (fun u => 1 + (adj u).length) (n - 1)
  have htot : (∑ u : Fin n, (1 + (adj u).length)) = n + adjSteps adj := by
    rw [Finset.sum_add_distrib]
    simp [adjSteps, Fintype.card_fin]
  omega

/-- Specification of `bfsM`: when `augPath = some p`, `p` is a shortest residual `s`-`t`
augmenting path of length at most `n`; when `augPath = none`, `f` has no augmenting path and
`cut = f.reachableCut`. -/
theorem bfsM_spec {n : ℕ} {N : Network (Fin n)} {adj : Fin n → List (Fin n)}
    (hadj : AdjValid N adj) (f : N.Flow) :
    (∀ p, (bfsM N adj f).ret.augPath = some p →
      f.IsShortestAugmentingPath p ∧ p.length ≤ n) ∧
    ((bfsM N adj f).ret.augPath = none →
      (¬ ∃ p, f.IsAugmentingPath p) ∧ (bfsM N adj f).ret.cut = f.reachableCut) := by
  have hinv := (bfsM_loop_inv hadj f).1
  unfold bfsM
  simp only [TimeM.ret_bind]
  dsimp only [attachRet]
  split
  · rename_i rp_t hget
    simp only [TimeM.ret_bind, reverseM_ret, TimeM.ret_pure, Option.some.injEq,
      reduceCtorEq, false_implies, and_true]
    intro p hp
    subst hp
    have hv := hinv.valid_revPath N.t rp_t hget
    exact ⟨⟨hv.toIsRevWalkTo.isAugmentingPath, hv.length_eq⟩,
      by simpa [Fintype.card_fin] using hv.nodup.length_le_card⟩
  · rename_i hget
    simp only [TimeM.ret_bind, extractFinsetM_ret, TimeM.ret_pure, reduceCtorEq, false_implies,
      implies_true, true_and]
    intro _
    refine ⟨?_, ?_⟩
    · rw [f.exists_augmentingPath_iff_resReachable, ← f.resDist_lt_card_iff_resReachable,
        Fintype.card_fin]
      intro hlt
      have hsome := (hinv.isSome_iff N.t).mpr ⟨hlt, by omega⟩
      rw [hget] at hsome
      simp at hsome
    · ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, f.mem_reachableCut_iff,
        ← f.resDist_lt_card_iff_resReachable, Fintype.card_fin]
      rw [hinv.isSome_iff v]
      omega

/-- Every `bfsM` call charges at least `n` ticks (table initialization). -/
theorem n_le_bfsM_time {n : ℕ} (N : Network (Fin n)) (adj : Fin n → List (Fin n)) (f : N.Flow) :
    n ≤ (bfsM N adj f).time := by
  unfold bfsM
  simp only [TimeM.time_bind, attachRet_time, replicateM_time]
  omega

/-- Each `bfsM` call takes at most `adjSteps adj + 3 * n` charged `TimeM` ticks. -/
theorem bfsM_time_le {n : ℕ} {N : Network (Fin n)} {adj : Fin n → List (Fin n)}
    (hadj : AdjValid N adj) (f : N.Flow) :
    (bfsM N adj f).time ≤ adjSteps adj + 3 * n := by
  obtain ⟨hinv, hloop_le⟩ := bfsM_loop_inv hadj f
  unfold bfsM
  simp only [TimeM.time_bind, attachRet_time, replicateM_time]
  dsimp only [attachRet]
  split
  · rename_i rp_t hget
    simp only [TimeM.time_bind, reverseM_time, TimeM.time_pure]
    have hlen : rp_t.length ≤ n := by
      simpa [Fintype.card_fin] using (hinv.valid_revPath N.t rp_t hget).nodup.length_le_card
    omega
  · simp only [TimeM.time_bind, extractFinsetM_time, TimeM.time_pure]
    omega

/-! #### Explicit `n × n` `FlowMatrix` and arc-by-arc bottleneck augmentation -/

/-- Concrete `n × n` `Vector` matrix storing arc flows, paired with erased feasibility proofs so
`toFlow` performs `O(1)` matrix lookups with zero stacked closures. -/
structure FlowMatrix {n : ℕ} (N : Network (Fin n)) where
  /-- Concrete `n × n` matrix of arc flows. -/
  mat : Vector (Vector ℕ n) n
  /-- Capacity bound on every entry (erased `Prop`). -/
  le_cap : ∀ u v, fget mat u v ≤ N.cap u v
  /-- Flow conservation at intermediate vertices (erased `Prop`). -/
  conserve : ∀ v, v ≠ N.s → v ≠ N.t → ∑ u, fget mat u v = ∑ w, fget mat v w

/-- View a `FlowMatrix N` as an `N.Flow` whose `toFun` is `O(1)` `fget` lookup. -/
@[expose] def FlowMatrix.toFlow {n : ℕ} {N : Network (Fin n)} (M : FlowMatrix N) : N.Flow where
  toFun u v := fget M.mat u v
  le_cap := M.le_cap
  conserve := M.conserve

@[simp]
theorem FlowMatrix.toFlow_apply {n : ℕ} {N : Network (Fin n)} (M : FlowMatrix N) (u v : Fin n) :
    M.toFlow u v = fget M.mat u v := rfl

/-- Allocate the all-zero `FlowMatrix N` in `2 * n` `TimeM` ticks. -/
@[expose] def initFlowMatrixM {n : ℕ} (N : Network (Fin n)) : TimeM ℕ (FlowMatrix N) := do
  let ⟨row, hrow⟩ ← attachRet (replicateM n (0 : ℕ))
  let ⟨mat, hmat⟩ ← attachRet (replicateM n row)
  pure
    { mat := mat
      le_cap := fun u v => by
        rw [hmat, replicateM_ret, hrow, replicateM_ret]
        simp [fget]
      conserve := fun v _ _ => by
        rw [hmat, replicateM_ret, hrow, replicateM_ret]
        simp [fget] }

@[simp]
theorem initFlowMatrixM_toFlow {n : ℕ} (N : Network (Fin n)) :
    (initFlowMatrixM N).ret.toFlow = Network.Flow.zero N := by
  ext u v
  simp [initFlowMatrixM, fget]

@[simp]
theorem initFlowMatrixM_time {n : ℕ} (N : Network (Fin n)) :
    (initFlowMatrixM N).time = 2 * n := by
  simp only [initFlowMatrixM, TimeM.time_bind, attachRet_time, replicateM_time, TimeM.time_pure]
  omega

/-- Push `δ` units along directed arcs `es` in `mat`, charging `1` tick per arc. -/
@[expose] def updateArcsMatM {n : ℕ} (δ : ℕ) :
    List (Fin n × Fin n) → Vector (Vector ℕ n) n → TimeM ℕ (Vector (Vector ℕ n) n)
  | [], mat => pure mat
  | (a, b) :: es, mat => do
    ✓
    let cancel := min δ (fget mat b a)
    let mat₁ := fset mat b a (fget mat b a - cancel)
    let mat₂ := fset mat₁ a b (fget mat a b + (δ - cancel))
    updateArcsMatM δ es mat₂

@[simp]
theorem updateArcsMatM_time {n : ℕ} (δ : ℕ) (es : List (Fin n × Fin n))
    (mat : Vector (Vector ℕ n) n) :
    (updateArcsMatM δ es mat).time = es.length := by
  induction es generalizing mat with
  | nil => rfl
  | cons e es' ih =>
    rcases e with ⟨a, b⟩
    simp only [updateArcsMatM, TimeM.time_bind, TimeM.time_tick, ih, List.length_cons]
    omega

private theorem fget_updateArcsMatM_ret {n : ℕ} (δ : ℕ) {es : List (Fin n × Fin n)}
    (hnodup : es.Nodup) (hloopless : ∀ e ∈ es, e.1 ≠ e.2)
    (hnoswap : ∀ u v, (u, v) ∈ es → (v, u) ∉ es)
    (mat : Vector (Vector ℕ n) n) (u v : Fin n) :
    fget (updateArcsMatM δ es mat).ret u v =
      if (u, v) ∈ es then fget mat u v + (δ - min δ (fget mat v u))
      else if (v, u) ∈ es then fget mat u v - min δ (fget mat u v)
      else fget mat u v := by
  induction es generalizing mat with
  | nil => simp [updateArcsMatM]
  | cons e es' ih =>
    rcases e with ⟨a, b⟩
    obtain ⟨hab_not_es, hnodup'⟩ := List.nodup_cons.mp hnodup
    have hab_ne : a ≠ b := hloopless (a, b) List.mem_cons_self
    have hba_not_es : (b, a) ∉ es' := fun h =>
      hnoswap a b List.mem_cons_self (List.mem_cons_of_mem (a, b) h)
    let cancel := min δ (fget mat b a)
    let mat₁ := fset mat b a (fget mat b a - cancel)
    let mat₂ := fset mat₁ a b (fget mat a b + (δ - cancel))
    have hstep_fget : ∀ x y : Fin n,
        fget mat₂ x y =
          if (x, y) = (a, b) then fget mat x y + (δ - min δ (fget mat y x))
          else if (y, x) = (a, b) then fget mat x y - min δ (fget mat x y)
          else fget mat x y := by
      intro x y
      by_cases hxy : (x, y) = (a, b)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
        simp [mat₂, cancel]
      · have hab_xy : (a, b) ≠ (x, y) := Ne.symm hxy
        by_cases hyx : (y, x) = (a, b)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hyx
          simp [hxy, mat₂, mat₁, cancel, fget_fset_ne _ _ hab_xy]
        · have hba_xy : (b, a) ≠ (x, y) := fun h => by
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
            exact hyx rfl
          simp [hxy, hyx, mat₂, mat₁, fget_fset_ne _ _ hab_xy, fget_fset_ne _ _ hba_xy]
    simp only [updateArcsMatM, TimeM.ret_bind]
    rw [ih hnodup' (fun e' he' => hloopless e' (List.mem_cons_of_mem _ he'))
      (fun x y hxy hyx =>
        hnoswap x y (List.mem_cons_of_mem _ hxy) (List.mem_cons_of_mem _ hyx)) mat₂]
    by_cases huv_es : (u, v) ∈ es'
    · have huv_ne : (u, v) ≠ (a, b) := fun h => hab_not_es (h ▸ huv_es)
      have hvu_ne : (v, u) ≠ (a, b) := fun h =>
        hba_not_es (by rcases Prod.mk.inj h with ⟨rfl, rfl⟩; exact huv_es)
      simp only [huv_es, List.mem_cons_of_mem _ huv_es, ↓reduceIte, hstep_fget, huv_ne, hvu_ne]
    · by_cases hvu_es : (v, u) ∈ es'
      · have hvu_ne : (v, u) ≠ (a, b) := fun h => hab_not_es (h ▸ hvu_es)
        have huv_ne : (u, v) ≠ (a, b) := fun h =>
          hba_not_es (by rcases Prod.mk.inj h with ⟨rfl, rfl⟩; exact hvu_es)
        simp only [huv_es, hvu_es, List.mem_cons, huv_ne, false_or,
          List.mem_cons_of_mem _ hvu_es, ↓reduceIte, hstep_fget, hvu_ne]
      · simp only [huv_es, hvu_es, ↓reduceIte, hstep_fget, List.mem_cons, or_false]

/-- Compute `δ ← bottleneckM M.toFlow p` (`(pathArcs p).length` ticks) and update `M` arc-by-arc
along `pathArcs p` using `δ` (`(pathArcs p).length` ticks). -/
@[expose] def augmentFlowMatrixM {n : ℕ} {N : Network (Fin n)} (M : FlowMatrix N)
    (p : List (Fin n)) (hp : M.toFlow.IsAugmentingPath p) : TimeM ℕ (FlowMatrix N) := do
  let ⟨δ, hδ⟩ ← attachRet (bottleneckM M.toFlow p)
  let ⟨mat', hmat'⟩ ← attachRet (updateArcsMatM δ (pathArcs p) M.mat)
  have hfun : ∀ u v, fget mat' u v = (M.toFlow.augmentByBottleneck p hp) u v := fun u v => by
    rw [hmat', fget_updateArcsMatM_ret δ (nodup_pathArcs hp.nodup)
      (fun e he => ne_of_mem_pathArcs hp.nodup he)
      (fun a b hab => not_swap_mem_pathArcs hp.nodup hab), hδ, bottleneckM_ret]
    rfl
  pure
    { mat := mat'
      le_cap := fun u v => by
        rw [hfun u v]
        exact (M.toFlow.augmentByBottleneck p hp).le_cap u v
      conserve := fun v hvs hvt => by
        simp only [hfun]
        exact (M.toFlow.augmentByBottleneck p hp).conserve v hvs hvt }

@[simp]
theorem augmentFlowMatrixM_toFlow {n : ℕ} {N : Network (Fin n)} (M : FlowMatrix N)
    (p : List (Fin n)) (hp : M.toFlow.IsAugmentingPath p) :
    (augmentFlowMatrixM M p hp).ret.toFlow = M.toFlow.augmentByBottleneck p hp := by
  ext u v
  simp only [augmentFlowMatrixM, TimeM.ret_bind, attachRet_val, bottleneckM_ret, TimeM.ret_pure,
    FlowMatrix.toFlow_apply]
  exact fget_updateArcsMatM_ret (M.toFlow.bottleneck p) (nodup_pathArcs hp.nodup)
    (fun e he => ne_of_mem_pathArcs hp.nodup he)
    (fun a b hab => not_swap_mem_pathArcs hp.nodup hab) M.mat u v

@[simp]
theorem augmentFlowMatrixM_time {n : ℕ} {N : Network (Fin n)} (M : FlowMatrix N)
    (p : List (Fin n)) (hp : M.toFlow.IsAugmentingPath p) :
    (augmentFlowMatrixM M p hp).time = 2 * (pathArcs p).length := by
  simp only [augmentFlowMatrixM, TimeM.time_bind, attachRet_time, bottleneckM_time,
    attachRet_val, updateArcsMatM_time, TimeM.time_pure]
  omega

/-- Output of the Edmonds–Karp algorithm on `N : Network (Fin n)`. -/
structure Output {n : ℕ} (N : Network (Fin n)) where
  /-- Final integral flow on `N`. -/
  flow : N.Flow
  /-- Residual-reachability cut certifying optimality (`flow.reachableCut`). -/
  cut : Finset (Fin n)
  /-- Number of shortest-path augmentations performed. -/
  augmentations : ℕ

/-- Mathematical upper bound on the number of shortest-path augmentations performed by Edmonds–Karp
on `N` ([CLRS2009], Theorem 26.8, p. 729). -/
def maxAugmentations {n : ℕ} (N : Network (Fin n)) : ℕ :=
  N.symArcs.card * (n / 2)

/-- Bounded-fuel Edmonds–Karp loop over `FlowMatrix N`: runs `bfsM` and augments along shortest
paths while `fuel` remains, finishing with one certifying `bfsM` search when `fuel = 0` or
`augPath = none`. -/
@[expose] def edmondsKarpLoopM {n : ℕ} (N : Network (Fin n)) (adj : Fin n → List (Fin n)) :
    ℕ → FlowMatrix N → ℕ → TimeM ℕ (Output N)
  | 0, M, k => do
    let res ← bfsM N adj M.toFlow
    pure { flow := M.toFlow, cut := res.cut, augmentations := k }
  | fuel + 1, M, k => do
    let res ← bfsM N adj M.toFlow
    match haug : res.augPath with
    | none => pure { flow := M.toFlow, cut := res.cut, augmentations := k }
    | some p =>
      let M' ← augmentFlowMatrixM M p (res.augPath_valid p haug)
      edmondsKarpLoopM N adj fuel M' (k + 1)

/-- Execute the **Edmonds–Karp shortest-augmenting-path algorithm** on `N : Network (Fin n)` using
candidate neighbor lists `adj` in `TimeM ℕ`. -/
@[expose] def edmondsKarpM {n : ℕ} (N : Network (Fin n))
    (adj : Fin n → List (Fin n)) : TimeM ℕ (Output N) := do
  let M₀ ← initFlowMatrixM N
  ✓
  if N.s = N.t then
    pure { flow := M₀.toFlow, cut := ∅, augmentations := 0 }
  else
    let m ← countAdjM adj
    edmondsKarpLoopM N adj (m * (n / 2)) M₀ 0

/-- Dense specialization of `edmondsKarpM` using `defaultAdj n` (`List.finRange n` at every
vertex), requiring no external adjacency structure. -/
@[expose] def edmondsKarpDenseM {n : ℕ} (N : Network (Fin n)) : TimeM ℕ (Output N) :=
  edmondsKarpM N (defaultAdj n)

private theorem isShortestAugmentingSeq_snoc {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}
    {k : ℕ} {flows : ℕ → N.Flow} {paths : ℕ → List V}
    (hseq : N.IsShortestAugmentingSeq k flows paths)
    {p : List V} (hp : (flows k).IsShortestAugmentingPath p) :
    N.IsShortestAugmentingSeq (k + 1)
      (fun t => if t ≤ k then flows t else (flows k).augmentByBottleneck p hp.isAugmentingPath)
      (fun t => if t < k then paths t else p) := by
  intro t ht
  by_cases hlt : t < k
  · have hle : t ≤ k := Nat.le_of_lt hlt
    have hsucc : t + 1 ≤ k := hlt
    obtain ⟨hpt, hnext⟩ := hseq t hlt
    simp only [hle, hlt, hsucc, ↓reduceIte]
    exact ⟨hpt, hnext⟩
  · have heq : t = k := by omega
    subst heq
    have hnot_le : ¬ t + 1 ≤ t := by omega
    have hnot_lt : ¬ t < t := Nat.lt_irrefl t
    simp only [le_rfl, hnot_lt, hnot_le, ↓reduceIte]
    exact ⟨hp, trivial⟩

private theorem edmondsKarpLoopM_stop {n : ℕ} {N : Network (Fin n)}
    {adj : Fin n → List (Fin n)} (hadj : AdjValid N adj) (hst : N.s ≠ N.t)
    {k : ℕ} {M : FlowMatrix N} {flows : ℕ → N.Flow} {paths : ℕ → List (Fin n)}
    (hseq : N.IsShortestAugmentingSeq k flows paths)
    (hnone : (bfsM N adj M.toFlow).ret.augPath = none) :
    (¬ ∃ p, M.toFlow.IsAugmentingPath p) ∧
      (bfsM N adj M.toFlow).ret.cut = M.toFlow.reachableCut ∧
      k ≤ maxAugmentations N ∧
      k ≤ n * N.posArcs.card ∧
      (bfsM N adj M.toFlow).time ≤ (maxAugmentations N - k + 1) * (adjSteps adj + 5 * n) := by
  have hbfs := bfsM_spec hadj M.toFlow
  have hbfs_t := bfsM_time_le hadj M.toFlow
  obtain ⟨hno, hcut⟩ := hbfs.2 hnone
  have hk_sym : k ≤ maxAugmentations N := by
    simpa [maxAugmentations, Fintype.card_fin] using N.shortestAugmentingSeq_length_le hst hseq
  have hk_pos : k ≤ n * N.posArcs.card := by
    simpa [Fintype.card_fin] using N.shortestAugmentingSeq_length_le_card_mul_posArcs hst hseq
  have ht_bound : (bfsM N adj M.toFlow).time ≤
      (maxAugmentations N - k + 1) * (adjSteps adj + 5 * n) :=
    calc
      (bfsM N adj M.toFlow).time ≤ adjSteps adj + 3 * n := hbfs_t
      _ ≤ 1 * (adjSteps adj + 5 * n) := by omega
      _ ≤ (maxAugmentations N - k + 1) * (adjSteps adj + 5 * n) := Nat.mul_le_mul_right _ (by omega)
  exact ⟨hno, hcut, hk_sym, hk_pos, ht_bound⟩

private theorem edmondsKarpLoopM_spec {n : ℕ} {N : Network (Fin n)}
    {adj : Fin n → List (Fin n)} (hadj : AdjValid N adj) (hst : N.s ≠ N.t) :
    ∀ (fuel k : ℕ) (M : FlowMatrix N) (flows : ℕ → N.Flow) (paths : ℕ → List (Fin n)),
      maxAugmentations N ≤ fuel + k →
      N.IsShortestAugmentingSeq k flows paths →
      flows k = M.toFlow →
      let call := edmondsKarpLoopM N adj fuel M k
      (¬ ∃ p, call.ret.flow.IsAugmentingPath p) ∧
        call.ret.cut = call.ret.flow.reachableCut ∧
        call.ret.augmentations ≤ maxAugmentations N ∧
        call.ret.augmentations ≤ n * N.posArcs.card ∧
        call.time ≤ (maxAugmentations N - k + 1) * (adjSteps adj + 5 * n)
  | 0, k, M, flows, paths, hfuel, hseq, hfk => by
    simp only [edmondsKarpLoopM, TimeM.ret_bind, TimeM.ret_pure, TimeM.time_bind, TimeM.time_pure]
    rcases haug : (bfsM N adj M.toFlow).ret.augPath with _ | p
    · simpa using edmondsKarpLoopM_stop hadj hst hseq haug
    · obtain ⟨hshort, _⟩ := (bfsM_spec hadj M.toFlow).1 p haug
      have hseq' := isShortestAugmentingSeq_snoc hseq (hfk ▸ hshort)
      have hlen' : k + 1 ≤ maxAugmentations N := by
        simpa [maxAugmentations, Fintype.card_fin] using N.shortestAugmentingSeq_length_le hst hseq'
      omega
  | fuel + 1, k, M, flows, paths, hfuel, hseq, hfk => by
    have hbfs := bfsM_spec hadj M.toFlow
    have hbfs_t := bfsM_time_le hadj M.toFlow
    simp only [edmondsKarpLoopM, TimeM.ret_bind, TimeM.time_bind]
    split
    · rename_i haug
      simpa [TimeM.ret_pure, TimeM.time_pure] using
        edmondsKarpLoopM_stop hadj hst hseq haug
    · rename_i p haug
      simp only [TimeM.ret_bind, TimeM.time_bind, augmentFlowMatrixM_time]
      obtain ⟨hshort, hplen⟩ := hbfs.1 p haug
      have hp : M.toFlow.IsAugmentingPath p := (bfsM N adj M.toFlow).ret.augPath_valid p haug
      have hshort' : (flows k).IsShortestAugmentingPath p := hfk ▸ hshort
      have hseq' := isShortestAugmentingSeq_snoc hseq hshort'
      have hlen' : k + 1 ≤ maxAugmentations N := by
        simpa [maxAugmentations, Fintype.card_fin] using N.shortestAugmentingSeq_length_le hst hseq'
      let M' := (augmentFlowMatrixM M p hp).ret
      have hfk' :
          (if k + 1 ≤ k then flows (k + 1)
           else (flows k).augmentByBottleneck p hshort'.isAugmentingPath) = M'.toFlow := by
        have hnot : ¬ k + 1 ≤ k := by omega
        simp only [hnot, ↓reduceIte, M', augmentFlowMatrixM_toFlow]
        ext u v
        change (flows k).augmentFun p ((flows k).bottleneck p) u v =
          M.toFlow.augmentFun p (M.toFlow.bottleneck p) u v
        rw [hfk]
      obtain ⟨hno, hcut, hk_sym, hk_pos, hrec_t⟩ :=
        edmondsKarpLoopM_spec hadj hst fuel (k + 1) M' _ _ (by omega) hseq' hfk'
      dsimp only [M', hp] at hrec_t
      have hp_ne : p ≠ [] := by intro hnil; have := hp.head?; simp [hnil] at this
      have harc_len : (pathArcs p).length ≤ n := by have := length_pathArcs_add_one hp_ne; omega
      have hrem : maxAugmentations N - k + 1 = 1 + (maxAugmentations N - (k + 1) + 1) := by omega
      have hmul : (maxAugmentations N - k + 1) * (adjSteps adj + 5 * n) =
          (adjSteps adj + 5 * n) + (maxAugmentations N - (k + 1) + 1) * (adjSteps adj + 5 * n) := by
        rw [hrem, Nat.add_mul, Nat.one_mul]
      exact ⟨hno, hcut, hk_sym, hk_pos, by omega⟩

/-- `edmondsKarpLoopM_spec` for the call made by `edmondsKarpM`: zero flow, no augmentations yet
and `adjSteps adj * (n / 2)` fuel. Shared by `edmondsKarpM_correct` and `edmondsKarpM_time_le`. -/
private theorem edmondsKarpLoopM_spec_init {n : ℕ} {N : Network (Fin n)}
    {adj : Fin n → List (Fin n)} (hadj : AdjValid N adj) (hst : N.s ≠ N.t) :
    let call := edmondsKarpLoopM N adj (adjSteps adj * (n / 2)) (initFlowMatrixM N).ret 0
    (¬ ∃ p, call.ret.flow.IsAugmentingPath p) ∧
      call.ret.cut = call.ret.flow.reachableCut ∧
      call.ret.augmentations ≤ maxAugmentations N ∧
      call.ret.augmentations ≤ n * N.posArcs.card ∧
      call.time ≤ (maxAugmentations N + 1) * (adjSteps adj + 5 * n) := by
  refine edmondsKarpLoopM_spec hadj hst _ 0 _ (fun _ => Network.Flow.zero N) (fun _ => [])
    ?_ (fun _ ht => absurd ht (Nat.not_lt_zero _)) (initFlowMatrixM_toFlow N).symm
  simp only [maxAugmentations, Nat.add_zero]
  exact Nat.mul_le_mul_right _ (card_symArcs_le_adjSteps hadj)

/-- **Edmonds–Karp correctness theorem** ([EdmondsKarp1972], Theorem 1, p. 251; [CLRS2009],
Theorems 26.6 & 26.8, pp. 723, 729): on any integral network `N : Network (Fin n)` with `N.s ≠ N.t`
and valid candidate neighbor lists `adj`, `edmondsKarpM N adj` returns an integral maximum flow
`out.flow` and minimum `s`-`t` cut `out.cut = out.flow.reachableCut` with
`out.flow.value = N.cutCapacity out.cut` in at most `N.symArcs.card * (n / 2)` (and at most
`n * N.posArcs.card`) augmentations. -/
theorem edmondsKarpM_correct {n : ℕ} {N : Network (Fin n)} {adj : Fin n → List (Fin n)}
    (hadj : AdjValid N adj) (hst : N.s ≠ N.t) :
    let out := (edmondsKarpM N adj).ret
    out.flow.IsMaxFlow ∧
      N.IsMinCut out.cut ∧
      out.flow.value = (N.cutCapacity out.cut : ℤ) ∧
      out.cut = out.flow.reachableCut ∧
      out.augmentations ≤ N.symArcs.card * (n / 2) ∧
      out.augmentations ≤ n * N.posArcs.card := by
  unfold edmondsKarpM
  simp only [TimeM.ret_bind, hst, ↓reduceIte, countAdjM_ret]
  obtain ⟨hno, hcut_eq, haug_sym, haug_pos, _⟩ := edmondsKarpLoopM_spec_init hadj hst
  let out := (edmondsKarpLoopM N adj (adjSteps adj * (n / 2)) (initFlowMatrixM N).ret 0).ret
  change out.flow.IsMaxFlow ∧ N.IsMinCut out.cut ∧ out.flow.value = (N.cutCapacity out.cut : ℤ) ∧
    out.cut = out.flow.reachableCut ∧ out.augmentations ≤ N.symArcs.card * (n / 2) ∧
    out.augmentations ≤ n * N.posArcs.card
  have hmax : out.flow.IsMaxFlow := (out.flow.isMaxFlow_iff_not_exists_augmentingPath hst).mpr hno
  have his_cut := out.flow.reachableCut_isCut hno
  have hval := out.flow.value_eq_cutCapacity_reachableCut hno
  have hmin := out.flow.isMinCut_of_value_eq_cutCapacity his_cut hval
  rw [← hcut_eq] at hmin hval
  exact ⟨hmax, hmin, hval, hcut_eq, haug_sym, haug_pos⟩

/-- **Edmonds–Karp `TimeM` complexity bound** ([EdmondsKarp1972], Theorem 1, p. 251; [CLRS2009],
Theorem 26.8, p. 729): `edmondsKarpM N adj` terminates in at most
`(N.symArcs.card * (n / 2) + 2) * (adjSteps adj + 5 * n)` charged ticks (`O(|V| |E|^2)` when
`adjSteps adj = O(|E|)` and `|V| = O(|E|)`).

**Limitations / cost model:** each charged tick treats `Vector` indexing/update (`FlowMatrix`),
`Finset.insert`, `ℕ` arithmetic, and `N.cap u v` evaluation as unit-cost primitives; persistent
`Vector` copy-on-write and bit-level arithmetic costs are not modeled. -/
theorem edmondsKarpM_time_le {n : ℕ} {N : Network (Fin n)} {adj : Fin n → List (Fin n)}
    (hadj : AdjValid N adj) :
    (edmondsKarpM N adj).time ≤ (N.symArcs.card * (n / 2) + 2) * (adjSteps adj + 5 * n) := by
  have hn : 0 < n := Nat.zero_lt_of_lt N.s.isLt
  unfold edmondsKarpM
  simp only [TimeM.time_bind, initFlowMatrixM_time, TimeM.time_tick]
  by_cases hst : N.s = N.t
  · simp only [hst, ↓reduceIte, TimeM.time_pure]
    have hbase : 2 * n + (1 + 0) ≤ 2 * (adjSteps adj + 5 * n) := by omega
    exact le_trans hbase (Nat.mul_le_mul_right _ (by omega))
  · simp only [hst, ↓reduceIte, TimeM.time_bind, countAdjM_time, countAdjM_ret]
    obtain ⟨_, _, _, _, hloop_t⟩ := edmondsKarpLoopM_spec_init hadj hst
    simp only [maxAugmentations] at hloop_t
    have hmul : (N.symArcs.card * (n / 2) + 2) * (adjSteps adj + 5 * n) =
        (adjSteps adj + 5 * n) + (N.symArcs.card * (n / 2) + 1) * (adjSteps adj + 5 * n) := by
      rw [show N.symArcs.card * (n / 2) + 2 = 1 + (N.symArcs.card * (n / 2) + 1) by omega,
        Nat.add_mul, Nat.one_mul]
    omega

/-- Sparse `posArcs` corollary of `edmondsKarpM_time_le`: `edmondsKarpM N adj` takes at most
`(n * N.posArcs.card + 2) * (adjSteps adj + 5 * n)` charged ticks. -/
theorem edmondsKarpM_time_le_posArcs {n : ℕ} {N : Network (Fin n)} {adj : Fin n → List (Fin n)}
    (hadj : AdjValid N adj) :
    (edmondsKarpM N adj).time ≤ (n * N.posArcs.card + 2) * (adjSteps adj + 5 * n) := by
  have h1 := edmondsKarpM_time_le hadj
  have h2 := N.card_symArcs_le_two_mul_posArcs
  have hdiv : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  have hsym : N.symArcs.card * (n / 2) ≤ n * N.posArcs.card := by
    calc
      N.symArcs.card * (n / 2) ≤ (2 * N.posArcs.card) * (n / 2) := Nat.mul_le_mul_right _ h2
      _ = N.posArcs.card * (2 * (n / 2)) := by
        rw [Nat.mul_comm 2 N.posArcs.card, Nat.mul_assoc]
      _ ≤ N.posArcs.card * n := Nat.mul_le_mul_left _ hdiv
      _ = n * N.posArcs.card := Nat.mul_comm _ _
  exact le_trans h1 (Nat.mul_le_mul_right _ (by omega))

/-- Correctness of `edmondsKarpDenseM` without external adjacency obligations. -/
theorem edmondsKarpDenseM_correct {n : ℕ} {N : Network (Fin n)} (hst : N.s ≠ N.t) :
    let out := (edmondsKarpDenseM N).ret
    out.flow.IsMaxFlow ∧
      N.IsMinCut out.cut ∧
      out.flow.value = (N.cutCapacity out.cut : ℤ) ∧
      out.cut = out.flow.reachableCut ∧
      out.augmentations ≤ N.symArcs.card * (n / 2) ∧
      out.augmentations ≤ n * N.posArcs.card :=
  edmondsKarpM_correct (adjValid_defaultAdj N) hst

/-- Polynomial `O(n^5)` `TimeM` step bound for `edmondsKarpDenseM` under the same unit-cost
`Vector`, `Finset.insert`, `ℕ`, and `N.cap` primitive model as `edmondsKarpM_time_le`. -/
theorem edmondsKarpDenseM_time_le {n : ℕ} (N : Network (Fin n)) :
    (edmondsKarpDenseM N).time ≤ (n * n * (n / 2) + 2) * (n * n + 5 * n) := by
  have h1 := edmondsKarpM_time_le (adjValid_defaultAdj N)
  rw [adjSteps_defaultAdj] at h1
  have hsq : N.symArcs.card ≤ n * n := by
    simpa [Fintype.card_fin] using N.card_symArcs_le_card_sq
  have hmul : N.symArcs.card * (n / 2) ≤ n * n * (n / 2) := Nat.mul_le_mul_right _ hsq
  exact le_trans h1 (Nat.mul_le_mul_right _ (by omega))

end ExecutableFin

end Cslib.Algorithms.Lean.MaxFlow
