/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Sparse.Conjunctive
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Pruning a level along a Hausdorff decomposition

Arvind, Köbler and Mundhenk's procedure `PRUNE` [Arvind, Köbler and Mundhenk, Theorem 3.4]
[ArvindKoblerMundhenk1992], on an abstract list of nodes. Let `N` be a level whose members of a
set `L` are exactly its first `h + 1` nodes, and let `L` have a Hausdorff decomposition on `N`:
there are sets `C 0 ⊇ C 1 ⊇ ⋯` such that a node is in `L` exactly when it is in `C (2 d)` but not
in `C (2 d + 1)` for some `d < D`. If each `C j` with `j < 2 D` reduces conjunctively to a set with
at most `s` members on `N`, the queries `Q j` of a node all lying in it exactly when the node is
in `C j`, then `PRUNE` keeps the node at position `h` (`Cslib.Complexity.BTT.getElem_mem_prune`)
and keeps at most `2 D (s + 2) ^ (2 D)` nodes (`Cslib.Complexity.BTT.length_prune_le`).

`PRUNE` works with positions in `N`. At depth `d` it runs `SEARCH-RIGHT` with the queries
`Q (2 d)` from each start position (`Cslib.Complexity.BTT.searchRightFrom`), and `SEARCH-LEFT`
with the queries `Q (2 d + 1)` from each position that `SEARCH-RIGHT` keeps
(`Cslib.Complexity.BTT.searchLeftFrom`). `SEARCH-LEFT` is `SEARCH-RIGHT` on the positions up to
its start in decreasing order. The positions kept by `SEARCH-LEFT` are the start positions of the
next depth.

Why the node at position `h` is kept, following the source. At depth `d`, some start position
`l ≤ h` begins a run of nodes in `C (2 d)` reaching `h`. Let `r ≥ h` end the longest such run.
`SEARCH-RIGHT` keeps `r`, since the next node, if any, is outside `C (2 d)`
(`Cslib.Complexity.BTT.mem_searchRightFrom`). The nodes after `h` up to `r` are in `C (2 d)` but
not in `L`, so they are in `C (2 d + 1)`. Let `m` start the longest run of nodes in `C (2 d + 1)`
ending at `r`; `SEARCH-LEFT` keeps `m` (`Cslib.Complexity.BTT.mem_searchLeftFrom`). If the node at
`h` is outside `C (2 d + 1)`, then `m = h + 1`, and `h` is collected as `r` when `r = h` or as
`m - 1` otherwise. If it is in `C (2 d + 1)`, then `m ≤ h`, and the nodes from `m` to `h` are in
`L` and in `C (2 d + 1)`, hence in `C (2 d + 2)`: the argument repeats at depth `d + 1` from `m`.
At depth `D` that would put the node at `h` in every `C j`, so outside `L`; the recursion collects
`h` before.

The source's `SEARCH-RIGHT` and `SEARCH-LEFT` stop once more than `s` distinct queries have been
collected, and its `PRUNE` returns the nodes before those that `SEARCH-LEFT` keeps. Here both scans
are `Cslib.Complexity.Conjunctive.searchRight`, which reads the whole list and does not test its
first node against the empty set of queries, so `SEARCH-LEFT` from `r` never keeps `r + 1`. The
positions kept by `SEARCH-RIGHT` are collected as well, which covers the case `r = h`, where the
source's `SEARCH-LEFT` keeps `r + 1`, possibly past the end of the level.

## Main definitions

* `Cslib.Complexity.BTT.queriesAt`: the queries of the node at a position.
* `Cslib.Complexity.BTT.searchRightFrom`, `Cslib.Complexity.BTT.searchLeftFrom`: `SEARCH-RIGHT`
  and `SEARCH-LEFT` on positions.
* `Cslib.Complexity.BTT.prunePositions`, `Cslib.Complexity.BTT.prune`: `PRUNE`, on positions and
  on nodes.

## Main results

* `Cslib.Complexity.BTT.mem_searchRightFrom`, `Cslib.Complexity.BTT.mem_searchLeftFrom`: the
  searches keep the ends of runs of nodes of a set with conjunctive queries (the source's Claims 1
  and 2).
* `Cslib.Complexity.BTT.getElem_mem_prune`: `PRUNE` keeps the last node of the level in `L` (the
  source's Claim 3).
* `Cslib.Complexity.BTT.prune_sublist`, `Cslib.Complexity.BTT.length_prune_le`: `PRUNE` keeps at
  most `2 D (s + 2) ^ (2 D)` nodes of its level, in order.
* `Cslib.Complexity.BTT.computableInPolyTime_prune`: `PRUNE` with a fixed number of depths is
  polynomial-time.

## References

* [V. Arvind, J. Köbler, M. Mundhenk, *On Bounded Truth-Table, Conjunctive, and Randomized
  Reductions to Sparse Sets*][ArvindKoblerMundhenk1992]
-/

@[expose] public section

namespace Cslib.Complexity.BTT

open Conjunctive

/-! ### `SEARCH-RIGHT` and `SEARCH-LEFT` on positions -/

section Search

variable {α κ : Type*} [DecidableEq κ]

/-- The queries `Q` of the node at position `i` of `N`; there are none past the end of `N`. -/
def queriesAt (Q : α → List κ) (N : List α) (i : ℕ) : List κ :=
  (N.map Q).getD i []

/-- **`SEARCH-RIGHT` from the position `l`**, with the queries `Q` and the bound `s`: the
positions of `N` kept by `Cslib.Complexity.Conjunctive.searchRight` on the positions from `l` on,
in increasing order. -/
def searchRightFrom (Q : α → List κ) (s : ℕ) (N : List α) (l : ℕ) : List ℕ :=
  searchRight (queriesAt Q N) s ((List.range N.length).drop l)

/-- **`SEARCH-LEFT` from the position `r`**, with the queries `Q` and the bound `s`: the positions
kept by `Cslib.Complexity.Conjunctive.searchRight` on the positions up to `r`, in decreasing
order. -/
def searchLeftFrom (Q : α → List κ) (s : ℕ) (N : List α) (r : ℕ) : List ℕ :=
  searchRight (queriesAt Q N) s (List.range (r + 1)).reverse

variable {Q : α → List κ} {s : ℕ} {N : List α}

/-- Splitting the positions from `a` below `c` at `b`. -/
private theorem range'_split {a b c : ℕ} (hab : a ≤ b) (hbc : b < c) :
    List.range' a (c - a) = List.range' a (b - a) ++ b :: List.range' (b + 1) (c - (b + 1)) := by
  rw [← List.range'_succ]
  have happ := List.range'_append_1 (s := a) (m := b - a) (n := c - (b + 1) + 1)
  rw [show a + (b - a) = b by omega] at happ
  rw [happ]
  congr 1
  omega

omit [DecidableEq κ] in
theorem queriesAt_of_lt {i : ℕ} (hi : i < N.length) : queriesAt Q N i = Q N[i] := by
  simp [queriesAt, List.getElem?_eq_getElem hi]

theorem length_searchRightFrom_le (l : ℕ) : (searchRightFrom Q s N l).length ≤ s + 2 :=
  length_searchRight_le _

theorem length_searchLeftFrom_le (r : ℕ) : (searchLeftFrom Q s N r).length ≤ s + 2 :=
  length_searchRight_le _

variable {C : α → Prop} {K : Set κ}

/-- **`SEARCH-RIGHT` keeps the end of a run** (the source's Claim 1). If the nodes at the positions
from `l` to `r` are in a set `C` whose members are the nodes with all their queries in `K`, which
has at most `s` members, and the node after `r`, if any, is not in `C`, then `SEARCH-RIGHT` from
`l` keeps `r`. -/
theorem mem_searchRightFrom (hC : ∀ y ∈ N, C y ↔ ∀ w ∈ Q y, w ∈ K)
    (hc : ∀ T : Finset κ, (∀ w ∈ T, w ∈ K) → T.card ≤ s) {l r : ℕ} (hlr : l ≤ r)
    (hr : r < N.length) (hrun : ∀ i (hi : i < N.length), l ≤ i → i ≤ r → C N[i])
    (hnext : ∀ hr' : r + 1 < N.length, ¬ C N[r + 1]) :
    r ∈ searchRightFrom Q s N l := by
  have hsplit : (List.range N.length).drop l =
      List.range' l (r - l) ++ r :: List.range' (r + 1) (N.length - (r + 1)) := by
    rw [List.range_eq_range', List.drop_range', Nat.zero_add, Nat.mul_one]
    exact range'_split hlr hr
  rw [searchRightFrom, hsplit]
  refine mem_searchRight (K := K) hc (fun x hx w hw => ?_) fun z hz => ?_
  · have hx' : l ≤ x ∧ x ≤ r := by
      simp only [List.mem_append, List.mem_range'_1, List.mem_singleton] at hx
      omega
    have hxN : x < N.length := by omega
    rw [queriesAt_of_lt hxN] at hw
    exact (hC _ (List.getElem_mem hxN)).1 (hrun x hxN hx'.1 hx'.2) w hw
  · obtain ⟨rfl, hz'⟩ : z = r + 1 ∧ r + 1 < N.length := by
      rcases hlen : N.length - (r + 1) with _ | k
      · simp [hlen] at hz
      · rw [hlen, List.range'_succ, List.head?_cons, Option.mem_some_iff] at hz
        omega
    have hout := hnext hz'
    rw [hC _ (List.getElem_mem hz')] at hout
    push Not at hout
    rwa [queriesAt_of_lt hz']

/-- **`SEARCH-LEFT` keeps the start of a run** (the source's Claim 2). If the nodes at the
positions from `m` to `r` are in a set `C` whose members are the nodes with all their queries in
`K`, which has at most `s` members, and the node before `m`, if any, is not in `C`, then
`SEARCH-LEFT` from `r` keeps `m`. -/
theorem mem_searchLeftFrom (hC : ∀ y ∈ N, C y ↔ ∀ w ∈ Q y, w ∈ K)
    (hc : ∀ T : Finset κ, (∀ w ∈ T, w ∈ K) → T.card ≤ s) {m r : ℕ} (hmr : m ≤ r)
    (hr : r < N.length) (hrun : ∀ i (hi : i < N.length), m ≤ i → i ≤ r → C N[i])
    (hprev : ∀ hm : 0 < m, ¬ C N[m - 1]) :
    m ∈ searchLeftFrom Q s N r := by
  have hsplit : (List.range (r + 1)).reverse =
      (List.range' (m + 1) (r - m)).reverse ++ m :: (List.range m).reverse := by
    have hrange : List.range (r + 1) = List.range m ++ m :: List.range' (m + 1) (r - m) := by
      rw [List.range_eq_range', List.range_eq_range']
      simpa using range'_split (Nat.zero_le m) (show m < r + 1 by omega)
    rw [hrange, List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append]
  rw [searchLeftFrom, hsplit]
  refine mem_searchRight (K := K) hc (fun x hx w hw => ?_) fun z hz => ?_
  · have hx' : m ≤ x ∧ x ≤ r := by
      simp only [List.mem_append, List.mem_reverse, List.mem_range'_1, List.mem_singleton] at hx
      omega
    have hxN : x < N.length := by omega
    rw [queriesAt_of_lt hxN] at hw
    exact (hC _ (List.getElem_mem hxN)).1 (hrun x hxN hx'.1 hx'.2) w hw
  · obtain ⟨hm, rfl⟩ : 0 < m ∧ z = m - 1 := by
      rcases m with _ | m
      · simp at hz
      · rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
          List.head?_cons, Option.mem_some_iff] at hz
        omega
    have hzN : m - 1 < N.length := by omega
    have hout := hprev hm
    rw [hC _ (List.getElem_mem hzN)] at hout
    push Not at hout
    rwa [queriesAt_of_lt hzN]

end Search

/-! ### `PRUNE` -/

section Prune

variable {α κ : Type*} [DecidableEq κ]

/-- **`PRUNE` on positions**: the positions of `N` collected at the depths `d, …, d + n - 1` from
the start positions `starts`, with the queries `Q` and the bound `s`. At depth `d`, `SEARCH-RIGHT`
with the queries `Q (2 d)` runs from every start position, and `SEARCH-LEFT` with the queries
`Q (2 d + 1)` from every position it keeps. The positions kept by `SEARCH-RIGHT`, the positions
before those kept by `SEARCH-LEFT`, and the positions collected from the latter at the next depths
are collected. -/
def prunePositions (Q : ℕ → α → List κ) (s : ℕ) (N : List α) : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, _ => []
  | n + 1, d, starts =>
    let right := starts.flatMap (searchRightFrom (Q (2 * d)) s N)
    let left := right.flatMap (searchLeftFrom (Q (2 * d + 1)) s N)
    right ++ left.map (· - 1) ++ prunePositions Q s N n (d + 1) left

/-- **`PRUNE`** with the queries `Q`, the bound `s` and `D` depths: the nodes of `N` at the
positions collected from the first position, in their order in `N`. -/
def prune (Q : ℕ → α → List κ) (s D : ℕ) (N : List α) : List α :=
  ((N.zip (List.range N.length)).filter fun p => decide (p.2 ∈ prunePositions Q s N D 0 [0])).map
    Prod.fst

variable {Q : ℕ → α → List κ} {s D : ℕ} {N : List α}

theorem prune_sublist : (prune Q s D N).Sublist N := by
  have h := (List.filter_sublist (l := N.zip (List.range N.length))
    (p := fun p => decide (p.2 ∈ prunePositions Q s N D 0 [0]))).map Prod.fst
  rwa [List.map_fst_zip (by simp)] at h

/-- A node at a collected position is kept. -/
theorem getElem_mem_prune_of_mem {h : ℕ} (hh : h < N.length)
    (hmem : h ∈ prunePositions Q s N D 0 [0]) : N[h] ∈ prune Q s D N := by
  refine List.mem_map.2 ⟨(N[h], h), List.mem_filter.2 ⟨?_, by simpa using hmem⟩, rfl⟩
  rw [List.mem_iff_getElem]
  exact ⟨h, by simpa using hh, by simp⟩

private theorem length_flatMap_le {ι β : Type*} (l : List ι) (f : ι → List β) {c : ℕ}
    (hf : ∀ x, (f x).length ≤ c) : (l.flatMap f).length ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := hf x
    omega

/-- At most `2 n (s + 2) ^ (2 n)` positions are collected from each start position. -/
theorem length_prunePositions_le (n d : ℕ) (starts : List ℕ) :
    (prunePositions Q s N n d starts).length ≤ 2 * n * starts.length * (s + 2) ^ (2 * n) := by
  induction n generalizing d starts with
  | zero => simp [prunePositions]
  | succ n ih =>
    set right := starts.flatMap (searchRightFrom (Q (2 * d)) s N)
    set left := right.flatMap (searchLeftFrom (Q (2 * d + 1)) s N)
    have hright : right.length ≤ starts.length * (s + 2) :=
      length_flatMap_le _ _ fun _ => length_searchRightFrom_le _
    have hleft : left.length ≤ starts.length * (s + 2) ^ 2 :=
      (length_flatMap_le _ _ fun _ => length_searchLeftFrom_le _).trans
        ((Nat.mul_le_mul_right _ hright).trans_eq (by ring))
    have hrec := ih (d + 1) left
    simp only [prunePositions, List.length_append, List.length_map]
    set P := s + 2
    set X := P ^ (2 * n)
    set Y := starts.length * P ^ 2 * X
    have hX : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
    have h1 : starts.length * P ≤ Y := by
      have : P ≤ P ^ 2 * X := (Nat.le_self_pow (by omega) P).trans (Nat.le_mul_of_pos_right _ hX)
      calc starts.length * P ≤ starts.length * (P ^ 2 * X) := Nat.mul_le_mul_left _ this
        _ = Y := by ring
    have h2 : starts.length * P ^ 2 ≤ Y := Nat.le_mul_of_pos_right _ hX
    have h3 : 2 * n * left.length * X ≤ 2 * n * Y := by
      calc 2 * n * left.length * X ≤ 2 * n * (starts.length * P ^ 2) * X :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hleft)
        _ = 2 * n * Y := by ring
    have hgoal : 2 * (n + 1) * starts.length * P ^ (2 * (n + 1)) = 2 * (n + 1) * Y := by
      rw [show 2 * (n + 1) = 2 + 2 * n by ring, pow_add]
      ring
    rw [hgoal]
    have := hright.trans h1
    have := hleft.trans h2
    have := hrec.trans h3
    nlinarith

/-- **`PRUNE` keeps at most `2 D (s + 2) ^ (2 D)` nodes.** -/
theorem length_prune_le : (prune Q s D N).length ≤ 2 * D * (s + 2) ^ (2 * D) := by
  set I := prunePositions Q s N D 0 [0]
  have hnodup : (((N.zip (List.range N.length)).filter fun p => decide (p.2 ∈ I)).map
      Prod.snd).Nodup := by
    refine List.Nodup.sublist (List.filter_sublist.map _) ?_
    rw [List.map_snd_zip (by simp)]
    exact List.nodup_range
  have hsub : (((N.zip (List.range N.length)).filter fun p => decide (p.2 ∈ I)).map
      Prod.snd) ⊆ I := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
    simpa using (List.mem_filter.1 hp).2
  have := (hnodup.length_le_of_subset hsub).trans (length_prunePositions_le D 0 [0])
  rw [prune, List.length_map]
  simpa using this

variable {C : ℕ → α → Prop} {K : ℕ → Set κ} {h : ℕ}

/-- The end of the longest run of positions satisfying `P` from `h`, below `n`. -/
private theorem exists_run_end {P : ℕ → Prop} {h n : ℕ} (hP : P h) (hn : h < n) :
    ∃ r, h ≤ r ∧ r < n ∧ (∀ i, h ≤ i → i ≤ r → P i) ∧ (r + 1 < n → ¬ P (r + 1)) := by
  classical
  have hex : ∃ j, h ≤ j ∧ (n ≤ j + 1 ∨ ¬ P (j + 1)) := ⟨n, by omega, .inl (by omega)⟩
  obtain ⟨hhr, hstop⟩ := Nat.find_spec hex
  have hmin : ∀ j, h ≤ j → j < Nat.find hex → j + 1 < n ∧ P (j + 1) := fun j hj hjr => by
    have := Nat.find_min hex hjr
    push Not at this
    exact this hj
  refine ⟨Nat.find hex, hhr, ?_, fun i hi hir => ?_, fun hr1 => ?_⟩
  · by_contra hrn
    have := hmin (n - 1) (by omega) (by omega)
    omega
  · induction i, hi using Nat.le_induction with
    | base => exact hP
    | succ i hhi _ => exact (hmin i hhi (by omega)).2
  · rcases hstop with h1 | h1
    · omega
    · exact h1

/-- The start of the longest run of positions satisfying `P` up to `r`. -/
private theorem exists_run_start {P : ℕ → Prop} {a r : ℕ} (ha : ∀ i, a ≤ i → i ≤ r → P i) :
    ∃ m ≤ a, (∀ i, m ≤ i → i ≤ r → P i) ∧ (0 < m → ¬ P (m - 1)) := by
  classical
  have hex : ∃ m, ∀ i, m ≤ i → i ≤ r → P i := ⟨a, ha⟩
  refine ⟨Nat.find hex, Nat.find_min' hex ha, Nat.find_spec hex, fun hm hP => ?_⟩
  refine Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega) fun i hi hir => ?_
  rcases Nat.eq_or_lt_of_le hi with heq | hlt
  · rwa [← heq]
  · exact Nat.find_spec hex i (by omega) hir

/-- **`PRUNE` collects the last position of the level in `L`** (the source's Claim 3), from any
start position `l ≤ h` at depth `d` whose run of nodes in `C (2 d)` reaches `h`. -/
private theorem mem_prunePositions (hh : h < N.length)
    (hnest : ∀ j, ∀ y ∈ N, C (j + 1) y → C j y)
    (hleft : ∀ i (hi : i < N.length), i ≤ h ↔ ∃ d < D, C (2 * d) N[i] ∧ ¬ C (2 * d + 1) N[i])
    (hQ : ∀ j < 2 * D, ∀ y ∈ N, C j y ↔ ∀ w ∈ Q j y, w ∈ K j)
    (hc : ∀ j < 2 * D, ∀ T : Finset κ, (∀ w ∈ T, w ∈ K j) → T.card ≤ s) :
    ∀ n d (starts : List ℕ) (l : ℕ), d + n = D → l ∈ starts → l ≤ h →
      (∀ i (hi : i < N.length), l ≤ i → i ≤ h → C (2 * d) N[i]) →
      h ∈ prunePositions Q s N n d starts := by
  have hmono : ∀ y ∈ N, ∀ j j', j ≤ j' → C j' y → C j y := fun y hy _ _ hjj' =>
    antitone_nat_of_succ_le (f := fun j => C j y) (fun j => hnest j y hy) hjj'
  intro n
  induction n with
  | zero =>
    intro d starts l hd _ hlh hrun
    obtain ⟨d', hd', -, hout⟩ := (hleft h hh).1 le_rfl
    exact absurd (hmono _ (List.getElem_mem hh) _ _ (by omega) (hrun h hh hlh le_rfl)) hout
  | succ n ih =>
    intro d starts l hd hl hlh hrun
    have hdD : d < D := by omega
    /- The longest run of nodes in `C (2 d)` from `l` ends at some `r ≥ h`. -/
    obtain ⟨r, hhr, hrN, hrun', hnext⟩ := exists_run_end
      (P := fun i => ∀ hi : i < N.length, C (2 * d) N[i]) (fun hi => hrun h hi hlh le_rfl) hh
    have hrunr : ∀ i (hi : i < N.length), l ≤ i → i ≤ r → C (2 * d) N[i] := by
      intro i hi hli hir
      rcases le_or_gt i h with hih | hhi
      · exact hrun i hi hli hih
      · exact hrun' i hhi.le hir hi
    have hr : r ∈ starts.flatMap (searchRightFrom (Q (2 * d)) s N) :=
      List.mem_flatMap.2 ⟨l, hl, mem_searchRightFrom (hQ _ (by omega)) (hc _ (by omega))
        (hlh.trans hhr) hrN hrunr fun hr' hC => hnext hr' fun _ => hC⟩
    /- The nodes after `h` up to `r` are not in `L`, so they are in `C (2 d + 1)`. -/
    have hodd : ∀ i (hi : i < N.length), h < i → i ≤ r → C (2 * d + 1) N[i] := by
      intro i hi hhi hir
      by_contra hout
      exact absurd ((hleft i hi).2 ⟨d, hdD, hrunr i hi (by omega) hir, hout⟩) (by omega)
    obtain ⟨m, hmh, hrunm, hprev⟩ := exists_run_start
      (P := fun i => ∀ hi : i < N.length, C (2 * d + 1) N[i]) (a := h + 1) (r := r)
      fun i hhi hir hi => hodd i hi (by omega) hir
    have hmem_left : m ≤ r → m ∈ (starts.flatMap (searchRightFrom (Q (2 * d)) s N)).flatMap
        (searchLeftFrom (Q (2 * d + 1)) s N) := fun hmr =>
      List.mem_flatMap.2 ⟨r, hr, mem_searchLeftFrom (hQ _ (by omega)) (hc _ (by omega)) hmr hrN
        (fun i hi hmi hir => hrunm i hmi hir hi)
        fun hm hC => hprev hm fun _ => hC⟩
    simp only [prunePositions, List.mem_append, List.mem_map]
    by_cases hCh : C (2 * d + 1) N[h]
    · /- The run of nodes in `C (2 d + 1)` reaches back to `m ≤ h`; from `m` to `h` the nodes are
      in `L`, so in `C (2 d + 2)`. -/
      have hmh' : m ≤ h := by
        by_contra hmh'
        exact hprev (by omega) (by simpa [show m - 1 = h by omega] using fun _ : h < N.length =>
          hCh)
      refine .inr (ih (d + 1) _ m (by omega) (hmem_left (hmh'.trans hhr)) hmh'
        fun i hi hmi hih => ?_)
      obtain ⟨d', hd', hin, hout⟩ := (hleft i hi).1 hih
      have hodd' := hrunm i hmi (hih.trans hhr) hi
      rcases le_or_gt d' d with hd'd | hdd'
      · exact absurd (hmono _ (List.getElem_mem hi) _ _ (by omega) hodd') hout
      · exact hmono _ (List.getElem_mem hi) _ _ (by omega) hin
    · /- The node at `h` is not in `C (2 d + 1)`, so the run starts at `m = h + 1`. -/
      have hm : m = h + 1 := by
        refine le_antisymm hmh (Nat.succ_le_of_lt (lt_of_not_ge fun hmh' => hCh ?_))
        exact hrunm h hmh' hhr hh
      rcases Nat.eq_or_lt_of_le hhr with rfl | hhr'
      · exact .inl (.inl hr)
      · exact .inl (.inr ⟨m, hmem_left (by omega), by omega⟩)

/-- **`PRUNE` keeps the last node of the level in `L`** (the source's Claim 3). Let the sets
`C j` decrease along `N`, and let `L` be `⋃ d < D, C (2 d) \ C (2 d + 1)` on `N`, whose members in
`N` are exactly the nodes at positions `i ≤ h`. If, for each `j < 2 D`, the nodes of `N` in `C j`
are those with all their queries `Q j` in a set `K j` with at most `s` members, then `PRUNE` keeps
the node at position `h`. -/
theorem getElem_mem_prune (hh : h < N.length)
    (hnest : ∀ j, ∀ y ∈ N, C (j + 1) y → C j y)
    (hleft : ∀ i (hi : i < N.length), i ≤ h ↔ ∃ d < D, C (2 * d) N[i] ∧ ¬ C (2 * d + 1) N[i])
    (hQ : ∀ j < 2 * D, ∀ y ∈ N, C j y ↔ ∀ w ∈ Q j y, w ∈ K j)
    (hc : ∀ j < 2 * D, ∀ T : Finset κ, (∀ w ∈ T, w ∈ K j) → T.card ≤ s) :
    N[h] ∈ prune Q s D N := by
  refine getElem_mem_prune_of_mem hh
    (mem_prunePositions hh hnest hleft hQ hc D 0 [0] 0 (by omega) (by simp) (by omega) ?_)
  intro i hi _ hih
  obtain ⟨d, -, hin, -⟩ := (hleft i hi).1 hih
  exact antitone_nat_of_succ_le (f := fun j => C j N[i])
    (fun j => hnest j _ (List.getElem_mem hi)) (Nat.zero_le _) (by simpa using hin)

end Prune

/-! ### Polynomial time -/

open Turing.MultiTapeTM ComputableInPolyTime

section PolyTime

variable {γ α κ : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool} {encK : κ ↪ List Bool}
  [DecidableEq κ]

omit [DecidableEq κ] in
/-- The queries at a position are polynomial-time. -/
theorem computableInPolyTime_queriesAt {Q : γ → α → List κ} {N : γ → List α}
    (hQ : ComputableInPolyTime (fun p : γ × α => Q p.1 p.2) (encPair encIn encA) (encList encK))
    (hN : ComputableInPolyTime N encIn (encList encA)) :
    ComputableInPolyTime (fun p : γ × ℕ => queriesAt (Q p.1) (N p.1) p.2)
      (encPair encIn encUnary) (encList encK) := by
  have hQ' : ComputableInPolyTime (fun p : (γ × ℕ) × α => Q p.1.1 p.2)
      (encPair (encPair encIn encUnary) encA) (encList encK) :=
    hQ.comp (((fst encIn encUnary).comp (fst _ encA)).prod (snd _ encA))
  unfold queriesAt
  fun_prop

/-- `SEARCH-RIGHT` from a computed position is polynomial-time. -/
theorem computableInPolyTime_searchRightFrom {Q : γ → α → List κ} {s : γ → ℕ} {N : γ → List α}
    {l : γ → ℕ}
    (hQ : ComputableInPolyTime (fun p : γ × α => Q p.1 p.2) (encPair encIn encA) (encList encK))
    (hs : ComputableInPolyTime s encIn encUnary) (hN : ComputableInPolyTime N encIn (encList encA))
    (hl : ComputableInPolyTime l encIn encUnary) :
    ComputableInPolyTime (fun x => searchRightFrom (Q x) (s x) (N x) (l x)) encIn
      (encList encUnary) :=
  computableInPolyTime_searchRight (encA := encUnary)
    (Q := fun x => queriesAt (Q x) (N x)) (computableInPolyTime_queriesAt hQ hN) hs (by fun_prop)

/-- `SEARCH-LEFT` from a computed position is polynomial-time. -/
theorem computableInPolyTime_searchLeftFrom {Q : γ → α → List κ} {s : γ → ℕ} {N : γ → List α}
    {r : γ → ℕ}
    (hQ : ComputableInPolyTime (fun p : γ × α => Q p.1 p.2) (encPair encIn encA) (encList encK))
    (hs : ComputableInPolyTime s encIn encUnary) (hN : ComputableInPolyTime N encIn (encList encA))
    (hr : ComputableInPolyTime r encIn encUnary) :
    ComputableInPolyTime (fun x => searchLeftFrom (Q x) (s x) (N x) (r x)) encIn
      (encList encUnary) :=
  computableInPolyTime_searchRight (encA := encUnary)
    (Q := fun x => queriesAt (Q x) (N x)) (computableInPolyTime_queriesAt hQ hN) hs (by fun_prop)

/-- `PRUNE` on positions with a fixed number `n` of depths from a fixed depth `d` is
polynomial-time, uniformly in the start positions. -/
theorem computableInPolyTime_prunePositions {Q : γ → ℕ → α → List κ} {s : γ → ℕ}
    {N : γ → List α}
    (hQ : ∀ j, ComputableInPolyTime (fun p : γ × α => Q p.1 j p.2) (encPair encIn encA)
      (encList encK))
    (hs : ComputableInPolyTime s encIn encUnary) (hN : ComputableInPolyTime N encIn (encList encA))
    (n d : ℕ) :
    ComputableInPolyTime (fun p : γ × List ℕ => prunePositions (Q p.1) (s p.1) (N p.1) n d p.2)
      (encPair encIn (encList encUnary)) (encList encUnary) := by
  induction n generalizing d with
  | zero => exact const _
  | succ n ih =>
    have hQ' (j : ℕ) : ComputableInPolyTime (fun p : (γ × List ℕ) × α => Q p.1.1 j p.2)
        (encPair (encPair encIn (encList encUnary)) encA) (encList encK) :=
      (hQ j).comp (((fst encIn (encList encUnary)).comp (fst _ encA)).prod (snd _ encA))
    have hs' : ComputableInPolyTime (fun p : γ × List ℕ => s p.1)
        (encPair encIn (encList encUnary)) encUnary := hs.comp (fst _ _)
    have hN' : ComputableInPolyTime (fun p : γ × List ℕ => N p.1)
        (encPair encIn (encList encUnary)) (encList encA) := hN.comp (fst _ _)
    have hright : ComputableInPolyTime
        (fun p : γ × List ℕ => p.2.flatMap (searchRightFrom (Q p.1 (2 * d)) (s p.1) (N p.1)))
        (encPair encIn (encList encUnary)) (encList encUnary) :=
      flatMapWithInput (snd _ _) (computableInPolyTime_searchRightFrom
        (encIn := encPair (encPair encIn (encList encUnary)) encUnary)
        (Q := fun q => Q q.1.1 (2 * d)) (s := fun q => s q.1.1) (N := fun q => N q.1.1)
        (l := fun q => q.2)
        ((hQ (2 * d)).comp ((((fst _ _).comp (fst _ _)).comp (fst _ encA)).prod (snd _ encA)))
        (hs.comp ((fst _ _).comp (fst _ _))) (hN.comp ((fst _ _).comp (fst _ _))) (snd _ _))
    have hleft : ComputableInPolyTime
        (fun p : γ × List ℕ => (p.2.flatMap (searchRightFrom (Q p.1 (2 * d)) (s p.1)
          (N p.1))).flatMap (searchLeftFrom (Q p.1 (2 * d + 1)) (s p.1) (N p.1)))
        (encPair encIn (encList encUnary)) (encList encUnary) :=
      flatMapWithInput hright (computableInPolyTime_searchLeftFrom
        (encIn := encPair (encPair encIn (encList encUnary)) encUnary)
        (Q := fun q => Q q.1.1 (2 * d + 1)) (s := fun q => s q.1.1) (N := fun q => N q.1.1)
        (r := fun q => q.2)
        ((hQ (2 * d + 1)).comp ((((fst _ _).comp (fst _ _)).comp (fst _ encA)).prod
          (snd _ encA)))
        (hs.comp ((fst _ _).comp (fst _ _))) (hN.comp ((fst _ _).comp (fst _ _))) (snd _ _))
    have hrec := (ih (d + 1)).comp ((fst encIn (encList encUnary)).prod hleft)
    simp only [prunePositions]
    fun_prop

/-- **`PRUNE` with a fixed number `D` of depths is polynomial-time**, for polynomial-time
queries, bound and level. -/
theorem computableInPolyTime_prune {Q : γ → ℕ → α → List κ} {s : γ → ℕ} {N : γ → List α}
    (D : ℕ)
    (hQ : ∀ j, ComputableInPolyTime (fun p : γ × α => Q p.1 j p.2) (encPair encIn encA)
      (encList encK))
    (hs : ComputableInPolyTime s encIn encUnary)
    (hN : ComputableInPolyTime N encIn (encList encA)) :
    ComputableInPolyTime (fun x => prune (Q x) (s x) D (N x)) encIn (encList encA) := by
  have hpos : ComputableInPolyTime (fun x => prunePositions (Q x) (s x) (N x) D 0 [0]) encIn
      (encList encUnary) :=
    (computableInPolyTime_prunePositions hQ hs hN D 0).comp (id'.prod (const _))
  have hzip : ComputableInPolyTime (fun x => (N x).zip (List.range (N x).length)) encIn
      (encList (encPair encA encUnary)) :=
    (zip encA encUnary).comp (hN.prod (range.comp ((length_list encA).comp hN)))
  have htest : ComputableInPolyTime
      (fun q : γ × (α × ℕ) => decide (q.2.2 ∈ prunePositions (Q q.1) (s q.1) (N q.1) D 0 [0]))
      (encPair encIn (encPair encA encUnary)) encBool :=
    decide_mem (hpos.comp (fst _ _)) ((snd encA encUnary).comp (snd _ _))
  have hfilter := filterWithInput (list := fun x => (N x).zip (List.range (N x).length))
    (test := fun x p => decide (p.2 ∈ prunePositions (Q x) (s x) (N x) D 0 [0])) hzip htest
  unfold prune
  fun_prop

end PolyTime

end Cslib.Complexity.BTT
