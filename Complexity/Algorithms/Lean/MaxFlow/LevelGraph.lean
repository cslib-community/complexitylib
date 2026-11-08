/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.MaxFlow.EdmondsKarp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Level Networks, Blocking Flows, and the Dinitz Phase Lemma

Formalizes the phase analysis of **Dinitz's blocking-flow algorithm** ([Dinic1970];
[Schrijver2003], Section 10.6; see [Dinitz2006] for the history of the original version):
augmenting an integral flow by a blocking flow of the level network of its residual network
strictly increases the residual distance from `N.s` to `N.t`, so at most `|V| - 1` such phases
can occur.

## Mathematical overview

1. **Level networks (`Flow.levelNet`):** for vertex labels `d : V → ℕ`, the level network of `f`
   keeps the residual arcs `u → v` with `d v = d u + 1`, with residual capacity as capacity. For
   `d = f.resDist` (shortest residual distances from `N.s`, `Flow.resDist`) these are exactly the
   residual arcs from one breadth-first layer to the next. A level network has no antiparallel
   arcs (`Flow.levelNet_cap_eq_zero_of_pos`).
2. **Augmenting by a subnetwork flow (`Flow.augmentBy`, `Flow.augmentLevel`):** a flow `g` of a
   network with the same terminals whose capacities are bounded by the residual capacities of `f`
   is added to `f` by first cancelling reverse flow. The value adds (`Flow.value_augmentBy`) and
   the residual capacities change by `- g u v + g v u` (`Flow.resCap_augmentBy`); compare
   [CLRS2009], Lemma 26.1, stated there for networks without antiparallel arcs.
3. **Blocking flows (`Flow.IsBlocking`):** every simple `s`-`t` path along arcs of positive
   capacity contains an arc saturated by the flow.
4. **Phase lemma:** augmenting by any flow of the level network of `f.resDist` never decreases a
   residual distance from `N.s` (`Flow.resDist_le_resDist_augmentLevel`), and augmenting by a
   blocking flow strictly increases the residual distance of a reachable `N.t`
   (`Flow.resDist_lt_resDist_augmentLevel`): a shortest residual walk of the new flow that is no
   longer than before must run along unsaturated level arcs, contradicting blocking.
5. **Phase bound (`Network.IsDinitzRun.length_le`):** the distance of `N.t` is at least `1` before
   the first phase and at most `|V|` (the unreachable value of `Flow.resDist`), so every run of
   Dinitz phases (`Network.IsDinitzRun`), from any initial flow, has at most `|V| - 1` phases.
6. **Breadth-first layers (`Flow.resBall`, `Flow.bfsDist`):** computable residual distances,
   proved equal to `Flow.resDist` (`Flow.bfsDist_eq_resDist`).
7. **Deciding blocking (`Flow.slackNet`, `Flow.unsatArcs`):** `g` is blocking exactly when the
   network of unused capacities `L.cap - g` has no augmenting path for its zero flow
   (`Flow.isBlocking_iff_not_exists_slackNet`), which one breadth-first search decides
   (`Flow.isBlocking_iff_bfsDist_slackNet`, `Decidable g.IsBlocking`).

## Main definitions

* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.levelNet`: the level network of a flow.
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.augmentBy`, `Flow.augmentLevel`: augmentation by a
  flow of a residual subnetwork.
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.IsBlocking`: blocking flows.
* `Cslib.Algorithms.Lean.MaxFlow.Network.IsDinitzStep`, `Network.IsDinitzRun`: Dinitz phases and
  runs of phases.
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.resBall`, `Flow.bfsDist`: breadth-first layers.
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.slackNet`, `Flow.unsatArcs`: unused capacities and
  unsaturated arcs of a flow.

## Main results

* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.resDist_le_resDist_augmentLevel`: distance
  monotonicity under level augmentations.
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.resDist_lt_resDist_augmentLevel`: the Dinitz phase
  lemma.
* `Cslib.Algorithms.Lean.MaxFlow.Network.IsDinitzRun.length_le`: at most `|V| - 1` phases.
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.bfsDist_eq_resDist`: breadth-first layers compute
  residual distances.
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.isBlocking_iff_bfsDist_slackNet`: blocking is
  decidable by one breadth-first search.

## References

* [E. A. Dinic, *Algorithm for solution of a problem of maximum flow in networks with power
  estimation*][Dinic1970]
* [Y. Dinitz, *Dinitz' Algorithm: The Original Version and Even's Version*][Dinitz2006]
* [A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*][Schrijver2003]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

namespace Network

variable {V : Type*} [Fintype V] {N : Network V}

namespace Flow

/-! ### Level networks -/

/-- The level network of the residual network of `f` with respect to vertex labels `d`: it keeps
the residual arcs `u → v` with `d v = d u + 1`. With `d = f.resDist` these are the arcs on
shortest residual paths from `N.s`. -/
@[expose] def levelNet (f : N.Flow) (d : V → ℕ) : Network V where
  cap u v := if d v = d u + 1 then f.resCap u v else 0
  s := N.s
  t := N.t

@[simp]
theorem levelNet_s (f : N.Flow) (d : V → ℕ) : (f.levelNet d).s = N.s := rfl

@[simp]
theorem levelNet_t (f : N.Flow) (d : V → ℕ) : (f.levelNet d).t = N.t := rfl

theorem levelNet_cap (f : N.Flow) (d : V → ℕ) (u v : V) :
    (f.levelNet d).cap u v = if d v = d u + 1 then f.resCap u v else 0 := rfl

theorem levelNet_cap_le_resCap (f : N.Flow) (d : V → ℕ) (u v : V) :
    (f.levelNet d).cap u v ≤ f.resCap u v := by
  rw [levelNet_cap]
  split_ifs <;> omega

theorem levelNet_cap_pos_iff (f : N.Flow) (d : V → ℕ) (u v : V) :
    0 < (f.levelNet d).cap u v ↔ d v = d u + 1 ∧ 0 < f.resCap u v := by
  rw [levelNet_cap]
  split_ifs with h <;> simp [h]

theorem levelNet_cap_eq_zero_of_pos (f : N.Flow) (d : V → ℕ) {u v : V}
    (h : 0 < (f.levelNet d).cap u v) : (f.levelNet d).cap v u = 0 := by
  rw [levelNet_cap_pos_iff] at h
  rw [levelNet_cap]
  split_ifs <;> omega

/-! ### Augmenting by a flow of a residual subnetwork -/

/-- Arc flows of `f` augmented by the arc flows `g` of a subnetwork of the residual network: the
net amount `g u v - g v u` (if positive) first cancels reverse flow `f v u`, and the remainder is
added to `f u v`. -/
@[expose] def augmentByFun (f : N.Flow) (g : V → V → ℕ) (u v : V) : ℕ :=
  f u v + ((g u v - g v u) - min (g u v - g v u) (f v u)) - min (g v u - g u v) (f u v)

private theorem augmentByFun_sub (f : N.Flow) {L : Network V} (g : L.Flow)
    (hcap : ∀ u v, L.cap u v ≤ f.resCap u v) (u v : V) :
    (f.augmentByFun g u v : ℤ) - (f.augmentByFun g v u : ℤ) =
      ((f u v : ℤ) - (f v u : ℤ)) + ((g u v : ℤ) - (g v u : ℤ)) := by
  have h₁ := le_trans (g.le_cap u v) (hcap u v)
  have h₂ := le_trans (g.le_cap v u) (hcap v u)
  have hf₁ := f.le_cap u v
  have hf₂ := f.le_cap v u
  unfold augmentByFun resCap at *
  omega

/-- Augment `f` by a flow `g` of a network `L` with the same terminals whose capacities are
bounded by the residual capacities of `f` ([CLRS2009], Lemma 26.1, there for networks without
antiparallel arcs). -/
@[expose] def augmentBy (f : N.Flow) {L : Network V} (g : L.Flow) (hs : L.s = N.s)
    (ht : L.t = N.t) (hcap : ∀ u v, L.cap u v ≤ f.resCap u v) : N.Flow where
  toFun := f.augmentByFun g
  le_cap u v := by
    have h₁ := le_trans (g.le_cap u v) (hcap u v)
    have hf₁ := f.le_cap u v
    unfold augmentByFun
    unfold resCap at h₁
    omega
  conserve v hvs hvt := by
    have hsum : (∑ w : V, ((f.augmentByFun g v w : ℤ) - (f.augmentByFun g w v : ℤ))) = 0 := by
      simp only [f.augmentByFun_sub g hcap v]
      rw [Finset.sum_add_distrib, ← f.netOut_eq_sum_sub v, ← g.netOut_eq_sum_sub v,
        f.netOut_eq_zero hvs hvt, g.netOut_eq_zero (hs ▸ hvs) (ht ▸ hvt), add_zero]
    rw [Finset.sum_sub_distrib] at hsum
    have heq : ((∑ u : V, f.augmentByFun g u v : ℕ) : ℤ) =
        ((∑ w : V, f.augmentByFun g v w : ℕ) : ℤ) := by
      rw [Nat.cast_sum, Nat.cast_sum]
      omega
    exact Int.ofNat.inj heq

theorem augmentBy_apply (f : N.Flow) {L : Network V} (g : L.Flow) (hs : L.s = N.s)
    (ht : L.t = N.t) (hcap : ∀ u v, L.cap u v ≤ f.resCap u v) (u v : V) :
    f.augmentBy g hs ht hcap u v = f.augmentByFun g u v := rfl

/-- Augmenting by `g` adds the value of `g`. -/
theorem value_augmentBy (f : N.Flow) {L : Network V} (g : L.Flow) (hs : L.s = N.s)
    (ht : L.t = N.t) (hcap : ∀ u v, L.cap u v ≤ f.resCap u v) :
    (f.augmentBy g hs ht hcap).value = f.value + g.value := by
  rw [value, netOut_eq_sum_sub]
  change ∑ v : V, ((f.augmentByFun g N.s v : ℤ) - (f.augmentByFun g v N.s : ℤ)) = _
  simp only [f.augmentByFun_sub g hcap N.s]
  rw [Finset.sum_add_distrib, ← f.netOut_eq_sum_sub, ← g.netOut_eq_sum_sub, value, value, hs]

/-- Residual capacities after augmenting by `g`, as integers. -/
theorem resCap_augmentBy_coe (f : N.Flow) {L : Network V} (g : L.Flow) (hs : L.s = N.s)
    (ht : L.t = N.t) (hcap : ∀ u v, L.cap u v ≤ f.resCap u v) (u v : V) :
    ((f.augmentBy g hs ht hcap).resCap u v : ℤ) =
      (f.resCap u v : ℤ) - (g u v : ℤ) + (g v u : ℤ) := by
  rw [resCap_coe, resCap_coe, augmentBy_apply, augmentBy_apply, f.augmentByFun_sub g hcap u v]
  omega

/-- Residual capacities after augmenting by `g`: `g u v` is used up and `g v u` is freed. -/
theorem resCap_augmentBy (f : N.Flow) {L : Network V} (g : L.Flow) (hs : L.s = N.s)
    (ht : L.t = N.t) (hcap : ∀ u v, L.cap u v ≤ f.resCap u v) (u v : V) :
    (f.augmentBy g hs ht hcap).resCap u v = f.resCap u v - g u v + g v u := by
  have h := f.resCap_augmentBy_coe g hs ht hcap u v
  have hle := le_trans (g.le_cap u v) (hcap u v)
  omega

/-! ### Blocking flows -/

/-- A flow `g` of `L` is *blocking* if every simple `L.s`-`L.t` path along arcs of positive
capacity contains an arc saturated by `g` ([Dinic1970]; [Schrijver2003], Section 10.6). -/
@[expose] def IsBlocking {L : Network V} (g : L.Flow) : Prop :=
  ∀ p : List V, p.Nodup → p.head? = some L.s → p.getLast? = some L.t →
    (∀ e ∈ pathArcs p, 0 < L.cap e.1 e.2) → ∃ e ∈ pathArcs p, g e.1 e.2 = L.cap e.1 e.2

/-- Augment `f` by a flow `g` of its level network `f.levelNet d`. -/
@[expose] def augmentLevel (f : N.Flow) {d : V → ℕ} (g : (f.levelNet d).Flow) : N.Flow :=
  f.augmentBy g rfl rfl (f.levelNet_cap_le_resCap d)

theorem value_augmentLevel (f : N.Flow) {d : V → ℕ} (g : (f.levelNet d).Flow) :
    (f.augmentLevel g).value = f.value + g.value :=
  f.value_augmentBy g rfl rfl _

theorem resCap_augmentLevel (f : N.Flow) {d : V → ℕ} (g : (f.levelNet d).Flow) (u v : V) :
    (f.augmentLevel g).resCap u v = f.resCap u v - g u v + g v u :=
  f.resCap_augmentBy g rfl rfl _ u v

/-- A positive residual arc after a level augmentation was a residual arc before, or the reverse
of a level arc. -/
private theorem pos_resCap_or_of_pos_resCap_augmentLevel (f : N.Flow) {d : V → ℕ}
    (g : (f.levelNet d).Flow) {u v : V} (h : 0 < (f.augmentLevel g).resCap u v) :
    0 < f.resCap u v ∨ d u = d v + 1 := by
  rw [resCap_augmentLevel] at h
  by_cases hf : 0 < f.resCap u v
  · exact .inl hf
  · right
    have hgvu : 0 < g v u := by omega
    have hcap : 0 < (f.levelNet d).cap v u := lt_of_lt_of_le hgvu (g.le_cap v u)
    exact ((f.levelNet_cap_pos_iff d v u).mp hcap).1

/-- **Distance monotonicity**: augmenting by any flow of the level network of shortest residual
distances never decreases a residual distance from `N.s` ([Dinic1970]; [Schrijver2003],
Section 10.6). -/
theorem resDist_le_resDist_augmentLevel (f : N.Flow) (g : (f.levelNet f.resDist).Flow)
    (v : V) : f.resDist v ≤ (f.augmentLevel g).resDist v := by
  have hwalk : ∀ {w : V} {k : ℕ}, (f.augmentLevel g).HasResWalkOfLen w k → f.resDist w ≤ k := by
    intro w k h
    induction h with
    | zero => simp
    | @succ u w k _ hpos ih =>
      rcases f.pos_resCap_or_of_pos_resCap_augmentLevel g hpos with hf | hlev
      · have := f.resDist_le_add_one_of_pos_resCap hf
        omega
      · omega
  by_cases hlt : (f.augmentLevel g).resDist v < Fintype.card V
  · exact hwalk ((f.augmentLevel g).hasResWalkOfLen_resDist hlt)
  · exact le_trans (f.resDist_le_card v) (Nat.le_of_not_lt hlt)

/-- **Dinitz phase lemma** ([Dinic1970]; [Schrijver2003], Section 10.6): if `N.t` is
residually reachable and `g` is a blocking flow of the level network of shortest residual
distances, then augmenting by `g` strictly increases the residual distance of `N.t`. -/
theorem resDist_lt_resDist_augmentLevel (f : N.Flow) (g : (f.levelNet f.resDist).Flow)
    (hg : g.IsBlocking) (hreach : f.ResReachable N.s N.t) :
    f.resDist N.t < (f.augmentLevel g).resDist N.t := by
  have hmono := f.resDist_le_resDist_augmentLevel g N.t
  have hlt : f.resDist N.t < Fintype.card V := (f.resDist_lt_card_iff_resReachable N.t).mpr hreach
  by_contra hnot
  have heq : (f.augmentLevel g).resDist N.t = f.resDist N.t := by omega
  -- Along a shortest residual walk of `f.augmentLevel g` that is also shortest for `f`, every arc
  -- is an unsaturated arc of the level network.
  have hclaim : ∀ {w : V} {k : ℕ}, (f.augmentLevel g).HasResWalkOfLen w k → f.resDist w = k →
      ∃ p : List V, p.Nodup ∧ p.head? = some N.s ∧ p.getLast? = some w ∧
        (∀ x ∈ p, f.resDist x ≤ k) ∧
        ∀ e ∈ pathArcs p, 0 < (f.levelNet f.resDist).cap e.1 e.2 ∧
          g e.1 e.2 < (f.levelNet f.resDist).cap e.1 e.2 := by
    intro w k h
    induction h with
    | zero =>
      intro _
      refine ⟨[N.s], List.nodup_singleton _, rfl, rfl, ?_, by simp⟩
      intro x hx
      rw [List.mem_singleton.mp hx]
      simp
    | @succ u w k hu hpos ih =>
      intro hw
      have hu_le : f.resDist u ≤ k := le_trans (f.resDist_le_resDist_augmentLevel g u)
        ((f.augmentLevel g).resDist_le_of_hasResWalkOfLen hu)
      rcases f.pos_resCap_or_of_pos_resCap_augmentLevel g hpos with hf | hlev
      · have htri := f.resDist_le_add_one_of_pos_resCap hf
        have hu_eq : f.resDist u = k := by omega
        obtain ⟨p, hnd, hs, hlast, hle, harcs⟩ := ih hu_eq
        have hcap_pos : 0 < (f.levelNet f.resDist).cap u w :=
          (f.levelNet_cap_pos_iff f.resDist u w).mpr ⟨by omega, hf⟩
        have hrev : (f.levelNet f.resDist).cap w u = 0 :=
          f.levelNet_cap_eq_zero_of_pos f.resDist hcap_pos
        have hgwu : g w u = 0 := Nat.eq_zero_of_le_zero (hrev ▸ g.le_cap w u)
        have hunsat : g u w < (f.levelNet f.resDist).cap u w := by
          have hres := f.resCap_augmentLevel g u w
          have hcap_eq : (f.levelNet f.resDist).cap u w = f.resCap u w := by
            rw [levelNet_cap]
            split_ifs <;> omega
          rw [hgwu] at hres
          omega
        have hp_ne : p ≠ [] := by
          rintro rfl
          simp at hs
        have hw_notin : w ∉ p := fun hmem => by
          have := hle w hmem
          omega
        refine ⟨p ++ [w], ?_, ?_, by simp, ?_, ?_⟩
        · refine List.nodup_append.mpr ⟨hnd, List.nodup_singleton w, ?_⟩
          intro a ha b hb hab
          rw [List.mem_singleton.mp hb] at hab
          exact hw_notin (hab ▸ ha)
        · rw [List.head?_append_of_ne_nil p hp_ne]
          exact hs
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · have := hle x hx
            omega
          · rw [List.mem_singleton.mp hx]
            omega
        · intro e he
          rw [pathArcs_append_singleton hp_ne hlast, List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact harcs e he
          · exact ⟨hcap_pos, hunsat⟩
      · omega
  obtain ⟨p, hnd, hs, hlast, _, harcs⟩ :=
    hclaim ((f.augmentLevel g).hasResWalkOfLen_resDist (v := N.t) (by omega)) heq.symm
  obtain ⟨e, he, hsat⟩ := hg p hnd hs hlast fun e he => (harcs e he).1
  have := (harcs e he).2
  omega

end Flow

/-- One **Dinitz phase** from `f` to `f'`: `N.t` is residually reachable from `N.s` and `f'`
augments `f` by a blocking flow of the level network of shortest residual distances. -/
@[expose] def IsDinitzStep (f f' : N.Flow) : Prop :=
  f.ResReachable N.s N.t ∧
    ∃ g : (f.levelNet f.resDist).Flow, g.IsBlocking ∧ f' = f.augmentLevel g

/-- A Dinitz phase step through any labelling equal to the residual distances. -/
theorem isDinitzStep_of_isBlocking {f : N.Flow} {d : V → ℕ} (hd : ∀ v, d v = f.resDist v)
    (hreach : f.ResReachable N.s N.t) (g : (f.levelNet d).Flow) (hg : g.IsBlocking) :
    N.IsDinitzStep f (f.augmentLevel g) := by
  obtain rfl : d = f.resDist := funext hd
  exact ⟨hreach, g, hg, rfl⟩

/-- Each Dinitz phase strictly increases the residual distance of `N.t`. -/
theorem IsDinitzStep.resDist_lt {f f' : N.Flow} (h : N.IsDinitzStep f f') :
    f.resDist N.t < f'.resDist N.t := by
  obtain ⟨hreach, g, hg, rfl⟩ := h
  exact f.resDist_lt_resDist_augmentLevel g hg hreach

/-- A blocking flow exists only when `N.s ≠ N.t`: for `N.s = N.t` the one-vertex path has no
arc. -/
theorem IsDinitzStep.source_ne_sink {f f' : N.Flow} (h : N.IsDinitzStep f f') : N.s ≠ N.t := by
  obtain ⟨_, g, hg, _⟩ := h
  intro hst
  obtain ⟨e, he, _⟩ := hg [N.s] (List.nodup_singleton _) rfl (by simp [hst]) (by simp)
  simp at he

/-- A run of `T` Dinitz phases `flows 0 → flows 1 → ⋯ → flows T`. -/
@[expose] def IsDinitzRun (T : ℕ) (flows : ℕ → N.Flow) : Prop :=
  ∀ i < T, N.IsDinitzStep (flows i) (flows (i + 1))

/-- After `T` Dinitz phases the residual distance of `N.t` has grown by at least `T`. -/
theorem IsDinitzRun.resDist_add_le {T : ℕ} {flows : ℕ → N.Flow} (h : N.IsDinitzRun T flows) :
    (flows 0).resDist N.t + T ≤ (flows T).resDist N.t := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hstep := (h T (Nat.lt_succ_self T)).resDist_lt
    have := ih fun i hi => h i (Nat.lt_succ_of_lt hi)
    omega

/-- **Phase bound** ([Dinic1970]; [Schrijver2003], Section 10.6): every run of Dinitz phases
has at most `|V| - 1` phases, from any initial flow. -/
theorem IsDinitzRun.length_le {T : ℕ} {flows : ℕ → N.Flow} (h : N.IsDinitzRun T flows) :
    T ≤ Fintype.card V - 1 := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · exact Nat.zero_le _
  have hst := (h 0 hT).source_ne_sink
  have hpos : 0 < (flows 0).resDist N.t := by
    rcases Nat.eq_zero_or_pos ((flows 0).resDist N.t) with h0 | h0
    · exact absurd ((flows 0).eq_source_of_resDist_eq_zero h0).symm hst
    · exact h0
  have hadd := h.resDist_add_le
  have hle := (flows T).resDist_le_card N.t
  omega

/-! ### Breadth-first layers -/

section Layers

variable [DecidableEq V]

namespace Flow

/-- Vertices reachable from `N.s` by residual walks of at most `k` arcs, computed layer by
layer. -/
@[expose] def resBall (f : N.Flow) : ℕ → Finset V
  | 0 => {N.s}
  | k + 1 =>
    let B := f.resBall k
    B ∪ Finset.univ.filter fun v => ∃ u ∈ B, 0 < f.resCap u v

theorem mem_resBall_iff (f : N.Flow) (k : ℕ) (v : V) :
    v ∈ f.resBall k ↔ ∃ m ≤ k, f.HasResWalkOfLen v m := by
  induction k generalizing v with
  | zero =>
    rw [resBall, Finset.mem_singleton]
    simp only [Nat.le_zero, exists_eq_left]
    constructor
    · rintro rfl
      exact .zero
    · intro h
      cases h
      rfl
  | succ k ih =>
    simp only [resBall, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, ih]
    constructor
    · rintro (⟨m, hm, hw⟩ | ⟨u, ⟨m, hm, hw⟩, hpos⟩)
      · exact ⟨m, by omega, hw⟩
      · exact ⟨m + 1, by omega, hw.succ hpos⟩
    · rintro ⟨m, hm, hw⟩
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact .inl ⟨m, by omega, hw⟩
      · have hm' : m = k + 1 := by omega
        subst hm'
        cases hw with
        | succ hu hpos => exact .inr ⟨_, ⟨k, le_rfl, hu⟩, hpos⟩

theorem mem_resBall_iff_resDist_le (f : N.Flow) {k : ℕ} (hk : k < Fintype.card V) (v : V) :
    v ∈ f.resBall k ↔ f.resDist v ≤ k := by
  rw [mem_resBall_iff]
  constructor
  · rintro ⟨m, hm, hw⟩
    exact le_trans (f.resDist_le_of_hasResWalkOfLen hw) hm
  · intro hle
    exact ⟨f.resDist v, hle, f.hasResWalkOfLen_resDist (by omega)⟩

/-- Breadth-first layer index of `v`: the number of balls `f.resBall k`, `k < |V|`, that miss
`v`. Equal to `f.resDist v` (`bfsDist_eq_resDist`), but computable. -/
@[expose] def bfsDist (f : N.Flow) (v : V) : ℕ :=
  ((Finset.range (Fintype.card V)).filter fun k => v ∉ f.resBall k).card

theorem bfsDist_eq_resDist (f : N.Flow) (v : V) : f.bfsDist v = f.resDist v := by
  have hfilter : (Finset.range (Fintype.card V)).filter (fun k => v ∉ f.resBall k) =
      Finset.range (f.resDist v) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hk, hnot⟩
      rw [f.mem_resBall_iff_resDist_le hk] at hnot
      omega
    · intro hk
      have hle := f.resDist_le_card v
      have hk' : k < Fintype.card V := by omega
      refine ⟨hk', ?_⟩
      rw [f.mem_resBall_iff_resDist_le hk']
      omega
  rw [bfsDist, hfilter, Finset.card_range]

end Flow

end Layers

/-! ### Slack networks and deciding blocking -/

namespace Flow

variable {L : Network V}

/-- The network of unused capacities `L.cap u v - g u v` of a flow `g` of `L`. Its residual
arcs for the zero flow are the unsaturated arcs of `g`. -/
@[expose] def slackNet (g : L.Flow) : Network V where
  cap u v := L.cap u v - g u v
  s := L.s
  t := L.t

theorem resCap_zero_slackNet (g : L.Flow) (u v : V) :
    (Flow.zero g.slackNet).resCap u v = L.cap u v - g u v := by
  simp only [resCap, slackNet, zero_apply, Nat.sub_zero, Nat.add_zero]

theorem isAugmentingPath_of_slackNet {g : L.Flow} {p : List V}
    (hp : (Flow.zero g.slackNet).IsAugmentingPath p) : g.IsAugmentingPath p := by
  obtain ⟨hnd, hs, ht, hpos⟩ := hp
  refine ⟨hnd, hs, ht, fun e he => ?_⟩
  have h := hpos e he
  rw [resCap_zero_slackNet] at h
  unfold resCap
  omega

/-- If no path of unsaturated arcs joins the terminals, `g` is blocking. -/
theorem isBlocking_of_not_exists_slackNet {g : L.Flow}
    (h : ¬ ∃ p, (Flow.zero g.slackNet).IsAugmentingPath p) : g.IsBlocking := by
  intro p hnd hs ht _
  by_contra hno
  refine h ⟨p, hnd, hs, ht, fun e he => ?_⟩
  rw [resCap_zero_slackNet]
  have hle := g.le_cap e.1 e.2
  have hne : g e.1 e.2 ≠ L.cap e.1 e.2 := fun heq => hno ⟨e, he, heq⟩
  omega

/-- `g` is blocking exactly when no path of unsaturated arcs joins the terminals. -/
theorem isBlocking_iff_not_exists_slackNet {g : L.Flow} :
    g.IsBlocking ↔ ¬ ∃ p, (Flow.zero g.slackNet).IsAugmentingPath p := by
  refine ⟨fun hg ⟨p, hnd, hs, ht, hpos⟩ => ?_, isBlocking_of_not_exists_slackNet⟩
  have hcap : ∀ e ∈ pathArcs p, 0 < L.cap e.1 e.2 := fun e he => by
    have h := hpos e he
    rw [resCap_zero_slackNet] at h
    omega
  obtain ⟨e, he, hsat⟩ := hg p hnd hs ht hcap
  have h := hpos e he
  rw [resCap_zero_slackNet] at h
  omega

/-- Arcs not saturated by `g`. -/
def unsatArcs (g : L.Flow) : Finset (V × V) :=
  Finset.univ.filter fun e => g e.1 e.2 < L.cap e.1 e.2

@[simp]
theorem mem_unsatArcs (g : L.Flow) (e : V × V) : e ∈ g.unsatArcs ↔ g e.1 e.2 < L.cap e.1 e.2 := by
  simp only [unsatArcs, Finset.mem_filter, Finset.mem_univ, true_and]

section Decide

variable [DecidableEq V]

/-- Blocking is decided by one breadth-first search in the slack network. -/
theorem isBlocking_iff_bfsDist_slackNet {g : L.Flow} :
    g.IsBlocking ↔ Fintype.card V ≤ (Flow.zero g.slackNet).bfsDist L.t := by
  rw [isBlocking_iff_not_exists_slackNet, exists_augmentingPath_iff_resReachable,
    ← resDist_lt_card_iff_resReachable, bfsDist_eq_resDist, not_lt]
  rfl

instance (g : L.Flow) : Decidable g.IsBlocking :=
  decidable_of_iff _ isBlocking_iff_bfsDist_slackNet.symm

end Decide

end Flow

end Network

end Cslib.Algorithms.Lean.MaxFlow
