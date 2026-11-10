/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.MaxFlow.LevelGraph

/-!
# Dinitz's Blocking-Flow Maximum-Flow Algorithm

Formalizes an executable version of **Dinitz's algorithm** ([Dinic1970]; [Schrijver2003],
Section 10.6) over `Network (Fin n)`: repeatedly compute the breadth-first levels of the residual
network, find a blocking flow of the level network, and augment by it, until `N.t` is no longer
residually reachable from `N.s`.

## Mathematical and algorithmic overview

1. **Greedy blocking flows (`greedyBlockingFlow`):** inside a level network `L`, while a path of
   unsaturated arcs joins the terminals (found by `bfsM` on the slack network `Flow.slackNet`), push
   its bottleneck. Since a level network has no antiparallel arcs, each push only increases arc
   flows and saturates a new arc (`Flow.card_unsatArcs_augmentByBottleneck_lt`), so the loop stops
   with a blocking flow after at most `|Flow.unsatArcs|` pushes (`greedyBlockingFlow_spec`), which
   is at most `|N.posArcs|` at the zero flow of a level network
   (`Flow.card_unsatArcs_zero_levelNet_le`).
2. **Phases (`dinitzLoop`, `dinitz`):** each phase computes `Flow.bfsDist` (equal to
   `Flow.resDist`), stops if `N.t` is unreachable, and otherwise augments by a greedy blocking flow
   of the level network. The phases form a run of Dinitz phases (`dinitz_isDinitzRun`), hence there
   are at most `n - 1` of them (`Network.IsDinitzRun.length_le`).
3. **Correctness (`dinitz_correct`):** the final flow has no augmenting path, so it is a maximum
   flow and its residual-reachability cut is a minimum cut of equal capacity, by the max-flow
   min-cut API of `Complexity.Algorithms.Lean.MaxFlow.Basic`.

## Cost model and limitations

* Proved quantities: at most `n - 1` phases and at most `(n - 1) * |N.posArcs|` bottleneck pushes
  in total (`dinitz_correct`). No running time is charged: the functions are pure, not `TimeM`.
* The blocking flow is found by a fresh breadth-first search per push, not by the depth-first
  search with dead-end deletion that gives Dinitz's `O(|V| |E|)` time per phase and
  `O(|V|^2 |E|)` overall; this module does not claim those time bounds.
* `Flow.bfsDist` recomputes breadth-first balls and is meant for specification and small
  evaluations; `FlowMatrix.ofFlow` tabulates flows between phases.

## Main definitions

* `Cslib.Algorithms.Lean.MaxFlow.greedyBlockingFlow`: greedy blocking flows in a network without
  antiparallel arcs.
* `Cslib.Algorithms.Lean.MaxFlow.DinitzOutput`, `dinitzLoop`, `dinitz`, `dinitzDense`: the
  algorithm.

## Main results

* `Cslib.Algorithms.Lean.MaxFlow.greedyBlockingFlow_spec`: the greedy search returns a blocking
  flow after at most `|unsaturated arcs|` pushes.
* `Cslib.Algorithms.Lean.MaxFlow.dinitz_isDinitzRun`: the phases of `dinitz` form a run of Dinitz
  phases from the zero flow.
* `Cslib.Algorithms.Lean.MaxFlow.dinitz_correct`, `dinitzDense_correct`: maximum flow, minimum cut
  of equal value, and the phase and push bounds.

## References

* [E. A. Dinic, *Algorithm for solution of a problem of maximum flow in networks with power
  estimation*][Dinic1970]
* [A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*][Schrijver2003]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

namespace Network

variable {V : Type*} [Fintype V] {N : Network V}

/-! ### Greedy blocking flows -/

namespace Flow

variable {L : Network V} [DecidableEq V]

/-- Pushing the bottleneck along a path of unsaturated arcs of a network without antiparallel
arcs only increases arc flows. -/
theorem le_augmentByBottleneck_of_slackNet (hanti : ∀ u v, 0 < L.cap u v → L.cap v u = 0)
    {g : L.Flow} {p : List V} (hp : (Flow.zero g.slackNet).IsAugmentingPath p) (u v : V) :
    g u v ≤ g.augmentByBottleneck p (isAugmentingPath_of_slackNet hp) u v := by
  change g u v ≤ g.augmentFun p (g.bottleneck p) u v
  unfold augmentFun
  split_ifs with huv hvu
  · omega
  · have hslack := hp.pos_resCap hvu
    rw [resCap_zero_slackNet] at hslack
    have hslack' : 0 < L.cap v u - g v u := hslack
    have hcap : L.cap u v = 0 := hanti v u (by omega)
    have hle := g.le_cap u v
    omega
  · exact le_rfl

/-- The bottleneck push saturates an arc that was unsaturated. -/
theorem exists_saturated_augmentByBottleneck_of_slackNet (hst : L.s ≠ L.t) {g : L.Flow}
    {p : List V} (hp : (Flow.zero g.slackNet).IsAugmentingPath p) :
    ∃ e : V × V, g e.1 e.2 < L.cap e.1 e.2 ∧
      L.cap e.1 e.2 ≤ g.augmentByBottleneck p (isAugmentingPath_of_slackNet hp) e.1 e.2 := by
  have hp' := isAugmentingPath_of_slackNet hp
  have hne : pathArcs p ≠ [] := pathArcs_ne_nil_of_head?_ne_getLast? hst hp'.head? hp'.getLast?
  obtain ⟨e, he, heq⟩ := g.exists_mem_pathArcs_resCap_eq_bottleneck hne
  have hres := g.resCap_augment hp'.nodup hp'.head? hp'.getLast? (g.bottleneck p)
    (fun _ he => g.bottleneck_le_resCap he) e.1 e.2
  simp only [Prod.mk.eta, he, ↓reduceIte] at hres
  have hslack := hp.pos_resCap he
  rw [resCap_zero_slackNet] at hslack
  refine ⟨e, by omega, ?_⟩
  change L.cap e.1 e.2 ≤ (g.augment p hp'.nodup hp'.head? hp'.getLast? (g.bottleneck p)
    (fun _ he => g.bottleneck_le_resCap he)) e.1 e.2
  unfold resCap at hres heq
  omega

/-- Each bottleneck push along unsaturated arcs saturates a new arc and keeps saturated arcs
saturated. -/
theorem card_unsatArcs_augmentByBottleneck_lt (hanti : ∀ u v, 0 < L.cap u v → L.cap v u = 0)
    (hst : L.s ≠ L.t) {g : L.Flow} {p : List V}
    (hp : (Flow.zero g.slackNet).IsAugmentingPath p) :
    (g.augmentByBottleneck p (isAugmentingPath_of_slackNet hp)).unsatArcs.card <
      g.unsatArcs.card := by
  obtain ⟨e, hlt, hsat⟩ := exists_saturated_augmentByBottleneck_of_slackNet hst hp
  have hsub : (g.augmentByBottleneck p (isAugmentingPath_of_slackNet hp)).unsatArcs ⊆
      g.unsatArcs := by
    intro x hx
    rw [mem_unsatArcs] at hx ⊢
    have := le_augmentByBottleneck_of_slackNet hanti hp x.1 x.2
    omega
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨e, ?_, ?_⟩)
  · exact (mem_unsatArcs _ _).mpr hlt
  · rw [mem_unsatArcs, not_lt]
    exact hsat

/-- A level network has at most `|N.posArcs|` arcs: it has no antiparallel arcs and its arcs lie
in `N.symArcs`. -/
theorem card_unsatArcs_zero_levelNet_le (f : N.Flow) (d : V → ℕ) :
    (Flow.zero (f.levelNet d)).unsatArcs.card ≤ N.posArcs.card := by
  set A := (Flow.zero (f.levelNet d)).unsatArcs
  have hmem : ∀ e, e ∈ A ↔ d e.2 = d e.1 + 1 ∧ 0 < f.resCap e.1 e.2 := fun e => by
    simp only [A, mem_unsatArcs, zero_apply, levelNet_cap_pos_iff]
  have hsym : ∀ e ∈ A, e.1 ≠ e.2 ∧ 0 < N.cap e.1 e.2 + N.cap e.2 e.1 := fun e he => by
    obtain ⟨hd, hpos⟩ := (hmem e).mp he
    have := f.resCap_le_cap_add_cap e.1 e.2
    refine ⟨fun h => ?_, by omega⟩
    rw [h] at hd
    omega
  have hA : A ⊆ N.symArcs := fun e he => by
    simp only [symArcs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hsym e he
  have hB : A.image Prod.swap ⊆ N.symArcs := fun e he => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hne, hpos⟩ := hsym x hx
    simp only [symArcs, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
      Prod.snd_swap]
    exact ⟨hne.symm, by omega⟩
  have hdisj : Disjoint A (A.image Prod.swap) := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he'
    have h₁ := ((hmem x).mp hx).1
    have h₂ := ((hmem x.swap).mp he).1
    simp only [Prod.fst_swap, Prod.snd_swap] at h₂
    omega
  have hcard : A.card + (A.image Prod.swap).card ≤ N.symArcs.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset hA hB)
  have himg : (A.image Prod.swap).card = A.card :=
    Finset.card_image_of_injective _ Prod.swap_injective
  have := N.card_symArcs_le_two_mul_posArcs
  omega

end Flow

end Network

/-! ### Executable Dinitz over `Fin n` -/

section ExecutableFin

open Network

/-- Tabulate a flow as a `FlowMatrix`, so that later lookups are `O(1)`. -/
@[expose] def FlowMatrix.ofFlow {n : ℕ} {N : Network (Fin n)} (f : N.Flow) : FlowMatrix N where
  mat := Vector.ofFn fun u => Vector.ofFn fun v => f u v
  le_cap u v := by simpa [fget, vget] using f.le_cap u v
  conserve v hvs hvt := by simpa [fget, vget] using f.conserve v hvs hvt

@[simp]
theorem FlowMatrix.toFlow_ofFlow {n : ℕ} {N : Network (Fin n)} (f : N.Flow) :
    (FlowMatrix.ofFlow f).toFlow = f := by
  ext u v
  simp [FlowMatrix.ofFlow, fget, vget]

/-- Breadth-first distances `Flow.bfsDist` of `f`, tabulated. -/
@[expose] def bfsDistVec {n : ℕ} {N : Network (Fin n)} (f : N.Flow) : Vector ℕ n :=
  Vector.ofFn f.bfsDist

@[simp]
theorem vget_bfsDistVec {n : ℕ} {N : Network (Fin n)} (f : N.Flow) (v : Fin n) :
    vget (bfsDistVec f) v = f.resDist v := by
  simp [bfsDistVec, vget, Flow.bfsDist_eq_resDist]

/-- Result of the greedy blocking-flow search. -/
structure BlockingFlowResult {n : ℕ} (L : Network (Fin n)) where
  /-- The flow found. -/
  flow : FlowMatrix L
  /-- Number of bottleneck pushes performed. -/
  pushes : ℕ

/-- Greedy blocking flow: while a path of unsaturated arcs joins the terminals (found by `bfsM`
on `slackNet`), push its bottleneck. -/
@[expose] def greedyBlockingFlow {n : ℕ} (L : Network (Fin n)) (adj : Fin n → List (Fin n)) :
    ℕ → FlowMatrix L → ℕ → BlockingFlowResult L
  | 0, G, k => ⟨G, k⟩
  | fuel + 1, G, k =>
    let res := (bfsM G.toFlow.slackNet adj (Flow.zero G.toFlow.slackNet)).ret
    match hp : res.augPath with
    | none => ⟨G, k⟩
    | some p =>
      greedyBlockingFlow L adj fuel
        (augmentFlowMatrixM G p (Flow.isAugmentingPath_of_slackNet (res.augPath_valid p hp))).ret
        (k + 1)

/-- **Greedy blocking flows**: on a network `L` without antiparallel arcs and with `L.s ≠ L.t`,
with valid neighbor lists and enough fuel, `greedyBlockingFlow` returns a blocking flow after at
most `|G.toFlow.unsatArcs|` further bottleneck pushes. -/
theorem greedyBlockingFlow_spec {n : ℕ} {L : Network (Fin n)} {adj : Fin n → List (Fin n)}
    (hadj : AdjValid L adj) (hanti : ∀ u v, 0 < L.cap u v → L.cap v u = 0) (hst : L.s ≠ L.t) :
    ∀ (fuel : ℕ) (G : FlowMatrix L) (k : ℕ), G.toFlow.unsatArcs.card < fuel →
      (greedyBlockingFlow L adj fuel G k).flow.toFlow.IsBlocking ∧
        (greedyBlockingFlow L adj fuel G k).pushes ≤ k + G.toFlow.unsatArcs.card
  | 0, G, k, hfuel => absurd hfuel (Nat.not_lt_zero _)
  | fuel + 1, G, k, hfuel => by
    have hadj' : AdjValid G.toFlow.slackNet adj := fun u v huv hpos =>
      hadj u v huv (by simp only [Flow.slackNet] at hpos; omega)
    have hbfs := bfsM_spec hadj' (Flow.zero G.toFlow.slackNet)
    simp only [greedyBlockingFlow]
    split
    · rename_i hnone
      exact ⟨Flow.isBlocking_of_not_exists_slackNet (hbfs.2 hnone).1, Nat.le_add_right _ _⟩
    · rename_i p hp
      have hp' := (bfsM _ adj _).ret.augPath_valid p hp
      have hlt := Flow.card_unsatArcs_augmentByBottleneck_lt hanti hst hp'
      have hfun := augmentFlowMatrixM_toFlow G p (Flow.isAugmentingPath_of_slackNet hp')
      obtain ⟨hblk, hpush⟩ := greedyBlockingFlow_spec hadj hanti hst fuel
        (augmentFlowMatrixM G p (Flow.isAugmentingPath_of_slackNet hp')).ret (k + 1)
        (by rw [hfun]; omega)
      rw [hfun] at hpush
      exact ⟨hblk, by omega⟩

/-- Output of Dinitz's algorithm on `N : Network (Fin n)`. -/
structure DinitzOutput {n : ℕ} (N : Network (Fin n)) where
  /-- Final integral flow on `N`. -/
  flow : N.Flow
  /-- Residual-reachability cut certifying optimality (`flow.reachableCut`). -/
  cut : Finset (Fin n)
  /-- Number of blocking-flow phases. -/
  phases : ℕ
  /-- Total number of bottleneck pushes over all phases. -/
  augmentations : ℕ

/-- Phases of Dinitz's algorithm with `fuel` remaining phases: compute the breadth-first levels;
stop if `N.t` is unreachable, and otherwise find a blocking flow of the level network greedily and
augment by it. -/
@[expose] def dinitzLoop {n : ℕ} (N : Network (Fin n)) (adj : Fin n → List (Fin n)) :
    ℕ → FlowMatrix N → ℕ → ℕ → DinitzOutput N
  | 0, M, ph, k =>
    let lv := bfsDistVec M.toFlow
    { flow := M.toFlow, cut := Finset.univ.filter fun v => vget lv v < n, phases := ph,
      augmentations := k }
  | fuel + 1, M, ph, k =>
    let lv := bfsDistVec M.toFlow
    if n ≤ vget lv N.t then
      { flow := M.toFlow, cut := Finset.univ.filter fun v => vget lv v < n, phases := ph,
        augmentations := k }
    else
      let B := greedyBlockingFlow (M.toFlow.levelNet (vget lv)) adj (n * n + 1)
        (FlowMatrix.ofFlow (Flow.zero _)) 0
      dinitzLoop N adj fuel (FlowMatrix.ofFlow (M.toFlow.augmentLevel B.flow.toFlow)) (ph + 1)
        (k + B.pushes)

/-- **Dinitz's blocking-flow algorithm** on `N : Network (Fin n)` with candidate neighbor lists
`adj`. -/
@[expose] def dinitz {n : ℕ} (N : Network (Fin n)) (adj : Fin n → List (Fin n)) :
    DinitzOutput N :=
  if N.s = N.t then
    { flow := Flow.zero N, cut := ∅, phases := 0, augmentations := 0 }
  else
    dinitzLoop N adj (n - 1) (FlowMatrix.ofFlow (Flow.zero N)) 0 0

/-- Dense specialization of `dinitz` using `defaultAdj n`. -/
@[expose] def dinitzDense {n : ℕ} (N : Network (Fin n)) : DinitzOutput N :=
  dinitz N (defaultAdj n)

private theorem filter_bfsDistVec_eq_reachableCut {n : ℕ} {N : Network (Fin n)} (f : N.Flow) :
    (Finset.univ.filter fun v => vget (bfsDistVec f) v < n) = f.reachableCut := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, vget_bfsDistVec, f.mem_reachableCut_iff,
    ← f.resDist_lt_card_iff_resReachable, Fintype.card_fin]

private theorem dinitzLoop_spec {n : ℕ} {N : Network (Fin n)} {adj : Fin n → List (Fin n)}
    (hadj : AdjValid N adj) (hst : N.s ≠ N.t) :
    ∀ (fuel : ℕ) (M : FlowMatrix N) (ph k : ℕ) (flows : ℕ → N.Flow),
      n ≤ fuel + ph + 1 → N.IsDinitzRun ph flows → flows ph = M.toFlow →
      k ≤ ph * N.posArcs.card →
      let out := dinitzLoop N adj fuel M ph k
      ¬ out.flow.ResReachable N.s N.t ∧ out.cut = out.flow.reachableCut ∧
        (∃ flows' : ℕ → N.Flow, N.IsDinitzRun out.phases flows' ∧ flows' 0 = flows 0 ∧
          flows' out.phases = out.flow) ∧
        out.augmentations ≤ out.phases * N.posArcs.card
  | 0, M, ph, k, flows, hfuel, hrun, hph, hk => by
    simp only [dinitzLoop]
    refine ⟨fun hreach => ?_, filter_bfsDistVec_eq_reachableCut _, ⟨flows, hrun, rfl, hph⟩, hk⟩
    have hlt := (M.toFlow.resDist_lt_card_iff_resReachable N.t).mpr hreach
    have hadd := hrun.resDist_add_le
    have hpos : 0 < (flows 0).resDist N.t := by
      rcases Nat.eq_zero_or_pos ((flows 0).resDist N.t) with h0 | h0
      · exact absurd ((flows 0).eq_source_of_resDist_eq_zero h0).symm hst
      · exact h0
    rw [hph, Fintype.card_fin] at *
    omega
  | fuel + 1, M, ph, k, flows, hfuel, hrun, hph, hk => by
    simp only [dinitzLoop]
    split
    · rename_i hge
      refine ⟨fun hreach => ?_, filter_bfsDistVec_eq_reachableCut _, ⟨flows, hrun, rfl, hph⟩, hk⟩
      have hlt := (M.toFlow.resDist_lt_card_iff_resReachable N.t).mpr hreach
      rw [vget_bfsDistVec] at hge
      rw [Fintype.card_fin] at hlt
      omega
    · rename_i hlt
      rw [vget_bfsDistVec] at hlt
      have hreach : M.toFlow.ResReachable N.s N.t := by
        rw [← M.toFlow.resDist_lt_card_iff_resReachable, Fintype.card_fin]
        omega
      have hd : ∀ v, vget (bfsDistVec M.toFlow) v = M.toFlow.resDist v := vget_bfsDistVec _
      have hadjL : AdjValid (M.toFlow.levelNet (vget (bfsDistVec M.toFlow))) adj :=
        fun u v huv hpos => hadj u v huv (by
          have h₁ := M.toFlow.levelNet_cap_le_resCap (vget (bfsDistVec M.toFlow)) u v
          have h₂ := M.toFlow.levelNet_cap_le_resCap (vget (bfsDistVec M.toFlow)) v u
          have h₃ := M.toFlow.resCap_le_cap_add_cap u v
          have h₄ := M.toFlow.resCap_le_cap_add_cap v u
          omega)
      have hcardL := Flow.card_unsatArcs_zero_levelNet_le M.toFlow (vget (bfsDistVec M.toFlow))
      have hfuelL : (FlowMatrix.ofFlow
          (Flow.zero (M.toFlow.levelNet (vget (bfsDistVec M.toFlow))))).toFlow.unsatArcs.card <
          n * n + 1 := by
        rw [FlowMatrix.toFlow_ofFlow]
        have := Finset.card_le_univ
          (Flow.zero (M.toFlow.levelNet (vget (bfsDistVec M.toFlow)))).unsatArcs
        simp only [Fintype.card_prod, Fintype.card_fin] at this
        omega
      obtain ⟨hblk, hpush⟩ := greedyBlockingFlow_spec hadjL
        (fun u v h => M.toFlow.levelNet_cap_eq_zero_of_pos _ h) hst (n * n + 1)
        (FlowMatrix.ofFlow (Flow.zero _)) 0 hfuelL
      rw [FlowMatrix.toFlow_ofFlow] at hpush
      set B := greedyBlockingFlow (M.toFlow.levelNet (vget (bfsDistVec M.toFlow))) adj (n * n + 1)
        (FlowMatrix.ofFlow (Flow.zero _)) 0 with hB
      have hstep : N.IsDinitzStep M.toFlow (M.toFlow.augmentLevel B.flow.toFlow) :=
        isDinitzStep_of_isBlocking hd hreach B.flow.toFlow hblk
      let flows' : ℕ → N.Flow := fun i =>
        if i ≤ ph then flows i else M.toFlow.augmentLevel B.flow.toFlow
      have hrun' : N.IsDinitzRun (ph + 1) flows' := by
        intro i hi
        rcases Nat.lt_or_ge i ph with hlt' | hge'
        · have h₁ : i ≤ ph := Nat.le_of_lt hlt'
          have h₂ : i + 1 ≤ ph := hlt'
          simp only [flows', h₁, h₂, ↓reduceIte]
          exact hrun i hlt'
        · have heq : i = ph := by omega
          subst heq
          have h₂ : ¬ i + 1 ≤ i := by omega
          simp only [flows', le_rfl, h₂, ↓reduceIte, hph]
          exact hstep
      obtain ⟨h₁, h₂, ⟨flows'', hrun'', h0, hlast⟩, h₄⟩ := dinitzLoop_spec hadj hst fuel
        (FlowMatrix.ofFlow (M.toFlow.augmentLevel B.flow.toFlow)) (ph + 1) (k + B.pushes) flows'
        (by omega) hrun' (by simp [flows'])
        (by rw [Nat.succ_mul]; omega)
      refine ⟨h₁, h₂, ⟨flows'', hrun'', ?_, hlast⟩, h₄⟩
      rw [h0]
      simp [flows']

/-- The phases of `dinitz` form a run of Dinitz phases from the zero flow to the output flow. -/
theorem dinitz_isDinitzRun {n : ℕ} {N : Network (Fin n)} {adj : Fin n → List (Fin n)}
    (hadj : AdjValid N adj) :
    ∃ flows : ℕ → N.Flow, N.IsDinitzRun (dinitz N adj).phases flows ∧
      flows 0 = Flow.zero N ∧ flows (dinitz N adj).phases = (dinitz N adj).flow := by
  unfold dinitz
  split
  · exact ⟨fun _ => Flow.zero N, fun i hi => absurd hi (Nat.not_lt_zero i), rfl, rfl⟩
  · rename_i hst
    have hn : 0 < n := Nat.zero_lt_of_lt N.s.isLt
    obtain ⟨_, _, ⟨flows, hrun, h0, hlast⟩, _⟩ := dinitzLoop_spec hadj hst (n - 1)
      (FlowMatrix.ofFlow (Flow.zero N)) 0 0 (fun _ => Flow.zero N) (by omega)
      (fun i hi => absurd hi (Nat.not_lt_zero i)) (by simp) (by simp)
    exact ⟨flows, hrun, h0, hlast⟩

/-- **Correctness of Dinitz's algorithm** ([Dinic1970]; [Schrijver2003], Section 10.6): on
`N : Network (Fin n)` with `N.s ≠ N.t` and valid neighbor lists, `dinitz N adj` returns a maximum
flow and a minimum cut of equal value, after at most `n - 1` phases of at most `|N.posArcs|`
bottleneck pushes each. -/
theorem dinitz_correct {n : ℕ} {N : Network (Fin n)} {adj : Fin n → List (Fin n)}
    (hadj : AdjValid N adj) (hst : N.s ≠ N.t) :
    let out := dinitz N adj
    out.flow.IsMaxFlow ∧ N.IsMinCut out.cut ∧ out.flow.value = (N.cutCapacity out.cut : ℤ) ∧
      out.cut = out.flow.reachableCut ∧ out.phases ≤ n - 1 ∧
      out.augmentations ≤ (n - 1) * N.posArcs.card := by
  have hn : 0 < n := Nat.zero_lt_of_lt N.s.isLt
  obtain ⟨hno, hcut, ⟨flows, hrun, _, _⟩, hk⟩ := dinitzLoop_spec hadj hst (n - 1)
    (FlowMatrix.ofFlow (Flow.zero N)) 0 0 (fun _ => Flow.zero N) (by omega)
    (fun i hi => absurd hi (Nat.not_lt_zero i)) (by simp) (by simp)
  have hphases := hrun.length_le
  rw [Fintype.card_fin] at hphases
  simp only [dinitz, hst, ↓reduceIte]
  set out := dinitzLoop N adj (n - 1) (FlowMatrix.ofFlow (Flow.zero N)) 0 0
  have hno' : ¬ ∃ p, out.flow.IsAugmentingPath p := by
    rwa [out.flow.exists_augmentingPath_iff_resReachable]
  have hmax := (out.flow.isMaxFlow_iff_not_exists_augmentingPath hst).mpr hno'
  have his := out.flow.reachableCut_isCut hno'
  have hval := out.flow.value_eq_cutCapacity_reachableCut hno'
  have hmin := out.flow.isMinCut_of_value_eq_cutCapacity his hval
  rw [← hcut] at hmin hval
  exact ⟨hmax, hmin, hval, hcut, hphases,
    le_trans hk (Nat.mul_le_mul_right _ hphases)⟩

/-- Correctness of `dinitzDense` without external adjacency obligations. -/
theorem dinitzDense_correct {n : ℕ} {N : Network (Fin n)} (hst : N.s ≠ N.t) :
    let out := dinitzDense N
    out.flow.IsMaxFlow ∧ N.IsMinCut out.cut ∧ out.flow.value = (N.cutCapacity out.cut : ℤ) ∧
      out.cut = out.flow.reachableCut ∧ out.phases ≤ n - 1 ∧
      out.augmentations ≤ (n - 1) * N.posArcs.card :=
  dinitz_correct (adjValid_defaultAdj N) hst

end ExecutableFin

end Cslib.Algorithms.Lean.MaxFlow
