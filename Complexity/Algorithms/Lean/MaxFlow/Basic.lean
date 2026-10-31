/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.List.Nodup
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic

/-!
# Integral Network Flows and the Max-Flow / Min-Cut Theorem

Formalizes finite directed flow networks with non-negative integral arc capacities, feasible
integral flows, `s`-`t` cuts, residual networks, simple augmenting paths, and the **Ford–Fulkerson
Max-Flow / Min-Cut Theorem** ([FordFulkerson1956], Theorem 1, pp. 400–402; [FordFulkerson1962],
Chapter I, Sections 4–8; [CLRS2009], Sections 26.1–26.2, Theorem 26.6).

## Model and source mapping

* **Flow network (`Network V`):** directed capacities `cap : V → V → ℕ` (`0` for absent arcs) with
  designated source `s : V` and sink `t : V`. Unlike [CLRS2009], Section 26.1, which forbids
  antiparallel arcs, `Network V` permits arbitrary antiparallel capacities `cap u v` and `cap v u`
  (as in [EdmondsKarp1972], Section 1.1, p. 249) as well as arcs entering `s` or leaving `t`.
* **Feasible flow (`Network.Flow`):** non-negative integral arc flow `f : V → V → ℕ` bounded by
  `cap` (`f u v ≤ cap u v`) and satisfying inflow-equals-outflow conservation
  `∑ u, f u v = ∑ w, f v w` at every intermediate vertex `v ≠ s, t`. Its net `value : ℤ` is the net
  outflow from `s` (`(∑ w, (f s w : ℤ)) - (∑ u, (f u s : ℤ))`).
* **Residual capacity (`Flow.resCap`):** `resCap f u v = (cap u v - f u v) + f v u`, combining
  unused forward capacity on `(u, v)` with cancellable reverse flow on `(v, u)`.
* **Source comparison:** [FordFulkerson1956], pp. 399–402 states Theorem 1 (*Minimal cut theorem*)
  in the chain-flow / disconnecting-arc-set model; here we formalize the equivalent arc-flow,
  residual-network, and vertex-partition `s`-`t` cut formulation of [FordFulkerson1962], Chapter I,
  Sections 4–8 and [CLRS2009], Theorem 26.6, specialized to non-negative integral capacities `ℕ`.

## Main definitions

* `Cslib.Algorithms.Lean.MaxFlow.Network`: integral directed flow network on vertex type `V`
  (with equivalence transport `Network.reindex`).
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow`: feasible integral flow on `N`.
* `Cslib.Algorithms.Lean.MaxFlow.Network.IsCut`, `Network.cutCapacity`, `Network.IsMinCut`:
  vertex-partition `s`-`t` cuts and their forward capacities.
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.resCap`: residual arc capacity.
* `Cslib.Algorithms.Lean.MaxFlow.pathArcs`, `Flow.IsAugmentingPath`, `Flow.bottleneck`,
  `Flow.augment`: simple residual `s`-`t` augmenting paths and bottleneck flow augmentation.
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.reachableCut`: residual-reachability `s`-`t` cut.

## Main results

* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.value_eq_netFlow_across_cut`: net flow across any
  `s`-`t` cut equals `f.value`.
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.value_le_cutCapacity`: weak duality
  (`f.value ≤ cutCapacity S` for every feasible flow `f` and `s`-`t` cut `S`).
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.isMaxFlow_iff_not_exists_augmentingPath` and
  `isMaxFlow_iff_exists_cut_value_eq`: Ford–Fulkerson optimality characterizations.
* `Cslib.Algorithms.Lean.MaxFlow.Network.exists_maxFlow_eq_minCut`: existence of an integral
  maximum flow and minimum `s`-`t` cut of equal value when `N.s ≠ N.t`.

## References

* [L. R. Ford, Jr. and D. R. Fulkerson, *Maximal Flow Through a Network*][FordFulkerson1956]
* [L. R. Ford, Jr. and D. R. Fulkerson, *Flows in Networks*][FordFulkerson1962]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

/-- A directed flow network on vertex type `V` with non-negative integral arc capacities `cap`,
source `s`, and sink `t`. -/
structure Network (V : Type*) where
  /-- Non-negative integral capacity of each directed arc `(u, v)`. -/
  cap : V → V → ℕ
  /-- Source vertex. -/
  s : V
  /-- Sink vertex. -/
  t : V

/-- Consecutive directed arcs `(v₀, v₁), (v₁, v₂), …` along a vertex list. -/
@[expose] def pathArcs {V : Type*} : List V → List (V × V)
  | u :: v :: rest => (u, v) :: pathArcs (v :: rest)
  | _ => []

/-- Tail suffix of `ys` starting at the first occurrence of `x` (`[]` when `x ∉ ys`). -/
private def suffixFrom {V : Type*} [DecidableEq V] (x : V) : List V → List V
  | [] => []
  | y :: ys => if y = x then y :: ys else suffixFrom x ys

/-- Constructive loop erasure turning any walk into a duplicate-free (`Nodup`) simple path with the
same endpoints and a subset of directed arcs. -/
def loopErase {V : Type*} [DecidableEq V] : List V → List V
  | [] => []
  | x :: xs =>
    let ys := loopErase xs
    if x ∈ ys then suffixFrom x ys else x :: ys

section PathLemmas

variable {V : Type*}

@[simp]
theorem pathArcs_nil : pathArcs ([] : List V) = [] := rfl

@[simp]
theorem pathArcs_singleton (x : V) : pathArcs [x] = [] := rfl

@[simp]
theorem pathArcs_cons_cons (u v : V) (rest : List V) :
    pathArcs (u :: v :: rest) = (u, v) :: pathArcs (v :: rest) := rfl

theorem fst_mem_of_mem_pathArcs {p : List V} {e : V × V} (h : e ∈ pathArcs p) : e.1 ∈ p := by
  induction p with
  | nil => simp at h
  | cons u rest ih =>
    rcases rest with _ | ⟨v, rest'⟩
    · simp at h
    · simp only [pathArcs_cons_cons, List.mem_cons] at h
      rcases h with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem u (ih h')

theorem snd_mem_of_mem_pathArcs {p : List V} {e : V × V} (h : e ∈ pathArcs p) : e.2 ∈ p := by
  induction p with
  | nil => simp at h
  | cons u rest ih =>
    rcases rest with _ | ⟨v, rest'⟩
    · simp at h
    · simp only [pathArcs_cons_cons, List.mem_cons] at h
      rcases h with rfl | h'
      · exact List.mem_cons_of_mem u List.mem_cons_self
      · exact List.mem_cons_of_mem u (ih h')

theorem pathArcs_append_singleton {p : List V} {x y : V} (hp : p ≠ [])
    (hlast : p.getLast? = some x) :
    pathArcs (p ++ [y]) = pathArcs p ++ [(x, y)] := by
  induction p with
  | nil => exact absurd rfl hp
  | cons u rest ih =>
    rcases rest with _ | ⟨v, rest'⟩
    · simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      rfl
    · simp only [List.cons_append, pathArcs_cons_cons]
      congr 1
      apply ih (List.cons_ne_nil v rest')
      simpa using hlast

theorem pathArcs_ne_nil_of_head?_ne_getLast? {p : List V} {s t : V} (hst : s ≠ t)
    (hs : p.head? = some s) (ht : p.getLast? = some t) : pathArcs p ≠ [] := by
  rcases p with _ | ⟨u, _ | ⟨v, rest⟩⟩
  · simp at hs
  · simp only [List.head?_cons, Option.some.injEq] at hs
    simp only [List.getLast?_singleton, Option.some.injEq] at ht
    exact absurd (hs.symm.trans ht) hst
  · simp

theorem length_pathArcs_add_one {p : List V} (hp : p ≠ []) :
    (pathArcs p).length + 1 = p.length := by
  induction p with
  | nil => exact absurd rfl hp
  | cons u rest ih =>
    rcases rest with _ | ⟨v, rest'⟩
    · rfl
    · have hrec := ih (List.cons_ne_nil v rest')
      simp only [pathArcs_cons_cons, List.length_cons] at hrec ⊢
      omega

theorem ne_of_mem_pathArcs {p : List V} (hp : p.Nodup) {u v : V}
    (he : (u, v) ∈ pathArcs p) : u ≠ v := by
  induction p with
  | nil => simp at he
  | cons x rest ih =>
    rcases rest with _ | ⟨y, rest'⟩
    · simp at he
    · obtain ⟨hx, hnodup⟩ := List.nodup_cons.mp hp
      simp only [pathArcs_cons_cons, List.mem_cons] at he
      rcases he with ⟨rfl, rfl⟩ | he'
      · intro hxy
        exact hx (hxy ▸ List.mem_cons_self)
      · exact ih hnodup he'

theorem map_fst_pathArcs_sublist (p : List V) : List.Sublist ((pathArcs p).map Prod.fst) p := by
  induction p with
  | nil => exact List.Sublist.slnil
  | cons x rest ih =>
    rcases rest with _ | ⟨y, rest'⟩
    · exact List.nil_sublist [x]
    · simp only [pathArcs_cons_cons, List.map_cons]
      exact List.Sublist.cons_cons x ih

theorem nodup_pathArcs {p : List V} (hp : p.Nodup) : (pathArcs p).Nodup :=
  List.Nodup.of_map Prod.fst (hp.sublist (map_fst_pathArcs_sublist p))

theorem not_swap_mem_pathArcs {p : List V} (hp : p.Nodup) {u v : V}
    (he : (u, v) ∈ pathArcs p) : (v, u) ∉ pathArcs p := by
  induction p with
  | nil => simp at he
  | cons x rest ih =>
    rcases rest with _ | ⟨y, rest'⟩
    · simp at he
    · obtain ⟨hx, hnodup⟩ := List.nodup_cons.mp hp
      simp only [pathArcs_cons_cons, List.mem_cons, Prod.mk.injEq] at he ⊢
      intro hswap
      rcases he with ⟨rfl, rfl⟩ | he'
      · rcases hswap with ⟨hxy, _⟩ | hswap'
        · exact hx (hxy ▸ List.mem_cons_self)
        · exact hx (snd_mem_of_mem_pathArcs hswap')
      · rcases hswap with ⟨rfl, rfl⟩ | hswap'
        · exact hx (snd_mem_of_mem_pathArcs he')
        · exact ih hnodup he' hswap'

private theorem pathArcs_suffix {l₁ l₂ : List V} (h : l₁ <:+ l₂) :
    pathArcs l₁ <:+ pathArcs l₂ := by
  obtain ⟨pre, rfl⟩ := h
  induction pre with
  | nil => exact List.suffix_refl _
  | cons a pre' ih =>
    refine ih.trans ?_
    simp only [List.cons_append]
    rcases htail : pre' ++ l₁ with _ | ⟨b, rest⟩
    · exact List.suffix_refl []
    · exact List.suffix_cons (a, b) (pathArcs (b :: rest))

private theorem suffixFrom_eq_cons_and_suffix [DecidableEq V] {ys : List V} {x : V} (hx : x ∈ ys) :
    ∃ rest, suffixFrom x ys = x :: rest ∧ (x :: rest) <:+ ys := by
  induction ys with
  | nil => simp at hx
  | cons y ys' ih =>
    simp only [suffixFrom]
    by_cases hxy : y = x
    · subst hxy
      exact ⟨ys', by simp, List.suffix_refl _⟩
    · have hx' : x ∈ ys' := by
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact absurd rfl hxy
        · exact hmem
      obtain ⟨rest, hdrop, hsuf⟩ := ih hx'
      exact ⟨rest, by simp [hxy, hdrop], hsuf.trans (List.suffix_cons y ys')⟩

theorem head?_loopErase [DecidableEq V] (p : List V) : (loopErase p).head? = p.head? := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
    rw [loopErase]
    split_ifs with hx
    · obtain ⟨rest, hdrop, _⟩ := suffixFrom_eq_cons_and_suffix hx
      rw [hdrop]
      rfl
    · rfl

theorem getLast?_loopErase [DecidableEq V] (p : List V) :
    (loopErase p).getLast? = p.getLast? := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
    rcases xs with _ | ⟨y, xs'⟩
    · rfl
    · have hys_ne : loopErase (y :: xs') ≠ [] := by
        intro hnil
        have hhead := head?_loopErase (y :: xs')
        rw [hnil] at hhead
        simp at hhead
      rw [loopErase]
      split_ifs with hx
      · obtain ⟨rest, hdrop, hsuf⟩ := suffixFrom_eq_cons_and_suffix hx
        obtain ⟨pre, hpre⟩ := hsuf
        rw [hdrop]
        have hlast : (pre ++ x :: rest).getLast? = (x :: rest).getLast? :=
          List.getLast?_append_of_ne_nil pre (List.cons_ne_nil x rest)
        rw [← hlast, hpre, ih, List.getLast?_cons_cons]
      · rw [List.getLast?_cons_of_ne_nil hys_ne, ih, List.getLast?_cons_cons]

theorem nodup_loopErase [DecidableEq V] (p : List V) : (loopErase p).Nodup := by
  induction p with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [loopErase]
    split_ifs with hx
    · obtain ⟨rest, hdrop, hsuf⟩ := suffixFrom_eq_cons_and_suffix hx
      rw [hdrop]
      exact ih.sublist hsuf.sublist
    · exact List.nodup_cons.mpr ⟨hx, ih⟩

theorem mem_pathArcs_loopErase [DecidableEq V] {p : List V} {e : V × V}
    (he : e ∈ pathArcs (loopErase p)) : e ∈ pathArcs p := by
  induction p with
  | nil => simp [loopErase] at he
  | cons x xs ih =>
    rw [loopErase] at he
    split_ifs at he with hx
    · obtain ⟨rest, hdrop, hsuf⟩ := suffixFrom_eq_cons_and_suffix hx
      rw [hdrop] at he
      have he_ys : e ∈ pathArcs (loopErase xs) := (pathArcs_suffix hsuf).subset he
      have he_xs : e ∈ pathArcs xs := ih he_ys
      rcases xs with _ | ⟨y, xs'⟩
      · simp at he_xs
      · exact List.mem_cons_of_mem (x, y) he_xs
    · rcases xs with _ | ⟨y, xs'⟩
      · simp [loopErase] at he
      · have hhead := head?_loopErase (y :: xs')
        rcases hys : loopErase (y :: xs') with _ | ⟨z, zs⟩
        · rw [hys] at hhead
          simp at hhead
        · rw [hys] at hhead he
          simp only [List.head?_cons, Option.some.injEq] at hhead
          subst hhead
          simp only [pathArcs_cons_cons, List.mem_cons] at he ⊢
          rcases he with rfl | he'
          · exact .inl rfl
          · exact .inr (ih (hys ▸ he'))

theorem length_loopErase_le [DecidableEq V] (p : List V) : (loopErase p).length ≤ p.length := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
    rw [loopErase]
    split_ifs with hx
    · obtain ⟨rest, hdrop, hsuf⟩ := suffixFrom_eq_cons_and_suffix hx
      rw [hdrop]
      exact le_trans hsuf.sublist.length_le (Nat.le_succ_of_le ih)
    · simp only [List.length_cons]
      omega

private theorem sum_ite_mem_fst [Fintype V] [DecidableEq V] {q : List (V × V)} (hq : q.Nodup)
    (u : V) :
    (∑ v : V, if (u, v) ∈ q then (1 : ℤ) else 0) =
      (q.map fun e => if e.1 = u then (1 : ℤ) else 0).sum := by
  induction q with
  | nil => simp
  | cons e q' ih =>
    rcases e with ⟨a, b⟩
    obtain ⟨hab, hq'⟩ := List.nodup_cons.mp hq
    have hsplit : ∀ v : V,
        (if (u, v) ∈ (a, b) :: q' then (1 : ℤ) else 0) =
          (if u = a ∧ v = b then 1 else 0) + (if (u, v) ∈ q' then 1 else 0) := by
      intro v
      simp only [List.mem_cons, Prod.mk.injEq]
      by_cases huv : u = a ∧ v = b
      · rcases huv with ⟨rfl, rfl⟩
        simp [hab]
      · simp [huv]
    simp only [hsplit, Finset.sum_add_distrib, List.map_cons, List.sum_cons, ih hq']
    congr 1
    rw [Finset.sum_eq_single b]
    · by_cases hua : u = a
      · subst hua
        simp
      · have hne : a ≠ u := fun h => hua h.symm
        simp [hua, hne]
    · intro v _ hvb
      simp [hvb]
    · intro hb
      exact absurd (Finset.mem_univ b) hb

private theorem sum_ite_mem_snd [Fintype V] [DecidableEq V] {q : List (V × V)} (hq : q.Nodup)
    (u : V) :
    (∑ v : V, if (v, u) ∈ q then (1 : ℤ) else 0) =
      (q.map fun e => if e.2 = u then (1 : ℤ) else 0).sum := by
  induction q with
  | nil => simp
  | cons e q' ih =>
    rcases e with ⟨a, b⟩
    obtain ⟨hab, hq'⟩ := List.nodup_cons.mp hq
    have hsplit : ∀ v : V,
        (if (v, u) ∈ (a, b) :: q' then (1 : ℤ) else 0) =
          (if v = a ∧ u = b then 1 else 0) + (if (v, u) ∈ q' then 1 else 0) := by
      intro v
      simp only [List.mem_cons, Prod.mk.injEq]
      by_cases hvu : v = a ∧ u = b
      · rcases hvu with ⟨rfl, rfl⟩
        simp [hab]
      · simp [hvu]
    simp only [hsplit, Finset.sum_add_distrib, List.map_cons, List.sum_cons, ih hq']
    congr 1
    rw [Finset.sum_eq_single a]
    · by_cases hub : u = b
      · subst hub
        simp
      · have hne : b ≠ u := fun h => hub h.symm
        simp [hub, hne]
    · intro v _ hva
      simp [hva]
    · intro ha
      exact absurd (Finset.mem_univ a) ha

private theorem map_pathArcs_sub_sum [DecidableEq V] {p : List V} {s t : V}
    (hs : p.head? = some s) (ht : p.getLast? = some t) (u : V) :
    ((pathArcs p).map fun e =>
      (if e.1 = u then (1 : ℤ) else 0) - (if e.2 = u then 1 else 0)).sum =
      (if s = u then 1 else 0) - (if t = u then 1 else 0) := by
  induction p generalizing s with
  | nil => simp at hs
  | cons x rest ih =>
    simp only [List.head?_cons, Option.some.injEq] at hs
    subst hs
    rcases rest with _ | ⟨y, rest'⟩
    · simp only [List.getLast?_singleton, Option.some.injEq] at ht
      subst ht
      simp
    · simp only [pathArcs_cons_cons, List.map_cons, List.sum_cons]
      have hrec := ih (s := y) rfl (by simpa using ht)
      omega

theorem sum_pathArcs_sign [Fintype V] [DecidableEq V] {p : List V} {s t : V}
    (hp : p.Nodup) (hs : p.head? = some s) (ht : p.getLast? = some t) (u : V) :
    (∑ v : V, ((if (u, v) ∈ pathArcs p then (1 : ℤ) else 0) -
      (if (v, u) ∈ pathArcs p then (1 : ℤ) else 0))) =
      (if s = u then 1 else 0) - (if t = u then 1 else 0) := by
  have hnodup := nodup_pathArcs hp
  rw [Finset.sum_sub_distrib, sum_ite_mem_fst hnodup u, sum_ite_mem_snd hnodup u]
  have hmap :
      ((pathArcs p).map fun e => if e.1 = u then (1 : ℤ) else 0).sum -
        ((pathArcs p).map fun e => if e.2 = u then (1 : ℤ) else 0).sum =
      ((pathArcs p).map fun e =>
        (if e.1 = u then (1 : ℤ) else 0) - (if e.2 = u then 1 else 0)).sum := by
    induction pathArcs p with
    | nil => simp
    | cons e es ihe =>
      simp only [List.map_cons, List.sum_cons]
      omega
  rw [hmap, map_pathArcs_sub_sum hs ht u]

end PathLemmas

namespace Network

variable {V : Type*}

section CutsAndFlows

variable [Fintype V] (N : Network V)

/-- A vertex set `S` is an `s`-`t` cut when it contains the source `N.s` and excludes the sink
`N.t`. -/
@[expose] def IsCut (S : Finset V) : Prop := N.s ∈ S ∧ N.t ∉ S

instance instDecidableIsCut [DecidableEq V] (S : Finset V) :
    Decidable (N.IsCut S) := by
  unfold IsCut
  infer_instance

/-- Forward capacity of an `s`-`t` cut `S`: total capacity of arcs from `S` to `Finset.univ \ S`.
-/
@[expose] def cutCapacity [DecidableEq V] (S : Finset V) : ℕ :=
  ∑ u ∈ S, ∑ v ∈ Finset.univ \ S, N.cap u v

/-- `S` is a minimum `s`-`t` cut if it is an `s`-`t` cut of minimum `cutCapacity`. -/
@[expose] def IsMinCut [DecidableEq V] (S : Finset V) : Prop :=
  N.IsCut S ∧ ∀ T, N.IsCut T → N.cutCapacity S ≤ N.cutCapacity T

/-- A feasible integral flow on `N`: non-negative arc flows bounded by `N.cap` and conserved at
every vertex `v ≠ N.s, N.t`. -/
@[ext]
structure Flow where
  /-- Integral flow assigned to each directed arc `(u, v)`. -/
  toFun : V → V → ℕ
  /-- Capacity bound on every directed arc. -/
  le_cap : ∀ u v, toFun u v ≤ N.cap u v
  /-- Flow conservation (inflow equals outflow) at every intermediate vertex. -/
  conserve : ∀ v, v ≠ N.s → v ≠ N.t → ∑ u, toFun u v = ∑ w, toFun v w

instance : CoeFun N.Flow (fun _ => V → V → ℕ) := ⟨Flow.toFun⟩

namespace Flow

variable {N}

/-- The identically zero feasible flow on `N`. -/
@[expose] def zero (N : Network V) : N.Flow where
  toFun _ _ := 0
  le_cap _ _ := Nat.zero_le _
  conserve _ _ _ := rfl

@[simp]
theorem zero_apply (u v : V) : Flow.zero N u v = 0 := rfl

/-- Net outflow from vertex `v`: total outgoing flow minus total incoming flow. -/
@[expose] def netOut (f : N.Flow) (v : V) : ℤ :=
  (∑ w, (f v w : ℤ)) - (∑ u, (f u v : ℤ))

/-- Value of a flow `f`: net outflow from the source `N.s`. -/
@[expose] def value (f : N.Flow) : ℤ := f.netOut N.s

@[simp]
theorem value_zero : (Flow.zero N).value = 0 := by
  simp [value, netOut]

theorem netOut_eq_zero (f : N.Flow) {v : V} (hvs : v ≠ N.s) (hvt : v ≠ N.t) :
    f.netOut v = 0 := by
  unfold netOut
  have h := congrArg (Nat.cast (R := ℤ)) (f.conserve v hvs hvt)
  rw [Nat.cast_sum, Nat.cast_sum] at h
  omega

theorem netOut_eq_sum_sub (f : N.Flow) (u : V) :
    f.netOut u = ∑ v, ((f u v : ℤ) - (f v u : ℤ)) := by
  rw [netOut, Finset.sum_sub_distrib]

/-- A feasible flow `f` is a maximum flow if every feasible flow on `N` has value at most
`f.value`. -/
@[expose] def IsMaxFlow (f : N.Flow) : Prop :=
  ∀ g : N.Flow, g.value ≤ f.value

theorem value_nonneg_of_isMaxFlow {f : N.Flow} (hf : f.IsMaxFlow) : 0 ≤ f.value := by
  simpa using hf (Flow.zero N)

private theorem sum_univ_eq_add_sdiff [DecidableEq V] (S : Finset V) (g : V → ℤ) :
    ∑ v, g v = (∑ v ∈ S, g v) + ∑ v ∈ Finset.univ \ S, g v := by
  rw [← Finset.sum_union disjoint_sdiff_self_right,
    Finset.union_sdiff_of_subset (Finset.subset_univ S)]

/-- **Net-flow-across-cut lemma** ([FordFulkerson1962], Chapter I, Section 4, Lemma 4.1; [CLRS2009],
Lemma 26.4, p. 717): for every feasible flow `f` and `s`-`t` cut `S`, `f.value` equals the total
flow leaving `S` minus the total flow entering `S`. -/
theorem value_eq_netFlow_across_cut [DecidableEq V] (f : N.Flow) {S : Finset V} (hS : N.IsCut S) :
    f.value =
      (∑ u ∈ S, ∑ v ∈ Finset.univ \ S, (f u v : ℤ)) -
        (∑ u ∈ S, ∑ v ∈ Finset.univ \ S, (f v u : ℤ)) := by
  have hval : f.value = ∑ u ∈ S, f.netOut u := by
    symm
    refine Finset.sum_eq_single N.s (fun u hu hus => ?_) (fun hs => absurd hS.1 hs)
    have hut : u ≠ N.t := fun h => hS.2 (h ▸ hu)
    exact f.netOut_eq_zero hus hut
  rw [hval]
  simp only [netOut]
  rw [Finset.sum_sub_distrib]
  have hsplit₁ : ∑ u ∈ S, ∑ v, (f u v : ℤ) =
      (∑ u ∈ S, ∑ v ∈ S, (f u v : ℤ)) + (∑ u ∈ S, ∑ v ∈ Finset.univ \ S, (f u v : ℤ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => sum_univ_eq_add_sdiff S _
  have hsplit₂ : ∑ u ∈ S, ∑ v, (f v u : ℤ) =
      (∑ u ∈ S, ∑ v ∈ S, (f v u : ℤ)) + (∑ u ∈ S, ∑ v ∈ Finset.univ \ S, (f v u : ℤ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => sum_univ_eq_add_sdiff S _
  have hcomm : (∑ u ∈ S, ∑ v ∈ S, (f v u : ℤ)) = ∑ u ∈ S, ∑ v ∈ S, (f u v : ℤ) :=
    Finset.sum_comm
  omega

/-- **Weak duality** ([FordFulkerson1956], p. 400; [CLRS2009], Corollary 26.5, p. 718): the value
of any feasible flow is bounded above by the capacity of any `s`-`t` cut. -/
theorem value_le_cutCapacity [DecidableEq V] (f : N.Flow) {S : Finset V} (hS : N.IsCut S) :
    f.value ≤ (N.cutCapacity S : ℤ) := by
  rw [f.value_eq_netFlow_across_cut hS]
  have hle : ∑ u ∈ S, ∑ v ∈ Finset.univ \ S, (f u v : ℤ) ≤
      ∑ u ∈ S, ∑ v ∈ Finset.univ \ S, (N.cap u v : ℤ) :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => by
      have := f.le_cap u v
      omega
  have hnonneg : 0 ≤ ∑ u ∈ S, ∑ v ∈ Finset.univ \ S, (f v u : ℤ) :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => by omega
  have hcast : (N.cutCapacity S : ℤ) = ∑ u ∈ S, ∑ v ∈ Finset.univ \ S, (N.cap u v : ℤ) := by
    simp only [cutCapacity, Nat.cast_sum]
  omega

/-- Singleton source cut bound when `N.s ≠ N.t`. -/
theorem value_le_source_outCap [DecidableEq V] (f : N.Flow) (hst : N.s ≠ N.t) :
    f.value ≤ (N.cutCapacity {N.s} : ℤ) :=
  f.value_le_cutCapacity ⟨Finset.mem_singleton_self N.s, by simp [hst.symm]⟩

/-- Residual capacity of directed pair `(u, v)` with respect to `f`: unused forward capacity
`N.cap u v - f u v` plus cancellable reverse flow `f v u`. -/
@[expose] def resCap (f : N.Flow) (u v : V) : ℕ :=
  (N.cap u v - f u v) + f v u

theorem resCap_coe (f : N.Flow) (u v : V) :
    (f.resCap u v : ℤ) = (N.cap u v : ℤ) - ((f u v : ℤ) - (f v u : ℤ)) := by
  unfold resCap
  have h := f.le_cap u v
  omega

theorem resCap_le_cap_add_cap (f : N.Flow) (u v : V) :
    f.resCap u v ≤ N.cap u v + N.cap v u := by
  unfold resCap
  have h := f.le_cap v u
  omega

/-- A simple residual `s`-`t` augmenting path for `f`: a duplicate-free vertex walk from `N.s` to
`N.t` whose consecutive arcs all have positive residual capacity. -/
@[expose] def IsAugmentingPath (f : N.Flow) (p : List V) : Prop :=
  p.Nodup ∧ p.head? = some N.s ∧ p.getLast? = some N.t ∧
    ∀ e ∈ pathArcs p, 0 < f.resCap e.1 e.2

theorem IsAugmentingPath.nodup {f : N.Flow} {p : List V} (hp : f.IsAugmentingPath p) :
    p.Nodup :=
  let ⟨h, _, _, _⟩ := hp; h

theorem IsAugmentingPath.head? {f : N.Flow} {p : List V} (hp : f.IsAugmentingPath p) :
    p.head? = some N.s :=
  let ⟨_, h, _, _⟩ := hp; h

theorem IsAugmentingPath.getLast? {f : N.Flow} {p : List V} (hp : f.IsAugmentingPath p) :
    p.getLast? = some N.t :=
  let ⟨_, _, h, _⟩ := hp; h

theorem IsAugmentingPath.pos_resCap {f : N.Flow} {p : List V} (hp : f.IsAugmentingPath p)
    {e : V × V} (he : e ∈ pathArcs p) : 0 < f.resCap e.1 e.2 :=
  let ⟨_, _, _, h⟩ := hp; h e he

instance instDecidableIsAugmentingPath [DecidableEq V] (f : N.Flow) (p : List V) :
    Decidable (f.IsAugmentingPath p) := by
  unfold IsAugmentingPath
  infer_instance

private theorem foldl_min_le_init {α : Type*} (w : α → ℕ) (es : List α) (init : ℕ) :
    es.foldl (fun acc a => min acc (w a)) init ≤ init := by
  induction es generalizing init with
  | nil => exact le_rfl
  | cons a es' ih => exact le_trans (ih (min init (w a))) (Nat.min_le_left init (w a))

private theorem foldl_min_le_mem {α : Type*} (w : α → ℕ) {es : List α} (init : ℕ) {x : α}
    (hx : x ∈ es) :
    es.foldl (fun acc a => min acc (w a)) init ≤ w x := by
  induction es generalizing init with
  | nil => simp at hx
  | cons a es' ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact le_trans (foldl_min_le_init w es' (min init (w x))) (Nat.min_le_right init (w x))
    · exact ih (min init (w a)) hx'

private theorem foldl_min_eq_init_or_mem {α : Type*} (w : α → ℕ) (es : List α) (init : ℕ) :
    es.foldl (fun acc a => min acc (w a)) init = init ∨
      ∃ x ∈ es, es.foldl (fun acc a => min acc (w a)) init = w x := by
  induction es generalizing init with
  | nil => exact .inl rfl
  | cons a es' ih =>
    simp only [List.foldl_cons]
    by_cases hle : init ≤ w a
    · rw [Nat.min_eq_left hle]
      rcases ih init with hinit | ⟨x, hx, heq⟩
      · exact .inl hinit
      · exact .inr ⟨x, List.mem_cons_of_mem a hx, heq⟩
    · rw [Nat.min_eq_right (Nat.le_of_not_le hle)]
      rcases ih (w a) with hinit | ⟨x, hx, heq⟩
      · exact .inr ⟨a, List.mem_cons_self, hinit⟩
      · exact .inr ⟨x, List.mem_cons_of_mem a hx, heq⟩

/-- Bottleneck residual capacity along vertex list `p` (`0` when `pathArcs p` is empty). -/
@[expose] def bottleneck (f : N.Flow) (p : List V) : ℕ :=
  match pathArcs p with
  | [] => 0
  | e :: es => es.foldl (fun acc b => min acc (f.resCap b.1 b.2)) (f.resCap e.1 e.2)

theorem bottleneck_le_resCap (f : N.Flow) {p : List V} {e : V × V} (he : e ∈ pathArcs p) :
    f.bottleneck p ≤ f.resCap e.1 e.2 := by
  unfold bottleneck
  rcases h : pathArcs p with _ | ⟨e₀, es⟩
  · rw [h] at he
    simp at he
  · dsimp only
    rw [h] at he
    rcases List.mem_cons.mp he with rfl | he'
    · exact foldl_min_le_init (fun b : V × V => f.resCap b.1 b.2) es (f.resCap e.1 e.2)
    · exact foldl_min_le_mem (fun b : V × V => f.resCap b.1 b.2) (f.resCap e₀.1 e₀.2) he'

theorem exists_mem_pathArcs_resCap_eq_bottleneck (f : N.Flow) {p : List V}
    (hp : pathArcs p ≠ []) :
    ∃ e ∈ pathArcs p, f.resCap e.1 e.2 = f.bottleneck p := by
  unfold bottleneck
  rcases h : pathArcs p with _ | ⟨e₀, es⟩
  · exact absurd h hp
  · dsimp only
    rcases foldl_min_eq_init_or_mem (fun b : V × V => f.resCap b.1 b.2) es
        (f.resCap e₀.1 e₀.2) with hinit | ⟨e, he, heq⟩
    · exact ⟨e₀, List.mem_cons_self, hinit.symm⟩
    · exact ⟨e, List.mem_cons_of_mem e₀ he, heq.symm⟩

theorem bottleneck_pos (f : N.Flow) (hst : N.s ≠ N.t) {p : List V} (hp : f.IsAugmentingPath p) :
    0 < f.bottleneck p := by
  obtain ⟨_, hs, ht, hpos⟩ := hp
  have hne := pathArcs_ne_nil_of_head?_ne_getLast? hst hs ht
  obtain ⟨e, he, heq⟩ := f.exists_mem_pathArcs_resCap_eq_bottleneck hne
  rw [← heq]
  exact hpos e he

/-- Pointwise arc-flow update pushing `δ` units along simple path `p` (cancelling reverse flow
first before adding forward flow). -/
@[expose] def augmentFun [DecidableEq V] (f : N.Flow) (p : List V) (δ : ℕ) (u v : V) : ℕ :=
  if (u, v) ∈ pathArcs p then
    f u v + (δ - min δ (f v u))
  else if (v, u) ∈ pathArcs p then
    f u v - min δ (f u v)
  else
    f u v

private theorem augmentFun_sub_eq [DecidableEq V] (f : N.Flow) {p : List V} (hp : p.Nodup)
    (δ : ℕ) (u v : V) :
    (f.augmentFun p δ u v : ℤ) - (f.augmentFun p δ v u : ℤ) =
      ((f u v : ℤ) - (f v u : ℤ)) +
        (δ : ℤ) * ((if (u, v) ∈ pathArcs p then 1 else 0) -
          (if (v, u) ∈ pathArcs p then 1 else 0)) := by
  unfold augmentFun
  by_cases huv : (u, v) ∈ pathArcs p
  · have hvu : (v, u) ∉ pathArcs p := not_swap_mem_pathArcs hp huv
    simp only [huv, hvu, ↓reduceIte]
    omega
  · by_cases hvu : (v, u) ∈ pathArcs p
    · simp only [huv, hvu, ↓reduceIte]
      omega
    · simp [huv, hvu]

/-- Push `δ` units of flow along a simple `s`-`t` path `p` when `δ ≤ f.resCap e.1 e.2` on every
arc of `p`. -/
@[expose] def augment [DecidableEq V] (f : N.Flow) (p : List V) (hp : p.Nodup)
    (hs : p.head? = some N.s) (ht : p.getLast? = some N.t) (δ : ℕ)
    (hδ : ∀ e ∈ pathArcs p, δ ≤ f.resCap e.1 e.2) : N.Flow where
  toFun := f.augmentFun p δ
  le_cap u v := by
    unfold augmentFun
    split_ifs with huv hvu
    · have hres : δ ≤ f.resCap u v := hδ (u, v) huv
      unfold resCap at hres
      have hcap := f.le_cap u v
      omega
    · exact le_trans (Nat.sub_le _ _) (f.le_cap u v)
    · exact f.le_cap u v
  conserve v hvs hvt := by
    have hsum : (∑ w : V, ((f.augmentFun p δ v w : ℤ) - (f.augmentFun p δ w v : ℤ))) = 0 := by
      simp only [f.augmentFun_sub_eq hp δ v]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_pathArcs_sign hp hs ht v,
        ← f.netOut_eq_sum_sub v, f.netOut_eq_zero hvs hvt]
      have hsv : N.s ≠ v := hvs.symm
      have htv : N.t ≠ v := hvt.symm
      simp [hsv, htv]
    rw [Finset.sum_sub_distrib] at hsum
    have heq : ((∑ u : V, f.augmentFun p δ u v : ℕ) : ℤ) =
        ((∑ w : V, f.augmentFun p δ v w : ℕ) : ℤ) := by
      rw [Nat.cast_sum, Nat.cast_sum]
      omega
    exact Int.ofNat.inj heq

theorem value_augment [DecidableEq V] (f : N.Flow) (hst : N.s ≠ N.t) {p : List V}
    (hp : p.Nodup) (hs : p.head? = some N.s) (ht : p.getLast? = some N.t) (δ : ℕ)
    (hδ : ∀ e ∈ pathArcs p, δ ≤ f.resCap e.1 e.2) :
    (f.augment p hp hs ht δ hδ).value = f.value + (δ : ℤ) := by
  have hts : N.t ≠ N.s := hst.symm
  rw [value, netOut_eq_sum_sub]
  change ∑ v : V, ((f.augmentFun p δ N.s v : ℤ) - (f.augmentFun p δ v N.s : ℤ)) =
    f.value + (δ : ℤ)
  simp only [f.augmentFun_sub_eq hp δ N.s]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_pathArcs_sign hp hs ht N.s]
  have hbase : (∑ x : V, ((f N.s x : ℤ) - (f x N.s : ℤ))) = f.value :=
    (f.netOut_eq_sum_sub N.s).symm
  rw [hbase]
  simp [hts]

theorem resCap_augment [DecidableEq V] (f : N.Flow) {p : List V}
    (hp : p.Nodup) (hs : p.head? = some N.s) (ht : p.getLast? = some N.t) (δ : ℕ)
    (hδ : ∀ e ∈ pathArcs p, δ ≤ f.resCap e.1 e.2) (u v : V) :
    (f.augment p hp hs ht δ hδ).resCap u v =
      if (u, v) ∈ pathArcs p then f.resCap u v - δ
      else if (v, u) ∈ pathArcs p then f.resCap u v + δ
      else f.resCap u v := by
  have hcoe₁ := (f.augment p hp hs ht δ hδ).resCap_coe u v
  have hcoe₂ := f.resCap_coe u v
  have hdiff := f.augmentFun_sub_eq hp δ u v
  change ((f.augment p hp hs ht δ hδ).resCap u v : ℤ) = _ at hcoe₁
  have hfun : (f.augment p hp hs ht δ hδ : V → V → ℕ) = f.augmentFun p δ := rfl
  rw [hfun] at hcoe₁
  by_cases huv : (u, v) ∈ pathArcs p
  · have hvu : (v, u) ∉ pathArcs p := not_swap_mem_pathArcs hp huv
    have hle := hδ (u, v) huv
    simp only [huv, hvu, ↓reduceIte] at hdiff ⊢
    omega
  · by_cases hvu : (v, u) ∈ pathArcs p
    · simp only [huv, hvu, ↓reduceIte] at hdiff ⊢
      omega
    · simp only [huv, hvu, ↓reduceIte] at hdiff ⊢
      omega

/-- Bottleneck augmentation along an augmenting path `p`. -/
@[expose] def augmentByBottleneck [DecidableEq V] (f : N.Flow) (p : List V)
    (hp : f.IsAugmentingPath p) : N.Flow :=
  f.augment p hp.nodup hp.head? hp.getLast? (f.bottleneck p) (fun _ he => f.bottleneck_le_resCap he)

theorem value_augmentByBottleneck [DecidableEq V] (f : N.Flow) (hst : N.s ≠ N.t) {p : List V}
    (hp : f.IsAugmentingPath p) :
    (f.augmentByBottleneck p hp).value = f.value + (f.bottleneck p : ℤ) :=
  f.value_augment hst hp.nodup hp.head? hp.getLast? (f.bottleneck p)
    (fun _ he => f.bottleneck_le_resCap he)

theorem lt_value_augmentByBottleneck [DecidableEq V] (f : N.Flow) (hst : N.s ≠ N.t) {p : List V}
    (hp : f.IsAugmentingPath p) :
    f.value < (f.augmentByBottleneck p hp).value := by
  rw [f.value_augmentByBottleneck hst hp]
  have hpos := f.bottleneck_pos hst hp
  omega

/-- Residual reachability: `v` is reachable from `u` via positive-residual-capacity arcs. -/
@[expose] def ResReachable (f : N.Flow) (u v : V) : Prop :=
  Relation.ReflTransGen (fun x y => 0 < f.resCap x y) u v

private theorem exists_walk_of_resReachable (f : N.Flow) {u v : V} (h : f.ResReachable u v) :
    ∃ p : List V, p.head? = some u ∧ p.getLast? = some v ∧
      ∀ e ∈ pathArcs p, 0 < f.resCap e.1 e.2 := by
  induction h with
  | refl => exact ⟨[u], rfl, rfl, by simp⟩
  | @tail b c _ hstep ih =>
    obtain ⟨p, hhead, hlast, harcs⟩ := ih
    have hp_ne : p ≠ [] := by
      intro hnil
      rw [hnil] at hhead
      simp at hhead
    refine ⟨p ++ [c], ?_, ?_, ?_⟩
    · rw [List.head?_append_of_ne_nil p hp_ne]
      exact hhead
    · simp
    · intro e he
      rw [pathArcs_append_singleton hp_ne hlast, List.mem_append, List.mem_singleton] at he
      rcases he with he' | rfl
      · exact harcs e he'
      · exact hstep

theorem exists_augmentingPath_iff_resReachable (f : N.Flow) :
    (∃ p, f.IsAugmentingPath p) ↔ f.ResReachable N.s N.t := by
  classical
  constructor
  · rintro ⟨p, _, hs, ht, harcs⟩
    have hwalk : ∀ q : List V, ∀ u v : V,
        q.head? = some u → q.getLast? = some v →
        (∀ e ∈ pathArcs q, 0 < f.resCap e.1 e.2) → f.ResReachable u v := by
      intro q
      induction q with
      | nil => intro u v hu; simp at hu
      | cons x rest ih =>
        intro u v hu hv hq
        simp only [List.head?_cons, Option.some.injEq] at hu
        subst hu
        rcases rest with _ | ⟨y, rest'⟩
        · simp only [List.getLast?_singleton, Option.some.injEq] at hv
          subst hv
          exact .refl
        · have hstep : 0 < f.resCap x y := hq (x, y) List.mem_cons_self
          have htail : f.ResReachable y v :=
            ih y v rfl (by simpa using hv) (fun e he => hq e (List.mem_cons_of_mem _ he))
          exact Relation.ReflTransGen.head hstep htail
    exact hwalk p N.s N.t hs ht harcs
  · intro hreach
    obtain ⟨p, hs, ht, harcs⟩ := f.exists_walk_of_resReachable hreach
    refine ⟨loopErase p, nodup_loopErase p, ?_, ?_, ?_⟩
    · rw [head?_loopErase, hs]
    · rw [getLast?_loopErase, ht]
    · intro e he
      exact harcs e (mem_pathArcs_loopErase he)

/-- Residual-reachability cut associated with a flow `f`: all vertices reachable from `N.s` along
positive-residual-capacity arcs. -/
noncomputable def reachableCut (f : N.Flow) : Finset V :=
  open scoped Classical in
  Finset.univ.filter fun v => f.ResReachable N.s v

theorem mem_reachableCut_iff (f : N.Flow) (v : V) :
    v ∈ f.reachableCut ↔ f.ResReachable N.s v := by
  classical
  simp [reachableCut]

theorem reachableCut_isCut (f : N.Flow) (hno : ¬ ∃ p, f.IsAugmentingPath p) :
    N.IsCut f.reachableCut := by
  refine ⟨(f.mem_reachableCut_iff N.s).mpr .refl, ?_⟩
  rw [f.mem_reachableCut_iff, ← f.exists_augmentingPath_iff_resReachable]
  exact hno

theorem value_eq_cutCapacity_reachableCut [DecidableEq V] (f : N.Flow)
    (hno : ¬ ∃ p, f.IsAugmentingPath p) :
    f.value = (N.cutCapacity f.reachableCut : ℤ) := by
  have hcut := f.reachableCut_isCut hno
  rw [f.value_eq_netFlow_across_cut hcut]
  have hsat : ∀ u ∈ f.reachableCut, ∀ v ∈ Finset.univ \ f.reachableCut,
      f u v = N.cap u v ∧ f v u = 0 := by
    intro u hu v hv
    have hu_r : f.ResReachable N.s u := (f.mem_reachableCut_iff u).mp hu
    have hv_nr : ¬ f.ResReachable N.s v := by
      rw [Finset.mem_sdiff, f.mem_reachableCut_iff] at hv
      exact hv.2
    have hzero : f.resCap u v = 0 := by
      by_contra hpos
      exact hv_nr (hu_r.tail (Nat.pos_of_ne_zero hpos))
    unfold resCap at hzero
    have hle := f.le_cap u v
    omega
  have hfwd : (∑ u ∈ f.reachableCut, ∑ v ∈ Finset.univ \ f.reachableCut, (f u v : ℤ)) =
      ∑ u ∈ f.reachableCut, ∑ v ∈ Finset.univ \ f.reachableCut, (N.cap u v : ℤ) :=
    Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => by
      rw [(hsat u hu v hv).1]
  have hbwd : (∑ u ∈ f.reachableCut, ∑ v ∈ Finset.univ \ f.reachableCut, (f v u : ℤ)) = 0 :=
    Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun v hv => by
      simp [(hsat u hu v hv).2]
  rw [hfwd, hbwd, sub_zero]
  simp only [cutCapacity, Nat.cast_sum]

/-- **Ford–Fulkerson augmenting-path characterization** ([FordFulkerson1956], Theorem 1,
pp. 400–402; [CLRS2009], Theorem 26.6, p. 720, `(1) ↔ (2)`): when `N.s ≠ N.t`, a feasible flow `f`
is a maximum flow if and only if it admits no residual `s`-`t` augmenting path. -/
theorem isMaxFlow_iff_not_exists_augmentingPath (f : N.Flow) (hst : N.s ≠ N.t) :
    f.IsMaxFlow ↔ ¬ ∃ p, f.IsAugmentingPath p := by
  classical
  constructor
  · rintro hf ⟨p, hp⟩
    have hlt := f.lt_value_augmentByBottleneck hst hp
    have hle := hf (f.augmentByBottleneck p hp)
    omega
  · intro hno g
    rw [f.value_eq_cutCapacity_reachableCut hno]
    exact g.value_le_cutCapacity (f.reachableCut_isCut hno)

/-- **Ford–Fulkerson strong-duality characterization** ([FordFulkerson1956], Theorem 1,
pp. 400–402; [CLRS2009], Theorem 26.6, p. 720, `(1) ↔ (3)`): when `N.s ≠ N.t`, a feasible flow `f`
is a maximum flow if and only if `f.value` equals the capacity of some `s`-`t` cut `S` (which is
then automatically a minimum `s`-`t` cut). -/
theorem isMaxFlow_iff_exists_cut_value_eq [DecidableEq V] (f : N.Flow) (hst : N.s ≠ N.t) :
    f.IsMaxFlow ↔ ∃ S, N.IsCut S ∧ f.value = (N.cutCapacity S : ℤ) := by
  constructor
  · intro hf
    have hno := (f.isMaxFlow_iff_not_exists_augmentingPath hst).mp hf
    exact ⟨f.reachableCut, f.reachableCut_isCut hno, f.value_eq_cutCapacity_reachableCut hno⟩
  · rintro ⟨S, hS, hval⟩ g
    rw [hval]
    exact g.value_le_cutCapacity hS

theorem isMinCut_of_value_eq_cutCapacity [DecidableEq V] (f : N.Flow) {S : Finset V}
    (hS : N.IsCut S) (hval : f.value = (N.cutCapacity S : ℤ)) : N.IsMinCut S := by
  refine ⟨hS, fun T hT => ?_⟩
  have hle := f.value_le_cutCapacity hT
  omega

end Flow

/-- **Existence of an integral maximum flow and minimum `s`-`t` cut** ([FordFulkerson1956],
Theorem 1, pp. 400–402; [FordFulkerson1962], Chapter I, Theorem 5.1 & Integrity Theorem 8.1):
every finite integral network `N` with `N.s ≠ N.t` admits an integral feasible flow `f` and an
`s`-`t` cut `S` such that `f` is a maximum flow, `S` is a minimum `s`-`t` cut, and
`f.value = N.cutCapacity S`. -/
theorem exists_maxFlow_eq_minCut [DecidableEq V] (hst : N.s ≠ N.t) :
    ∃ (f : N.Flow) (S : Finset V),
      f.IsMaxFlow ∧ N.IsMinCut S ∧ f.value = (N.cutCapacity S : ℤ) := by
  have hstep : ∀ k : ℕ, ∀ f : N.Flow,
      ((N.cutCapacity {N.s} : ℤ) - f.value).toNat ≤ k →
      ∃ g : N.Flow, ¬ ∃ p, g.IsAugmentingPath p := by
    intro k
    induction k with
    | zero =>
      intro f hk
      by_cases haug : ∃ p, f.IsAugmentingPath p
      · obtain ⟨p, hp⟩ := haug
        have hlt := f.lt_value_augmentByBottleneck hst hp
        have hcap := (f.augmentByBottleneck p hp).value_le_source_outCap hst
        omega
      · exact ⟨f, haug⟩
    | succ k ih =>
      intro f hk
      by_cases haug : ∃ p, f.IsAugmentingPath p
      · obtain ⟨p, hp⟩ := haug
        let f' := f.augmentByBottleneck p hp
        have hlt : f.value < f'.value := f.lt_value_augmentByBottleneck hst hp
        have hcap : f'.value ≤ (N.cutCapacity {N.s} : ℤ) := f'.value_le_source_outCap hst
        exact ih f' (by omega)
      · exact ⟨f, haug⟩
  obtain ⟨f, hno⟩ := hstep (N.cutCapacity {N.s}) (Flow.zero N) (by simp)
  have hcut := f.reachableCut_isCut hno
  have hval := f.value_eq_cutCapacity_reachableCut hno
  exact ⟨f, f.reachableCut, (f.isMaxFlow_iff_not_exists_augmentingPath hst).mpr hno,
    f.isMinCut_of_value_eq_cutCapacity hcut hval, hval⟩

end CutsAndFlows

/-! ### Equivalence transport of networks, flows, and cuts -/

section Reindex

variable {V W : Type*}

/-- Transport a directed flow network `N : Network V` across a vertex equivalence `e : V ≃ W`. -/
@[expose] def reindex (e : V ≃ W) (N : Network V) : Network W where
  cap x y := N.cap (e.symm x) (e.symm y)
  s := e N.s
  t := e N.t

/-- Push a feasible flow `f : N.Flow` forward along `e : V ≃ W`. -/
@[expose] def Flow.reindex [Fintype V] [Fintype W] (e : V ≃ W) {N : Network V}
    (f : N.Flow) : (N.reindex e).Flow where
  toFun x y := f (e.symm x) (e.symm y)
  le_cap x y := f.le_cap (e.symm x) (e.symm y)
  conserve x hxs hxt := by
    have hxs' : e.symm x ≠ N.s := fun h => hxs (by simpa [Network.reindex] using congrArg e h)
    have hxt' : e.symm x ≠ N.t := fun h => hxt (by simpa [Network.reindex] using congrArg e h)
    rw [e.symm.sum_comp (fun v => f (e.symm x) v), e.symm.sum_comp (fun u => f u (e.symm x))]
    exact f.conserve (e.symm x) hxs' hxt'

/-- Pull a feasible flow `g : (N.reindex e).Flow` back to `N.Flow`. -/
@[expose] def Flow.ofReindex [Fintype V] [Fintype W] (e : V ≃ W) {N : Network V}
    (g : (N.reindex e).Flow) : N.Flow where
  toFun u v := g (e u) (e v)
  le_cap u v := by simpa [Network.reindex] using g.le_cap (e u) (e v)
  conserve u hus hut := by
    have hus' : e u ≠ (N.reindex e).s := fun h => hus (e.injective h)
    have hut' : e u ≠ (N.reindex e).t := fun h => hut (e.injective h)
    rw [e.sum_comp (fun y => g (e u) y), e.sum_comp (fun x => g x (e u))]
    exact g.conserve (e u) hus' hut'

@[simp]
theorem Flow.value_reindex [Fintype V] [Fintype W] (e : V ≃ W) {N : Network V}
    (f : N.Flow) : (f.reindex e).value = f.value := by
  simp only [Flow.value, Flow.netOut, Network.reindex, Flow.reindex, Equiv.symm_apply_apply]
  change (∑ y : W, (f N.s (e.symm y) : ℤ)) - (∑ y : W, (f (e.symm y) N.s : ℤ)) = _
  rw [e.symm.sum_comp (fun v => (f N.s v : ℤ)), e.symm.sum_comp (fun u => (f u N.s : ℤ))]

@[simp]
theorem Flow.value_ofReindex [Fintype V] [Fintype W] (e : V ≃ W) {N : Network V}
    (g : (N.reindex e).Flow) : (g.ofReindex e).value = g.value := by
  simp only [Flow.value, Flow.netOut, Network.reindex, Flow.ofReindex]
  change (∑ v : V, (g (e N.s) (e v) : ℤ)) - (∑ v : V, (g (e v) (e N.s) : ℤ)) = _
  rw [e.sum_comp (fun y => (g (e N.s) y : ℤ)), e.sum_comp (fun x => (g x (e N.s) : ℤ))]

theorem Flow.isMaxFlow_ofReindex [Fintype V] [Fintype W] (e : V ≃ W) {N : Network V}
    {g : (N.reindex e).Flow} (hg : g.IsMaxFlow) : (g.ofReindex e).IsMaxFlow := by
  intro f
  rw [Flow.value_ofReindex, ← f.value_reindex e]
  exact hg (f.reindex e)

/-- Pull an `s`-`t` cut `S : Finset W` of `N.reindex e` back to `Finset V`. -/
@[expose] def cutOfReindex [Fintype V] [DecidableEq W] (e : V ≃ W)
    (S : Finset W) : Finset V :=
  Finset.univ.filter fun u => e u ∈ S

theorem isCut_cutOfReindex [Fintype V] [DecidableEq W] (e : V ≃ W) {N : Network V}
    {S : Finset W} (hS : (N.reindex e).IsCut S) : N.IsCut (cutOfReindex e S) := by
  refine ⟨?_, ?_⟩
  · simp only [cutOfReindex, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hS.1
  · simp only [cutOfReindex, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hS.2

theorem cutCapacity_cutOfReindex [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (N : Network V) (S : Finset W) :
    N.cutCapacity (cutOfReindex e S) = (N.reindex e).cutCapacity S := by
  have hL :
      N.cutCapacity (cutOfReindex e S) =
        ∑ u : V, ∑ v : V, if e u ∈ S ∧ e v ∉ S then N.cap u v else 0 := by
    unfold cutCapacity cutOfReindex
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : e u ∈ S
    · simp only [hu, ↓reduceIte, true_and]
      have hsdiff : Finset.univ \ Finset.univ.filter (fun v : V => e v ∈ S) =
          Finset.univ.filter (fun v : V => e v ∉ S) := by
        ext v
        simp
      rw [hsdiff, Finset.sum_filter]
    · simp [hu]
  have hR :
      (N.reindex e).cutCapacity S =
        ∑ x : W, ∑ y : W, if x ∈ S ∧ y ∉ S then N.cap (e.symm x) (e.symm y) else 0 := by
    unfold cutCapacity reindex
    have hsdiff : Finset.univ \ S = Finset.univ.filter (fun y : W => y ∉ S) := by
      ext y
      simp
    have hmem : S = Finset.univ.filter (fun x : W => x ∈ S) := by
      ext x
      simp
    rw [hsdiff]
    conv_lhs => rw [hmem]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ S
    · simp [hx, Finset.sum_filter]
    · simp [hx]
  rw [hL, hR, ← e.sum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← e.sum_comp]
  simp

end Reindex

end Network

end Cslib.Algorithms.Lean.MaxFlow
