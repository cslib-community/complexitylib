/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.UniqueGames.Propagation
public import Cslib.Algorithms.Lean.TimeM
import all CslibFrontier.Computability.PCP.Approximation.UniqueGames.Propagation
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# The cost of label propagation for unique games

`Cslib.Complexity.UniqueGames.Propagation.solveM` is the propagation algorithm
`Cslib.Complexity.UniqueGames.Propagation.solve` in the `TimeM` monad, with explicit charges.
It returns the same answer (`solveM_ret`). On an instance with `N` vertex slots and `E` edges, it
is charged at most `(L + 5) · N + (9 L + 16) · E + 1` steps for a list of `L` labels
(`solveM_time_le`), that is `O(L · (N + E))`. On a well-formed instance `N` is the declared
number of vertices. Khot observes that propagation runs in polynomial time
[Khot, Section 2.4][Khot2010]. The explicit charge and its analysis are this formalization's own,
in the cost model below.

## Cost model

The charges are for a RAM-style implementation in which the vertex table and the incidence lists
are arrays with unit-cost access, and every table on the labels (a stored table `α → α`, the
candidate table, the inverse of an edge's bijection) is an array of `L` entries:

* computing the number of slots: `E + 1`; building the incidence lists: `N + 2 E`;
  allocating the vertex table: `N`;
* in the outer loop, `1` per edge to read the table at its first endpoint, and, when that
  endpoint starts a new component, `L + 1` to reset the candidate table and `L + 1` to write the
  identity table at the seed;
* `1` per pop of the stack, and `3 (L + 1)` per incident edge visited: inverting the edge's
  bijection, composing it with a stored table, and filtering the candidates, one pass each;
* settling a component: `L + 1` to pick a surviving candidate and `L + 1` per vertex frozen;
* extracting the labelling: `N`; the final check: `3` per edge.

The returned values are the closures of the reference algorithm, which inverts an edge's
bijection by a linear search; the charges are those of the array implementation, which inverts
it once per visit. The bound is a statement about this explicit cost model, not about
multi-tape Turing machines: it does not by itself show that `GapUniqueGames (Fin L) 1 s` is in
`PromiseP` under the encoding of `Cslib.Complexity.UniqueGamesConjecture`.

## Main definitions

* `Cslib.Complexity.UniqueGames.Propagation.solveM`: label propagation with its charges.

## Main results

* `Cslib.Complexity.UniqueGames.Propagation.solveM_ret`: `solveM` returns `solve`.
* `Cslib.Complexity.UniqueGames.Propagation.solveM_time_le`,
  `Cslib.Complexity.UniqueGames.Propagation.solveM_time_le_of_wellFormed`: the step bound.

## References

* [S. Khot, *On the Unique Games Conjecture*, Section 2.4][Khot2010]
-/

public section

namespace Cslib.Complexity.UniqueGames.Propagation

open Cslib.PCP Cslib.PCP.Encoded Cslib.Algorithms.Lean

variable {α : Type} [DecidableEq α]

/-! ## Incidence lists -/

private theorem getD_set_ite {β : Type} (l : List β) {i : ℕ} (hi : i < l.length) (x d : β)
    (u : ℕ) : (l.set i x).getD u d = if u = i then x else l.getD u d := by
  split_ifs with h
  · subst h
    simp [List.getD_eq_getElem?_getD, hi]
  · exact List.getD_set_ne (Ne.symm h)

omit [DecidableEq α] in
/-- Insert an edge into the incidence lists of its endpoints (once for a loop). -/
@[expose] def insertEdge (bs : List (List (Edge (α → α)))) (e : Edge (α → α)) :
    List (List (Edge (α → α))) :=
  if e.src = e.dst then bs.set e.src (e :: bs.getD e.src [])
  else (bs.set e.src (e :: bs.getD e.src [])).set e.dst (e :: bs.getD e.dst [])

omit [DecidableEq α] in
/-- The incidence lists of the slots below `n`, preserving the order of the edges. -/
@[expose] def buckets (n : ℕ) (l : List (Edge (α → α))) : List (List (Edge (α → α))) :=
  l.foldr (fun e bs => insertEdge bs e) (List.replicate n [])

omit [DecidableEq α] in
/-- With endpoints below `n`, `buckets n l` has `n` entries, the incidence lists in `l`. -/
theorem buckets_spec (n : ℕ) (l : List (Edge (α → α))) (hl : ∀ e ∈ l, e.src < n ∧ e.dst < n) :
    (buckets n l).length = n ∧ ∀ u, (buckets n l).getD u [] = l.filter (incident u) := by
  induction l with
  | nil =>
    refine ⟨List.length_replicate, fun u => ?_⟩
    change (List.replicate n []).getD u [] = []
    by_cases hu : u < n
    · exact List.getD_replicate _ hu
    · exact List.getD_eq_default _ _ (by simpa using hu)
  | cons e l ih =>
    obtain ⟨hlen, hget⟩ := ih fun d hd => hl d (List.mem_cons_of_mem _ hd)
    have he := hl e (by simp)
    change (insertEdge (buckets n l) e).length = n ∧
      ∀ u, (insertEdge (buckets n l) e).getD u [] = (e :: l).filter (incident u)
    unfold insertEdge
    split_ifs with hsd
    · refine ⟨by rw [List.length_set, hlen], fun u => ?_⟩
      have hs : e.src < (buckets n l).length := by rw [hlen]; exact he.1
      rw [getD_set_ite _ hs, List.filter_cons, hget, hget]
      by_cases hu : u = e.src
      · subst hu; simp [incident]
      · simp [incident, hu, Ne.symm hu, ← hsd]
    · have hlen1 : ((buckets n l).set e.src (e :: (buckets n l).getD e.src [])).length = n := by
        rw [List.length_set, hlen]
      refine ⟨by rw [List.length_set, hlen1], fun u => ?_⟩
      have hs : e.src < (buckets n l).length := by rw [hlen]; exact he.1
      have hd : e.dst < ((buckets n l).set e.src (e :: (buckets n l).getD e.src [])).length := by
        rw [hlen1]; exact he.2
      rw [getD_set_ite _ hd, getD_set_ite _ hs, List.filter_cons, hget, hget, hget]
      by_cases hu : u = e.dst
      · subst hu; simp [incident]
      · by_cases hu' : u = e.src
        · subst hu'; simp [incident, hsd]
        · simp [incident, hu, hu', Ne.symm hu, Ne.symm hu']

omit [DecidableEq α] in
/-- The incidence lists of a graph's slots are its `adj` lists. -/
theorem buckets_getD (g : Graph (α → α)) (u : ℕ) :
    (buckets (slots g) g.edges).getD u [] = adj g u :=
  (buckets_spec _ _ fun _ he => ⟨src_lt_slots he, dst_lt_slots he⟩).2 u

/-! ## The costed algorithm -/

omit [DecidableEq α] in
/-- The charge for one pass over a table on the labels. -/
@[expose] def pass (labels : List α) : ℕ := labels.length + 1

/-- Compute the number of slots: one step per edge and one more. -/
@[expose] def slotsM {C : Type} (g : Graph C) : TimeM ℕ ℕ := do
  TimeM.tick (g.edges.length + 1)
  return slots g

omit [DecidableEq α] in
/-- Build the incidence lists: `n` steps to allocate, two per edge to insert. -/
@[expose] def bucketsM (n : ℕ) :
    List (Edge (α → α)) → TimeM ℕ (List (List (Edge (α → α))))
  | [] => do
    TimeM.tick n
    return List.replicate n []
  | e :: l => do
    let bs ← bucketsM n l
    TimeM.tick 2
    return insertEdge bs e

/-- Visit an edge: three passes over tables on the labels (inverting the bijection, composing,
filtering the candidates). -/
@[expose] def visitM (labels : List α) (S : State α) (e : Edge (α → α)) : TimeM ℕ (State α) := do
  TimeM.tick (3 * pass labels)
  return visit labels S e

/-- Visit a list of edges in order. -/
@[expose] def visitAllM (labels : List α) : State α → List (Edge (α → α)) → TimeM ℕ (State α)
  | S, [] => return S
  | S, e :: l => do
    let T ← visitM labels S e
    visitAllM labels T l

/-- Pop a slot (one step) and visit the edges of its incidence list. -/
@[expose] def scanM (labels : List α) (bs : List (List (Edge (α → α)))) (S : State α) :
    TimeM ℕ (State α) :=
  match S.stack with
  | [] => return S
  | u :: rest => do
    TimeM.tick 1
    visitAllM labels { S with stack := rest, comp := u :: S.comp } (bs.getD u [])

/-- Scan until the stack is empty, for at most `fuel` pops. -/
@[expose] def exploreM (labels : List α) (bs : List (List (Edge (α → α)))) :
    (fuel : ℕ) → State α → TimeM ℕ (State α)
  | 0, S => return S
  | k + 1, S =>
    match S.stack with
    | [] => return S
    | _ :: _ => do
      let T ← scanM labels bs S
      exploreM labels bs k T

omit [DecidableEq α] in
/-- Freeze the tables of the listed slots at the guess `c`, one pass each. -/
@[expose] def freezeAllM (labels : List α) (c : α) :
    List (Option (α → α)) → List ℕ → TimeM ℕ (List (Option (α → α)))
  | t, [] => return t
  | t, v :: l => do
    TimeM.tick (pass labels)
    freezeAllM labels c (t.set v (freeze c (t.getD v none))) l

/-- Pick a surviving guess (one pass) and freeze the component. -/
@[expose] def settleM [Inhabited α] (labels : List α) (S : State α) : TimeM ℕ (State α) := do
  TimeM.tick (pass labels)
  let t ← freezeAllM labels ((labels.find? S.cand).getD default) S.table S.comp
  return { S with table := t, comp := [] }

/-- Process one edge of the outer loop: read the table at its first endpoint (one step) and, if
that endpoint is unvisited, reset the candidate table and write the identity table at the seed
(one pass each), then explore and settle its component. -/
@[expose] def stepM [Inhabited α] (labels : List α) (n : ℕ) (bs : List (List (Edge (α → α))))
    (S : State α) (e : Edge (α → α)) : TimeM ℕ (State α) := do
  TimeM.tick 1
  match S.get e.src with
  | some _ => return S
  | none => do
    TimeM.tick (2 * pass labels)
    let T ← exploreM labels bs n (start S e.src)
    settleM labels T

/-- The outer loop over a list of edges. -/
@[expose] def stepsM [Inhabited α] (labels : List α) (n : ℕ)
    (bs : List (List (Edge (α → α)))) : State α → List (Edge (α → α)) → TimeM ℕ (State α)
  | S, [] => return S
  | S, e :: l => do
    let T ← stepM labels n bs S e
    stepsM labels n bs T l

/-- Check a labelling edge by edge: two reads and a comparison per edge. -/
@[expose] def checkAllM (σ : ℕ → α) : List (Edge (α → α)) → TimeM ℕ Bool
  | [] => return true
  | e :: l => do
    TimeM.tick 3
    if e.constraint (σ e.src) = σ e.dst then checkAllM σ l else return false

/-- Label propagation with its charges. -/
@[expose] def solveM [Inhabited α] (labels : List α) (g : Graph (α → α)) :
    TimeM ℕ (Option (ℕ → α)) := do
  let n ← slotsM g
  let bs ← bucketsM n g.edges
  TimeM.tick n
  let S ← stepsM labels n bs (init g) g.edges
  TimeM.tick n
  let σ : ℕ → α := fun v => (S.get v).elim default fun f => f default
  let ok ← checkAllM σ g.edges
  return if ok then some σ else none

/-! ## Return values -/

omit [DecidableEq α] in
/-- `bucketsM` builds `buckets`. -/
theorem bucketsM_ret (n : ℕ) (l : List (Edge (α → α))) : (bucketsM n l).ret = buckets n l := by
  induction l with
  | nil => rfl
  | cons e l ih => simp only [bucketsM, TimeM.ret_bind, ih]; rfl

omit [DecidableEq α] in
/-- `bucketsM` costs `n` plus two per edge. -/
theorem bucketsM_time (n : ℕ) (l : List (Edge (α → α))) :
    (bucketsM n l).time = n + 2 * l.length := by
  induction l with
  | nil => simp [bucketsM]
  | cons e l ih =>
    simp only [bucketsM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, List.length_cons]
    ring

/-- `visitAllM` visits the edges in order. -/
theorem visitAllM_ret (labels : List α) (l : List (Edge (α → α))) (S : State α) :
    (visitAllM labels S l).ret = l.foldl (visit labels) S := by
  induction l generalizing S with
  | nil => rfl
  | cons e l ih => simp only [visitAllM, visitM, TimeM.ret_bind, ih]; rfl

/-- `scanM` computes `scan`, given the incidence lists. -/
theorem scanM_ret (labels : List α) {g : Graph (α → α)} {bs : List (List (Edge (α → α)))}
    (hbs : ∀ u, bs.getD u [] = adj g u) (S : State α) :
    (scanM labels bs S).ret = scan labels g S := by
  unfold scanM scan
  cases S.stack with
  | nil => rfl
  | cons u rest => simp only [TimeM.ret_bind, visitAllM_ret, hbs]

/-- `exploreM` computes the iterated `scan`, given the incidence lists. -/
theorem exploreM_ret (labels : List α) {g : Graph (α → α)} {bs : List (List (Edge (α → α)))}
    (hbs : ∀ u, bs.getD u [] = adj g u) (k : ℕ) (S : State α) :
    (exploreM labels bs k S).ret = (scan labels g)^[k] S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    unfold exploreM
    cases hst : S.stack with
    | nil =>
      exact (Function.iterate_fixed (scan_nil labels g hst) _).symm
    | cons u rest =>
      simp only [TimeM.ret_bind, ih, scanM_ret labels hbs, Function.iterate_succ_apply]

omit [DecidableEq α] in
/-- `freezeAllM` freezes the listed slots in order. -/
theorem freezeAllM_ret (labels : List α) (c : α) (l : List ℕ) (t : List (Option (α → α))) :
    (freezeAllM labels c t l).ret =
      l.foldl (fun t v => t.set v (freeze c (t.getD v none))) t := by
  induction l generalizing t with
  | nil => rfl
  | cons v l ih => simp only [freezeAllM, TimeM.ret_bind, ih]; rfl

omit [DecidableEq α] in
/-- `settleM` computes `settle`. -/
theorem settleM_ret [Inhabited α] (labels : List α) (S : State α) :
    (settleM labels S).ret = settle labels S := by
  simp only [settleM, TimeM.ret_bind, freezeAllM_ret]; rfl

/-- `stepM` computes `step`, given the incidence lists. -/
theorem stepM_ret [Inhabited α] (labels : List α) {g : Graph (α → α)}
    {bs : List (List (Edge (α → α)))} (hbs : ∀ u, bs.getD u [] = adj g u) (S : State α)
    (e : Edge (α → α)) : (stepM labels (slots g) bs S e).ret = step labels g S e := by
  unfold stepM step
  cases S.get e.src with
  | some _ => rfl
  | none => simp only [TimeM.ret_bind, settleM_ret, exploreM_ret labels hbs]

/-- `stepsM` computes the outer loop, given the incidence lists. -/
theorem stepsM_ret [Inhabited α] (labels : List α) {g : Graph (α → α)}
    {bs : List (List (Edge (α → α)))} (hbs : ∀ u, bs.getD u [] = adj g u)
    (l : List (Edge (α → α))) (S : State α) :
    (stepsM labels (slots g) bs S l).ret = l.foldl (step labels g) S := by
  induction l generalizing S with
  | nil => rfl
  | cons e l ih => simp only [stepsM, TimeM.ret_bind, ih, stepM_ret labels hbs]; rfl

/-- `checkAllM` checks every edge. -/
theorem checkAllM_ret (σ : ℕ → α) (l : List (Edge (α → α))) :
    (checkAllM σ l).ret = l.all fun e => decide (e.constraint (σ e.src) = σ e.dst) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [checkAllM, TimeM.ret_bind, List.all_cons]
    split_ifs with h
    · simp [h, ih]
    · simp [h]

/-- The costed algorithm returns `solve`. -/
theorem solveM_ret [Inhabited α] (labels : List α) (g : Graph (α → α)) :
    (solveM labels g).ret = solve labels g := by
  simp only [solveM, TimeM.ret_bind, bucketsM_ret, checkAllM_ret]
  rw [show (slotsM g).ret = slots g from rfl, stepsM_ret labels (buckets_getD g)]
  rfl

/-! ## Time bounds -/

/-- The amortized weight of a slot: one pop, one pass to freeze it, and three passes for each
incident edge. -/
private def weight (labels : List α) (g : Graph (α → α)) (v : ℕ) : ℕ :=
  1 + pass labels + 3 * pass labels * (adj g v).length

/-- The remaining credit of a search state. -/
private def credit (labels : List α) (g : Graph (α → α)) (S : State α) : ℕ :=
  S.wpot (weight labels g) + pass labels * S.comp.length

/-- `visitAllM` costs three passes per edge. -/
theorem visitAllM_time (labels : List α) (l : List (Edge (α → α))) (S : State α) :
    (visitAllM labels S l).time = 3 * pass labels * l.length := by
  induction l generalizing S with
  | nil => rfl
  | cons e l ih =>
    simp only [visitAllM, visitM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
      TimeM.ret_bind, TimeM.ret_pure, ih, List.length_cons]
    ring

private theorem scanM_time (labels : List α) {g : Graph (α → α)}
    {bs : List (List (Edge (α → α)))} (hbs : ∀ u, bs.getD u [] = adj g u) {S : State α}
    (hlen : S.table.length = slots g) :
    (scanM labels bs S).time + credit labels g (scan labels g S) ≤ credit labels g S := by
  unfold scanM
  cases hst : S.stack with
  | nil => simp [scan_nil labels g hst]
  | cons u rest =>
    simp only [TimeM.time_bind, TimeM.time_tick, visitAllM_time, hbs]
    rw [scan_cons labels g hst]
    set S1 : State α := { S with stack := rest, comp := u :: S.comp } with hS1
    have hstep := foldl_visit_step labels (adj g u) (S := S1) (adj_bounds hlen u)
    have hw := hstep.wpot (weight labels g)
    have hS1w : S1.wpot (weight labels g) + weight labels g u = S.wpot (weight labels g) := by
      simp only [State.wpot, hst, List.map_cons, List.sum_cons]
      have : S1.unvisited = S.unvisited := rfl
      rw [this]
      ring
    have hwu : weight labels g u = 1 + pass labels + 3 * pass labels * (adj g u).length := rfl
    unfold credit
    rw [hstep.comp]
    have hc : S1.comp.length = S.comp.length + 1 := by simp [hS1]
    rw [hc]
    nlinarith

private theorem exploreM_time (labels : List α) {g : Graph (α → α)}
    {bs : List (List (Edge (α → α)))} (hbs : ∀ u, bs.getD u [] = adj g u) (k : ℕ)
    {S : State α} (hlen : S.table.length = slots g) :
    (exploreM labels bs k S).time + credit labels g ((scan labels g)^[k] S) ≤
      credit labels g S := by
  induction k generalizing S with
  | zero => simp [exploreM]
  | succ k ih =>
    unfold exploreM
    cases hst : S.stack with
    | nil =>
      simp only [TimeM.time_pure, zero_add]
      rw [Function.iterate_fixed (scan_nil labels g hst)]
    | cons u rest =>
      simp only [TimeM.time_bind, Function.iterate_succ_apply]
      have h1 := scanM_time labels hbs hlen (S := S)
      have h2 := ih (S := scan labels g S) (by rw [length_scan, hlen])
      rw [scanM_ret labels hbs]
      omega

omit [DecidableEq α] in
/-- `freezeAllM` costs one pass per slot. -/
theorem freezeAllM_time (labels : List α) (c : α) (l : List ℕ) (t : List (Option (α → α))) :
    (freezeAllM labels c t l).time = pass labels * l.length := by
  induction l generalizing t with
  | nil => rfl
  | cons v l ih =>
    simp only [freezeAllM, TimeM.time_bind, TimeM.time_tick, ih, List.length_cons]
    ring

omit [DecidableEq α] in
/-- `settleM` costs one pass plus one pass per slot of the component. -/
theorem settleM_time [Inhabited α] (labels : List α) (S : State α) :
    (settleM labels S).time = pass labels + pass labels * S.comp.length := by
  simp [settleM, freezeAllM_time]

omit [DecidableEq α] in
private theorem credit_settle [Inhabited α] (labels : List α) (g : Graph (α → α))
    (S : State α) : credit labels g (settle labels S) = S.wpot (weight labels g) := by
  simp only [credit, State.wpot, unvisited_settle]
  simp [settle]

omit [DecidableEq α] in
private theorem credit_start (labels : List α) (g : Graph (α → α)) {S : State α} {s : ℕ}
    (hs : s < S.table.length) (hnone : S.get s = none) :
    credit labels g (start S s) ≤ S.wpot (weight labels g) := by
  have hun : (start S s).unvisited = S.unvisited.erase s := unvisited_push hs id
  have h := Finset.sum_erase_add _ (weight labels g) (mem_unvisited hs hnone)
  simp only [credit, State.wpot]
  rw [hun]
  simp only [start, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_nil,
    mul_zero, add_zero]
  omega

private theorem stepM_time [Inhabited α] (labels : List α) {g : Graph (α → α)}
    {bs : List (List (Edge (α → α)))} (hbs : ∀ u, bs.getD u [] = adj g u) {S : State α}
    (hlen : S.table.length = slots g) {e : Edge (α → α)} (he : e ∈ g.edges) :
    (stepM labels (slots g) bs S e).time + credit labels g (step labels g S e) ≤
      credit labels g S + 1 + 3 * pass labels := by
  unfold stepM step
  cases hs : S.get e.src with
  | some _ => simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]; omega
  | none =>
    simp only [TimeM.time_bind, TimeM.time_tick, settleM_time, exploreM_ret labels hbs]
    have hlt : e.src < S.table.length := hlen ▸ src_lt_slots he
    have h1 := exploreM_time labels hbs (slots g) (S := start S e.src)
      (by simp [start, hlen])
    have h2 := credit_start labels g hlt hs
    rw [credit_settle]
    have h3 : credit labels g S = S.wpot (weight labels g) + pass labels * S.comp.length := rfl
    have h4 : credit labels g ((scan labels g)^[slots g] (start S e.src)) =
        ((scan labels g)^[slots g] (start S e.src)).wpot (weight labels g) +
          pass labels * ((scan labels g)^[slots g] (start S e.src)).comp.length := rfl
    omega

private theorem stepsM_time [Inhabited α] (labels : List α) {g : Graph (α → α)}
    {bs : List (List (Edge (α → α)))} (hbs : ∀ u, bs.getD u [] = adj g u)
    (l : List (Edge (α → α))) (hl : ∀ e ∈ l, e ∈ g.edges) {S : State α}
    (hlen : S.table.length = slots g) :
    (stepsM labels (slots g) bs S l).time ≤
      credit labels g S + (1 + 3 * pass labels) * l.length := by
  induction l generalizing S with
  | nil => simp [stepsM]
  | cons e l ih =>
    simp only [stepsM, TimeM.time_bind, List.length_cons]
    have h1 := stepM_time labels hbs hlen (hl e (by simp))
    have h2 := ih (fun d hd => hl d (List.mem_cons_of_mem _ hd))
      (S := step labels g S e) (by rw [length_step, hlen])
    rw [stepM_ret labels hbs]
    nlinarith

omit [DecidableEq α] in
/-- Every edge is in the incidence lists of at most its two endpoints. -/
private theorem sum_length_adj_le (g : Graph (α → α)) :
    ∑ v ∈ Finset.range (slots g), (adj g v).length ≤ 2 * g.edges.length := by
  have key : ∀ (l : List (Edge (α → α))) (s : Finset ℕ),
      ∑ v ∈ s, (l.filter (incident v)).length ≤ 2 * l.length := by
    intro l s
    induction l with
    | nil => simp
    | cons e l ih =>
      have hcount : ∀ v, ((e :: l).filter (incident v)).length =
          (l.filter (incident v)).length + if incident v e then 1 else 0 := by
        intro v
        rw [List.filter_cons]
        split_ifs <;> simp
      simp only [hcount, Finset.sum_add_distrib, List.length_cons]
      have h2 : ∑ v ∈ s, (if incident v e = true then 1 else 0) ≤ 2 := by
        rw [Finset.sum_boole]
        refine (Finset.card_le_card (t := {e.src, e.dst}) ?_).trans Finset.card_le_two
        intro v hv
        simp only [Finset.mem_filter, incident, Bool.or_eq_true, beq_iff_eq] at hv
        rcases hv.2 with h | h <;> simp [h]
      omega
  exact key _ _

omit [DecidableEq α] in
private theorem credit_init (labels : List α) (g : Graph (α → α)) :
    credit labels g (init g) ≤
      (1 + pass labels) * slots g + 6 * pass labels * g.edges.length := by
  have hun : (init g).unvisited = Finset.range (slots g) := by
    ext v
    simp [State.unvisited, init, State.get]
  simp only [credit, State.wpot]
  rw [hun]
  simp only [init, List.map_nil, List.sum_nil, List.length_nil, mul_zero, add_zero, weight,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum]
  have := sum_length_adj_le g
  nlinarith

/-- `checkAllM` costs at most three steps per edge. -/
theorem checkAllM_time (σ : ℕ → α) (l : List (Edge (α → α))) :
    (checkAllM σ l).time ≤ 3 * l.length := by
  induction l with
  | nil => simp [checkAllM]
  | cons e l ih =>
    simp only [checkAllM, TimeM.time_bind, TimeM.time_tick, List.length_cons]
    split_ifs
    · omega
    · simp only [TimeM.time_pure]; omega

/-- **The step bound**: label propagation on `slots g` slots and `|E|` edges, with `L` labels,
is charged `O(L · (slots g + |E|))` steps in the cost model of this module. Khot observes that
propagation runs in polynomial time [Khot, Section 2.4][Khot2010]; this explicit charge and its
analysis are this formalization's own. -/
theorem solveM_time_le [Inhabited α] (labels : List α) (g : Graph (α → α)) :
    (solveM labels g).time ≤
      (labels.length + 5) * slots g + (9 * labels.length + 16) * g.edges.length + 1 := by
  simp only [solveM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
  rw [show (slotsM g).ret = slots g from rfl, show (slotsM g).time = g.edges.length + 1 from rfl,
    bucketsM_time, bucketsM_ret]
  have h1 := stepsM_time labels (buckets_getD g) g.edges (fun _ h => h)
    (S := init g) List.length_replicate
  have h2 := credit_init labels g
  have h3 := checkAllM_time
    (fun v => ((stepsM labels (slots g) (buckets (slots g) g.edges) (init g) g.edges).ret.get
      v).elim default fun f => f default) g.edges
  simp only [pass] at h1 h2
  nlinarith

/-- **The step bound on well-formed instances**: `O(L · (|V| + |E|))` charged steps. -/
theorem solveM_time_le_of_wellFormed [Inhabited α] (labels : List α) {g : Graph (α → α)}
    (hg : g.WellFormed) :
    (solveM labels g).time ≤
      (labels.length + 5) * g.vertices + (9 * labels.length + 16) * g.edges.length + 1 := by
  simpa only [slots_eq_vertices hg] using solveM_time_le labels g

end Cslib.Complexity.UniqueGames.Propagation
