/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.LabelCover
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Satisfiable unique games are easy: label propagation

A unique game with value `1` has a satisfying labelling that can be found in polynomial time, by
guessing the label of one vertex of each connected component and propagating it along the
bijections on the edges [Khot, Section 2.4][Khot2010]. This is why the Unique Games Conjecture
(`Cslib.Complexity.UniqueGamesConjecture`) asks for completeness `1 - ε` rather than `1`.

The algorithm `Cslib.Complexity.UniqueGames.Propagation.solve` runs on the executable instances
`Cslib.PCP.Encoded.Graph (α → α)` of `Cslib.Complexity.GapUniqueGames`, given a list `labels` of
the labels. It explores the components one at a time and carries all guesses for a component's
seed in lockstep. Every vertex reached from the seed `s` stores a table `α → α`, sending each
guess for the label of `s` to the label it forces at that vertex, and a candidate table records
the guesses not yet refuted. An edge with one stored endpoint stores a table at the other
endpoint: the edge's bijection composed with the stored table, or its inverse composed with it
when the edge points towards the stored endpoint. An edge with both endpoints stored removes
the guesses that violate it. When the component is exhausted, any surviving guess fixes a label
at each of its vertices. A final check of every edge makes the answer sound unconditionally.

The search is written here rather than reusing `Cslib.Algorithms.Lean.DFS` or the breadth-first
reachability modules: those track only a set of visited vertices, while propagation stores a
table at each vertex, prunes the candidates on closing edges and settles each component when it
is exhausted.

## Main definitions

* `Cslib.Complexity.UniqueGames.Propagation.solve`: the propagation algorithm, returning a
  satisfying labelling or `none`.
* `Cslib.Complexity.UniqueGames.Propagation.labelling`: the labelling it extracts.

## Main results

* `Cslib.Complexity.UniqueGames.Propagation.solve_sound`: an answer of `solve` satisfies every
  edge, for any instance.
* `Cslib.Complexity.UniqueGames.Propagation.solve_eq_some_labelling`: if `labels` contains every
  label, every edge carries an injective table and the instance is satisfiable, then `solve`
  returns the extracted labelling.
* `Cslib.Complexity.UniqueGames.Propagation.solve_isSome_iff`,
  `Cslib.Complexity.UniqueGames.Propagation.solve_isSome_iff_unsatVal_eq_zero`: on unique games,
  `solve` succeeds exactly on the satisfiable instances, those of value `1`.
* `Cslib.Complexity.mem_yes_gapUniqueGames_one_iff`: the yes-instances of
  `GapUniqueGames α 1 s` are the satisfiable unique games.
* `Cslib.Complexity.solvedBy_gapUniqueGames_one`: `solve` decides `GapUniqueGames α 1 s`, for
  every soundness `s`.

Completeness needs injective tables: a constant table loses the information that propagation
relies on, and `solve` may then miss a satisfying labelling (a counterexample is in the tests).
The cost of the algorithm is analysed in
`CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime`. This file does not show
that `GapUniqueGames (Fin L) 1 s` is in `PromiseP` under the encoding of
`Cslib.Complexity.UniqueGamesConjecture`; that wiring is not done.

## References

* [S. Khot, *On the Unique Games Conjecture*, Section 2.4][Khot2010]
* [S. Khot, *On the power of unique 2-prover 1-round games*][Khot2002]
-/

public section

namespace Cslib.Complexity.UniqueGames.Propagation

open Cslib.PCP Cslib.PCP.Encoded

/-! ## The algorithm -/

section Algorithm

variable {α : Type}

/-- The number of vertex slots used by the algorithm: the declared vertex count, enlarged to
cover every endpoint, so that edges outside the declared range are still handled. -/
@[expose] def slots {C : Type} (g : Graph C) : ℕ :=
  g.edges.foldl (fun n e => max n (max e.src e.dst + 1)) g.vertices

/-- The state of the search. -/
structure State (α : Type) where
  /-- For each slot, `none` if unvisited, or the table sending each guess for the label of the
  current seed to the label it forces at that slot (a constant table once the component is
  settled). -/
  table : List (Option (α → α))
  /-- The guesses for the current seed's label that no edge has refuted yet. -/
  cand : α → Bool
  /-- The visited slots whose incident edges remain to be processed. -/
  stack : List ℕ
  /-- The processed slots of the current component. -/
  comp : List ℕ

namespace State

/-- The table stored at slot `v`. -/
@[expose] def get (S : State α) (v : ℕ) : Option (α → α) := S.table.getD v none

end State

/-- Store the table `f` at slot `w` and push `w` onto the stack. -/
@[expose] def push (S : State α) (w : ℕ) (f : α → α) : State α :=
  { S with table := S.table.set w (some f), stack := w :: S.stack }

/-- Whether `v` is an endpoint of `e`. -/
@[expose] def incident (v : ℕ) (e : Edge (α → α)) : Bool :=
  e.src == v || e.dst == v

/-- The edges incident to `v`, in order. -/
@[expose] def adj (g : Graph (α → α)) (v : ℕ) : List (Edge (α → α)) :=
  g.edges.filter (incident v)

/-- Fix the guess `c`: a stored table becomes the constant table of its value at `c`. -/
@[expose] def freeze (c : α) (o : Option (α → α)) : Option (α → α) :=
  o.map fun f _ => f c

/-- Start a new component at the seed `s`: its table is the identity, every guess is a
candidate and the stack holds `s`. -/
@[expose] def start (S : State α) (s : ℕ) : State α :=
  { table := S.table.set s (some id), cand := fun _ => true, stack := [s], comp := [] }

/-- The initial state: every slot unvisited. -/
@[expose] def init (g : Graph (α → α)) : State α :=
  { table := List.replicate (slots g) none, cand := fun _ => true, stack := [], comp := [] }

variable [DecidableEq α]

/-- The inverse of a table `π` on the labels in `labels`: the first `a ∈ labels` with
`π a = b`, or `b` if there is none. -/
@[expose] def preimage (labels : List α) (π : α → α) (b : α) : α :=
  (labels.find? fun a => decide (π a = b)).getD b

/-- Propagate along `e` when exactly one endpoint is visited. -/
@[expose] def extend (labels : List α) (S : State α) (e : Edge (α → α)) : State α :=
  match S.get e.src, S.get e.dst with
  | some f, none => push S e.dst (e.constraint ∘ f)
  | none, some h => push S e.src (preimage labels e.constraint ∘ h)
  | _, _ => S

/-- Remove the guesses that violate `e` when both endpoints are visited. -/
@[expose] def prune (S : State α) (e : Edge (α → α)) : State α :=
  match S.get e.src, S.get e.dst with
  | some f, some h => { S with cand := fun a => S.cand a && decide (e.constraint (f a) = h a) }
  | _, _ => S

/-- Process an edge: propagate along it, then prune by it. -/
@[expose] def visit (labels : List α) (S : State α) (e : Edge (α → α)) : State α :=
  prune (extend labels S e) e

/-- Pop a slot from the stack and process its incident edges. -/
@[expose] def scan (labels : List α) (g : Graph (α → α)) (S : State α) : State α :=
  match S.stack with
  | [] => S
  | u :: rest =>
      (adj g u).foldl (visit labels) { S with stack := rest, comp := u :: S.comp }

/-- Settle an exhausted component: fix the first surviving guess and freeze the tables of the
component's slots. -/
@[expose] def settle [Inhabited α] (labels : List α) (S : State α) : State α :=
  { S with
    table := S.comp.foldl
      (fun t v => t.set v (freeze ((labels.find? S.cand).getD default) (t.getD v none))) S.table
    comp := [] }

/-- Process the first endpoint of an edge: if it is unvisited, explore its component from it
(`slots g` pops suffice) and settle the component. -/
@[expose] def step [Inhabited α] (labels : List α) (g : Graph (α → α)) (S : State α)
    (e : Edge (α → α)) : State α :=
  match S.get e.src with
  | some _ => S
  | none => settle labels ((scan labels g)^[slots g] (start S e.src))

/-- Run the search over the first endpoints of all edges. -/
@[expose] def run [Inhabited α] (labels : List α) (g : Graph (α → α)) : State α :=
  g.edges.foldl (step labels g) (init g)

/-- The labelling extracted from the search; vertices on no edge get `default`. -/
@[expose] def labelling [Inhabited α] (labels : List α) (g : Graph (α → α)) (v : ℕ) : α :=
  ((run labels g).get v).elim default fun f => f default

/-- Check a labelling against every edge. -/
@[expose] def check (g : Graph (α → α)) (σ : ℕ → α) : Bool :=
  g.edges.all fun e => decide (e.constraint (σ e.src) = σ e.dst)

/-- **Label propagation** [Khot, Section 2.4][Khot2010]: the extracted labelling if it satisfies
every edge, and `none` otherwise. -/
@[expose] def solve [Inhabited α] (labels : List α) (g : Graph (α → α)) : Option (ℕ → α) :=
  if check g (labelling labels g) then some (labelling labels g) else none

end Algorithm

/-! ## Soundness -/

section Soundness

variable {α : Type} [DecidableEq α]

/-- `check` decides whether a labelling satisfies every edge. -/
theorem check_eq_true_iff (g : Graph (α → α)) (σ : ℕ → α) :
    check g σ = true ↔ ∀ i, (g.toGraph permutationEval).Satisfies σ i := by
  simp only [check, List.all_eq_true, decide_eq_true_eq, ConstraintGraph.Satisfies,
    Graph.toGraph, permutationEval]
  constructor
  · intro h i
    exact h _ (List.get_mem _ _)
  · intro h e he
    obtain ⟨i, rfl⟩ := List.get_of_mem he
    exact h i

/-- **Soundness**: an answer of `solve` satisfies every edge, for any instance. -/
theorem solve_sound [Inhabited α] {labels : List α} {g : Graph (α → α)} {σ : ℕ → α}
    (h : solve labels g = some σ) : ∀ i, (g.toGraph permutationEval).Satisfies σ i := by
  unfold solve at h
  split_ifs at h with hc
  cases h
  exact (check_eq_true_iff g _).1 hc

end Soundness

/-! ## Basic lemmas -/

section Basic

variable {α : Type}

private theorem slots_mono {C : Type} (l : List (Edge C)) (n : ℕ) :
    n ≤ l.foldl (fun n e => max n (max e.src e.dst + 1)) n := by
  induction l generalizing n with
  | nil => exact le_rfl
  | cons e l ih => exact (le_max_left _ _).trans (ih _)

private theorem lt_slots_of_mem {C : Type} (l : List (Edge C)) (n : ℕ) {e : Edge C}
    (he : e ∈ l) :
    max e.src e.dst < l.foldl (fun n e => max n (max e.src e.dst + 1)) n := by
  induction l generalizing n with
  | nil => simp at he
  | cons d l ih =>
    rcases List.mem_cons.1 he with rfl | he
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        ((le_max_right _ _).trans (slots_mono l _))
    · exact ih _ he

/-- The first endpoint of an edge is below `slots g`. -/
theorem src_lt_slots {C : Type} {g : Graph C} {e : Edge C} (he : e ∈ g.edges) :
    e.src < slots g :=
  (le_max_left _ _).trans_lt (lt_slots_of_mem g.edges g.vertices he)

/-- The second endpoint of an edge is below `slots g`. -/
theorem dst_lt_slots {C : Type} {g : Graph C} {e : Edge C} (he : e ∈ g.edges) :
    e.dst < slots g :=
  (le_max_right _ _).trans_lt (lt_slots_of_mem g.edges g.vertices he)

/-- The slots include the declared vertices. -/
theorem vertices_le_slots {C : Type} (g : Graph C) : g.vertices ≤ slots g :=
  slots_mono _ _

/-- On a well-formed graph the slots are exactly the declared vertices. -/
theorem slots_eq_vertices {C : Type} {g : Graph C} (hg : g.WellFormed) :
    slots g = g.vertices := by
  have key : ∀ l : List (Edge C), (∀ e ∈ l, e.src < g.vertices ∧ e.dst < g.vertices) →
      l.foldl (fun n e => max n (max e.src e.dst + 1)) g.vertices = g.vertices := by
    intro l hl
    induction l with
    | nil => rfl
    | cons e l ih =>
      have he := hl e (by simp)
      rw [List.foldl_cons, max_eq_left (by omega)]
      exact ih fun d hd => hl d (List.mem_cons_of_mem _ hd)
  exact key g.edges hg

namespace State

/-- A slot is done when it is visited and no longer on the stack. -/
private def Done (S : State α) (v : ℕ) : Prop := (S.get v).isSome ∧ v ∉ S.stack

/-- An edge is settled when both endpoints are visited and every surviving guess satisfies it. -/
private def Settled (S : State α) (e : Edge (α → α)) : Prop :=
  ∃ f h, S.get e.src = some f ∧ S.get e.dst = some h ∧
    ∀ a, S.cand a = true → e.constraint (f a) = h a

/-- The unvisited slots. -/
private def unvisited (S : State α) : Finset ℕ :=
  (Finset.range S.table.length).filter fun v => (S.get v).isNone

/-- The termination measure of the search: unvisited slots plus stack entries. -/
private def potential (S : State α) : ℕ := S.unvisited.card + S.stack.length

/-- A weighted potential: the weights of the unvisited slots and of the stack entries. -/
private def wpot (S : State α) (w : ℕ → ℕ) : ℕ := ∑ v ∈ S.unvisited, w v + (S.stack.map w).sum

/-- With unit weights the weighted potential is the potential. -/
private theorem wpot_one (S : State α) : S.wpot (fun _ => 1) = S.potential := by
  simp [wpot, potential]

end State

/-- Monotone progress within one component's search: stored tables persist, candidates only
shrink, done slots are unchanged, every new stack entry is a newly visited slot, and no
weighted potential increases. -/
private structure Step (S T : State α) : Prop where
  /-- Stored tables persist. -/
  get : ∀ v f, S.get v = some f → T.get v = some f
  /-- Candidates only shrink. -/
  cand : ∀ a, T.cand a = true → S.cand a = true
  /-- The done slots are unchanged. -/
  done : ∀ v, T.Done v ↔ S.Done v
  /-- The number of slots is unchanged. -/
  length : T.table.length = S.table.length
  /-- A new stack entry is a newly visited slot. -/
  stack : ∀ v, v ∈ T.stack → v ∈ S.stack ∨ ((S.get v).isNone ∧ (T.get v).isSome)
  /-- The component is unchanged. -/
  comp : T.comp = S.comp
  /-- No weighted potential increases. -/
  wpot : ∀ w, T.wpot w ≤ S.wpot w

/-- The potential does not increase along a `Step`. -/
private theorem Step.potential_le {S T : State α} (h : Step S T) : T.potential ≤ S.potential := by
  simpa only [State.wpot_one] using h.wpot fun _ => 1

/-- `Step` is reflexive. -/
private theorem Step.refl (S : State α) : Step S S :=
  ⟨fun _ _ h => h, fun _ h => h, fun _ => Iff.rfl, rfl, fun _ h => Or.inl h, rfl, fun _ => le_rfl⟩

/-- `Step` is transitive. -/
private theorem Step.trans {S T U : State α} (h₁ : Step S T) (h₂ : Step T U) : Step S U where
  get v f h := h₂.get v f (h₁.get v f h)
  cand a h := h₁.cand a (h₂.cand a h)
  done v := (h₂.done v).trans (h₁.done v)
  length := h₂.length.trans h₁.length
  stack v hv := by
    rcases h₂.stack v hv with hv | ⟨hT, hU⟩
    · rcases h₁.stack v hv with hv | ⟨hS, hT'⟩
      · exact Or.inl hv
      · obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 hT'
        exact Or.inr ⟨hS, by rw [h₂.get v f hf]; rfl⟩
    · refine Or.inr ⟨?_, hU⟩
      cases hS : S.get v with
      | none => rfl
      | some f => simp [h₁.get v f hS] at hT
  comp := h₂.comp.trans h₁.comp
  wpot w := (h₂.wpot w).trans (h₁.wpot w)

/-- A settled edge stays settled along a `Step`. -/
private theorem State.Settled.mono {S T : State α} {e : Edge (α → α)} (h : S.Settled e)
    (hST : Step S T) : T.Settled e := by
  obtain ⟨f, k, hf, hk, hfk⟩ := h
  exact ⟨f, k, hST.get _ _ hf, hST.get _ _ hk, fun a ha => hfk a (hST.cand a ha)⟩

/-- `push` stores its table. -/
private theorem get_push_self {S : State α} {w : ℕ} (hw : w < S.table.length) (f : α → α) :
    (push S w f).get w = some f :=
  List.getD_set_self hw

/-- `push` leaves the other slots alone. -/
private theorem get_push_ne (S : State α) {w v : ℕ} (h : w ≠ v) (f : α → α) :
    (push S w f).get v = S.get v :=
  List.getD_set_ne h

/-- `push` keeps the number of slots. -/
private theorem length_push (S : State α) (w : ℕ) (f : α → α) :
    (push S w f).table.length = S.table.length :=
  List.length_set

/-- `push` visits its slot. -/
private theorem unvisited_push {S : State α} {w : ℕ} (hw : w < S.table.length) (f : α → α) :
    (push S w f).unvisited = S.unvisited.erase w := by
  ext v
  simp only [State.unvisited, Finset.mem_filter, Finset.mem_range, Finset.mem_erase,
    length_push]
  by_cases hv : w = v
  · subst hv
    simp [get_push_self hw]
  · rw [get_push_ne S hv]
    simp [Ne.symm hv]

/-- An unvisited slot in range is in `unvisited`. -/
private theorem mem_unvisited {S : State α} {w : ℕ} (hw : w < S.table.length)
    (hnone : S.get w = none) : w ∈ S.unvisited := by
  simp [State.unvisited, hw, hnone]

/-- Pushing an unvisited slot in range is a `Step`. -/
private theorem step_push {S : State α} {w : ℕ} (hw : w < S.table.length) (hnone : S.get w = none)
    (f : α → α) : Step S (push S w f) where
  get v g hv := by
    have : w ≠ v := by rintro rfl; simp [hnone] at hv
    rw [get_push_ne S this, hv]
  cand _ h := h
  done v := by
    by_cases hv : w = v
    · subst hv
      simp [State.Done, push, hnone]
    · unfold State.Done
      rw [get_push_ne S hv]
      simp [push, Ne.symm hv]
  length := length_push S w f
  stack v hv := by
    rcases List.mem_cons.1 hv with rfl | hv
    · exact Or.inr ⟨by simp [hnone], by simp [get_push_self hw]⟩
    · exact Or.inl hv
  comp := rfl
  wpot w' := by
    have h := Finset.sum_erase_add _ w' (mem_unvisited hw hnone)
    simp only [State.wpot, unvisited_push hw f]
    simp only [push, List.map_cons, List.sum_cons]
    omega

end Basic

/-! ## Visiting an edge -/

section Visit

variable {α : Type} [DecidableEq α]

private theorem prune_eq (S : State α) (e : Edge (α → α)) :
    ∃ p : α → Bool, prune S e = { S with cand := fun a => S.cand a && p a } := by
  unfold prune
  split
  · exact ⟨_, rfl⟩
  · exact ⟨fun _ => true, by simp⟩

private theorem get_prune (S : State α) (e : Edge (α → α)) (v : ℕ) :
    (prune S e).get v = S.get v := by
  obtain ⟨p, hp⟩ := prune_eq S e
  rw [hp]
  rfl

private theorem step_prune (S : State α) (e : Edge (α → α)) : Step S (prune S e) := by
  obtain ⟨p, hp⟩ := prune_eq S e
  rw [hp]
  exact ⟨fun _ _ h => h, fun a h => by simp only [Bool.and_eq_true] at h; exact h.1,
    fun _ => Iff.rfl, rfl, fun _ h => Or.inl h, rfl, fun _ => le_rfl⟩

private theorem step_extend (labels : List α) {S : State α} {e : Edge (α → α)}
    (hsrc : e.src < S.table.length) (hdst : e.dst < S.table.length) :
    Step S (extend labels S e) := by
  unfold extend
  split
  · exact step_push hdst (by assumption) _
  · exact step_push hsrc (by assumption) _
  · exact Step.refl S

/-- Visiting an edge with endpoints in range is a `Step`. -/
private theorem step_visit (labels : List α) {S : State α} {e : Edge (α → α)}
    (hsrc : e.src < S.table.length) (hdst : e.dst < S.table.length) :
    Step S (visit labels S e) :=
  (step_extend labels hsrc hdst).trans (step_prune _ e)

private theorem get_extend (labels : List α) {S : State α} (e : Edge (α → α)) {v : ℕ}
    {f : α → α} (hv : S.get v = some f) : (extend labels S e).get v = some f := by
  unfold extend
  split
  · rename_i hd
    have : e.dst ≠ v := by rintro rfl; simp [hv] at hd
    rw [get_push_ne S this, hv]
  · rename_i hs _
    have : e.src ≠ v := by rintro rfl; simp [hv] at hs
    rw [get_push_ne S this, hv]
  · exact hv

private theorem cand_extend (labels : List α) (S : State α) (e : Edge (α → α)) :
    (extend labels S e).cand = S.cand := by
  unfold extend
  split <;> rfl

private theorem length_extend (labels : List α) (S : State α) (e : Edge (α → α)) :
    (extend labels S e).table.length = S.table.length := by
  unfold extend
  split <;> first | exact length_push _ _ _ | rfl

/-- Visiting an edge keeps the stored tables. -/
private theorem get_visit (labels : List α) {S : State α} (e : Edge (α → α)) {v : ℕ} {f : α → α}
    (hv : S.get v = some f) : (visit labels S e).get v = some f := by
  unfold visit
  rw [get_prune]
  exact get_extend labels e hv

/-- Visiting an edge keeps the number of slots. -/
private theorem length_visit (labels : List α) (S : State α) (e : Edge (α → α)) :
    (visit labels S e).table.length = S.table.length := by
  obtain ⟨p, hp⟩ := prune_eq (extend labels S e) e
  unfold visit
  rw [hp]
  exact length_extend labels S e

/-- Visiting an edge with a visited endpoint settles it. -/
private theorem visit_settled (labels : List α) {S : State α} {e : Edge (α → α)}
    (hsrc : e.src < S.table.length) (hdst : e.dst < S.table.length)
    (hvis : (S.get e.src).isSome ∨ (S.get e.dst).isSome) :
    (visit labels S e).Settled e := by
  have key : ∃ f h, (extend labels S e).get e.src = some f ∧
      (extend labels S e).get e.dst = some h := by
    unfold extend
    cases hs : S.get e.src with
    | none =>
      cases hd : S.get e.dst with
      | none => simp [hs, hd] at hvis
      | some h =>
        by_cases heq : e.src = e.dst
        · rw [heq] at hs; simp [hs] at hd
        · exact ⟨_, h, get_push_self hsrc _, by rw [get_push_ne S heq, hd]⟩
    | some f =>
      cases hd : S.get e.dst with
      | none =>
        by_cases heq : e.src = e.dst
        · rw [heq] at hs; simp [hs] at hd
        · exact ⟨f, _, by rw [get_push_ne S (Ne.symm heq), hs], get_push_self hdst _⟩
      | some h => exact ⟨f, h, hs, hd⟩
  obtain ⟨f, h, hf, hh⟩ := key
  refine ⟨f, h, by unfold visit; rw [get_prune]; exact hf,
    by unfold visit; rw [get_prune]; exact hh, fun a ha => ?_⟩
  unfold visit prune at ha
  simp only [hf, hh, Bool.and_eq_true, decide_eq_true_eq] at ha
  exact ha.2

/-- `preimage` inverts an injective table on the listed labels. -/
theorem preimage_apply {labels : List α} {π : α → α} (hπ : Function.Injective π) {a : α}
    (ha : a ∈ labels) : preimage labels π (π a) = a := by
  unfold preimage
  cases h : labels.find? (fun b => decide (π b = π a)) with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd (by simp) (h a ha)
  | some b =>
    have := List.find?_some h
    simp only [decide_eq_true_eq] at this
    exact hπ this

/-- The semantic invariant against a satisfying labelling `τ` and a seed `s`: every stored table
sends the seed's label to the vertex's label, and the seed's label is still a candidate. -/
private structure SemInv (τ : ℕ → α) (s : ℕ) (S : State α) : Prop where
  val : ∀ v f, S.get v = some f → f (τ s) = τ v
  cand : S.cand (τ s) = true

private theorem sem_extend {labels : List α} (hlabels : ∀ a, a ∈ labels) {τ : ℕ → α} {s : ℕ}
    {S : State α} {e : Edge (α → α)} (hπ : Function.Injective e.constraint)
    (hsat : e.constraint (τ e.src) = τ e.dst) (h : SemInv τ s S) :
    SemInv τ s (extend labels S e) := by
  refine ⟨fun v f hv => ?_, by rw [cand_extend]; exact h.cand⟩
  unfold extend at hv
  split at hv
  · rename_i f0 hs hd
    by_cases hw : e.dst = v
    · subst hw
      by_cases hlt : e.dst < S.table.length
      · rw [get_push_self hlt] at hv
        cases hv
        simp only [Function.comp_apply, h.val _ _ hs, hsat]
      · rw [push, State.get, List.set_eq_of_length_le (by omega)] at hv
        exact h.val _ _ hv
    · rw [get_push_ne S hw] at hv
      exact h.val _ _ hv
  · rename_i h0 hs hd
    by_cases hw : e.src = v
    · subst hw
      by_cases hlt : e.src < S.table.length
      · rw [get_push_self hlt] at hv
        cases hv
        simp only [Function.comp_apply, h.val _ _ hd, ← hsat, preimage_apply hπ (hlabels _)]
      · rw [push, State.get, List.set_eq_of_length_le (by omega)] at hv
        exact h.val _ _ hv
    · rw [get_push_ne S hw] at hv
      exact h.val _ _ hv
  · exact h.val _ _ hv

private theorem sem_prune {τ : ℕ → α} {s : ℕ} {S : State α} {e : Edge (α → α)}
    (hsat : e.constraint (τ e.src) = τ e.dst) (h : SemInv τ s S) :
    SemInv τ s (prune S e) := by
  refine ⟨fun v f hv => h.val v f (by rwa [get_prune] at hv), ?_⟩
  unfold prune
  split
  · rename_i f0 h0 hs hd
    simp only [h.cand, h.val _ _ hs, h.val _ _ hd, hsat, decide_true, Bool.and_self]
  · exact h.cand

private theorem sem_visit {labels : List α} (hlabels : ∀ a, a ∈ labels) {τ : ℕ → α} {s : ℕ}
    {S : State α} {e : Edge (α → α)} (hπ : Function.Injective e.constraint)
    (hsat : e.constraint (τ e.src) = τ e.dst) (h : SemInv τ s S) :
    SemInv τ s (visit labels S e) :=
  sem_prune hsat (sem_extend hlabels hπ hsat h)

/-- Visiting a list of edges with endpoints in range is a `Step`. -/
private theorem foldl_visit_step (labels : List α) (l : List (Edge (α → α))) {S : State α}
    (hl : ∀ e ∈ l, e.src < S.table.length ∧ e.dst < S.table.length) :
    Step S (l.foldl (visit labels) S) := by
  induction l generalizing S with
  | nil => exact Step.refl S
  | cons e l ih =>
    have h1 := step_visit labels (hl e (by simp)).1 (hl e (by simp)).2 (S := S)
    refine h1.trans (ih fun d hd => ?_)
    rw [h1.length]
    exact hl d (List.mem_cons_of_mem _ hd)

private theorem foldl_visit_settled (labels : List α) {u : ℕ} (l : List (Edge (α → α)))
    {S : State α} (hl : ∀ e ∈ l, e.src < S.table.length ∧ e.dst < S.table.length)
    (hinc : ∀ e ∈ l, e.src = u ∨ e.dst = u) (hu : (S.get u).isSome) :
    ∀ e ∈ l, (l.foldl (visit labels) S).Settled e := by
  induction l generalizing S with
  | nil => simp
  | cons e l ih =>
    have hb := hl e (by simp)
    have h1 := step_visit labels hb.1 hb.2 (S := S)
    have hl' : ∀ d ∈ l, d.src < (visit labels S e).table.length ∧
        d.dst < (visit labels S e).table.length := fun d hd => by
      rw [h1.length]; exact hl d (List.mem_cons_of_mem _ hd)
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 hu
    have hu' : ((visit labels S e).get u).isSome := by rw [h1.get u f hf]; rfl
    rw [List.forall_mem_cons]
    refine ⟨?_, ih hl' (fun d hd => hinc d (List.mem_cons_of_mem _ hd)) hu'⟩
    have hs : (visit labels S e).Settled e := by
      apply visit_settled labels hb.1 hb.2
      rcases hinc e (by simp) with h | h
      · exact Or.inl (h ▸ hu)
      · exact Or.inr (h ▸ hu)
    exact hs.mono (foldl_visit_step labels l hl')

private theorem foldl_visit_sem {labels : List α} (hlabels : ∀ a, a ∈ labels) {τ : ℕ → α}
    {s : ℕ} (l : List (Edge (α → α))) {S : State α}
    (hl : ∀ e ∈ l, Function.Injective e.constraint ∧ e.constraint (τ e.src) = τ e.dst)
    (h : SemInv τ s S) : SemInv τ s (l.foldl (visit labels) S) := by
  induction l generalizing S with
  | nil => exact h
  | cons e l ih =>
    exact ih (fun d hd => hl d (List.mem_cons_of_mem _ hd))
      (sem_visit hlabels (hl e (by simp)).1 (hl e (by simp)).2 h)

/-- Visiting a list of edges keeps the number of slots. -/
private theorem foldl_visit_length (labels : List α) (l : List (Edge (α → α))) (S : State α) :
    (l.foldl (visit labels) S).table.length = S.table.length := by
  induction l generalizing S with
  | nil => rfl
  | cons e l ih => rw [List.foldl_cons, ih, length_visit]

/-- Visiting a list of edges keeps the stored tables. -/
private theorem foldl_visit_get (labels : List α) (l : List (Edge (α → α))) {S : State α} {v : ℕ}
    {f : α → α} (hv : S.get v = some f) : (l.foldl (visit labels) S).get v = some f := by
  induction l generalizing S with
  | nil => exact hv
  | cons e l ih => exact ih (get_visit labels e hv)

end Visit

/-! ## Scanning the stack -/

section Scan

variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
/-- The incident edges of `v` are the edges with `v` as an endpoint. -/
private theorem mem_adj {g : Graph (α → α)} {v : ℕ} {e : Edge (α → α)} :
    e ∈ adj g v ↔ e ∈ g.edges ∧ (e.src = v ∨ e.dst = v) := by
  simp [adj, incident]

/-- Scanning an empty stack does nothing. -/
private theorem scan_nil (labels : List α) (g : Graph (α → α)) {S : State α} (h : S.stack = []) :
    scan labels g S = S := by
  unfold scan; rw [h]

/-- Scanning pops the top slot and visits its incident edges. -/
private theorem scan_cons (labels : List α) (g : Graph (α → α)) {S : State α} {u : ℕ}
    {rest : List ℕ} (h : S.stack = u :: rest) :
    scan labels g S =
      (adj g u).foldl (visit labels) { S with stack := rest, comp := u :: S.comp } := by
  unfold scan; rw [h]

/-- Scanning keeps the number of slots. -/
private theorem length_scan (labels : List α) (g : Graph (α → α)) (S : State α) :
    (scan labels g S).table.length = S.table.length := by
  unfold scan
  split
  · rfl
  · exact foldl_visit_length _ _ _

private theorem get_scan (labels : List α) (g : Graph (α → α)) {S : State α} {v : ℕ}
    {f : α → α} (hv : S.get v = some f) : (scan labels g S).get v = some f := by
  unfold scan
  split
  · exact hv
  · exact foldl_visit_get labels _ hv

/-- Repeated scanning keeps the number of slots. -/
private theorem length_iterate_scan (labels : List α) (g : Graph (α → α)) (k : ℕ) (S : State α) :
    ((scan labels g)^[k] S).table.length = S.table.length := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', length_scan, ih]

/-- Repeated scanning keeps the stored tables. -/
private theorem get_iterate_scan (labels : List α) (g : Graph (α → α)) (k : ℕ) {S : State α} {v : ℕ}
    {f : α → α} (hv : S.get v = some f) : ((scan labels g)^[k] S).get v = some f := by
  induction k with
  | zero => exact hv
  | succ k ih => rw [Function.iterate_succ_apply']; exact get_scan labels g ih

omit [DecidableEq α] in
/-- With `slots g` slots, the incident edges of any slot have endpoints in range. -/
private theorem adj_bounds {g : Graph (α → α)} {S : State α} (hlen : S.table.length = slots g)
    (u : ℕ) : ∀ e ∈ adj g u, e.src < S.table.length ∧ e.dst < S.table.length := fun e he => by
  rw [hlen]
  exact ⟨src_lt_slots (mem_adj.1 he).1, dst_lt_slots (mem_adj.1 he).1⟩

private theorem potential_scan (labels : List α) (g : Graph (α → α)) {S : State α}
    (hlen : S.table.length = slots g) (hne : S.stack ≠ []) :
    (scan labels g S).potential < S.potential := by
  obtain ⟨u, rest, hst⟩ := List.exists_cons_of_ne_nil hne
  rw [scan_cons labels g hst]
  have h := foldl_visit_step labels (adj g u)
    (S := { S with stack := rest, comp := u :: S.comp }) (adj_bounds hlen u)
  refine lt_of_le_of_lt h.potential_le ?_
  have hu : ({ S with stack := rest, comp := u :: S.comp } : State α).unvisited = S.unvisited :=
    rfl
  simp only [State.potential, hst, List.length_cons, hu]
  omega

private theorem iterate_scan_stack (labels : List α) (g : Graph (α → α)) {S : State α}
    (hlen : S.table.length = slots g) (k : ℕ) :
    ((scan labels g)^[k] S).stack = [] ∨ ((scan labels g)^[k] S).potential + k ≤ S.potential := by
  induction k with
  | zero => exact Or.inr le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    by_cases hne : ((scan labels g)^[k] S).stack = []
    · left; rw [scan_nil labels g hne]; exact hne
    · right
      have hk := ih.resolve_left hne
      have := potential_scan labels g (by rw [length_iterate_scan, hlen]) hne
      omega

omit [DecidableEq α] in
private theorem potential_start {g : Graph (α → α)} {S : State α}
    (hlen : S.table.length = slots g) {s : ℕ} (hs : s < S.table.length) :
    (start S s).potential ≤ slots g := by
  have hself : (start S s).get s = some id := List.getD_set_self hs
  have hsub : (start S s).unvisited ⊆ (Finset.range S.table.length).erase s := by
    intro v hv
    simp only [State.unvisited, Finset.mem_filter, Finset.mem_range] at hv
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_range.2 (by simpa [start] using hv.1)⟩
    rintro rfl
    simp [hself] at hv
  have hcard := (Finset.card_le_card hsub).trans_eq
    (Finset.card_erase_of_mem (Finset.mem_range.2 hs))
  simp only [Finset.card_range] at hcard
  have : (start S s).stack.length = 1 := rfl
  unfold State.potential
  omega

private theorem iterate_scan_eq_nil (labels : List α) (g : Graph (α → α)) {S : State α}
    (hlen : S.table.length = slots g) (hs : S.potential ≤ slots g) :
    ((scan labels g)^[slots g] S).stack = [] := by
  rcases iterate_scan_stack labels g hlen (slots g) with h | h
  · exact h
  · have h0 : ((scan labels g)^[slots g] S).potential = 0 := by omega
    exact List.length_eq_zero_iff.1 (by unfold State.potential at h0; omega)

/-- The invariant of one component's search from the seed `s`, started on the state `S0`. -/
private structure Inv (g : Graph (α → α)) (τ : ℕ → α) (s : ℕ) (S0 S : State α) : Prop where
  length : S.table.length = slots g
  old : ∀ v f, S0.get v = some f → S.get v = some f
  sem : SemInv τ s S
  stack : ∀ v ∈ S.stack, (S.get v).isSome
  fresh : ∀ v, (S.get v).isSome → (S0.get v).isNone → v ∈ S.stack ∨ v ∈ S.comp
  settled : ∀ e ∈ g.edges, S.Done e.src ∨ S.Done e.dst → S.Settled e

private theorem inv_scan {labels : List α} (hlabels : ∀ a, a ∈ labels) {g : Graph (α → α)}
    (hinj : ∀ e ∈ g.edges, Function.Injective e.constraint) {τ : ℕ → α}
    (hτ : ∀ e ∈ g.edges, e.constraint (τ e.src) = τ e.dst) {s : ℕ}
    {S0 S : State α} (h : Inv g τ s S0 S) :
    Inv g τ s S0 (scan labels g S) := by
  cases hst : S.stack with
  | nil => rw [scan_nil labels g hst]; exact h
  | cons u rest =>
    rw [scan_cons labels g hst]
    set S1 : State α := { S with stack := rest, comp := u :: S.comp } with hS1
    have hb : ∀ e ∈ adj g u, e.src < S1.table.length ∧ e.dst < S1.table.length :=
      adj_bounds h.length u
    have hstep := foldl_visit_step labels (adj g u) hb
    have hu : (S1.get u).isSome := h.stack u (by simp [hst])
    have hsem : SemInv τ s S1 := ⟨h.sem.val, h.sem.cand⟩
    refine ⟨?_, fun v f hv => hstep.get v f (h.old v f hv), ?_, ?_, ?_, ?_⟩
    · rw [hstep.length]; exact h.length
    · exact foldl_visit_sem hlabels _
        (fun e he => ⟨hinj e (mem_adj.1 he).1, hτ e (mem_adj.1 he).1⟩) hsem
    · intro v hv
      rcases hstep.stack v hv with hv | ⟨_, hT⟩
      · have hv' : v ∈ S.stack := by rw [hst]; exact List.mem_cons_of_mem _ hv
        obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (h.stack v hv')
        rw [hstep.get v f hf]; rfl
      · exact hT
    · intro v hv h0
      cases hS : S.get v with
      | none =>
        -- newly visited during this scan: it is on the stack
        have : ¬ v ∈ (adj g u |>.foldl (visit labels) S1).stack → False := by
          intro hns
          have hdone : (adj g u |>.foldl (visit labels) S1).Done v := ⟨hv, hns⟩
          have hd1 := (hstep.done v).1 hdone
          have : (S1.get v).isSome := hd1.1
          simp [show S1.get v = S.get v from rfl, hS] at this
        by_contra hcon
        push Not at hcon
        exact this hcon.1
      | some f =>
        rcases h.fresh v (by simp [hS]) h0 with hv' | hv'
        · rw [hst] at hv'
          rcases List.mem_cons.1 hv' with rfl | hv'
          · right; rw [hstep.comp]; simp [S1]
          · -- still on the stack: a done slot stays done
            rcases em (v ∈ (adj g u |>.foldl (visit labels) S1).stack) with hin | hnin
            · exact Or.inl hin
            · have hT : (adj g u |>.foldl (visit labels) S1).Done v :=
                ⟨by rw [hstep.get v f hS]; rfl, hnin⟩
              have := ((hstep.done v).1 hT).2
              exact absurd hv' this
        · right; rw [hstep.comp]; simp [S1, hv']
    · have hdone : ∀ w, (adj g u |>.foldl (visit labels) S1).Done w → w = u ∨ S.Done w := by
        intro w hw
        have hw1 := (hstep.done w).1 hw
        by_cases hwu : w = u
        · exact Or.inl hwu
        · right
          refine ⟨hw1.1, ?_⟩
          rw [hst]
          simp only [List.mem_cons, not_or]
          exact ⟨hwu, hw1.2⟩
      have hsettled_adj := foldl_visit_settled labels (adj g u) hb
        (fun e he => (mem_adj.1 he).2) hu
      intro e he hd
      by_cases hinc : e.src = u ∨ e.dst = u
      · exact hsettled_adj e (mem_adj.2 ⟨he, hinc⟩)
      · push Not at hinc
        have hold : S.Done e.src ∨ S.Done e.dst := by grind
        have hS1 : S1.Settled e := h.settled e he hold
        exact hS1.mono hstep

private theorem inv_iterate_scan {labels : List α} (hlabels : ∀ a, a ∈ labels)
    {g : Graph (α → α)} (hinj : ∀ e ∈ g.edges, Function.Injective e.constraint) {τ : ℕ → α}
    (hτ : ∀ e ∈ g.edges, e.constraint (τ e.src) = τ e.dst) {s : ℕ}
    {S0 S : State α} (h : Inv g τ s S0 S) (k : ℕ) :
    Inv g τ s S0 ((scan labels g)^[k] S) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact inv_scan hlabels hinj hτ ih

end Scan

/-! ## Components and the outer loop -/

section Outer

variable {α : Type} [DecidableEq α]

/-- Between components: stored tables are constants given by a satisfying labelling, and the
visited slots are closed under edges. -/
private structure Good (g : Graph (α → α)) (τ : ℕ → α) (S : State α) : Prop where
  length : S.table.length = slots g
  const : ∀ v f, S.get v = some f → ∀ a, f a = τ v
  closed : ∀ e ∈ g.edges, (S.get e.src).isSome = (S.get e.dst).isSome
  sat : ∀ e ∈ g.edges, e.constraint (τ e.src) = τ e.dst

omit [DecidableEq α] in
private theorem inv_start {g : Graph (α → α)} {τ : ℕ → α} {S : State α} (h : Good g τ S)
    {s : ℕ} (hs : s < S.table.length) (hnone : S.get s = none) :
    Inv g τ s S (start S s) := by
  have hself : (start S s).get s = some id := List.getD_set_self hs
  have hne : ∀ v, v ≠ s → (start S s).get v = S.get v := fun v hv =>
    List.getD_set_ne (Ne.symm hv)
  refine ⟨?_, fun v f hv => ?_, ⟨fun v f hv => ?_, rfl⟩, ?_, ?_, ?_⟩
  · simp [start, h.length]
  · have : v ≠ s := by rintro rfl; simp [hnone] at hv
    rw [hne v this, hv]
  · by_cases hvs : v = s
    · subst hvs; rw [hself] at hv; cases hv; rfl
    · rw [hne v hvs] at hv; exact h.const v f hv _
  · intro v hv
    simp only [start, List.mem_singleton] at hv
    subst hv; rw [hself]; rfl
  · intro v hv h0
    by_cases hvs : v = s
    · subst hvs; left; simp [start]
    · rw [hne v hvs] at hv
      exact absurd hv (by simpa using h0)
  · intro e he hd
    have hold : (S.get e.src).isSome ∨ (S.get e.dst).isSome := by
      rcases hd with ⟨hd, hns⟩ | ⟨hd, hns⟩
      · have : e.src ≠ s := by rintro rfl; simp [start] at hns
        exact Or.inl (by rwa [hne _ this] at hd)
      · have : e.dst ≠ s := by rintro rfl; simp [start] at hns
        exact Or.inr (by rwa [hne _ this] at hd)
    have hboth : (S.get e.src).isSome ∧ (S.get e.dst).isSome := by
      have := h.closed e he
      rcases hold with h1 | h1
      · exact ⟨h1, this ▸ h1⟩
      · exact ⟨this.symm ▸ h1, h1⟩
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 hboth.1
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hboth.2
    have hsrc : e.src ≠ s := by rintro rfl; simp [hnone] at hf
    have hdst : e.dst ≠ s := by rintro rfl; simp [hnone] at hk
    refine ⟨f, k, by rw [hne _ hsrc, hf], by rw [hne _ hdst, hk], fun a _ => ?_⟩
    rw [h.const _ _ hf, h.const _ _ hk]
    exact h.sat e he

omit [DecidableEq α] in
private theorem foldl_freeze_get (c : α) (l : List ℕ) (t : List (Option (α → α))) (v : ℕ) :
    (l.foldl (fun t w => t.set w (freeze c (t.getD w none))) t).getD v none =
      if v ∈ l then freeze c (t.getD v none) else t.getD v none := by
  induction l generalizing t with
  | nil => simp
  | cons w l ih =>
    rw [List.foldl_cons, ih]
    by_cases hvw : w = v
    · subst hvw
      by_cases hlt : w < t.length
      · rw [List.getD_set_self hlt]
        have hidem : freeze c (freeze c (t.getD w none)) = freeze c (t.getD w none) := by
          cases t.getD w none <;> rfl
        split_ifs <;> simp_all
      · rw [List.set_eq_of_length_le (by omega)]
        have : t.getD w none = none := List.getD_eq_default _ _ (by omega)
        rw [this]
        split_ifs <;> rfl
    · rw [List.getD_set_ne hvw]
      simp [Ne.symm hvw]

omit [DecidableEq α] in
private theorem foldl_freeze_length (c : α) (l : List ℕ) (t : List (Option (α → α))) :
    (l.foldl (fun t w => t.set w (freeze c (t.getD w none))) t).length = t.length := by
  induction l generalizing t with
  | nil => rfl
  | cons w l ih => rw [List.foldl_cons, ih, List.length_set]

omit [DecidableEq α] in
/-- Settling freezes exactly the tables of the component. -/
private theorem settle_get [Inhabited α] (labels : List α) (S : State α) (v : ℕ) :
    (settle labels S).get v =
      if v ∈ S.comp then freeze ((labels.find? S.cand).getD default) (S.get v) else S.get v :=
  foldl_freeze_get _ _ _ _

omit [DecidableEq α] in
/-- Settling keeps the number of slots. -/
private theorem settle_length [Inhabited α] (labels : List α) (S : State α) :
    (settle labels S).table.length = S.table.length :=
  foldl_freeze_length _ _ _

omit [DecidableEq α] in
/-- Settling keeps the visited slots. -/
private theorem settle_isSome [Inhabited α] (labels : List α) (S : State α) (v : ℕ) :
    ((settle labels S).get v).isSome = (S.get v).isSome := by
  rw [settle_get]
  split_ifs <;> simp [freeze]

omit [DecidableEq α] in
/-- Settling keeps the unvisited slots. -/
private theorem unvisited_settle [Inhabited α] (labels : List α) (S : State α) :
    (settle labels S).unvisited = S.unvisited := by
  ext v
  simp only [State.unvisited, Finset.mem_filter, Finset.mem_range, settle_length,
    Option.isNone_iff_eq_none, ← Option.not_isSome_iff_eq_none, settle_isSome]

omit [DecidableEq α] in
private theorem settle_get_none [Inhabited α] (labels : List α) {S : State α} {v : ℕ}
    (hv : S.get v = none) : (settle labels S).get v = none := by
  rw [settle_get]
  split_ifs <;> simp [hv, freeze]

omit [DecidableEq α] in
/-- Settling a finished component preserves `Good`, against an updated labelling. -/
private theorem good_settle [Inhabited α] {labels : List α} (hlabels : ∀ a, a ∈ labels)
    {g : Graph (α → α)} {τ : ℕ → α} {s : ℕ} {S0 S : State α} (h0 : Good g τ S0)
    (h : Inv g τ s S0 S) (hstack : S.stack = []) :
    Good g (fun v => ((settle labels S).get v).elim (τ v) fun f => f default)
      (settle labels S) := by
  set c := (labels.find? S.cand).getD default with hc
  have hcand : S.cand c = true := by
    cases hf : labels.find? S.cand with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd h.sem.cand (by simpa using hf _ (hlabels _))
    | some b => simp only [hc, hf, Option.getD_some]; exact List.find?_some hf
  -- every stored table outside the component is an old constant
  have hold : ∀ v f, S.get v = some f → v ∉ S.comp → ∀ a, f a = f c := by
    intro v f hv hvc a
    cases h0v : S0.get v with
    | none =>
      rcases h.fresh v (by simp [hv]) (by simp [h0v]) with h1 | h1
      · simp [hstack] at h1
      · exact absurd h1 hvc
    | some f0 =>
      have := h.old v f0 h0v
      rw [hv] at this
      cases this
      rw [h0.const v f h0v a, h0.const v f h0v c]
  have hval : ∀ v f, S.get v = some f → (settle labels S).get v = some (fun _ => f c) := by
    intro v f hv
    rw [settle_get]
    split_ifs with hvc
    · rw [hv]; rfl
    · rw [hv]; congr 1 with a : 1; exact hold v f hv hvc a
  have hτ' : ∀ v f, S.get v = some f →
      ((settle labels S).get v).elim (τ v) (fun f => f default) = f c := by
    intro v f hv; rw [hval v f hv]; rfl
  have hclosed : ∀ e ∈ g.edges, (S.get e.src).isSome ∨ (S.get e.dst).isSome → S.Settled e := by
    intro e he hor
    apply h.settled e he
    rcases hor with h1 | h1
    · exact Or.inl ⟨h1, by simp [hstack]⟩
    · exact Or.inr ⟨h1, by simp [hstack]⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [settle_length]; exact h.length
  · intro v f hv a
    cases hS : S.get v with
    | none => rw [settle_get_none labels hS] at hv; cases hv
    | some f' =>
      rw [hval v f' hS] at hv
      cases hv
      exact (hτ' v f' hS).symm
  · intro e he
    rw [settle_isSome, settle_isSome]
    by_cases hor : (S.get e.src).isSome ∨ (S.get e.dst).isSome
    · obtain ⟨f, k, hf, hk, -⟩ := hclosed e he hor
      rw [hf, hk]; rfl
    · simp only [not_or, Bool.not_eq_true] at hor
      rw [hor.1, hor.2]
  · intro e he
    by_cases hor : (S.get e.src).isSome ∨ (S.get e.dst).isSome
    · obtain ⟨f, k, hf, hk, hfk⟩ := hclosed e he hor
      rw [hτ' _ _ hf, hτ' _ _ hk]
      exact hfk c hcand
    · simp only [not_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
        at hor
      rw [settle_get_none labels hor.1, settle_get_none labels hor.2]
      exact h0.sat e he

private theorem step_good [Inhabited α] {labels : List α} (hlabels : ∀ a, a ∈ labels)
    {g : Graph (α → α)} (hinj : ∀ e ∈ g.edges, Function.Injective e.constraint) {τ : ℕ → α}
    {S : State α} (h : Good g τ S) {e : Edge (α → α)} (he : e ∈ g.edges) :
    ∃ τ', Good g τ' (step labels g S e) := by
  unfold step
  cases hs : S.get e.src with
  | some _ => exact ⟨τ, h⟩
  | none =>
    have hlt : e.src < S.table.length := h.length ▸ src_lt_slots he
    have hinv := inv_iterate_scan hlabels hinj h.sat (inv_start h hlt hs) (slots g)
    have hnil := iterate_scan_eq_nil labels g (S := start S e.src)
      (by simp [start, h.length]) (potential_start h.length hlt)
    exact ⟨_, good_settle hlabels h hinv hnil⟩

private theorem get_step [Inhabited α] (labels : List α) (g : Graph (α → α)) {S : State α}
    (e : Edge (α → α)) {v : ℕ} (hv : (S.get v).isSome) :
    ((step labels g S e).get v).isSome := by
  unfold step
  cases hs : S.get e.src with
  | some _ => exact hv
  | none =>
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 hv
    have hne : e.src ≠ v := by rintro rfl; simp [hs] at hf
    have h1 : (start S e.src).get v = some f := by rw [← hf]; exact List.getD_set_ne hne
    rw [settle_isSome, get_iterate_scan labels g _ h1]; rfl

private theorem step_src [Inhabited α] (labels : List α) (g : Graph (α → α)) {S : State α}
    (hlen : S.table.length = slots g) {e : Edge (α → α)} (he : e ∈ g.edges) :
    ((step labels g S e).get e.src).isSome := by
  unfold step
  cases hs : S.get e.src with
  | some f => change (S.get e.src).isSome = true; rw [hs]; rfl
  | none =>
    have hlt : e.src < S.table.length := hlen ▸ src_lt_slots he
    have h1 : (start S e.src).get e.src = some id := List.getD_set_self hlt
    rw [settle_isSome, get_iterate_scan labels g _ h1]; rfl

/-- A step of the outer loop keeps the number of slots. -/
private theorem length_step [Inhabited α] (labels : List α) (g : Graph (α → α)) (S : State α)
    (e : Edge (α → α)) : (step labels g S e).table.length = S.table.length := by
  unfold step
  split
  · rfl
  · rw [settle_length, length_iterate_scan]
    exact List.length_set

private theorem foldl_step_isSome [Inhabited α] (labels : List α) (g : Graph (α → α))
    (l : List (Edge (α → α))) {S : State α} {v : ℕ} (hv : (S.get v).isSome) :
    ((l.foldl (step labels g) S).get v).isSome := by
  induction l generalizing S with
  | nil => exact hv
  | cons e l ih => exact ih (get_step labels g e hv)

private theorem foldl_step_good [Inhabited α] {labels : List α} (hlabels : ∀ a, a ∈ labels)
    {g : Graph (α → α)} (hinj : ∀ e ∈ g.edges, Function.Injective e.constraint)
    (l : List (Edge (α → α))) (hl : ∀ e ∈ l, e ∈ g.edges) {τ : ℕ → α} {S : State α}
    (h : Good g τ S) :
    ∃ τ', Good g τ' (l.foldl (step labels g) S) ∧
      ∀ e ∈ l, ((l.foldl (step labels g) S).get e.src).isSome := by
  induction l generalizing τ S with
  | nil => exact ⟨τ, h, by simp⟩
  | cons e l ih =>
    obtain ⟨τ1, h1⟩ := step_good hlabels hinj h (hl e (by simp))
    obtain ⟨τ2, h2, hsrc⟩ := ih (fun d hd => hl d (List.mem_cons_of_mem _ hd)) h1
    refine ⟨τ2, h2, ?_⟩
    rw [List.forall_mem_cons]
    exact ⟨foldl_step_isSome labels g l (step_src labels g h.length (hl e (by simp))), hsrc⟩

omit [DecidableEq α] in
private theorem good_init {g : Graph (α → α)} {τ : ℕ → α}
    (hτ : ∀ e ∈ g.edges, e.constraint (τ e.src) = τ e.dst) : Good g τ (init g) where
  length := List.length_replicate
  const v f hv := by simp [init, State.get] at hv
  closed e _ := by simp [init, State.get]
  sat := hτ

end Outer

/-! ## Completeness -/

section Completeness

variable {α : Type} [DecidableEq α]

/-- **Completeness of the extracted labelling**: if `labels` contains every label, every edge
carries an injective table and the instance is satisfiable, the extracted labelling satisfies
every edge. -/
theorem check_labelling [Inhabited α] {labels : List α} (hlabels : ∀ a, a ∈ labels)
    {g : Graph (α → α)} (hinj : ∀ e ∈ g.edges, Function.Injective e.constraint)
    (hsat : (g.toGraph permutationEval).Satisfiable) :
    check g (labelling labels g) = true := by
  obtain ⟨σ, hσ⟩ := hsat
  have hσ' : ∀ e ∈ g.edges, e.constraint (σ e.src) = σ e.dst := by
    have := (check_eq_true_iff g σ).2 hσ
    simpa [check] using this
  obtain ⟨τ, hτ, hsrc⟩ := foldl_step_good (labels := labels) hlabels hinj g.edges
    (fun _ h => h) (good_init hσ')
  change Good g τ (run labels g) at hτ
  rw [check, List.all_eq_true]
  intro e he
  have h1 : ((run labels g).get e.src).isSome := hsrc e he
  have h2 : ((run labels g).get e.dst).isSome := (hτ.closed e he) ▸ h1
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 h2
  simp only [labelling, hf, hk, Option.elim_some, decide_eq_true_eq]
  rw [hτ.const _ _ hf, hτ.const _ _ hk]
  exact hτ.sat e he

/-- **Completeness**: if `labels` contains every label, every edge carries an injective table and
the instance is satisfiable, `solve` returns the extracted labelling. -/
theorem solve_eq_some_labelling [Inhabited α] {labels : List α} (hlabels : ∀ a, a ∈ labels)
    {g : Graph (α → α)} (hinj : ∀ e ∈ g.edges, Function.Injective e.constraint)
    (hsat : (g.toGraph permutationEval).Satisfiable) :
    solve labels g = some (labelling labels g) := by
  simp only [solve, check_labelling hlabels hinj hsat, ite_true]

/-- On unique games, `solve` succeeds exactly on the satisfiable instances. -/
theorem solve_isSome_iff [Inhabited α] {labels : List α} (hlabels : ∀ a, a ∈ labels)
    {g : Graph (α → α)} (hg : IsUniqueGame g) :
    (solve labels g).isSome ↔ (g.toGraph permutationEval).Satisfiable := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1 h
    exact ⟨σ, solve_sound hσ⟩
  · intro h
    rw [solve_eq_some_labelling hlabels (fun e he => (hg e he).1) h]
    rfl

/-- On unique games, `solve` succeeds exactly on the instances of value `1`, those with no
unsatisfied proportion. -/
theorem solve_isSome_iff_unsatVal_eq_zero [Inhabited α] {labels : List α}
    (hlabels : ∀ a, a ∈ labels) {g : Graph (α → α)} (hg : IsUniqueGame g) :
    (solve labels g).isSome ↔ (g.toGraph permutationEval).unsatVal = 0 := by
  rw [solve_isSome_iff hlabels hg, (g.toGraph permutationEval).unsatVal_eq_zero_iff]

end Completeness

end Cslib.Complexity.UniqueGames.Propagation

namespace Cslib.Complexity

open Cslib.PCP Cslib.PCP.Encoded UniqueGames.Propagation

variable {α : Type}

/-- The yes-instances of `GapUniqueGames α 1 s` are the satisfiable unique games. -/
theorem mem_yes_gapUniqueGames_one_iff [DecidableEq α] [Nonempty α] {s : ℝ}
    {g : Graph (α → α)} :
    g ∈ (GapUniqueGames α 1 s).yes ↔
      IsUniqueGame g ∧ (g.toGraph permutationEval).Satisfiable := by
  simp only [GapUniqueGames, PromiseProblem.yes_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_yes_gapMax, Set.mem_ofPred_eq]
  rw [← (g.toGraph permutationEval).unsatVal_eq_zero_iff]
  have := (g.toGraph permutationEval).unsatVal_nonneg
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩

/-- **Satisfiable unique games are easy** [Khot, Section 2.4][Khot2010]: label propagation
decides `GapUniqueGames α 1 s` for every soundness `s`, given a list of all labels. This is the
decision problem only; its step count in an explicit cost model is in
`CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime`. -/
theorem solvedBy_gapUniqueGames_one [DecidableEq α] [Inhabited α] {labels : List α}
    (hlabels : ∀ a, a ∈ labels) (s : ℝ) :
    (GapUniqueGames α 1 s).SolvedBy fun g => (solve labels g).isSome := by
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨hu, hsat⟩ := mem_yes_gapUniqueGames_one_iff.1 hg
    exact (solve_isSome_iff hlabels hu).2 hsat
  · obtain ⟨⟨h1, h2⟩, hu⟩ := hg
    rw [Bool.eq_false_iff]
    intro h
    have h0 := (solve_isSome_iff_unsatVal_eq_zero hlabels hu).1 h
    simp only at h1 h2
    rw [h0] at h1
    linarith

end Cslib.Complexity
