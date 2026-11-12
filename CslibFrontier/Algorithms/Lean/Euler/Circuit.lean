/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Logic.Relation
public import CslibFrontier.Foundations.Data.List.ConsecutivePairs

/-!
# Euler circuits in finite multigraphs

A finite multigraph is given by a list `H : List (α × α)` of edges; parallel edges and self-loops
are allowed, and an edge `(a, b)` may be traversed in either direction. Its edges are compared up
to orientation through `undirected : α × α → Sym2 α`. A walk is a list of vertices and uses the
edges between consecutive entries (Mathlib's `List.consecutivePairs`). An **Euler circuit** of
`H` from `u` (`IsEulerCircuit H u w`) is a walk `w` from `u` back to `u` whose edges are those of
`H`, each used exactly once, in either direction.

**Euler's theorem** (`exists_isEulerCircuit_iff`): `H` has an Euler circuit from `u` exactly when
every vertex has even degree (`degree`, where a self-loop counts twice) and every edge is
connected to `u` by edges of `H`. Sufficiency is constructive: `eulerCircuit H u` runs
Hierholzer's algorithm, which walks greedily from `u` along unused edges (`walkFrom`) until it
returns, then repeatedly splices in a closed walk from a visited vertex that still has unused
edges (`splice`, `eulerLoop`).

## Model

Vertices form any type with decidable equality. The degree of `x` counts the endpoints of edges
of `H` equal to `x`. Connectivity is phrased with `Relation.EqvGen` of the relation "`(a, b)` is an
edge of `H`", analogous to `Cslib.Algorithms.Lean.TSP.eqvGen_kruskalEdges_completeEdges`.
Vertices without edges are irrelevant: the condition only concerns endpoints of edges, and the
empty multigraph has the Euler circuit `[u]`. Compared with the textbook statement for connected
graphs ([KorteVygen2018], Section 2.4), the model thus generalizes in three harmless ways:
connectivity is required of edges only, the empty multigraph is allowed, and so are self-loops.
Mathlib's `SimpleGraph.Walk.IsEulerian` proves the necessity of even degrees for simple graphs;
the list model here admits the multigraphs that Christofides' algorithm builds (a spanning tree
together with a matching may repeat an edge).

## Main definitions

* `Cslib.Algorithms.Lean.Euler.undirected`: an ordered pair as an unordered edge.
* `Cslib.Algorithms.Lean.Euler.IsEulerCircuit`: a closed walk using each edge once.
* `Cslib.Algorithms.Lean.Euler.degree`: the degree of a vertex in an edge list.
* `Cslib.Algorithms.Lean.Euler.walkFrom`: the greedy walk along unused edges.
* `Cslib.Algorithms.Lean.Euler.splice`: splice a closed walk into a walk at a vertex.
* `Cslib.Algorithms.Lean.Euler.eulerLoop`: repeatedly splice in closed walks.
* `Cslib.Algorithms.Lean.Euler.eulerCircuit`: Hierholzer's algorithm.

## Main results

* `Cslib.Algorithms.Lean.Euler.walkFrom_spec`: the trail lemma. When `u` and `t` are the only
  vertices of odd degree (or all degrees are even and `u = t`), the greedy walk from `u` ends at
  `t`, and the unused edges have even degrees.
* `Cslib.Algorithms.Lean.Euler.isEulerCircuit_eulerCircuit`: Hierholzer's algorithm returns an
  Euler circuit of every connected multigraph with even degrees.
* `Cslib.Algorithms.Lean.Euler.even_degree_of_isEulerCircuit`,
  `Cslib.Algorithms.Lean.Euler.eqvGen_of_isEulerCircuit`: the converse conditions.
* `Cslib.Algorithms.Lean.Euler.exists_isEulerCircuit_iff`: Euler's theorem.
* `Cslib.Algorithms.Lean.Euler.mem_of_isEulerCircuit`: an Euler circuit visits every vertex
  connected to its start.
* `Cslib.Algorithms.Lean.Euler.sum_map_consecutivePairs_eq`: for a symmetric weight, an Euler
  circuit weighs as much as its multigraph.

## References

* [C. Hierholzer, *Ueber die Möglichkeit, einen Linienzug ohne Wiederholung und ohne Unterbrechung
  zu umfahren*][Hierholzer1873]
* [B. Korte, J. Vygen, *Combinatorial Optimization: Theory and Algorithms*][KorteVygen2018],
  Section 2.4.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Euler

variable {α : Type*}

/-! ### Walks and their edges -/

/-! The edges of a walk `w` are the pairs of its consecutive entries, Mathlib's
`w.consecutivePairs` (`w.zip w.tail`). -/

/-- The unordered edge `{a, b}` underlying the ordered pair `(a, b)`. -/
def undirected (e : α × α) : Sym2 α := s(e.1, e.2)

@[simp] theorem undirected_mk (a b : α) : undirected (a, b) = s(a, b) := rfl

/-- Splitting a walk at a vertex `x` splits its edges. This generalizes
`Cslib.Orthogonal.consecutivePairs_join`, which joins routes of points at a common endpoint. -/
theorem consecutivePairs_append_cons (A : List α) (x : α) (B : List α) :
    (A ++ x :: B).consecutivePairs = (A ++ [x]).consecutivePairs ++ (x :: B).consecutivePairs := by
  induction A with
  | nil => simp
  | cons a A ih =>
    cases A with
    | nil => simp
    | cons b A =>
      simp only [List.cons_append, List.consecutivePairs_cons_cons] at ih ⊢
      rw [ih]

theorem mem_of_mem_consecutivePairs {w : List α} {e : α × α} (h : e ∈ w.consecutivePairs) :
    e.1 ∈ w ∧ e.2 ∈ w := by
  induction w with
  | nil => simp at h
  | cons a l ih =>
    cases l with
    | nil => simp at h
    | cons b l =>
      rw [List.consecutivePairs_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · obtain ⟨h1, h2⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

/-- A walk whose steps are related by `EqvGen r` relates its first vertex to all of its
vertices. -/
theorem eqvGen_of_mem_cons {r : α → α → Prop} :
    ∀ {a : α} {l : List α}, (∀ e ∈ (a :: l).consecutivePairs, Relation.EqvGen r e.1 e.2) →
      ∀ y ∈ a :: l, Relation.EqvGen r a y
  | a, [], _, y, hy => by rw [List.mem_singleton.mp hy]; exact .refl _
  | a, b :: l, h, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .refl _
    · exact .trans _ _ _ (h (a, b) (by simp))
        (eqvGen_of_mem_cons (fun e he => h e (by simp [he])) y hy)

/-- Replacing one occurrence of `x` by a closed walk `c` from `x` adds the edges of `c`. -/
theorem consecutivePairs_append_append {A c B : List α} {x : α} (hc1 : c.head? = some x)
    (hc2 : c.getLast? = some x) :
    (A ++ c ++ B).consecutivePairs.Perm
      ((A ++ x :: B).consecutivePairs ++ c.consecutivePairs) := by
  obtain ⟨c₁, rfl⟩ := List.head?_eq_some_iff.mp hc1
  obtain ⟨c₂, hc₂⟩ := List.getLast?_eq_some_iff.mp hc2
  have e1 : A ++ x :: c₁ ++ B = A ++ x :: (c₁ ++ B) := by simp
  have e2 : x :: (c₁ ++ B) = c₂ ++ x :: B := by
    rw [← List.cons_append, hc₂]
    simp
  rw [e1, consecutivePairs_append_cons A x (c₁ ++ B), e2, consecutivePairs_append_cons c₂ x B,
    ← hc₂, consecutivePairs_append_cons A x B, List.append_assoc]
  exact List.Perm.append_left _ List.perm_append_comm

theorem head?_append_append {A c B : List α} {x : α} (hc1 : c.head? = some x) :
    (A ++ c ++ B).head? = (A ++ x :: B).head? := by
  obtain ⟨c₁, rfl⟩ := List.head?_eq_some_iff.mp hc1
  cases A <;> simp

theorem getLast?_append_append {A c B : List α} {x : α} (hc2 : c.getLast? = some x) :
    (A ++ c ++ B).getLast? = (A ++ x :: B).getLast? := by
  simp only [List.getLast?_append, hc2, List.getLast?_cons]
  cases B.getLast? <;> rfl

/-! ### Euler circuits -/

/-- `w` is an **Euler circuit** of the multigraph `H` from `u`: a walk from `u` back to `u` that
uses every edge of `H` exactly once, in either direction. -/
structure IsEulerCircuit (H : List (α × α)) (u : α) (w : List α) : Prop where
  /-- The walk starts at `u`. -/
  head : w.head? = some u
  /-- The walk ends at `u`. -/
  getLast : w.getLast? = some u
  /-- The walk uses the edges of `H`, each once, in either direction. -/
  perm : (w.consecutivePairs.map undirected).Perm (H.map undirected)

/-- **Euler's theorem, necessity of connectivity**: every edge of a multigraph with an Euler
circuit from `u` is connected to `u`. -/
theorem eqvGen_of_isEulerCircuit {H : List (α × α)} {u : α} {w : List α}
    (h : IsEulerCircuit H u w) : ∀ e ∈ H, Relation.EqvGen (fun a b => (a, b) ∈ H) e.1 u := by
  obtain ⟨w', rfl⟩ := List.head?_eq_some_iff.mp h.head
  have hstep :
      ∀ e ∈ (u :: w').consecutivePairs, Relation.EqvGen (fun a b => (a, b) ∈ H) e.1 e.2 := by
    intro ⟨a, b⟩ he
    have hm : undirected (a, b) ∈ H.map undirected := h.perm.subset (List.mem_map_of_mem he)
    obtain ⟨⟨c, d⟩, hcd, hce⟩ := List.mem_map.mp hm
    simp only [undirected_mk, Sym2.eq_iff] at hce
    rcases hce with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .rel _ _ hcd
    · exact .symm _ _ (.rel _ _ hcd)
  intro e he
  have hm : undirected e ∈ (u :: w').consecutivePairs.map undirected :=
    h.perm.symm.subset (List.mem_map_of_mem he)
  obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hm
  have hf12 := mem_of_mem_consecutivePairs hf
  have he1 : e.1 ∈ u :: w' := by
    obtain ⟨a, b⟩ := e
    obtain ⟨c, d⟩ := f
    simp only [undirected_mk, Sym2.eq_iff] at hfe
    rcases hfe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hf12.1
    · exact hf12.2
  exact .symm _ _ (eqvGen_of_mem_cons hstep _ he1)

/-- An Euler circuit from `u` visits every vertex connected to `u` by edges of `H`. -/
theorem mem_of_isEulerCircuit {H : List (α × α)} {u : α} {w : List α} (h : IsEulerCircuit H u w)
    {x : α} (hx : Relation.EqvGen (fun a b => (a, b) ∈ H) x u) : x ∈ w := by
  have hedge : ∀ e ∈ H, e.1 ∈ w ∧ e.2 ∈ w := by
    intro ⟨a, b⟩ he
    obtain ⟨⟨c, d⟩, hf, hfe⟩ := List.mem_map.mp (h.perm.symm.subset (List.mem_map_of_mem he))
    have hf12 := mem_of_mem_consecutivePairs hf
    simp only [undirected_mk, Sym2.eq_iff] at hfe
    rcases hfe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hf12
    · exact ⟨hf12.2, hf12.1⟩
  have hu : u ∈ w := by
    obtain ⟨w', rfl⟩ := List.head?_eq_some_iff.mp h.head
    exact List.mem_cons_self ..
  suffices ∀ a b, Relation.EqvGen (fun a b => (a, b) ∈ H) a b → (a ∈ w ↔ b ∈ w) from
    (this x u hx).2 hu
  intro a b hab
  induction hab with
  | rel a b hab => exact ⟨fun _ => (hedge _ hab).2, fun _ => (hedge _ hab).1⟩
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- For a symmetric weight `δ`, an Euler circuit of `H` weighs as much as `H`. -/
theorem sum_map_consecutivePairs_eq {β : Type*} [AddCommMonoid β] {δ : α → α → β}
    (hsymm : ∀ a b, δ a b = δ b a) {H : List (α × α)} {u : α} {w : List α}
    (h : IsEulerCircuit H u w) :
    (w.consecutivePairs.map fun e => δ e.1 e.2).sum = (H.map fun e => δ e.1 e.2).sum := by
  have hd : ∀ L : List (α × α), (L.map fun e => δ e.1 e.2).sum =
      ((L.map undirected).map (Sym2.lift ⟨δ, hsymm⟩)).sum := by
    intro L
    simp only [List.map_map]
    rfl
  rw [hd, hd]
  exact (h.perm.map _).sum_eq

/-! ### Degrees -/

variable [DecidableEq α]

/-- The number of endpoints of `e` equal to `x`: `2` for a self-loop at `x`. -/
def ends (x : α) (e : α × α) : ℕ := (if x = e.1 then 1 else 0) + (if x = e.2 then 1 else 0)

/-- The degree of `x` in the multigraph with edge list `H`; a self-loop at `x` counts twice. -/
def degree (H : List (α × α)) (x : α) : ℕ := (H.map (ends x)).sum

@[simp] theorem degree_nil (x : α) : degree [] x = 0 := rfl

@[simp] theorem degree_cons (e : α × α) (H : List (α × α)) (x : α) :
    degree (e :: H) x = ends x e + degree H x := by
  simp [degree]

theorem degree_append (H K : List (α × α)) (x : α) :
    degree (H ++ K) x = degree H x + degree K x := by
  simp [degree]

/-- The degree depends only on the edges up to orientation. -/
theorem degree_eq_of_perm {H K : List (α × α)}
    (h : (H.map undirected).Perm (K.map undirected)) (x : α) : degree H x = degree K x := by
  have hd : ∀ L : List (α × α), degree L x = ((L.map undirected).map (Sym2.lift
      ⟨fun a b => (if x = a then 1 else 0) + (if x = b then 1 else 0),
        fun _ _ => Nat.add_comm _ _⟩)).sum := by
    intro L
    simp only [degree, List.map_map]
    rfl
  rw [hd, hd]
  exact (h.map _).sum_eq

/-- Twice the number of visits to `x` counts the edges of the walk at `x`, plus one for each end
of the walk at `x`. -/
theorem degree_consecutivePairs_cons (a : α) (l : List α) (x : α) :
    degree (a :: l).consecutivePairs x + (if x = a then 1 else 0) +
      (if x = (a :: l).getLast (List.cons_ne_nil a l) then 1 else 0) = 2 * (a :: l).count x := by
  induction l generalizing a with
  | nil =>
    by_cases h : x = a
    · subst h
      simp
    · simp [h, Ne.symm h]
  | cons b l ih =>
    have := ih b
    rw [List.consecutivePairs_cons_cons, degree_cons, List.getLast_cons_cons, List.count_cons]
    simp only [ends, beq_iff_eq] at this ⊢
    by_cases h : x = a
    · subst h
      simp only [ite_true] at this ⊢
      omega
    · simp only [h, ite_false, Ne.symm h] at this ⊢
      omega

/-- **Euler's theorem, necessity of even degrees**: a multigraph with an Euler circuit has only
vertices of even degree. -/
theorem even_degree_of_isEulerCircuit {H : List (α × α)} {u : α} {w : List α}
    (h : IsEulerCircuit H u w) (x : α) : Even (degree H x) := by
  obtain ⟨w', rfl⟩ := List.head?_eq_some_iff.mp h.head
  have hl : (u :: w').getLast (List.cons_ne_nil _ _) = u := by
    have := h.getLast
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at this
    exact Option.some.inj this
  have := degree_consecutivePairs_cons u w' x
  rw [hl] at this
  rw [← degree_eq_of_perm h.perm]
  exact Nat.even_iff.mpr (by split_ifs at this <;> omega)

/-! ### Greedy walks -/

/-- Whether `x` is an endpoint of `e`. -/
def touches (x : α) (e : α × α) : Bool := decide (x = e.1) || decide (x = e.2)

/-- The endpoint of `e` other than `x` (the second one when `x` is the first). -/
def other (x : α) (e : α × α) : α := if x = e.1 then e.2 else e.1

theorem undirected_eq_of_touches {x : α} {e : α × α} (h : touches x e = true) :
    undirected e = undirected (x, other x e) := by
  obtain ⟨a, b⟩ := e
  simp only [touches, Bool.or_eq_true, decide_eq_true_eq] at h
  by_cases ha : x = a
  · subst ha
    simp [other]
  · have hb : x = b := h.resolve_left ha
    subst hb
    simp only [other, ha, ↓reduceIte, undirected_mk]
    exact Sym2.eq_swap

theorem ends_of_touches {x : α} {e : α × α} (h : touches x e = true) (y : α) :
    ends y e = (if y = x then 1 else 0) + (if y = other x e then 1 else 0) := by
  obtain ⟨a, b⟩ := e
  simp only [touches, Bool.or_eq_true, decide_eq_true_eq] at h
  by_cases ha : x = a
  · subst ha
    simp [other, ends]
  · have hb : x = b := h.resolve_left ha
    subst hb
    simp only [other, ends, ha, ↓reduceIte]
    exact Nat.add_comm _ _

theorem degree_eq_zero_of_find?_eq_none {H : List (α × α)} {u : α}
    (h : H.find? (touches u) = none) : degree H u = 0 := by
  rw [List.find?_eq_none] at h
  unfold degree
  apply List.sum_eq_zero
  intro n hn
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hn
  have := h e he
  simp only [touches, Bool.or_eq_true, decide_eq_true_eq, not_or] at this
  simp [ends, this.1, this.2]

/-- Follow unused edges of `H` greedily from `u`, for at most `fuel` steps. Returns the walk and
the edges it did not use. -/
def walkFrom : ℕ → List (α × α) → α → List α × List (α × α)
  | 0, H, u => ([u], H)
  | fuel + 1, H, u =>
    match H.find? (touches u) with
    | none => ([u], H)
    | some e =>
      let r := walkFrom fuel (H.erase e) (other u e)
      (u :: r.1, r.2)

theorem length_walkFrom_snd_le (fuel : ℕ) (H : List (α × α)) (u : α) :
    (walkFrom fuel H u).2.length ≤ H.length := by
  induction fuel generalizing H u with
  | zero => simp [walkFrom]
  | succ fuel ih =>
    simp only [walkFrom]
    split
    · exact le_rfl
    · exact (ih _ _).trans (List.length_erase_le ..)

/-- A greedy walk from a vertex with an unused edge uses at least one edge. -/
theorem length_walkFrom_snd_lt {fuel : ℕ} (hfuel : 0 < fuel) {H : List (α × α)} {u : α}
    {e : α × α} (he : e ∈ H) (hte : touches u e = true) :
    (walkFrom fuel H u).2.length < H.length := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    simp only [walkFrom]
    split
    · rename_i hnone
      rw [List.find?_eq_none] at hnone
      exact absurd hte (hnone e he)
    · rename_i f hf
      have hfH := List.mem_of_find?_eq_some hf
      calc _ ≤ (H.erase f).length := length_walkFrom_snd_le ..
        _ < H.length := by
          rw [List.length_erase_of_mem hfH]
          have := List.length_pos_of_mem hfH
          omega

/-- **The trail lemma.** Suppose that `u` and `t` are the only vertices of odd degree in `H`, or
that all degrees are even and `u = t`. Then the greedy walk from `u` ends at `t`, it and the unused
edges together are the edges of `H`, and the unused edges have even degrees. -/
theorem walkFrom_spec (fuel : ℕ) (H : List (α × α)) (u t : α) (hfuel : H.length ≤ fuel)
    (hpar : ∀ y, (degree H y + (if y = u then 1 else 0) + (if y = t then 1 else 0)) % 2 = 0) :
    (walkFrom fuel H u).1.head? = some u ∧ (walkFrom fuel H u).1.getLast? = some t ∧
      (H.map undirected).Perm
        (((walkFrom fuel H u).1.consecutivePairs ++ (walkFrom fuel H u).2).map undirected) ∧
      ∀ y, degree (walkFrom fuel H u).2 y % 2 = 0 := by
  induction fuel generalizing H u with
  | zero =>
    have hH : H = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hfuel)
    subst hH
    have hu := hpar u
    have hut : u = t := by
      by_contra h
      simp [h] at hu
    subst hut
    simp [walkFrom]
  | succ fuel ih =>
    cases hfind : H.find? (touches u) with
    | none =>
      have hdeg := degree_eq_zero_of_find?_eq_none hfind
      have hut : u = t := by
        by_contra h
        have hu := hpar u
        simp [h, hdeg] at hu
      subst hut
      simp only [walkFrom, hfind]
      refine ⟨rfl, rfl, by simp, fun y => ?_⟩
      have := hpar y
      split_ifs at this <;> omega
    | some e =>
      have he : e ∈ H := List.mem_of_find?_eq_some hfind
      have hte : touches u e = true := List.find?_some hfind
      have hperm : H.Perm (e :: H.erase e) := List.perm_cons_erase he
      have hlen : (H.erase e).length ≤ fuel := by
        rw [List.length_erase_of_mem he]
        omega
      have hpar' : ∀ y, (degree (H.erase e) y + (if y = other u e then 1 else 0) +
          (if y = t then 1 else 0)) % 2 = 0 := by
        intro y
        have h1 := hpar y
        rw [degree_eq_of_perm (hperm.map undirected), degree_cons, ends_of_touches hte] at h1
        split_ifs at h1 ⊢ <;> omega
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih (H.erase e) (other u e) hlen hpar'
      obtain ⟨r1, hr1⟩ := List.head?_eq_some_iff.mp ih1
      simp only [walkFrom, hfind]
      rw [hr1] at ih2 ih3 ⊢
      refine ⟨rfl, by simpa using ih2, ?_, ih4⟩
      simp only [List.consecutivePairs_cons_cons, List.cons_append, List.map_cons]
      refine (hperm.map undirected).trans ?_
      rw [List.map_cons, undirected_eq_of_touches hte]
      exact ih3.cons _

/-! ### Splicing closed walks -/

/-- Splice `c` into `w` in place of the first occurrence of `x`. -/
def splice (x : α) (c : List α) : List α → List α
  | [] => []
  | a :: w => if a = x then c ++ w else a :: splice x c w

theorem exists_splice {x : α} (c : List α) {w : List α} (hx : x ∈ w) :
    ∃ A B, w = A ++ x :: B ∧ splice x c w = A ++ c ++ B := by
  induction w with
  | nil => simp at hx
  | cons a w ih =>
    by_cases ha : a = x
    · subst ha
      exact ⟨[], w, rfl, by simp [splice]⟩
    · have hx' : x ∈ w := (List.mem_cons.mp hx).resolve_left (Ne.symm ha)
      obtain ⟨A, B, h1, h2⟩ := ih hx'
      exact ⟨a :: A, B, by simp [h1], by simp [splice, ha, h2]⟩

/-- If the edges of `H` are connected to a vertex of `w`, and the edges of `w` together with `R`
are those of `H`, then some vertex of `w` touches an edge of `R`, unless `R` is empty. -/
theorem eq_nil_of_forall_not_touches {H R : List (α × α)} {w : List α} {u : α} (hu : u ∈ w)
    (hconn : ∀ e ∈ H, Relation.EqvGen (fun a b => (a, b) ∈ H) e.1 u)
    (hperm : (H.map undirected).Perm ((w.consecutivePairs ++ R).map undirected))
    (hnt : ∀ x ∈ w, ∀ e ∈ R, touches x e = false) : R = [] := by
  have key : ∀ y z, Relation.EqvGen (fun a b => (a, b) ∈ H) y z → (y ∈ w ↔ z ∈ w) := by
    intro y z h
    induction h with
    | rel a b hab =>
      have hm : undirected (a, b) ∈ (w.consecutivePairs ++ R).map undirected :=
        hperm.subset (List.mem_map_of_mem hab)
      obtain ⟨⟨f1, f2⟩, hf, hfe⟩ := List.mem_map.mp hm
      simp only [undirected_mk, Sym2.eq_iff] at hfe
      rcases List.mem_append.mp hf with hf | hf
      · have := mem_of_mem_consecutivePairs hf
        rcases hfe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
      · have n1 : f1 ∉ w := fun hm => by simpa [touches] using hnt f1 hm _ hf
        have n2 : f2 ∉ w := fun hm => by simpa [touches] using hnt f2 hm _ hf
        rcases hfe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [n1, n2]
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  cases R with
  | nil => rfl
  | cons e R' =>
    exfalso
    have hm : undirected e ∈ H.map undirected := hperm.symm.subset (by simp)
    obtain ⟨h, hh, hhe⟩ := List.mem_map.mp hm
    have h1w : h.1 ∈ w := (key _ _ (hconn h hh)).mpr hu
    have ht : touches h.1 e = true := by
      obtain ⟨a, b⟩ := h
      obtain ⟨c, d⟩ := e
      simp only [undirected_mk, Sym2.eq_iff] at hhe
      simp only [touches]
      rcases hhe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    have := hnt _ h1w e List.mem_cons_self
    simp_all

/-- Splice closed walks from vertices of `w` that still touch an edge of `R`, for at most `fuel`
rounds. -/
def eulerLoop : ℕ → List α → List (α × α) → List α
  | 0, w, _ => w
  | fuel + 1, w, R =>
    match w.find? (fun x => R.any (touches x)) with
    | none => w
    | some x =>
      let r := walkFrom R.length R x
      eulerLoop fuel (splice x r.1 w) r.2

theorem eulerLoop_spec {H : List (α × α)} {u : α}
    (hconn : ∀ e ∈ H, Relation.EqvGen (fun a b => (a, b) ∈ H) e.1 u) (fuel : ℕ) :
    ∀ (w : List α) (R : List (α × α)), w.head? = some u → w.getLast? = some u →
      (H.map undirected).Perm ((w.consecutivePairs ++ R).map undirected) →
      (∀ y, degree R y % 2 = 0) → R.length ≤ fuel → IsEulerCircuit H u (eulerLoop fuel w R) := by
  induction fuel with
  | zero =>
    intro w R h1 h2 h3 _ h5
    have : R = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h5)
    subst this
    change IsEulerCircuit H u w
    exact ⟨h1, h2, by simpa using h3.symm⟩
  | succ fuel ih =>
    intro w R h1 h2 h3 h4 h5
    simp only [eulerLoop]
    split
    · rename_i hfind
      have hR : R = [] := by
        refine eq_nil_of_forall_not_touches (List.mem_of_mem_head? h1) hconn h3 ?_
        intro x hx e he
        rw [List.find?_eq_none] at hfind
        have := hfind x hx
        simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at this
        exact this e he
      subst hR
      exact ⟨h1, h2, by simpa using h3.symm⟩
    · rename_i x hfind
      have hxw : x ∈ w := List.mem_of_find?_eq_some hfind
      have hxR : R.any (touches x) = true :=
        List.find?_some (p := fun y => R.any (touches y)) hfind
      obtain ⟨e, he, hte⟩ := List.any_eq_true.mp hxR
      have hpar : ∀ y,
          (degree R y + (if y = x then 1 else 0) + (if y = x then 1 else 0)) % 2 = 0 :=
        fun y => by
          have := h4 y
          split_ifs <;> omega
      obtain ⟨s1, s2, s3, s4⟩ := walkFrom_spec R.length R x x le_rfl hpar
      obtain ⟨A, B, hw, hsp⟩ := exists_splice (walkFrom R.length R x).1 hxw
      have hlt := length_walkFrom_snd_lt (List.length_pos_of_mem he) he hte
      apply ih
      · rw [hsp, head?_append_append s1, ← hw, h1]
      · rw [hsp, getLast?_append_append s2, ← hw, h2]
      · rw [hsp]
        have hw' := consecutivePairs_append_append (A := A) (B := B) s1 s2
        rw [← hw] at hw'
        refine h3.trans ?_
        rw [List.map_append]
        refine (List.Perm.append_left _ s3).trans ?_
        rw [← List.map_append, ← List.append_assoc]
        exact ((hw'.append_right _).map _).symm
      · exact s4
      · omega

/-! ### Hierholzer's algorithm and Euler's theorem -/

/-- **Hierholzer's algorithm**: walk greedily from `u` until stuck, then splice in closed walks
from visited vertices with unused edges. -/
def eulerCircuit (H : List (α × α)) (u : α) : List α :=
  eulerLoop (walkFrom H.length H u).2.length (walkFrom H.length H u).1 (walkFrom H.length H u).2

/-- **Euler's theorem, sufficiency** ([Hierholzer1873]): if every degree in `H` is even and every
edge of `H` is connected to `u`, then Hierholzer's algorithm returns an Euler circuit of `H` from
`u`. -/
theorem isEulerCircuit_eulerCircuit {H : List (α × α)} {u : α} (heven : ∀ x, Even (degree H x))
    (hconn : ∀ e ∈ H, Relation.EqvGen (fun a b => (a, b) ∈ H) e.1 u) :
    IsEulerCircuit H u (eulerCircuit H u) := by
  have hpar : ∀ y,
      (degree H y + (if y = u then 1 else 0) + (if y = u then 1 else 0)) % 2 = 0 := fun y => by
    have := Nat.even_iff.mp (heven y)
    split_ifs <;> omega
  obtain ⟨s1, s2, s3, s4⟩ := walkFrom_spec H.length H u u le_rfl hpar
  exact eulerLoop_spec hconn _ _ _ s1 s2 s3 s4 le_rfl

/-- **Euler's theorem** for finite multigraphs ([Hierholzer1873]; [KorteVygen2018], Section 2.4):
`H` has an Euler circuit from `u` exactly when every degree is even and every edge is connected to
`u`. -/
theorem exists_isEulerCircuit_iff {H : List (α × α)} {u : α} :
    (∃ w, IsEulerCircuit H u w) ↔
      (∀ x, Even (degree H x)) ∧ ∀ e ∈ H, Relation.EqvGen (fun a b => (a, b) ∈ H) e.1 u :=
  ⟨fun ⟨_, h⟩ => ⟨even_degree_of_isEulerCircuit h, eqvGen_of_isEulerCircuit h⟩,
    fun ⟨h1, h2⟩ => ⟨_, isEulerCircuit_eulerCircuit h1 h2⟩⟩

end Cslib.Algorithms.Lean.Euler
