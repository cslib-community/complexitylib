/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.NNF.ReadOnce
public import CslibFrontier.Computability.Circuit.NNF.Disjunction
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.CubicEdgeColoring
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# A linear d-DNNF for `f_G`

**[ArenasBroadrickLiewVanDenBroeck2026, Proposition 5.1], upper bound.** For a cubic graph with
a proper `3`-edge-colouring on `n` vertices, `f_G` (`CubicEdgeColoring.someButNotAllColors`) is
computed by a d-DNNF with at most `150 n + 50` nodes (`CubicEdgeColoring.exists_dDNNF`).

The proof follows the paper. `f_G(x)` holds exactly when `G_x` contains colour `0` but not `1`,
or `1` but not `2`, or `2` but not `0`, three mutually exclusive conditions; their d-DNNFs are
joined by two deterministic `∨` gates. For colours `α` and `β`, the edges of these two colours
form disjoint alternating cycles. Reading each cycle in order and remembering the bits of its
first and of the previous vertex, together with whether an edge of colour `α`, resp. `β`, with
both ends true has been seen, is a read-once branching program with `16` states
(`CubicEdgeColoring.cycleProgram`), whose d-DNNF has linear size
(`Cslib.BranchingPrograms.ReadOnceProgram.toNNF`).

**The cycles.** With `σ = β ∘ α` (each colour acting as the involution `M.mate`), the cycle
through `x` is `x, α x, σ x, α σ x, …, σ^(p-1) x, α σ^(p-1) x` for the period `p` of `x` under
`σ` (`CubicEdgeColoring.cycleBlock`). Its vertices are distinct because `σ^k y = α y` is
impossible: reflecting along the cycle would give a fixed point of `α` or of `β`
(`CubicEdgeColoring.iterate_ne_mate`). Every edge of colour `α` or `β` at a vertex of the cycle
joins two cyclically consecutive vertices of it, and the cycles through distinct vertices
partition the graph (`CubicEdgeColoring.exists_isCycleCover`).

## Main definitions

* `Cslib.CubicEdgeColoring.cyclePairs`: the cyclically consecutive pairs of a list.
* `Cslib.CubicEdgeColoring.IsCycleCover`: a list of vertex lists covering every vertex once, in
  which every edge of colours `α` and `β` joins cyclically consecutive vertices.
* `Cslib.CubicEdgeColoring.cycleProgram`, `Cslib.CubicEdgeColoring.cycleOrder`: the read-once
  program reading such a cover, and its variable order.
* `Cslib.CubicEdgeColoring.cycleBlock`: the alternating cycle through a vertex.

## Main results

* `Cslib.CubicEdgeColoring.IsCycleCover.eval_cycleProgram`: on a cycle cover, the program
  decides "colour `α` but not `β`".
* `Cslib.CubicEdgeColoring.exists_isCycleCover`: alternating cycle covers exist.
* `Cslib.CubicEdgeColoring.exists_dDNNF`: Proposition 5.1, upper bound.

## References

* [M. Arenas, O. Broadrick, V. Liew, G. Van den Broeck, *d-DNNF is not polynomially closed under
  negation*][ArenasBroadrickLiewVanDenBroeck2026]
-/

@[expose] public section

namespace Cslib.CubicEdgeColoring

open Finset Circuits

variable {V : Type*}

/-! ### Cyclically consecutive pairs -/

/-- The consecutive pairs of `u :: l`, followed by the pair from the last vertex back to `v₀`. -/
def cyclePairsTail (v₀ : V) : V → List V → List (V × V)
  | _, [] => []
  | u, [v] => [(u, v), (v, v₀)]
  | u, v :: w :: l => (u, v) :: cyclePairsTail v₀ v (w :: l)

/-- The *cyclically consecutive pairs* of a list: each vertex with the next, and the last with
the first. -/
def cyclePairs : List V → List (V × V)
  | [] => []
  | [v₀] => [(v₀, v₀)]
  | v₀ :: v :: l => cyclePairsTail v₀ v₀ (v :: l)

theorem mem_of_mem_cyclePairsTail {v₀ u : V} :
    ∀ {l : List V} {p : V × V}, p ∈ cyclePairsTail v₀ u l →
      (p.1 = u ∨ p.1 ∈ l) ∧ (p.2 = v₀ ∨ p.2 ∈ l)
  | [], _, h => by simp [cyclePairsTail] at h
  | [v], p, h => by
    simp only [cyclePairsTail, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp
  | v :: w :: l, p, h => by
    simp only [cyclePairsTail, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := mem_of_mem_cyclePairsTail (u := v) h
      simp only [List.mem_cons] at this ⊢
      tauto

theorem mem_of_mem_cyclePairs {l : List V} {p : V × V} (h : p ∈ cyclePairs l) :
    p.1 ∈ l ∧ p.2 ∈ l := by
  match l, h with
  | [v₀], h => simp only [cyclePairs, List.mem_singleton] at h; subst h; simp
  | v₀ :: v :: l, h =>
    have := mem_of_mem_cyclePairsTail h
    simp only [List.mem_cons] at this ⊢
    tauto

theorem getElem_mem_cyclePairsTail (v₀ : V) :
    ∀ (u : V) (l : List V) (j : ℕ) (hj : j + 1 < l.length),
      (l[j], l[j + 1]) ∈ cyclePairsTail v₀ u l
  | _, [], _, hj => by simp at hj
  | _, [_], _, hj => by simp at hj
  | u, v :: w :: l, 0, _ => by
    simp only [cyclePairsTail, List.getElem_cons_zero, List.getElem_cons_succ]
    cases l <;> simp [cyclePairsTail]
  | u, v :: w :: l, j + 1, hj => by
    simp only [cyclePairsTail, List.getElem_cons_succ, List.mem_cons]
    exact .inr (getElem_mem_cyclePairsTail v₀ v (w :: l) j (by simp at hj ⊢; omega))

theorem head_mem_cyclePairsTail (v₀ u v : V) (l : List V) :
    (u, v) ∈ cyclePairsTail v₀ u (v :: l) := by
  cases l <;> simp [cyclePairsTail]

theorem last_mem_cyclePairsTail (v₀ : V) :
    ∀ (u : V) (l : List V) (hl : l ≠ []), (l.getLast hl, v₀) ∈ cyclePairsTail v₀ u l
  | _, [], hl => absurd rfl hl
  | _, [v], _ => by simp [cyclePairsTail]
  | u, v :: w :: l, _ => by
    simp only [cyclePairsTail, List.mem_cons]
    exact .inr (by simpa using last_mem_cyclePairsTail v₀ v (w :: l) (by simp))

/-- Each vertex of a list of at least two vertices and the next are cyclically consecutive. -/
theorem getElem_mem_cyclePairs {l : List V} {j : ℕ} (hj : j + 1 < l.length) :
    (l[j], l[j + 1]) ∈ cyclePairs l := by
  match l, j, hj with
  | v₀ :: v :: l, 0, _ => simpa [cyclePairs] using head_mem_cyclePairsTail v₀ v₀ v l
  | v₀ :: v :: l, j + 1, hj =>
    exact getElem_mem_cyclePairsTail v₀ v₀ (v :: l) j (by simp at hj ⊢; omega)

/-- The last vertex of a list and the first are cyclically consecutive. -/
theorem last_first_mem_cyclePairs {l : List V} (hl : 0 < l.length) :
    (l[l.length - 1], l[0]) ∈ cyclePairs l := by
  match l, hl with
  | [v₀], _ => simp [cyclePairs]
  | v₀ :: v :: l, _ =>
    have := last_mem_cyclePairsTail v₀ v₀ (v :: l) (by simp)
    simp only [List.getLast_eq_getElem, List.length_cons] at this
    simpa [cyclePairs] using this

/-! ### Reading a cycle cover -/

variable [DecidableEq V] (M : CubicEdgeColoring V) (α β : Fin 3)

/-- The labels of the cycle automaton: whether a cycle starts here, whether the previous vertex
is joined to this one by an edge of colour `α` and of colour `β`, and the same for this vertex
and the first vertex of its cycle, if it closes the cycle. -/
abbrev CycleLabel : Type := Bool × (Bool × Bool) × (Bool × Bool)

/-- Whether `u` is joined to `w` by an edge of colour `α`, and by one of colour `β`. -/
def pairLabel (u w : V) : Bool × Bool :=
  (decide (M.mate α u = w), decide (M.mate β u = w))

/-- The labelled inputs for `l` read after `u`, in a cycle starting at `v₀`. -/
def cycleItemsTail (v₀ : V) : V → List V → List (V × CycleLabel)
  | _, [] => []
  | u, [v] => [(v, false, M.pairLabel α β u v, M.pairLabel α β v v₀)]
  | u, v :: w :: l =>
    (v, false, M.pairLabel α β u v, (false, false)) :: cycleItemsTail v₀ v (w :: l)

/-- The labelled inputs for reading the cycle `l`. -/
def cycleItems : List V → List (V × CycleLabel)
  | [] => []
  | [v₀] => [(v₀, true, (false, false), M.pairLabel α β v₀ v₀)]
  | v₀ :: v :: l =>
    (v₀, true, (false, false), (false, false)) :: M.cycleItemsTail α β v₀ v₀ (v :: l)

theorem map_fst_cycleItemsTail (v₀ : V) :
    ∀ (u : V) (l : List V), (M.cycleItemsTail α β v₀ u l).map Prod.fst = l
  | _, [] => rfl
  | _, [_] => rfl
  | _, v :: w :: l => by
    simp only [cycleItemsTail, List.map_cons]
    rw [map_fst_cycleItemsTail v₀ v (w :: l)]

theorem map_fst_cycleItems : ∀ l : List V, (M.cycleItems α β l).map Prod.fst = l
  | [] => rfl
  | [_] => rfl
  | v₀ :: v :: l => by
    simp only [cycleItems, List.map_cons]
    rw [map_fst_cycleItemsTail]

/-- The transition of the cycle automaton on the state (first bit, previous bit, `α` seen,
`β` seen). -/
def cycleStep : CycleLabel → Bool × Bool × Bool × Bool → Bool → Bool × Bool × Bool × Bool
  | (st, (pa, pb), (ca, cb)), (f, p, s, d), b =>
    ((if st then b else f), b, s || (pa && p && b) || (ca && b && (if st then b else f)),
      d || (pb && p && b) || (cb && b && (if st then b else f)))

/-- The **cycle program** reading a list of cycles: it accepts when some cyclically consecutive
pair joined by an edge of colour `α` has both bits true and none joined by colour `β` does. -/
def cycleProgram (blocks : List (List V)) :
    BranchingPrograms.ReadOnceProgram (blocks.flatMap (M.cycleItems α β)).length
      (Bool × Bool × Bool × Bool) Bool :=
  .ofList (blocks.flatMap (M.cycleItems α β)) (false, false, false, false) cycleStep
    fun (_, _, s, d) => s && !d

/-- The order in which the cycle program reads the vertices. -/
def cycleOrder (blocks : List (List V)) : Fin (blocks.flatMap (M.cycleItems α β)).length → V :=
  BranchingPrograms.ReadOnceProgram.listOrder (blocks.flatMap (M.cycleItems α β))

/-- The run of the cycle program on a list of labelled vertices. -/
def cycleRun (x : V → Bool) (l : List (V × CycleLabel)) (q : Bool × Bool × Bool × Bool) :
    Bool × Bool × Bool × Bool :=
  l.foldl (fun s a => cycleStep a.2 s (x a.1)) q

omit [DecidableEq V] in
@[simp] theorem cycleRun_nil (x : V → Bool) (q : Bool × Bool × Bool × Bool) :
    cycleRun x [] q = q := rfl

omit [DecidableEq V] in
@[simp] theorem cycleRun_cons (x : V → Bool) (a : V × CycleLabel) (l : List (V × CycleLabel))
    (q : Bool × Bool × Bool × Bool) :
    cycleRun x (a :: l) q = cycleRun x l (cycleStep a.2 q (x a.1)) :=
  rfl

omit [DecidableEq V] in
theorem cycleRun_append (x : V → Bool) (l l' : List (V × CycleLabel))
    (q : Bool × Bool × Bool × Bool) : cycleRun x (l ++ l') q = cycleRun x l' (cycleRun x l q) :=
  List.foldl_append

/-- A cyclically consecutive pair joined by an edge of colour `γ`, with both bits true. -/
def pairHas (γ : Fin 3) (x : V → Bool) (p : V × V) : Bool :=
  decide (M.mate γ p.1 = p.2) && x p.1 && x p.2

theorem runList_cycleItemsTail (x : V → Bool) (v₀ : V) :
    ∀ (u : V) (l : List V) (s d : Bool), ∃ p',
      cycleRun x (M.cycleItemsTail α β v₀ u l) (x v₀, x u, s, d) =
        (x v₀, p', s || (cyclePairsTail v₀ u l).any (M.pairHas α x),
          d || (cyclePairsTail v₀ u l).any (M.pairHas β x))
  | u, [], s, d => ⟨x u, by simp [cyclePairsTail, cycleItemsTail]⟩
  | u, [v], s, d => ⟨x v, by
    simp only [cycleItemsTail, cycleRun_cons, cycleRun_nil, cyclePairsTail,
      List.any_cons, List.any_nil, cycleStep, pairLabel, pairHas, Bool.false_eq_true, ite_false]
    cases x u <;> cases x v <;> cases x v₀ <;> simp [Bool.or_assoc]⟩
  | u, v :: w :: l, s, d => by
    obtain ⟨p', hp'⟩ := runList_cycleItemsTail x v₀ v (w :: l)
      (s || M.pairHas α x (u, v)) (d || M.pairHas β x (u, v))
    refine ⟨p', ?_⟩
    simp only [cycleItemsTail, cycleRun_cons, cyclePairsTail, List.any_cons] at hp' ⊢
    convert hp' using 2 <;> simp [cycleStep, pairLabel, pairHas, Bool.or_assoc]

theorem runList_cycleItems (x : V → Bool) (l : List V) (f p s d : Bool) : ∃ f' p',
    cycleRun x (M.cycleItems α β l) (f, p, s, d) =
      (f', p', s || (cyclePairs l).any (M.pairHas α x),
        d || (cyclePairs l).any (M.pairHas β x)) := by
  match l with
  | [] => exact ⟨f, p, by simp [cycleItems, cyclePairs]⟩
  | [v₀] =>
    refine ⟨x v₀, x v₀, ?_⟩
    simp only [cycleItems, cycleRun_cons, cycleRun_nil, cyclePairs, List.any_cons,
      List.any_nil, cycleStep, pairLabel, pairHas, ite_true]
    cases x v₀ <;> simp
  | v₀ :: v :: l =>
    obtain ⟨p', hp'⟩ := M.runList_cycleItemsTail α β x v₀ v₀ (v :: l) s d
    refine ⟨x v₀, p', ?_⟩
    simp only [cycleItems, cycleRun_cons, cyclePairs] at hp' ⊢
    convert hp' using 2
    simp [cycleStep]

theorem runList_flatMap_cycleItems (x : V → Bool) :
    ∀ (blocks : List (List V)) (f p s d : Bool), ∃ f' p',
      cycleRun x (blocks.flatMap (M.cycleItems α β)) (f, p, s, d) =
        (f', p', s || (blocks.flatMap cyclePairs).any (M.pairHas α x),
          d || (blocks.flatMap cyclePairs).any (M.pairHas β x))
  | [], f, p, s, d => ⟨f, p, by simp⟩
  | b :: blocks, f, p, s, d => by
    obtain ⟨f₁, p₁, h₁⟩ := M.runList_cycleItems α β x b f p s d
    obtain ⟨f₂, p₂, h₂⟩ := runList_flatMap_cycleItems x blocks f₁ p₁
      (s || (cyclePairs b).any (M.pairHas α x)) (d || (cyclePairs b).any (M.pairHas β x))
    refine ⟨f₂, p₂, ?_⟩
    rw [List.flatMap_cons, cycleRun_append, h₁, h₂]
    simp only [List.flatMap_cons, List.any_append, Bool.or_assoc]

/-- **The cycle program** accepts exactly when some cyclically consecutive pair of a block is
joined by an edge of colour `α` with both bits true, and none by an edge of colour `β`. -/
theorem eval_cycleProgram (blocks : List (List V)) (x : V → Bool) :
    (M.cycleProgram α β blocks).eval (x ∘ M.cycleOrder α β blocks) =
      ((blocks.flatMap cyclePairs).any (M.pairHas α x) &&
        !(blocks.flatMap cyclePairs).any (M.pairHas β x)) := by
  obtain ⟨f', p', h⟩ := M.runList_flatMap_cycleItems α β x blocks false false false false
  rw [cycleProgram, cycleOrder, BranchingPrograms.ReadOnceProgram.eval_ofList, ← cycleRun, h]
  simp

/-- A **cycle cover** for the colours `α` and `β`: lists of vertices that together list every
vertex exactly once, such that every edge of colour `α` or `β` at a listed vertex joins
cyclically consecutive vertices of its list. -/
structure IsCycleCover (blocks : List (List V)) : Prop where
  /-- No vertex is listed twice. -/
  nodup : blocks.flatten.Nodup
  /-- Every vertex is listed. -/
  mem : ∀ v, v ∈ blocks.flatten
  /-- Edges of colour `α` or `β` join cyclically consecutive vertices. -/
  pairs : ∀ b ∈ blocks, ∀ v ∈ b, ∀ γ, (γ = α ∨ γ = β) → ∃ p ∈ cyclePairs b,
    M.mate γ p.1 = p.2 ∧ (p = (v, M.mate γ v) ∨ p = (M.mate γ v, v))

variable {M α β}

theorem IsCycleCover.any_pairHas_iff {blocks : List (List V)} (h : M.IsCycleCover α β blocks)
    (x : V → Bool) {γ : Fin 3} (hγ : γ = α ∨ γ = β) :
    (blocks.flatMap cyclePairs).any (M.pairHas γ x) = true ↔ M.HasColor x γ := by
  simp only [List.any_eq_true, List.mem_flatMap, pairHas, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨p, -, ⟨hp, hx1⟩, hx2⟩
    exact ⟨p.1, hx1, hp ▸ hx2⟩
  · rintro ⟨v, hv, hmv⟩
    obtain ⟨b, hb, hvb⟩ := List.mem_flatten.mp (h.mem v)
    obtain ⟨p, hp, hmate, rfl | rfl⟩ := h.pairs b hb v hvb γ hγ
    · exact ⟨_, ⟨b, hb, hp⟩, ⟨hmate, hv⟩, hmv⟩
    · exact ⟨_, ⟨b, hb, hp⟩, ⟨hmate, hmv⟩, hv⟩

/-- On a cycle cover, the cycle automaton decides whether `G_x` contains colour `α` but not
colour `β`. -/
theorem IsCycleCover.eval_cycleProgram {blocks : List (List V)}
    (h : M.IsCycleCover α β blocks) (x : V → Bool) :
    (M.cycleProgram α β blocks).eval (x ∘ M.cycleOrder α β blocks) = true ↔
      M.HasColor x α ∧ ¬M.HasColor x β := by
  have hα := h.any_pairHas_iff x (γ := α) (.inl rfl)
  have hβ := h.any_pairHas_iff x (γ := β) (.inr rfl)
  rw [CubicEdgeColoring.eval_cycleProgram]
  cases h1 : (blocks.flatMap cyclePairs).any (M.pairHas α x) <;>
    cases h2 : (blocks.flatMap cyclePairs).any (M.pairHas β x) <;> simp_all

theorem map_fst_flatMap_cycleItems (blocks : List (List V)) :
    (blocks.flatMap (M.cycleItems α β)).map Prod.fst = blocks.flatten := by
  simp only [List.map_flatMap, map_fst_cycleItems, List.flatMap_id']

/-! ### Alternating cycles -/

variable (M α β) in
/-- One step along the alternating cycle: an edge of colour `α`, then one of colour `β`. -/
def cycleStepMap (v : V) : V :=
  M.mate β (M.mate α v)

omit [DecidableEq V] in
theorem cycleStepMap_injective : Function.Injective (M.cycleStepMap α β) := fun u v h => by
  have := congrArg (fun w => M.mate α (M.mate β w)) h
  simpa only [cycleStepMap, M.mate_mate] using this

omit [DecidableEq V] in
theorem mate_mate_iterate (x : V) (i : ℕ) :
    M.mate β (M.mate α ((M.cycleStepMap α β)^[i] x)) = (M.cycleStepMap α β)^[i + 1] x := by
  rw [Function.iterate_succ_apply']; rfl

omit [DecidableEq V] in
theorem mate_iterate_succ (x : V) (i : ℕ) :
    M.mate β ((M.cycleStepMap α β)^[i + 1] x) = M.mate α ((M.cycleStepMap α β)^[i] x) := by
  rw [← mate_mate_iterate, M.mate_mate]

omit [DecidableEq V] in
/-- **No shortcut across a cycle**: `σ^k y = α y` is impossible. Reflecting along the cycle gives
`σ^(k-m) y = α σ^m y` for `m ≤ k`, which for `m = k/2` makes a vertex a fixed point of `α` or of
`β`. -/
theorem iterate_ne_mate (k : ℕ) (y : V) : (M.cycleStepMap α β)^[k] y ≠ M.mate α y := by
  intro h
  set σ := M.cycleStepMap α β
  have hrefl : ∀ m ≤ k, σ^[k - m] y = M.mate α (σ^[m] y) := by
    intro m
    induction m with
    | zero => intro; simpa using h
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      obtain ⟨j, hj⟩ : ∃ j, k - m = j + 1 := ⟨k - m - 1, by omega⟩
      rw [hj] at h1
      have h2 := congrArg (M.mate β) h1
      rw [mate_iterate_succ, mate_mate_iterate] at h2
      have h3 := congrArg (M.mate α) h2
      rw [M.mate_mate] at h3
      rw [show k - (m + 1) = j by omega, h3]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · have := hrefl m (by omega)
    rw [show 2 * m - m = m by omega] at this
    exact M.mate_ne α _ this.symm
  · have := hrefl (m + 1) (by omega)
    rw [show 2 * m + 1 - (m + 1) = m by omega] at this
    have h2 := congrArg (M.mate α) this
    rw [M.mate_mate, ← mate_mate_iterate] at h2
    exact M.mate_ne β _ h2.symm

omit [DecidableEq V] in
theorem iterate_ne_mate_iterate (x : V) (i i' : ℕ) :
    (M.cycleStepMap α β)^[i] x ≠ M.mate α ((M.cycleStepMap α β)^[i'] x) := by
  intro h
  set σ := M.cycleStepMap α β
  rcases le_total i' i with hle | hle
  · refine iterate_ne_mate (M := M) (α := α) (β := β) (i - i') (σ^[i'] x) ?_
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle, h]
  · refine iterate_ne_mate (M := M) (α := α) (β := β) (i' - i) (σ^[i] x) ?_
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle, h, M.mate_mate]

section Cycles

variable [Finite V]

variable (M α β) in
/-- The period of `x` along the alternating cycle. -/
noncomputable def cyclePeriod (x : V) : ℕ :=
  Function.minimalPeriod (M.cycleStepMap α β) x

omit [DecidableEq V] in
theorem cyclePeriod_pos (x : V) : 0 < M.cyclePeriod α β x :=
  Function.minimalPeriod_pos_of_mem_periodicPts (cycleStepMap_injective.mem_periodicPts x)

omit [DecidableEq V] [Finite V] in
theorem iterate_cyclePeriod (x : V) :
    (M.cycleStepMap α β)^[M.cyclePeriod α β x] x = x :=
  Function.iterate_minimalPeriod

variable (M α β) in
/-- The `j`-th vertex of the alternating cycle through `x`: `σ^i x` for `j = 2i` and
`α σ^i x` for `j = 2i + 1`. -/
def cycleVertex (x : V) (j : ℕ) : V :=
  if j % 2 = 0 then (M.cycleStepMap α β)^[j / 2] x else M.mate α ((M.cycleStepMap α β)^[j / 2] x)

omit [DecidableEq V] [Finite V] in
theorem cycleVertex_even (x : V) (i : ℕ) :
    M.cycleVertex α β x (2 * i) = (M.cycleStepMap α β)^[i] x := by
  simp [cycleVertex]

omit [DecidableEq V] [Finite V] in
theorem cycleVertex_odd (x : V) (i : ℕ) :
    M.cycleVertex α β x (2 * i + 1) = M.mate α ((M.cycleStepMap α β)^[i] x) := by
  simp only [cycleVertex, Nat.mul_add_mod, Nat.one_mod, Nat.one_ne_zero, ite_false]
  congr 2
  omega

variable (M α β) in
/-- The **alternating cycle** through `x`: `x, α x, σ x, α σ x, …, σ^(p-1) x, α σ^(p-1) x`. -/
noncomputable def cycleBlock (x : V) : List V :=
  List.ofFn fun j : Fin (2 * M.cyclePeriod α β x) => M.cycleVertex α β x j

omit [DecidableEq V] [Finite V] in
theorem length_cycleBlock (x : V) : (M.cycleBlock α β x).length = 2 * M.cyclePeriod α β x := by
  simp [cycleBlock]

omit [DecidableEq V] [Finite V] in
theorem getElem_cycleBlock (x : V) (j : ℕ) (hj : j < (M.cycleBlock α β x).length) :
    (M.cycleBlock α β x)[j] = M.cycleVertex α β x j := by
  simp [cycleBlock]

omit [DecidableEq V] [Finite V] in
theorem mem_cycleBlock {x v : V} :
    v ∈ M.cycleBlock α β x ↔ ∃ j < 2 * M.cyclePeriod α β x, M.cycleVertex α β x j = v := by
  simp only [cycleBlock, List.mem_ofFn]
  exact ⟨fun ⟨j, hj⟩ => ⟨j, j.isLt, hj⟩, fun ⟨j, hj, h⟩ => ⟨⟨j, hj⟩, h⟩⟩

omit [DecidableEq V] in
theorem self_mem_cycleBlock (x : V) : x ∈ M.cycleBlock α β x :=
  mem_cycleBlock.mpr ⟨0, by have := cyclePeriod_pos (M := M) (α := α) (β := β) x; omega,
    by simp [cycleVertex]⟩

omit [DecidableEq V] [Finite V] in
/-- The alternating cycle lists distinct vertices. -/
theorem nodup_cycleBlock (x : V) : (M.cycleBlock α β x).Nodup := by
  rw [cycleBlock, List.nodup_ofFn]
  rintro ⟨j, hj⟩ ⟨j', hj'⟩ h
  simp only at h
  have hinj : ∀ i i', i < M.cyclePeriod α β x → i' < M.cyclePeriod α β x →
      (M.cycleStepMap α β)^[i] x = (M.cycleStepMap α β)^[i'] x → i = i' :=
    fun i i' hi hi' h => Function.iterate_injOn_Iio_minimalPeriod hi hi' h
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j <;> obtain ⟨i', rfl | rfl⟩ := Nat.even_or_odd' j'
  · rw [cycleVertex_even, cycleVertex_even] at h
    exact Fin.ext (by simp only; rw [hinj i i' (by omega) (by omega) h])
  · rw [cycleVertex_even, cycleVertex_odd] at h
    exact absurd h (iterate_ne_mate_iterate x i i')
  · rw [cycleVertex_odd, cycleVertex_even] at h
    exact absurd h.symm (iterate_ne_mate_iterate x i' i)
  · rw [cycleVertex_odd, cycleVertex_odd] at h
    have h' := congrArg (M.mate α) h
    rw [M.mate_mate, M.mate_mate] at h'
    exact Fin.ext (by simp only; rw [hinj i i' (by omega) (by omega) h'])

omit [DecidableEq V] in
/-- **Edges along the cycle.** Every edge of colour `α` or `β` at a vertex of the alternating
cycle joins two cyclically consecutive vertices of it. -/
theorem cycleBlock_pairs (x : V) : ∀ v ∈ M.cycleBlock α β x, ∀ γ, (γ = α ∨ γ = β) →
    ∃ p ∈ cyclePairs (M.cycleBlock α β x),
      M.mate γ p.1 = p.2 ∧ (p = (v, M.mate γ v) ∨ p = (M.mate γ v, v)) := by
  intro v hv γ hγ
  set l := M.cycleBlock α β x
  set P := M.cyclePeriod α β x
  set σ := M.cycleStepMap α β
  have hP := cyclePeriod_pos (M := M) (α := α) (β := β) x
  have hlen : l.length = 2 * P := length_cycleBlock x
  have hget : ∀ j (hj : j < l.length), l[j] = M.cycleVertex α β x j := getElem_cycleBlock x
  -- Consecutive and closing pairs.
  have hcons : ∀ j (hj : j + 1 < 2 * P), (M.cycleVertex α β x j, M.cycleVertex α β x (j + 1)) ∈
      cyclePairs l := fun j hj => by
    rw [← hget j (by omega), ← hget (j + 1) (by omega)]
    exact getElem_mem_cyclePairs (by omega)
  have hclose : (M.mate α (σ^[P - 1] x), x) ∈ cyclePairs l := by
    have := last_first_mem_cyclePairs (l := l) (by omega)
    rwa [hget, hget, hlen, show 2 * P - 1 = 2 * (P - 1) + 1 by omega, cycleVertex_odd,
      show (0 : ℕ) = 2 * 0 from rfl, cycleVertex_even, Function.iterate_zero_apply] at this
  have hβlast : M.mate β (M.mate α (σ^[P - 1] x)) = x := by
    rw [mate_mate_iterate, show P - 1 + 1 = P by omega]
    exact iterate_cyclePeriod x
  obtain ⟨j, hj, rfl⟩ := mem_cycleBlock.mp hv
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [cycleVertex_even]
    rcases hγ with rfl | rfl
    · -- The edge of colour `α` at `σ^i x` leads to the next vertex.
      refine ⟨_, hcons (2 * i) (by omega), ?_, .inl ?_⟩ <;>
        rw [cycleVertex_even, cycleVertex_odd]
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · -- The edge of colour `β` at `x` closes the cycle.
        refine ⟨_, hclose, hβlast, .inr ?_⟩
        have h' := congrArg (M.mate γ) hβlast
        rw [M.mate_mate] at h'
        rw [Function.iterate_zero_apply, h']
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        refine ⟨_, hcons (2 * i' + 1) (by omega), ?_, .inr ?_⟩ <;>
          rw [show 2 * i' + 1 + 1 = 2 * (i' + 1) by omega, cycleVertex_odd, cycleVertex_even]
        · exact mate_mate_iterate x i'
        · rw [mate_iterate_succ]
  · rw [cycleVertex_odd]
    rcases hγ with rfl | rfl
    · refine ⟨_, hcons (2 * i) (by omega), ?_, .inr ?_⟩ <;>
        rw [cycleVertex_even, cycleVertex_odd]
      rw [M.mate_mate]
    · by_cases hi : i + 1 < P
      · refine ⟨_, hcons (2 * i + 1) (by omega), ?_, .inl ?_⟩ <;>
          rw [show 2 * i + 1 + 1 = 2 * (i + 1) by omega, cycleVertex_odd, cycleVertex_even]
        · exact mate_mate_iterate x i
        · rw [mate_mate_iterate]
      · obtain rfl : i = P - 1 := by omega
        exact ⟨_, hclose, hβlast, .inl (by rw [hβlast])⟩

omit [DecidableEq V] in
theorem mate_mem_cycleBlock {x v : V} (hv : v ∈ M.cycleBlock α β x) {γ : Fin 3}
    (hγ : γ = α ∨ γ = β) : M.mate γ v ∈ M.cycleBlock α β x := by
  obtain ⟨p, hp, -, rfl | rfl⟩ := cycleBlock_pairs x v hv γ hγ
  exacts [(mem_of_mem_cyclePairs hp).2, (mem_of_mem_cyclePairs hp).1]

omit [DecidableEq V] in
/-- **Alternating cycle covers exist**: the alternating cycles through the vertices of a set
closed under both colours partition it. -/
theorem exists_isCycleCover_of_closed : ∀ W : Finset V,
    (∀ v ∈ W, M.mate α v ∈ W ∧ M.mate β v ∈ W) → ∃ blocks : List (List V),
      blocks.flatten.Nodup ∧ (∀ v, v ∈ blocks.flatten ↔ v ∈ W) ∧
      ∀ b ∈ blocks, ∀ v ∈ b, ∀ γ, (γ = α ∨ γ = β) → ∃ p ∈ cyclePairs b,
        M.mate γ p.1 = p.2 ∧ (p = (v, M.mate γ v) ∨ p = (M.mate γ v, v)) := by
  classical
  intro W
  induction hW : #W using Nat.strong_induction_on generalizing W with
  | _ m ih =>
    intro hclosed
    rcases W.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact ⟨[], by simp, by simp, by simp⟩
    set b := M.cycleBlock α β x
    -- The cycle through `x` lies in `W`.
    have hσ : ∀ i, (M.cycleStepMap α β)^[i] x ∈ W := fun i => by
      induction i with
      | zero => exact hx
      | succ i ih' =>
        rw [Function.iterate_succ_apply']
        exact (hclosed _ (hclosed _ ih').1).2
    have hbW : ∀ v ∈ b, v ∈ W := fun v hv => by
      obtain ⟨j, -, rfl⟩ := mem_cycleBlock.mp hv
      unfold cycleVertex
      split_ifs
      exacts [hσ _, (hclosed _ (hσ _)).1]
    set W' := W.filter (· ∉ b)
    have hlt : #W' < m := hW ▸ card_lt_card (filter_ssubset.mpr ⟨x, hx, by
      simpa using self_mem_cycleBlock x⟩)
    have hclosed' : ∀ v ∈ W', M.mate α v ∈ W' ∧ M.mate β v ∈ W' := fun v hv => by
      simp only [W', mem_filter] at hv ⊢
      refine ⟨⟨(hclosed v hv.1).1, fun h => hv.2 ?_⟩, ⟨(hclosed v hv.1).2, fun h => hv.2 ?_⟩⟩
      · simpa [M.mate_mate] using mate_mem_cycleBlock h (γ := α) (.inl rfl)
      · simpa [M.mate_mate] using mate_mem_cycleBlock h (γ := β) (.inr rfl)
    obtain ⟨blocks, hnd, hmem, hpairs⟩ := ih _ hlt W' rfl hclosed'
    refine ⟨b :: blocks, ?_, fun v => ?_, ?_⟩
    · rw [List.flatten_cons, List.nodup_append]
      refine ⟨nodup_cycleBlock x, hnd, fun a ha a' ha' h => ?_⟩
      subst h
      exact (mem_filter.mp ((hmem a).mp ha')).2 ha
    · rw [List.flatten_cons, List.mem_append, hmem]
      constructor
      · rintro (h | h)
        exacts [hbW v h, (mem_filter.mp h).1]
      · intro h
        by_cases hvb : v ∈ b
        · exact .inl hvb
        · exact .inr (mem_filter.mpr ⟨h, hvb⟩)
    · intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact cycleBlock_pairs x
      · exact hpairs b' hb'

variable (M α β) in
omit [DecidableEq V] in
/-- **Alternating cycle covers exist** for every pair of colours. -/
theorem exists_isCycleCover : ∃ blocks, M.IsCycleCover α β blocks := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨blocks, hnd, hmem, hpairs⟩ :=
    exists_isCycleCover_of_closed (M := M) (α := α) (β := β) univ (by simp)
  exact ⟨blocks, hnd, fun v => (hmem v).mpr (mem_univ v), hpairs⟩

end Cycles

/-! ### Proposition 5.1 -/

section Assembly

variable [Fintype V]

omit [DecidableEq V] in
/-- `f_G` splits into three mutually exclusive conditions on the colours. -/
theorem someButNotAllColors_eq_true_iff (x : V → Bool) :
    M.someButNotAllColors x = true ↔
      (M.HasColor x 0 ∧ ¬M.HasColor x 1) ∨ (M.HasColor x 1 ∧ ¬M.HasColor x 2) ∨
        (M.HasColor x 2 ∧ ¬M.HasColor x 0) := by
  simp only [someButNotAllColors, decide_eq_true_eq, Fin.exists_fin_succ, Fin.exists_fin_zero]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  tauto

/-- The chosen alternating cycle cover for the colours `α` and `β`. -/
noncomputable def cover (α β : Fin 3) : List (List V) :=
  (M.exists_isCycleCover α β).choose

/-- The d-DNNF deciding "colour `α` but not colour `β`", from the cycle program on the chosen
cover. -/
noncomputable def colorDNNF (α β : Fin 3) :=
  (M.cycleProgram α β (M.cover α β)).toNNF (M.cycleOrder α β (M.cover α β))

theorem toFun_colorDNNF (α β : Fin 3) (x : V → Bool) :
    (M.colorDNNF α β).toFun x = true ↔ M.HasColor x α ∧ ¬M.HasColor x β := by
  rw [colorDNNF, BranchingPrograms.ReadOnceProgram.toFun_toNNF]
  exact (M.exists_isCycleCover α β).choose_spec.eval_cycleProgram x

theorem isDecomposable_colorDNNF (α β : Fin 3) : (M.colorDNNF α β).IsDecomposable :=
  BranchingPrograms.ReadOnceProgram.isDecomposable_toNNF _ _
    (BranchingPrograms.ReadOnceProgram.listOrder_injective (by
      rw [map_fst_flatMap_cycleItems]
      exact (M.exists_isCycleCover α β).choose_spec.nodup))

theorem isDeterministic_colorDNNF (α β : Fin 3) : (M.colorDNNF α β).IsDeterministic :=
  BranchingPrograms.ReadOnceProgram.isDeterministic_toNNF _ _

theorem size_colorDNNF (α β : Fin 3) :
    (M.colorDNNF α β).size ≤ 50 * Fintype.card V + 16 := by
  have hlen : (List.flatMap (M.cycleItems α β) (M.cover α β)).length ≤ Fintype.card V := by
    rw [← List.length_map (f := Prod.fst), map_fst_flatMap_cycleItems]
    exact (M.exists_isCycleCover α β).choose_spec.nodup.length_le_card
  simp only [NNF.size, BranchingPrograms.ReadOnceProgram.card_nnfNode,
    Fintype.card_prod, Fintype.card_bool]
  omega

/-- The d-DNNF of `f_G`: the disjunction of the three colour automata. -/
noncomputable def dDNNF :=
  NNF.disj (NNF.disj (M.colorDNNF 0 1) (M.colorDNNF 1 2)) (M.colorDNNF 2 0)

theorem toFun_dDNNF (x : V → Bool) : M.dDNNF.toFun x = M.someButNotAllColors x := by
  rw [Bool.eq_iff_iff, dDNNF, NNF.toFun_disj, NNF.toFun_disj, Bool.or_eq_true, Bool.or_eq_true,
    toFun_colorDNNF, toFun_colorDNNF, toFun_colorDNNF, someButNotAllColors_eq_true_iff]
  tauto

theorem isDecomposable_dDNNF : M.dDNNF.IsDecomposable :=
  NNF.isDecomposable_disj
    (NNF.isDecomposable_disj (M.isDecomposable_colorDNNF 0 1) (M.isDecomposable_colorDNNF 1 2))
    (M.isDecomposable_colorDNNF 2 0)

theorem isDeterministic_dDNNF : M.dDNNF.IsDeterministic := by
  refine NNF.isDeterministic_disj
    (NNF.isDeterministic_disj (M.isDeterministic_colorDNNF 0 1) (M.isDeterministic_colorDNNF 1 2)
      fun x => ?_) (M.isDeterministic_colorDNNF 2 0) fun x => ?_
  · rw [toFun_colorDNNF, toFun_colorDNNF]
    tauto
  · rw [NNF.toFun_disj, Bool.or_eq_true, toFun_colorDNNF, toFun_colorDNNF, toFun_colorDNNF]
    tauto

theorem size_dDNNF : M.dDNNF.size ≤ 150 * Fintype.card V + 50 := by
  rw [dDNNF, NNF.size_disj, NNF.size_disj]
  have := M.size_colorDNNF 0 1
  have := M.size_colorDNNF 1 2
  have := M.size_colorDNNF 2 0
  omega

/-- **[ArenasBroadrickLiewVanDenBroeck2026, Proposition 5.1], upper bound.** For a cubic graph
with a proper `3`-edge-colouring on `n` vertices, `f_G` is computed by a d-DNNF with at most
`150 n + 50` nodes. -/
theorem exists_dDNNF : ∃ (N : Type) (_ : Fintype N) (D : NNF V N), D.IsDecomposable ∧
    D.IsDeterministic ∧ (∀ x, D.toFun x = M.someButNotAllColors x) ∧
      D.size ≤ 150 * Fintype.card V + 50 :=
  ⟨_, inferInstance, M.dDNNF, M.isDecomposable_dDNNF, M.isDeterministic_dDNNF, M.toFun_dDNNF,
    M.size_dDNNF⟩

end Assembly

end Cslib.CubicEdgeColoring
