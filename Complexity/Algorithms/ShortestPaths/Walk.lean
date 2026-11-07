/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Algebra.Tropical
public import Complexity.Foundations.Data.List.Last
public import Mathlib.Data.Fintype.Card
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Bounds.Defs
import Mathlib.Order.Bounds.Basic

/-!
# Walks, negative cycles and shortest distances

A weighted digraph on a vertex type `V` is a matrix `W : Matrix V V (MinTropical R)`: the entry
`W i j` is the weight of the edge `i → j`, the tropical zero `0 = ⊤` means that there is no edge,
the tropical product `*` adds weights and the tropical sum `+` takes minima. A walk from `i` is a
list `l` of the vertices visited after `i`; it ends at `l.getLastD i`, has `l.length` edges and
tropical weight `walkWeight W i l`, the sum of its edge weights.

`IsShortestDistances W D` says that each `D i j` is the greatest lower bound of the weights of
the walks from `i` to `j`. Under `NoNegCycle W` (every closed walk has weight at least the
tropical one, that is, at least `0` in `R`) the lower bound is attained by a walk without repeated
vertices, so it suffices to check that `D` is achieved by walks and lies below every such simple
walk (`isShortestDistances_of_sound_complete`). Closed walks of length at most `card V` already
decide `NoNegCycle` (`noNegCycle_of_forall_length_le`).

## Main definitions

* `Cslib.Algorithms.ShortestPaths.walkWeight`: the weight of a walk.
* `Cslib.Algorithms.ShortestPaths.NoNegCycle`: every closed walk has nonnegative weight.
* `Cslib.Algorithms.ShortestPaths.IsShortestDistances`: `D` is the shortest-distance matrix.

## Main results

* `Cslib.Algorithms.ShortestPaths.exists_nodup_walk`: without negative cycles, every walk can be
  shortened to a walk with the same endpoints, no repeated vertex and no larger weight.
* `Cslib.Algorithms.ShortestPaths.isShortestDistances_of_sound_complete`: the criterion above.
* `Cslib.Algorithms.ShortestPaths.IsShortestDistances.unique`: shortest distances are unique.
* `Cslib.Algorithms.ShortestPaths.noNegCycle_of_forall_length_le`: short closed walks suffice.
* `Cslib.Algorithms.ShortestPaths.NoNegCycle.submatrix`,
  `Cslib.Algorithms.ShortestPaths.IsShortestDistances.submatrix`: invariance under relabelling.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Chapter 24
  (introduction, on negative-weight cycles and cycle-free shortest paths) and Section 25.1.
-/

public section

open MinTropical

namespace Cslib.Algorithms.ShortestPaths

variable {R : Type*} [LinearOrderedAddCommMonoidWithTop R] {V : Type*}

/-! ### Walks -/

/-- The weight of the walk that starts at `i` and then visits the vertices of `l` in order: the
product of its edge entries, which over `MinTropical R` is the sum of the edge weights. -/
@[expose] def walkWeight {α : Type*} [Mul α] [One α] (W : Matrix V V α) : V → List V → α
  | _, [] => 1
  | i, v :: l => W i v * walkWeight W v l

@[simp] theorem walkWeight_nil {α : Type*} [Mul α] [One α] (W : Matrix V V α) (i : V) :
    walkWeight W i [] = 1 := rfl

@[simp] theorem walkWeight_cons {α : Type*} [Mul α] [One α] (W : Matrix V V α) (i v : V)
    (l : List V) : walkWeight W i (v :: l) = W i v * walkWeight W v l := rfl

/-- The weight of a concatenation of walks. -/
theorem walkWeight_append {α : Type*} [Monoid α] (W : Matrix V V α) (i : V) (l₁ l₂ : List V) :
    walkWeight W i (l₁ ++ l₂) = walkWeight W i l₁ * walkWeight W (l₁.getLastD i) l₂ := by
  induction l₁ generalizing i with
  | nil => simp
  | cons v l ih => simp only [List.cons_append, walkWeight_cons, ih, List.getLastD_cons, mul_assoc]

/-- Relabelling the vertices of a walk. -/
theorem walkWeight_submatrix {U : Type*} {α : Type*} [Mul α] [One α] (W : Matrix V V α)
    (e : U → V) :
    ∀ (u : U) (l : List U), walkWeight (W.submatrix e e) u l = walkWeight W (e u) (l.map e)
  | _, [] => rfl
  | u, v :: l => by
    simp only [walkWeight_cons, List.map_cons, Matrix.submatrix_apply, walkWeight_submatrix W e v l]

/-- `W` has no negative cycles: every closed walk has weight at least `1`, that is, tropical
weight at least `0` in `R`. -/
@[expose] def NoNegCycle (W : Matrix V V (MinTropical R)) : Prop :=
  ∀ (i : V) (l : List V), l.getLastD i = i → 1 ≤ walkWeight W i l

variable {W : Matrix V V (MinTropical R)}

/-- A walk that revisits a vertex contains a closed subwalk: the walk from `i` along `l` splits
as a prefix `p` ending at `u`, a nonempty closed walk `c` at `u`, and a suffix `s`. -/
private theorem exists_split_of_not_nodup :
    ∀ (i : V) (l : List V), ¬ (i :: l).Nodup →
      ∃ (u : V) (p c s : List V), l = p ++ c ++ s ∧ p.getLastD i = u ∧ c ≠ [] ∧
        c.getLastD u = u
  | i, [], h => absurd (List.nodup_singleton i) h
  | i, v :: l, h => by
    rw [List.nodup_cons] at h
    by_cases hi : i ∈ v :: l
    · obtain ⟨s, t, hst⟩ := List.append_of_mem hi
      refine ⟨i, [], s ++ [i], t, by simp [hst], rfl, by simp, ?_⟩
      rw [List.getLastD_append]
      rfl
    · obtain ⟨u, p, c, s, rfl, hp, hc, hcu⟩ :=
        exists_split_of_not_nodup v l (fun hn => h ⟨hi, hn⟩)
      exact ⟨u, v :: p, c, s, rfl, by rw [List.getLastD_cons, hp], hc, hcu⟩

/-- Cutting a closed subwalk `c` out of a walk `p ++ c ++ s`. -/
private theorem walkWeight_split {i u : V} {p c s : List V} (hp : p.getLastD i = u)
    (hcu : c.getLastD u = u) :
    walkWeight W i (p ++ c ++ s) = walkWeight W i (p ++ s) * walkWeight W u c := by
  rw [walkWeight_append, walkWeight_append, List.getLastD_append, hp, hcu, walkWeight_append, hp]
  exact mul_right_comm _ _ _

private theorem getLastD_split {i u : V} {p c s : List V} (hp : p.getLastD i = u)
    (hcu : c.getLastD u = u) : (p ++ c ++ s).getLastD i = (p ++ s).getLastD i := by
  rw [List.getLastD_append, List.getLastD_append, List.getLastD_append, hp, hcu]

/-- **Cycle removal.** Without negative cycles, every walk can be replaced by a walk with the
same endpoints, no repeated vertex and no larger weight. -/
theorem exists_nodup_walk (hW : NoNegCycle W) (i : V) (l : List V) :
    ∃ l' : List V, (i :: l').Nodup ∧ l'.getLastD i = l.getLastD i ∧
      walkWeight W i l' ≤ walkWeight W i l := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    by_cases hnd : (i :: l).Nodup
    · exact ⟨l, hnd, rfl, le_rfl⟩
    · obtain ⟨u, p, c, s, rfl, hp, hc, hcu⟩ := exists_split_of_not_nodup i l hnd
      have hcpos : 0 < c.length := List.length_pos_iff.2 hc
      obtain ⟨l', hnd', hlast, hw⟩ :=
        ih (p ++ s).length (by simp only [List.length_append] at hn ⊢; omega) (p ++ s) rfl
      refine ⟨l', hnd', by rw [hlast, getLastD_split hp hcu], hw.trans ?_⟩
      rw [walkWeight_split hp hcu]
      exact le_mul_of_one_le_right' (hW u c hcu)

/-- Closed walks are nonnegative as soon as closed walks with at most `card V` edges are. -/
theorem noNegCycle_of_forall_length_le [Fintype V]
    (h : ∀ (i : V) (l : List V), l.length ≤ Fintype.card V → l.getLastD i = i →
      1 ≤ walkWeight W i l) : NoNegCycle W := by
  intro i l hl
  induction hn : l.length using Nat.strong_induction_on generalizing i l with
  | _ n ih =>
    by_cases hnd : l.Nodup
    · exact h i l (hn ▸ hnd.length_le_card) hl
    · obtain ⟨v, l', rfl⟩ : ∃ v l', l = v :: l' := by
        cases l with
        | nil => exact absurd List.nodup_nil hnd
        | cons v l' => exact ⟨v, l', rfl⟩
      obtain ⟨u, p, c, s, hl', hp, hc, hcu⟩ := exists_split_of_not_nodup v l' hnd
      have hsplit : v :: l' = (v :: p) ++ c ++ s := by rw [hl']; rfl
      have hp' : (v :: p).getLastD i = u := by rw [List.getLastD_cons, hp]
      rw [hsplit] at hl hn ⊢
      have hcpos : 0 < c.length := List.length_pos_iff.2 hc
      have h1 := ih ((v :: p) ++ s).length (by simp only [List.length_append] at hn ⊢; omega) i _
        (by rw [← getLastD_split hp' hcu, hl]) rfl
      have h2 := ih c.length
        (by simp only [List.length_append, List.length_cons] at hn; omega) u c hcu rfl
      rw [walkWeight_split hp' hcu]
      exact one_le_mul h1 h2

/-- Relabelling the vertices preserves the absence of negative cycles. -/
theorem NoNegCycle.submatrix {U : Type*} (hW : NoNegCycle W) (e : U ≃ V) :
    NoNegCycle (W.submatrix e e) := by
  intro u l hl
  rw [walkWeight_submatrix]
  exact hW (e u) (l.map e) (by rw [List.getLastD_map, hl])

/-! ### Shortest distances -/

/-- `D` is the shortest-distance matrix of `W`: each `D i j` is the greatest lower bound of the
weights of the walks from `i` to `j` (the tropical `0 = ⊤` if there is no such walk). -/
@[expose] def IsShortestDistances (W D : Matrix V V (MinTropical R)) : Prop :=
  ∀ i j, IsGLB {x | ∃ l : List V, l.getLastD i = j ∧ walkWeight W i l = x} (D i j)

/-- Shortest distances are unique. -/
theorem IsShortestDistances.unique {D₁ D₂ : Matrix V V (MinTropical R)}
    (h₁ : IsShortestDistances W D₁) (h₂ : IsShortestDistances W D₂) : D₁ = D₂ :=
  Matrix.ext fun i j => (h₁ i j).unique (h₂ i j)

/-- **Shortest-distance criterion.** Without negative cycles, `D` is the shortest-distance matrix
as soon as each entry is `0` or the weight of a walk with the right endpoints (soundness), and
each entry lies below the weight of every walk without repeated vertices (completeness). -/
theorem isShortestDistances_of_sound_complete {D : Matrix V V (MinTropical R)}
    (hW : NoNegCycle W)
    (hsound : ∀ i j, D i j = 0 ∨ ∃ l : List V, l.getLastD i = j ∧ walkWeight W i l = D i j)
    (hcomplete : ∀ i l, (i :: l).Nodup → D i (l.getLastD i) ≤ walkWeight W i l) :
    IsShortestDistances W D := by
  intro i j
  constructor
  · rintro _ ⟨l, rfl, rfl⟩
    obtain ⟨l', hnd, hlast, hw⟩ := exists_nodup_walk hW i l
    rw [← hlast]
    exact (hcomplete i l' hnd).trans hw
  · intro b hb
    rcases hsound i j with h | ⟨l, hl, hw⟩
    · rw [h]
      exact le_zero b
    · exact hw ▸ hb ⟨l, hl, rfl⟩

/-- Relabelling the vertices preserves shortest distances. -/
theorem IsShortestDistances.submatrix {U : Type*} {D : Matrix V V (MinTropical R)}
    (h : IsShortestDistances W D) (e : U ≃ V) :
    IsShortestDistances (W.submatrix e e) (D.submatrix e e) := by
  intro u u'
  have hset : {x | ∃ l : List U, l.getLastD u = u' ∧ walkWeight (W.submatrix e e) u l = x} =
      {x | ∃ l : List V, l.getLastD (e u) = e u' ∧ walkWeight W (e u) l = x} := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l.map e, by rw [List.getLastD_map, hl], (walkWeight_submatrix W e u l).symm⟩
    · rintro ⟨l, hl, rfl⟩
      refine ⟨l.map e.symm, ?_, ?_⟩
      · apply e.injective
        rw [← List.getLastD_map (f := e), List.map_map, Equiv.self_comp_symm, List.map_id, hl]
      · rw [walkWeight_submatrix, List.map_map, Equiv.self_comp_symm, List.map_id]
  rw [hset]
  exact h (e u) (e u')

end Cslib.Algorithms.ShortestPaths
