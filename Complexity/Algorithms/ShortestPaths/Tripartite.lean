/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ShortestPaths.Walk
public import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators

/-!
# The tripartite graph of a (min,+) product

The (min,+) product `A * B` of two `ι × ι` matrices is a shortest-distance block of a graph with
three copies of `ι`: `tripartite A B` on `Fin 3 × ι` has an edge `(0, i) → (1, j)` of weight
`A i j`, an edge `(1, j) → (2, k)` of weight `B j k` and no other edges. Every walk with a finite
weight climbs one layer per edge, so the graph has no cycles at all, hence no negative cycles,
and the walks from `(0, i)` to `(2, k)` of finite weight are exactly the two-edge walks through
some `(1, j)`. Thus the shortest distance from `(0, i)` to `(2, k)` is `(A * B) i k`.

This is the reduction from (min,+) products to all-pairs shortest paths on `3 n` vertices.

## Main definitions

* `Cslib.Algorithms.ShortestPaths.tripartite`: the tripartite graph of `A` and `B`.

## Main results

* `Cslib.Algorithms.ShortestPaths.noNegCycle_tripartite`: the tripartite graph has no negative
  cycles.
* `Cslib.Algorithms.ShortestPaths.isGLB_tripartite`: the shortest distance from `(0, i)` to
  `(2, k)` is `(A * B) i k`.
* `Cslib.Algorithms.ShortestPaths.IsShortestDistances.tripartite_block`: the same for any
  shortest-distance matrix of any relabelling of the tripartite graph.

## References

* [Vassilevska Williams and Williams, *Subcubic Equivalences Between Path, Matrix, and Triangle
  Problems*][VassilevskaWilliamsWilliams2018].
-/

public section

open MinTropical

namespace Cslib.Algorithms.ShortestPaths

variable {R : Type*} [LinearOrderedAddCommMonoidWithTop R] {ι : Type*}

/-- The tripartite graph on `Fin 3 × ι` of the (min,+) product `A * B`: edges `(0, i) → (1, j)`
of weight `A i j`, edges `(1, j) → (2, k)` of weight `B j k`, and no others. -/
@[expose] def tripartite {α : Type*} [Zero α] (A B : Matrix ι ι α) :
    Matrix (Fin 3 × ι) (Fin 3 × ι) α :=
  Matrix.of fun (a, i) (b, j) =>
    if a = 0 ∧ b = 1 then A i j else if a = 1 ∧ b = 2 then B i j else 0

private theorem tripartite_ne_zero {A B : Matrix ι ι (MinTropical R)} {u v : Fin 3 × ι}
    (h : tripartite A B u v ≠ 0) : (v.1 : ℕ) = u.1 + 1 := by
  obtain ⟨a, i⟩ := u
  obtain ⟨b, j⟩ := v
  simp only [tripartite, Matrix.of_apply] at h
  split_ifs at h with h1 h2
  · obtain ⟨rfl, rfl⟩ := h1
    rfl
  · obtain ⟨rfl, rfl⟩ := h2
    rfl
  · exact absurd rfl h

/-- A walk of finite weight in the tripartite graph climbs one layer per edge. -/
private theorem length_of_walkWeight_tripartite_ne_zero {A B : Matrix ι ι (MinTropical R)} :
    ∀ (u : Fin 3 × ι) (l : List (Fin 3 × ι)), walkWeight (tripartite A B) u l ≠ 0 →
      ((l.getLastD u).1 : ℕ) = u.1 + l.length
  | _, [], _ => rfl
  | u, v :: l, h => by
    rw [walkWeight_cons] at h
    have h1 : tripartite A B u v ≠ 0 := fun h0 => h (by rw [h0, zero_mul])
    have h2 : walkWeight (tripartite A B) v l ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
    rw [List.getLastD_cons, length_of_walkWeight_tripartite_ne_zero v l h2,
      tripartite_ne_zero h1, List.length_cons]
    omega

/-- The tripartite graph has no negative cycles: its only closed walks of finite weight are the
empty ones. -/
theorem noNegCycle_tripartite (A B : Matrix ι ι (MinTropical R)) :
    NoNegCycle (tripartite A B) := by
  intro u l hl
  by_cases h0 : walkWeight (tripartite A B) u l = 0
  · rw [h0]
    exact le_zero _
  · have := length_of_walkWeight_tripartite_ne_zero u l h0
    rw [hl] at this
    have hl0 : l = [] := List.length_eq_zero_iff.1 (by omega)
    subst hl0
    exact le_rfl

variable [Fintype ι]

/-- In the tripartite graph, the shortest distance from `(0, i)` to `(2, k)` is the
(min,+) product entry `(A * B) i k`. -/
theorem isGLB_tripartite (A B : Matrix ι ι (MinTropical R)) (i k : ι) :
    IsGLB {x | ∃ l : List (Fin 3 × ι), l.getLastD (0, i) = (2, k) ∧
      walkWeight (tripartite A B) (0, i) l = x} ((A * B) i k) := by
  constructor
  · rintro _ ⟨l, hl, rfl⟩
    by_cases h0 : walkWeight (tripartite A B) (0, i) l = 0
    · rw [h0]
      exact le_zero _
    have hlen := length_of_walkWeight_tripartite_ne_zero _ l h0
    rw [hl] at hlen
    have hlen' : l.length = 2 := by simpa using hlen.symm
    obtain ⟨⟨b, j⟩, w, rfl⟩ := List.length_eq_two.1 hlen'
    simp only [List.getLastD_cons, List.getLastD_nil] at hl
    subst hl
    rw [walkWeight_cons, walkWeight_cons, walkWeight_nil, mul_one, Matrix.mul_apply]
    by_cases hb : b = 1
    · subst hb
      simp only [tripartite, Matrix.of_apply]
      exact sum_le_of_mem (fun j => A i j * B j k) (Finset.mem_univ j)
    · have : tripartite A B (0, i) (b, j) = 0 := by
        simp [tripartite, hb]
      rw [this, zero_mul]
      exact le_zero _
  · intro x hx
    rw [Matrix.mul_apply]
    obtain ⟨j, -, hj⟩ := exists_sum_eq (Finset.univ_nonempty_iff.2 ⟨i⟩)
      (fun j => A i j * B j k)
    rw [hj]
    have := hx ⟨[(1, j), (2, k)], rfl, rfl⟩
    simpa [tripartite] using this

/-- If `D` is the shortest-distance matrix of any relabelling `e` of the tripartite graph of
`A` and `B`, then its block from layer `0` to layer `2` is the (min,+) product `A * B`. -/
theorem IsShortestDistances.tripartite_block {U : Type*} {A B : Matrix ι ι (MinTropical R)}
    (e : Fin 3 × ι ≃ U) {D : Matrix U U (MinTropical R)}
    (hD : IsShortestDistances ((tripartite A B).submatrix e.symm e.symm) D) (i k : ι) :
    D (e (0, i)) (e (2, k)) = (A * B) i k := by
  have h := hD.submatrix e
  rw [Matrix.submatrix_submatrix, e.symm_comp_self, Matrix.submatrix_id_id] at h
  exact (h (0, i) (2, k)).unique (isGLB_tripartite A B i k)

end Cslib.Algorithms.ShortestPaths
