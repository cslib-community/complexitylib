/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/IncMatrix.lean`)

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# The oriented incidence matrix of a simple graph

`SimpleGraph.orientedIncMatrix G` is the integer `V × G.edgeSet` matrix whose column at an edge
`e` has `1` in the row of one endpoint of `e`, `-1` in the row of the other, and `0` elsewhere.
The orientation of each edge is the arbitrary but fixed one given by the representative
`Quot.out e` of `e : Sym2 V`. No order on `V` is needed. Mathlib's `SimpleGraph.incMatrix` is the
unoriented incidence matrix.

The Gram matrix of this orientation is the Laplacian: `N * Nᵀ = G.lapMatrix ℤ`
(`SimpleGraph.orientedIncMatrix_mul_transpose`). Each column of `N` sums to zero, and pairing a
column with a vertex function `f` gives the difference of the values of `f` at the two endpoints
(`SimpleGraph.sum_mul_orientedIncMatrix`).

## Main definitions

* `SimpleGraph.orientedIncMatrix`: the oriented incidence matrix.

## Main results

* `SimpleGraph.sum_mul_orientedIncMatrix`: a vertex function paired with a column is the
  difference of its values at the endpoints.
* `SimpleGraph.orientedIncMatrix_mul_self`, `SimpleGraph.orientedIncMatrix_mul_of_ne`: products
  of two entries in one column.
* `SimpleGraph.orientedIncMatrix_mul_transpose`: `N * Nᵀ = G.lapMatrix ℤ`.
-/

public section

open Matrix

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The two endpoints `(Quot.out e).1` and `(Quot.out e).2` of an edge are distinct. -/
theorem out_fst_ne_out_snd_of_mem_edgeSet {e : Sym2 V} (he : e ∈ G.edgeSet) :
    e.out.1 ≠ e.out.2 := by
  intro h
  have : e.IsDiag := by
    rw [← Sym2.mk_fst_out_snd_out e, Sym2.mk_isDiag_iff]
    exact h
  exact G.not_isDiag_of_mem_edgeSet he this

variable [DecidableEq V]

/-- The **oriented incidence matrix** of `G`: the column of an edge `e` is `1` at the endpoint
`(Quot.out e).1`, `-1` at the endpoint `(Quot.out e).2`, and `0` elsewhere. -/
noncomputable def orientedIncMatrix : Matrix V G.edgeSet ℤ := Matrix.of fun v e =>
  (if v = (e : Sym2 V).out.1 then 1 else 0) - (if v = (e : Sym2 V).out.2 then 1 else 0)

variable {G}

/-- The entries of the oriented incidence matrix. -/
theorem orientedIncMatrix_apply (v : V) (e : G.edgeSet) : G.orientedIncMatrix v e =
    (if v = (e : Sym2 V).out.1 then 1 else 0) - (if v = (e : Sym2 V).out.2 then 1 else 0) := by
  rw [orientedIncMatrix, Matrix.of_apply]

/-- Pairing a vertex function with a column of the oriented incidence matrix gives the difference
of its values at the two endpoints. In particular every column sums to zero. -/
theorem sum_mul_orientedIncMatrix [Fintype V] (f : V → ℤ) (e : G.edgeSet) :
    ∑ v, f v * G.orientedIncMatrix v e = f (e : Sym2 V).out.1 - f (e : Sym2 V).out.2 := by
  simp [orientedIncMatrix_apply, mul_sub, Finset.sum_sub_distrib]

/-- The square of an entry of the oriented incidence matrix is `1` at the endpoints of the edge
and `0` elsewhere. -/
theorem orientedIncMatrix_mul_self (u : V) (e : G.edgeSet) :
    G.orientedIncMatrix u e * G.orientedIncMatrix u e = if u ∈ (e : Sym2 V) then 1 else 0 := by
  have hne := G.out_fst_ne_out_snd_of_mem_edgeSet e.2
  have hmem : u ∈ (e : Sym2 V) ↔ u = (e : Sym2 V).out.1 ∨ u = (e : Sym2 V).out.2 := by
    conv_lhs => rw [← Sym2.mk_fst_out_snd_out (e : Sym2 V)]
    exact Sym2.mem_iff
  by_cases h1 : u = (e : Sym2 V).out.1
  · subst h1
    simp [orientedIncMatrix_apply, hne, hmem]
  · by_cases h2 : u = (e : Sym2 V).out.2
    · subst h2
      simp [orientedIncMatrix_apply, Ne.symm hne, hmem]
    · simp [orientedIncMatrix_apply, h1, h2, hmem]

/-- An entry of the oriented incidence matrix vanishes off the endpoints of its edge. -/
theorem orientedIncMatrix_eq_zero_of_notMem {u : V} {e : G.edgeSet} (hu : u ∉ (e : Sym2 V)) :
    G.orientedIncMatrix u e = 0 := by
  have := orientedIncMatrix_mul_self u e
  rw [ite_eq_right_iff.mpr (fun h => absurd h hu)] at this
  exact mul_self_eq_zero.mp this

/-- For distinct vertices `u` and `w`, the product of their entries in the column of `e` is `-1`
when `e` joins them and `0` otherwise. -/
theorem orientedIncMatrix_mul_of_ne {u w : V} (huw : u ≠ w) (e : G.edgeSet) :
    G.orientedIncMatrix u e * G.orientedIncMatrix w e =
      if (e : Sym2 V) = s(u, w) then -1 else 0 := by
  have hne := G.out_fst_ne_out_snd_of_mem_edgeSet e.2
  have he : (e : Sym2 V) = s((e : Sym2 V).out.1, (e : Sym2 V).out.2) :=
    (Sym2.mk_fst_out_snd_out _).symm
  set a := (e : Sym2 V).out.1
  set b := (e : Sym2 V).out.2
  simp only [he, Sym2.eq_iff]
  by_cases h1 : u = a <;> by_cases h2 : u = b <;> by_cases h3 : w = a <;>
    by_cases h4 : w = b <;> simp_all [orientedIncMatrix_apply] <;> grind

variable [Fintype V] [DecidableRel G.Adj]

/-- **The Laplacian is the Gram matrix of the oriented incidence matrix**:
`N * Nᵀ = G.lapMatrix ℤ`, for the orientation of `SimpleGraph.orientedIncMatrix`. -/
theorem orientedIncMatrix_mul_transpose :
    G.orientedIncMatrix * G.orientedIncMatrixᵀ = G.lapMatrix ℤ := by
  ext u w
  rw [Matrix.mul_apply]
  simp only [transpose_apply]
  by_cases huw : u = w
  · subst huw
    simp only [orientedIncMatrix_mul_self, lapMatrix, degMatrix, Matrix.sub_apply,
      diagonal_apply_eq, adjMatrix_apply, G.loopless.irrefl, ite_false, sub_zero,
      Finset.sum_boole]
    rw [← card_incidenceFinset_eq_degree]
    norm_cast
    refine Finset.card_bij (fun e _ => (e : Sym2 V)) (fun e he => ?_)
      (fun _ _ _ _ h => Subtype.ext h) (fun e he => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      simp [mem_incidenceFinset, incidenceSet, he]
    · simp only [mem_incidenceFinset, incidenceSet, Set.mem_ofPred_eq] at he
      exact ⟨⟨e, he.1⟩, by simp [he.2], rfl⟩
  · simp only [orientedIncMatrix_mul_of_ne huw, lapMatrix, degMatrix, Matrix.sub_apply,
      diagonal_apply_ne _ huw, adjMatrix_apply, zero_sub]
    by_cases hadj : G.Adj u w
    · have : ∀ x : G.edgeSet, ((x : Sym2 V) = s(u, w)) ↔ x = ⟨s(u, w), hadj⟩ :=
        fun x => ⟨fun h => Subtype.ext h, fun h => h ▸ rfl⟩
      simp [this, hadj]
    · rw [Finset.sum_eq_zero fun x _ => ?_]
      · simp [hadj]
      · rw [ite_eq_right_iff]
        intro hx
        exact absurd (hx ▸ x.2 : s(u, w) ∈ G.edgeSet) hadj

end SimpleGraph
