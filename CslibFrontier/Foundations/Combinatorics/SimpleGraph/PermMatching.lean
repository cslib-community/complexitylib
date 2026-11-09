/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `Combinatorics/SimpleGraph/Matching.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.GroupTheory.Perm.Cycle.Type
import CslibFrontier.Foundations.GroupTheory.Perm.ReverseCycle
import Mathlib.Data.ZMod.Basic

/-!
# A perfect matching from a permutation with even cycles

If a permutation `σ` of the vertices of a finite simple graph `G` moves every vertex to a
neighbour, then its cycles are cycles of `G` (of length at least `2`, since `G` has no loops).
When all of them have even length, taking every other edge of each cycle gives a perfect matching
of `G` (`SimpleGraph.exists_isPerfectMatching_of_perm`). This is the combinatorial half of the
proof of Tutte's determinant criterion for perfect matchings [Tutte1947]: a nonzero term in the
expansion of the determinant of the Tutte matrix is such a permutation.

The matching is built by colouring every vertex `y` with the parity of its distance from a fixed
representative of its cycle along `σ`. Since the cycle has even length, the colour alternates
along `σ`, and each vertex is matched to `σ y` or to `σ⁻¹ y` according to its colour.

## Main results

* `SimpleGraph.exists_isPerfectMatching_of_perm`: a permutation along the edges of `G` with only
  even cycles gives a perfect matching.

## References

* [W. T. Tutte, *The factorization of linear graphs*][Tutte1947]
-/

public section

open Equiv Equiv.Perm Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A permutation that moves every vertex of `G` to a neighbour and has only cycles of even
length gives a perfect matching of `G`: match every other edge of each cycle. -/
theorem exists_isPerfectMatching_of_perm (σ : Perm V) (hadj : ∀ v, G.Adj v (σ v))
    (heven : ∀ n ∈ σ.cycleType, Even n) : ∃ M : G.Subgraph, M.IsPerfectMatching := by
  rw [forall_even_cycleType_iff] at heven
  have hfix : ∀ v, σ v ≠ v := fun v h => (hadj v).ne h.symm
  have hai : ∀ y, σ (σ⁻¹ y) = y := σ.apply_symm_apply
  have hia : ∀ y, σ⁻¹ (σ y) = y := σ.symm_apply_apply
  let q : V → Quotient (SameCycle.setoid σ) := Quotient.mk _
  have hrep : ∀ y, σ.SameCycle (q y).out y := fun y => Quotient.mk_out (s := SameCycle.setoid σ) y
  have hrepσ : ∀ y, (q (σ y)).out = (q y).out := fun y =>
    congrArg Quotient.out (Quotient.sound (sameCycle_apply_left.2 (SameCycle.refl σ y)))
  let k : V → ℤ := fun y => (hrep y).choose
  have hk : ∀ y, (σ ^ k y) (q y).out = y := fun y => (hrep y).choose_spec
  let col : V → ZMod 2 := fun y => (k y : ZMod 2)
  have hcol : ∀ y, col (σ y) = col y + 1 := by
    intro y
    have h1 : (σ ^ k (σ y)) (q y).out = (σ ^ (k y + 1)) (q y).out := by
      rw [← hrepσ, hk, add_comm, _root_.zpow_add, zpow_one, Perm.mul_apply, hrepσ, hk]
    rw [zpow_eq_zpow_on_iff σ (hfix _)] at h1
    have h2 : (2 : ℤ) ∣ (#(σ.cycleOf (q y).out).support : ℤ) := by
      exact_mod_cast (even_iff_two_dvd.1 (heven _))
    have h3 : k (σ y) % 2 = (k y + 1) % 2 := by
      rw [← Int.emod_emod_of_dvd _ h2, h1, Int.emod_emod_of_dvd _ h2]
    have h4 : ((k (σ y) : ℤ) : ZMod 2) = ((k y + 1 : ℤ) : ZMod 2) :=
      (ZMod.intCast_eq_intCast_iff' _ _ 2).2 h3
    simp only [col, h4]
    push_cast
    rfl
  have hcolinv : ∀ y, col (σ⁻¹ y) = col y + 1 := by
    intro y
    have := hcol (σ⁻¹ y)
    rw [hai] at this
    rw [this, add_assoc, show (1 + 1 : ZMod 2) = 0 from rfl, add_zero]
  let τ : V → V := fun y => if col y = 0 then σ y else σ⁻¹ y
  have hz : ∀ c : ZMod 2, c ≠ 0 → c + 1 = 0 := by decide
  have hτ : Function.Involutive τ := by
    intro y
    by_cases hy : col y = 0
    · have : col (σ y) ≠ 0 := by rw [hcol, hy]; decide
      simp only [τ, ite_eq_left hy, ite_eq_right this, hia]
    · have : col (σ⁻¹ y) = 0 := by rw [hcolinv]; exact hz _ hy
      simp only [τ, ite_eq_right hy, ite_eq_left this, hai]
  have hτadj : ∀ y, G.Adj y (τ y) := by
    intro y
    by_cases hy : col y = 0
    · simp only [τ, ite_eq_left hy]
      exact hadj y
    · simp only [τ, ite_eq_right hy]
      have := hadj (σ⁻¹ y)
      rw [hai] at this
      exact this.symm
  let M : G.Subgraph :=
    { verts := Set.univ
      Adj := fun v w => τ v = w
      adj_sub := fun h => h ▸ hτadj _
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨fun v w (h : τ v = w) => by rw [← h, hτ v]⟩ }
  exact ⟨M, Subgraph.isPerfectMatching_iff.2 fun v =>
    ⟨τ v, rfl, fun w (hw : τ v = w) => hw.symm⟩⟩

end SimpleGraph
