/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
-- upstream: candidate

import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.ActualMoment

/-! The compatible capacity schedule admits K beyond 2^64 and preserves a positive,
uncentered output after a real increment from zero row and default. These deterministic
fixtures do not instantiate every stochastic hypothesis of the moment theorem. -/

namespace NormalizedAtomCapacityTests
open Matrix.FourthRootHierarchyParams.NormalizedRow
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Matrix Cslib.RowCompression
open scoped BigOperators
open Classical in
private lemma unit_rank_zero (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (d : Unit → ℝ) : kthLargest HP.K univ d = 0 := by
  apply le_antisymm _ kthLargest_nonneg
  apply le_of_not_gt
  intro h
  have hh := (lt_kthLargest_iff (rank_pos HP) (le_refl (0 : ℝ))).mp h
  have hc := card_filter_le (s := (univ : Finset Unit)) (p := fun y => 0 < d y)
  have hk := rank_gt_one HP
  simp only [card_univ, Fintype.card_unit] at hc
  omega

open Classical in
/-- A genuine zero initial state followed by a nonzero first sample has nonzero actual
normalized output. Both encoded signals use the uncentered 3/4 preparatory mean. -/
theorem compatible_zero_start_nonzero_output (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ scale ζ : ℝ, 0 < scale ∧ scale ≤ HP.η ∧ 0 < ζ ∧ ζ ≤ scale / 2 ∧
    let w : Unit → Fin 2 → ℝ := fun _ ν => if ν = 0 then 1 else ζ * (3 / 4)
    let a := iterate univ (compatibleCapacity HP.K 1) (fun _ => HP.K) (fun _ => scale / 2)
      (fun _ => w) (⟨0, 0⟩ : State Unit) 1
    0 < a.defaultValue ∧ 0 < output HP ζ (a.row () 0) (a.row () 1)
      (firstRank univ HP.K a.defaultValue a.row) := by
  obtain ⟨scale, ζ, hs, hm, _hc, hζ, hζs, _hζθ⟩ := fixed_shape HP
  refine ⟨scale, ζ, hs, hm, hζ, hζs, ?_⟩
  dsimp only
  let w : Unit → Fin 2 → ℝ := fun _ ν => if ν = 0 then 1 else ζ * (3 / 4)
  let a := iterate univ (compatibleCapacity HP.K 1) (fun _ => HP.K) (fun _ => scale / 2)
    (fun _ => w) (⟨0, 0⟩ : State Unit) 1
  have heq : a = iterate univ (compatibleCapacity HP.K 1) (fun _ => HP.K) (fun _ => scale / 2)
      (fun _ => 0) ⟨0, w⟩ 1 := by
    simp only [a, iterate_succ, iterate_zero, advance, zero_add, add_zero]
  have hdef : scale / 2 ≤ a.defaultValue := by
    rw [heq]
    change scale / 2 ≤ newDefault univ (compatibleCapacity HP.K 1 0) HP.K (scale / 2) 0 (w + 0)
    exact (le_max_left _ _).trans (le_max_right _ _) |>.trans (le_max_left _ _)
  have href := reference_iterate_output_eq (H := output HP ζ) hs.le (rank_pos HP)
    (s := (univ : Finset Unit)) (a := (⟨0, w⟩ : State Unit)) (n := compatibleCapacity HP.K 1) (ρ
        := fun _ => scale / 2)
    (fun y _ => by change -scale ≤ (1 : ℝ); linarith)
    (fun y _ => by change |ζ * (3 / 4)| ≤ scale; rw [abs_mul, abs_of_pos hζ]; norm_num; linarith)
    (hm.trans_lt HP.η_lt_η₂) (threshold_margin HP)
    (fun _ _ _ hx => entry_zero HP hx) (fun _ _ _ hq => gate_zero HP hq)
    (fun _ _ _ _ hq hq' => gate_flat HP (hq.2.trans hm) (hq'.2.trans hm)) 1
    (fun i _ => (compatibleCapacity_bounds HP.K 1 i).1) (fun _ _ => by linarith) () (mem_univ _)
  refine ⟨by change 0 < a.defaultValue; linarith, ?_⟩
  change 0 < output HP ζ (a.row () 0) (a.row () 1) (firstRank univ HP.K a.defaultValue a.row)
  rw [heq, href]
  simp only [w, Fin.isValue, ↓reduceIte, one_ne_zero, firstRank,
    unit_rank_zero HP, max_self, output, HP.ρ_one 0 HP.η_pos.le, mul_one]
  have hQ : 0 < HP.toHierarchyParams.atomCutoff 1 := by
    rw [HP.toHierarchyParams.atomCutoff_eq (by norm_num) (by
      have := Nat.cast_nonneg (α := ℝ) HP.k
      linarith)]
    have h := HP.le_Q 1
    have ht := HP.θ₂_lt
    norm_num at ht
    linarith
  exact div_pos hQ (lt_of_lt_of_le (by norm_num : (0 : ℝ)<1 / 2) (clip_bounds _).1)
end NormalizedAtomCapacityTests

namespace NormalizedAtomCapacityTests
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Cslib Cslib.RowCompression Matrix
open Classical in
/-- Raising K preserves the hierarchy contracts: the gate requirement is a lower bound. -/
private def raiseRank (HP : FourthRootHierarchyParams 16 1 16 32 8) (K : ℕ) (hK : HP.K ≤ K) :
    FourthRootHierarchyParams 16 1 16 32 8 :=
  { HP with K := K, gate := HP.gate.trans (Nat.cast_le.mpr hK) }

open Classical in
/-- A genuine hierarchy with rank beyond the old schedule's terminal capacity,
compatible capacities at every horizon, and a positive output from the zero state. -/
theorem large_rank_regression : ∃ HP : FourthRootHierarchyParams 16 1 16 32 8,
    2 ^ 64 < HP.K ∧
    (∀ m i, HP.K ≤ compatibleCapacity HP.K m i ∧
      2 ^ (64 * dyadicSlack m i) ≤ compatibleCapacity HP.K m i) ∧
    ∃ scale ζ : ℝ, 0 < scale ∧ scale ≤ HP.η ∧ 0 < ζ ∧ ζ ≤ scale / 2 ∧
      let w : Unit → Fin 2 → ℝ := fun _ ν => if ν = 0 then 1 else ζ * (3 / 4)
      let a := iterate Finset.univ (compatibleCapacity HP.K 1) (fun _ => HP.K) (fun _ => scale / 2)
        (fun _ => w) (⟨0, 0⟩ : State Unit) 1
      0 < a.defaultValue ∧ 0 < Matrix.FourthRootHierarchyParams.NormalizedRow.output HP ζ
        (a.row () 0) (a.row () 1)
        (firstRank Finset.univ HP.K a.defaultValue a.row) := by
  obtain ⟨HP⟩ := FourthRootHierarchyParams.nonempty (by norm_num : (0 : ℝ)<16) (by norm_num : (0
      : ℝ)<1)
  let HP' := raiseRank HP (max HP.K (2 ^ 80)) (le_max_left _ _)
  refine ⟨HP', ?_, fun m i => compatibleCapacity_bounds HP'.K m i, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : 2 ^ 64 < (2 ^ 80 : ℕ)) (le_max_right _ _)
  · exact NormalizedAtomCapacityTests.compatible_zero_start_nonzero_output HP'
end NormalizedAtomCapacityTests
