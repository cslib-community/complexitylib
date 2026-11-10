/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.PartialCoverGreedyNative
import Mathlib.Tactic

/-!
# End-to-end native source greedy planning

The original input contains no threshold. Global budget one half over three
elements gives per-element budget one sixth and exact threshold three. Deliberately
duplicate serialized labels demonstrate that actual output indices are constructed
from the oracle table, not certified by a caller-supplied label-validity promise.
-/

open Cslib Cslib.Probability.StochasticOracle
open Cslib.Algorithms.Lean Multicover PartialCover GreedyNative Turing.MultiTapeTM

private def whole : Native.Row := ⟨97, [true, true, false], 2⟩
private def right : Native.Row := ⟨97, [false, true, true], 1⟩
private def left : Native.Row := ⟨97, [true, false, false], 1⟩
private def table : List Native.Row := [whole, right, left]
private def input : GreedyNative.Input :=
  ⟨⟨3, table, ⟨1 / 2, 1 / 2⟩⟩, by
    constructor
    · norm_num
    · constructor <;> norm_num⟩

private theorem count_three : GreedyNative.count input = 3 := by
  let t := thresholdInput input
  have hle := (Instance.pow_le_iff_rationalRepetitions_le t.val.q t.val.budget
    t.property.q_pos t.property.q_lt_one t.property.budget_pos 3).mp
      (by norm_num [t, thresholdInput, scaled, input])
  have hgt := (Instance.pow_le_iff_rationalRepetitions_le t.val.q t.val.budget
    t.property.q_pos t.property.q_lt_one t.property.budget_pos 2).not.mp
      (by norm_num [t, thresholdInput, scaled, input])
  change GreedyNative.count input ≤ 3 at hle
  change ¬GreedyNative.count input ≤ 2 at hgt
  omega

example : labels input = [1, 1, 1, 2, 2, 2] := by
  rw [labels, plan, count_three]
  norm_num [Native.batch, Native.initial, Native.advance, Native.select, Native.consider,
    Native.ratio, Native.gain, Native.decrement, numberedRows, input, table, whole, right, left,
    Function.iterate_succ_apply', List.range_succ]

example {j : ℕ} (hj : j ∈ labels input) : j < 3 := labels_lt input hj

private def coverInstance : Instance (Fin 3) (Fin 3) where
  ground := Finset.univ
  sets j := {j}
  sets_subset _ := Finset.subset_univ _
  weight _ := 1
  weight_nonneg _ := by norm_num
  dual _ := 1
  dual_nonneg _ := by norm_num
  dual_feasible _ := by simp

private def benchmark : List (Oracle (Fin 3)) :=
  [Native.interpret 3 right, Native.interpret 3 right, Native.interpret 3 right,
    Native.interpret 3 left, Native.interpret 3 left]

example :
    let calls := (labels input).map (oracleAt input.val)
    (∑ e ∈ coverInstance.ground, (1 / 2 : ℝ) ^ Instance.chances e
      (calls.map Oracle.eligible)) ≤ 1 / 2 ∧
    (bill calls : ℝ) ≤ Asymptotics.factor (1 / 2) (1 / 2) 3 * 5 := by
  have h := risk_bill input coverInstance rfl
    (by intro e; fin_cases e <;> simp [input, table, whole, right, left])
    (by intro row hr
        simp only [input, table, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> norm_num [whole, right, left])
    (by norm_num [input]) benchmark
    (by
      change List.Subset [Native.interpret 3 right, Native.interpret 3 right,
        Native.interpret 3 right, Native.interpret 3 left, Native.interpret 3 left]
        [Native.interpret 3 whole, Native.interpret 3 right, Native.interpret 3 left]
      have hr : Native.interpret 3 right ∈ [Native.interpret 3 whole,
          Native.interpret 3 right, Native.interpret 3 left] := .tail _ (.head _)
      have hl : Native.interpret 3 left ∈ [Native.interpret 3 whole,
          Native.interpret 3 right, Native.interpret 3 left] := .tail _ (.tail _ (.head _))
      exact List.cons_subset.mpr ⟨hr, List.cons_subset.mpr ⟨hr, List.cons_subset.mpr
        ⟨hr, List.cons_subset.mpr ⟨hl, List.cons_subset.mpr ⟨hl, List.nil_subset _⟩⟩⟩⟩⟩)
    (by
      change (∑ e : Fin 3, (input.val.parameters.q : ℝ) ^ Instance.chances e
        (benchmark.map Oracle.eligible)) ≤ (input.val.parameters.budget : ℝ)
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
      norm_num [input, benchmark, Instance.chances, Native.interpret, right, left])
  have hb : (bill benchmark : ℝ) = 5 := by
    norm_num [bill, benchmark, Native.interpret, right, left,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  dsimp only [input] at h ⊢
  rw [hb] at h
  norm_num [List.map_map, Function.comp_def] at h ⊢
  exact h

example : ∃ T S : GreedyNative.Input → ℕ,
    PolyBounded size T ∧ PolyBounded size S ∧
      ComputableInTimeAndSpace labels encoding (encList encNat) T S := uniform_plan
