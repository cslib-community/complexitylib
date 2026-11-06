/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.StochasticOracle.PartialCoverGreedy
import ComplexityTests.StochasticOraclePartialCover
import Mathlib.Tactic

/-!
# Executable multicover clients

Exact rational comparisons, repeated selection, zero marginals, non-covering
inputs, empty universes and the actual risk/benchmark/probability bridges.
-/

open Finset
open Cslib.Algorithms.Lean.Multicover
open Cslib.Probability.StochasticOracle.PartialCover.Instance
namespace ComplexityTests.StochasticOracleMulticoverGreedy

def left : Oracle Bool := ⟨{false}, 1⟩
def right : Oracle Bool := ⟨{true}, 1⟩
def both : Oracle Bool := ⟨univ, 3⟩
def useless : Oracle Bool := ⟨∅, 0⟩
def oracles : List (Oracle Bool) := [useless, left, right, both]

theorem cover : ∀ e : Bool, ∃ a ∈ oracles, e ∈ a.eligible := by
  intro e
  cases e
  · exact ⟨left, by simp [oracles], by simp [left]⟩
  · exact ⟨right, by simp [oracles], by simp [right]⟩

theorem nonneg : ∀ a ∈ oracles, 0 ≤ a.cost := by
  intro a ha
  simp only [oracles, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> norm_num [useless, left, right, both]

-- Higher gain is not preferred when its cost/gain ratio is worse.
example : choose (fun _ : Bool => 2) oracles = some left := by
  norm_num [Cslib.Algorithms.Lean.Multicover.choose,
    gain, ratio, oracles, useless, left, right, both, Finset.filter_insert, Finset.filter_singleton]
theorem batch_two : batch oracles 2 = [left, left, right, right] := by
  norm_num [batch, run, Cslib.Algorithms.Lean.Multicover.choose,
    reduce, gain, ratio, oracles, useless, left, right, both,
    Finset.filter_insert, Finset.filter_singleton]
example : bill (batch oracles 2) = 4 := by rw [batch_two]; norm_num [bill, left, right]
example : batch oracles 0 = [] := by decide
example : choose (fun _ : Bool => 0) oracles = none := by decide
example : batch ([] : List (Oracle Empty)) 5 = [] := by decide

-- Termination on an infeasible input does not establish multicover completion.
example : residual (fun _ : Bool => 1) (batch [left] 1) true = 1 := by decide

example (r : ℕ) : (batch oracles r).length ≤ 2 * r ∧
    ∀ e, residual (fun _ => r) (batch oracles r) e = 0 := by
  exact batch_spec oracles cover r

example (r : ℕ) (e : Bool) : r ≤ chances e ((batch oracles r).map Oracle.eligible) :=
  batch_chances oracles cover r e

-- A concrete feasible benchmark; the harmonic comparison is derived for the actual output.
example : bill (batch oracles 2) ≤ harmonic 4 * bill [both, both] := by
  apply batch_bill_le oracles [both, both] 2 nonneg
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hb
    subst b
    simp [oracles]
  · intro e
    cases e <;> decide

example : repeatFactor 3 7 = 3 ∧ repeatFactor 3 6 = 2 ∧ repeatFactor 3 0 = 0 := by decide

-- A normalized response model and a risk-feasible benchmark inhabit the source hypotheses.
noncomputable section
open StochasticOraclePartialCover

example :
    let r₀ := repetitions (1/2) (1/2)
    let r₁ := repetitions (1/2) ((1/2) / Fintype.card Bool)
    let calls := batch oracles r₁
    (∑ e ∈ singletons.ground, (1/2 : ℝ) ^ chances e (calls.map Oracle.eligible)) ≤ 1/2 ∧
    (bill calls : ℝ) ≤ (1 + Real.log (Fintype.card Bool * r₁)) *
      repeatFactor r₀ r₁ * (bill [both, both] : ℝ) := by
  apply greedy_risk_bill singletons rfl (by simp [singletons]) oracles [both, both]
    cover nonneg
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hb
    subst b
    simp [oracles]
  all_goals norm_num [singletons, chances, both]

def unitOracle : Oracle Unit := ⟨{()}, 1⟩

example : (3 / 4 : ℝ) ≤ event
    (one.law 1 fair [] ∅ ((batch [unitOracle] 2).map Oracle.eligible))
    (fun P => one.covered P = one.ground ∧
      one.cost P ≤ 1 * ∑ e ∈ one.ground, one.dual e) := by
  have hrep : repetitions (1 / 2) (1 / 4) = 2 := by
    have htwo := (pow_le_iff_repetitions_le (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num) (by norm_num : (0 : ℝ) < 1 / 4) 2).mp (by norm_num)
    have hone := (pow_le_iff_repetitions_le (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num) (by norm_num : (0 : ℝ) < 1 / 4) 1)
    norm_num at hone
    omega
  have hc : ∀ e : Unit, ∃ a ∈ [unitOracle], e ∈ a.eligible := by
    intro e; cases e; exact ⟨unitOracle, by simp, by simp [unitOracle]⟩
  have hb : (batch [unitOracle] 2).map Oracle.eligible = [{()}, {()}] := by decide
  have had : one.Admissible 1 (1 / 2) fair [] ∅
      ((batch [unitOracle] 2).map Oracle.eligible) := by
    rw [hb]
    exact fair_admissible 2 [] ∅
  have hrep' : repetitions (1 - (1 / 2 : ℝ)) ((1 / 4 : ℝ) / Fintype.card Unit) = 2 := by
    convert hrep using 1; norm_num
  have h := greedy_certified_completion (ρ := 1) one rfl (by simp [one]) [unitOracle] hc
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 4)
    fair (by rw [hrep']; exact had)
  have hx : repetitions (1 / 2) (1 / 4 / (Fintype.card Unit : ℝ)) = 2 := by
    simpa only [Fintype.card_unit, Nat.cast_one, div_one] using hrep
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] at h
  rw [hx] at h
  exact h

-- The generic response-law bridge preserves the complete certification event.
example {ρ p δ : ℝ} (hp : 0 < p) (hpone : p < 1) (hδ : 0 < δ)
    (K : ResponseKernel Bool)
    (had : singletons.Admissible ρ p K [] ∅
      ((batch oracles (repetitions (1 - p) (δ / Fintype.card Bool))).map Oracle.eligible)) :
    1 - δ ≤ event
      (singletons.law ρ K [] ∅
        ((batch oracles (repetitions (1 - p) (δ / Fintype.card Bool))).map Oracle.eligible))
      (fun P => singletons.covered P = singletons.ground ∧
        singletons.cost P ≤ ρ * ∑ e ∈ singletons.ground, singletons.dual e) :=
  greedy_certified_completion singletons rfl (by simp [singletons]) oracles cover hp hpone hδ K had

end
end ComplexityTests.StochasticOracleMulticoverGreedy
