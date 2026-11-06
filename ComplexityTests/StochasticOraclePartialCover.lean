/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.StochasticOracle.PartialCoverRisk
import Mathlib.Tactic

/-!
# Complete partial-cover certification clients

Overlapping responses, repeated sets and a rejected expensive overlap exercise
Lemma 1. A one-element stochastic instance realizes the conditional guarantee;
its exact two-call success probability is `3/4`. Empty and zero-call cases
exercise the boundary of the risk bound.
-/

noncomputable section
open Finset Cslib.Optimization.OneConstraint
open Cslib.Probability.StochasticOracle.PartialCover
open Cslib.Probability.StochasticOracle.PartialCover.Instance
namespace ComplexityTests.StochasticOraclePartialCover

/-- Two unit-weight singleton sets with tight dual prices. -/
def singletons : Instance Bool Bool where
  ground := univ
  sets b := {b}
  sets_subset _ := subset_univ _
  weight _ := 1
  weight_nonneg _ := by norm_num
  dual _ := 1
  dual_nonneg _ := by norm_num
  dual_feasible _ := by simp

example : singletons.Certified 1 ∅ {false} ∧
    ¬ singletons.Certified 1 {false} {false} ∧
    ¬ singletons.Certified 1 {false} {false, true} ∧
    singletons.Certified 1 {false} {true} := by
  norm_num [Certified, cost, covered, singletons]
  decide

/-- The overlapping two-set response is rejected because only one element is new. -/
example : singletons.retain 1 ∅ [{false}, {false, true}, {false}, {true}] = univ := by
  have hdiff : ({false, true} : Finset Bool) \ {false} = {true} := by decide
  have hdiff' : ({true} : Finset Bool) \ {false} = {true} := by decide
  norm_num [retain, Certified, cost, covered, singletons, hdiff, hdiff']
  decide

example : singletons.cost (singletons.retain 1 ∅ [{false}, {false, true}, {true}]) = 2 := by
  have hdiff : ({false, true} : Finset Bool) \ {false} = {true} := by decide
  have hdiff' : ({true} : Finset Bool) \ {false} = {true} := by decide
  norm_num [retain, Certified, cost, covered, singletons, hdiff, hdiff']

/-- One original set covers the only obligation; its dual price is tight. -/
def one : Instance Unit Unit where
  ground := {()}
  sets _ := {()}
  sets_subset _ := Subset.rfl
  weight _ := 1
  weight_nonneg _ := by norm_num
  dual _ := 1
  dual_nonneg _ := by norm_num
  dual_feasible _ := by simp

/-- Each call independently returns the singleton or the empty response with equal probability. -/
def fair : ResponseKernel Unit := fun _ =>
  pair {()} ∅ (1 / 2) (by norm_num) (by norm_num)

private theorem fair_good (h : List (Finset Unit)) (C : Finset Unit)
    (he : () ∉ one.covered C) :
    (1 / 2 : ℝ) ≤ event (fair h) (fun P => one.Certified 1 C P ∧ () ∈ one.covered P) := by
  have hC : C = ∅ := by
    ext u
    constructor
    · intro hu
      exact False.elim (he (mem_biUnion.mpr ⟨u, hu, by simp [one]⟩))
    · intro hu
      simp at hu
  subst C
  norm_num [fair, event, pair_mean, Certified, cost, covered, one]

/-- The history-conditional source assumption is inhabited for every call count. -/
theorem fair_admissible (n : ℕ) (h : List (Finset Unit)) (C : Finset Unit) :
    one.Admissible 1 (1 / 2) fair h C (List.replicate n {()}) := by
  induction n generalizing h C with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_, fun P _ => ih (P :: h) (one.step 1 C P)⟩
    intro e _ he
    cases e
    exact fair_good h C he

/-- Exact success of the actual response law, rather than a separately assumed probability. -/
example : event (one.law 1 fair [] ∅ [{()}, {()}]) (fun P => one.covered P = one.ground) =
    3 / 4 := by
  norm_num [law, event, fair, Distribution.mean_bind, pair_mean, Distribution.mean_pure,
    step, Certified, cost, covered, one]

/-- The generic theorem attains the exact probability in this instance. -/
example : (3 / 4 : ℝ) ≤
    event (one.law 1 fair [] ∅ [{()}, {()}]) (fun P => one.covered P = one.ground) := by
  have h := one.completion_bound 1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num) fair [{()}, {()}] (fair_admissible 2 [] ∅)
  norm_num [one, chances] at h
  exact h

example : event (one.law 1 fair [] ∅ []) (fun P => one.covered P = one.ground) = 0 := by
  norm_num [law, event, Distribution.mean_pure, covered, one]

/-- A second response guaranteed to succeed after the fair first response.
The complete response law is correlated rather than a product of call laws. -/
def correlated : ResponseKernel Unit := fun h =>
  if h = [] then fair h else Distribution.pure {()}

example : event (one.law 1 correlated [] ∅ [{()}, {()}])
    (fun P => one.covered P = one.ground) = 1 := by
  norm_num [law, correlated, event, fair, Distribution.mean_bind, pair_mean,
    Distribution.mean_pure, step, Certified, cost, covered, one]

example : ¬ one.Admissible 1 (1 / 2) (fun _ => Distribution.pure ∅) [] ∅ [{()}] := by
  norm_num [Admissible, event, Distribution.mean_pure, Certified, covered, one]

/-- Completion on an empty universe costs no original sets, even without any calls. -/
def empty : Instance Unit Unit where
  ground := ∅
  sets _ := ∅
  sets_subset _ := Subset.rfl
  weight _ := 1
  weight_nonneg _ := by norm_num
  dual _ := 0
  dual_nonneg _ := by norm_num
  dual_feasible _ := by simp

example : event (empty.law 1 fair [] ∅ [])
    (fun P => empty.covered P = empty.ground ∧ empty.cost P ≤ 0) = 1 := by
  norm_num [law, event, Distribution.mean_pure, covered, cost, empty]

example : repetitions (1 / 2) (1 / 4) = 2 := by
  have htwo := (pow_le_iff_repetitions_le (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) (by norm_num : (0 : ℝ) < 1 / 4) 2).mp (by norm_num)
  have hone := (pow_le_iff_repetitions_le (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) (by norm_num : (0 : ℝ) < 1 / 4) 1)
  norm_num at hone
  omega

example : repetitions (1 / 2) (1 / 2) = 1 := by
  have hone := (pow_le_iff_repetitions_le (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2) 1).mp (by norm_num)
  have hzero := (pow_le_iff_repetitions_le (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2) 0)
  norm_num at hzero
  omega

example : chances () ([false, true].flatMap fun b =>
    List.replicate (if b then 3 else 2) ({()} : Finset Unit)) = 5 := by
  decide

end ComplexityTests.StochasticOraclePartialCover
