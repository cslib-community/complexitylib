/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.FairDivision.MaximinShare
public import CslibFrontier.GameTheory.FairDivision.MMSPopulation
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Exact MMS existence and the logarithmic item threshold

Complete allocations are functions assigning every item to an agent. The
partition-comparison definitions below express exact goods and chores MMS
without choosing an ordering or an extremum representation for the benchmark:
for goods, every competing partition has a bundle worth at most the assigned
bundle; for chores, every competing partition has a bundle costing at least it.
For finite nonempty agent sets these are precisely the max-min and min-max
benchmarks in [EzraGarbuz2027], Section 1.1 (PDF pp. 3–5).

`not_goodsExistenceBudget` and `not_choresExistenceBudget` prove the negative
logarithmic threshold direction for all n ≥ 65536 and all real-valued additive
instances: positive integer counterexamples already suffice. The final theorem
keeps the positive existence direction attributed to Feige explicitly external.
It does not prove Feige's theorem or claim that it has been source-audited.

## Main results

- `not_goodsExistenceBudget`: no universal exact goods MMS guarantee at the
  explicit logarithmic item budget, for every sufficiently large n.
- `not_choresExistenceBudget`: the corresponding exact chores obstruction.
- `logarithmic_threshold_of_external_existence`: combines the proved negative
  direction with an explicitly supplied external positive-existence theorem.
-/

public section

open scoped BigOperators

namespace Cslib.FairDivision

open MMSAsymptotic

private theorem gap_pos (n : ℕ) (hn : 65536 ≤ n) : 0 < populationGap n := by
  have hr : 16 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) (by norm_num; exact hn)
  have hr' : (0 : ℝ) < Nat.log 2 n := by exact_mod_cast (show 0 < Nat.log 2 n by omega)
  dsimp only [populationGap]
  positivity

private theorem target_pos (n : ℕ) : 0 < 204 * (populationLength n : ℝ) ^ 3 := by
  have hk : 0 < populationLength n := by dsimp [populationLength]; omega
  positivity

private theorem cast_bundle {k d : ℕ} (f : Good k d → ℤ) (a : Allocation k d) (i : HighGood k d) :
    bundleValue (fun g => (f g : ℝ)) a i = ((∑ g ∈ bundle k d a i, f g : ℤ) : ℝ) := by
  simp [bundleValue, bundle]

/-- For every sufficiently large n, no universal exact-MMS goods guarantee can
cover n+640 floor(log₂ n) items. This ranges over all finite real additive instances. -/
theorem not_goodsExistenceBudget (n : ℕ) (hn : 65536 ≤ n) :
    ¬ GoodsExistenceBudget n (n + 640 * Nat.log 2 n) := by
  intro h
  obtain ⟨S, hp, hM, hg, _, _, hitems⟩ := population_hardness n hn
  let k := populationLength n
  let d := populationDummies n
  obtain ⟨a, ha⟩ := h (Good k d) (HighGood k d) (card_population n hn) hitems
    (fun i g => (goodsValue k d (S i) g : ℝ)) (by intro i g; exact_mod_cast (hp i g).1.le)
  obtain ⟨i, hi⟩ := hg a
  obtain ⟨p, hpart⟩ := ((hM i (204 * (k : ℤ) ^ 3)).1).mpr le_rfl
  obtain ⟨j, hj⟩ := ha i p
  rw [cast_bundle, cast_bundle] at hj
  have hb : (204 * (k : ℝ) ^ 3) ≤ ((∑ g ∈ bundle k d p j, goodsValue k d (S i) g : ℤ) : ℝ) := by
    exact_mod_cast hpart j
  have hgap := gap_pos n hn
  have ht := target_pos n
  nlinarith

/-- The same quantified item-budget obstruction for chores. -/
theorem not_choresExistenceBudget (n : ℕ) (hn : 65536 ≤ n) :
    ¬ ChoresExistenceBudget n (n + 640 * Nat.log 2 n) := by
  intro h
  obtain ⟨S, hp, hM, _, hc, _, hitems⟩ := population_hardness n hn
  let k := populationLength n
  let d := populationDummies n
  obtain ⟨a, ha⟩ := h (Good k d) (HighGood k d) (card_population n hn) hitems
    (fun i g => (choreCost k d (S i) g : ℝ)) (by intro i g; exact_mod_cast (hp i g).2.le)
  obtain ⟨i, hi⟩ := hc a
  obtain ⟨p, hpart⟩ := ((hM i (204 * (k : ℤ) ^ 3)).2).mpr le_rfl
  obtain ⟨j, hj⟩ := ha i p
  rw [cast_bundle, cast_bundle] at hj
  have hb : ((∑ g ∈ bundle k d p j, choreCost k d (S i) g : ℤ) : ℝ) ≤ 204 * (k : ℝ) ^ 3 := by
    exact_mod_cast hpart j
  have hgap := gap_pos n hn
  have ht := target_pos n
  nlinarith

/-- Conditional combination with the separate external positive-existence result
attributed to Feige in [EzraGarbuz2027], Section 1.2 (PDF pp. 5–6). For both goods
and chores, universal existence holds below one logarithmic excess and fails at
another. The positive direction is an explicit hypothesis, not a local theorem. -/
theorem logarithmic_threshold_of_external_existence
    (hFeige : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
      GoodsExistenceBudget n (n + ⌊c * Real.logb 2 n⌋₊) ∧
      ChoresExistenceBudget n (n + ⌊c * Real.logb 2 n⌋₊)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
      GoodsExistenceBudget n (n + ⌊c * Real.logb 2 n⌋₊) ∧
      ChoresExistenceBudget n (n + ⌊c * Real.logb 2 n⌋₊) ∧
      ¬ GoodsExistenceBudget n (n + 640 * Nat.log 2 n) ∧
      ¬ ChoresExistenceBudget n (n + 640 * Nat.log 2 n) := by
  obtain ⟨c, hc, N, hN⟩ := hFeige
  refine ⟨c, hc, max N 65536, fun n hn => ?_⟩
  exact ⟨(hN n (by omega)).1, (hN n (by omega)).2,
    not_goodsExistenceBudget n (by omega), not_choresExistenceBudget n (by omega)⟩

end Cslib.FairDivision
