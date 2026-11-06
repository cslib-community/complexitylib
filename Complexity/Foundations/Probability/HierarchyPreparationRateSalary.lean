/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyPreparationPayment
public import Complexity.Foundations.Probability.HierarchyPreparationSalary
public import Complexity.Foundations.Probability.HierarchyFixedCharge

/-!
# Terminal-rate salary for field-free PREP

These original comparisons concern the sufficient field-free envelope, not actual-error
lower bounds. Corresponding input and PREP requests retain both channels: the two grid
precision penalties cancel, leaving rank gap forty (pilot) or four (actual), and the
literal child-budget loss. The retained fourth-moment coefficient costs `2^(16*ka)`.
The existing root normalizer comparison has a constant independent of the terminal
rate, and therefore supplies no cancellation of that cost. A sharper relative PREP
comparison, or a sharper decoder comparison carrying a compensating rate factor, is
necessary to pay this envelope uniformly over unbounded terminal exponents.

No recursive success, availability, independence or noise-rarity conclusion is made.
In particular an unpaid sufficient envelope is not an estimator counterexample.

## Main results

* `evaluate_preparation_bounded_rate_paid_root`: fixed charge before geometry, including full rates.
* `preparation_rate_salary_iff`: exact production salary with the remaining rate cost.
* `preparation_rate_envelope_unpaid`: an obstruction to the sufficient envelope only.
* `exists_joint_preparation_rate_obstruction`: compatibility with the joint depth guards.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Cslib
variable {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- Exact terminal-rate cost, before any structural salary. -/
theorem preparation_rate_cost (ka : ℕ) :
    (rate ka)⁻¹ ^ 4 = (2 : ℝ) ^ (16 * (ka : ℝ)) := by
  simp only [rate, inv_pow, inv_inv, ← pow_mul]
  rw [← Real.rpow_natCast]
  congr 1
  push_cast
  ring

/-- The common source and terminal precision penalties do not pay the remaining
terminal-rate cost. This is an exact equivalence, with the production budget loss. -/
theorem preparation_rate_salary_iff (B : BudgetData HP P) (M : ℕ)
    (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (ka : ℕ) (ht : r.terminal.rate = rate ka) (c : ℝ) :
    let q := {r with task := .row 0 (if pilot then .pilotInput i else .input i)}
    c * (r.terminal.rate)⁻¹ ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 ↔
    c * (2 : ℝ) ^ (16 * (ka : ℝ)) ≤
      (2 : ℝ) ^ (4 * (((B.childBudget M : ℕ) : ℝ) - M) / (16 * B.slack) +
        4 * B.rankCharge * (if pilot then 40 else 4)) := by
  dsimp only
  have h := B.preparation_bias_production_salary_iff M pilot i r hr
    (c * (r.terminal.rate)⁻¹ ^ 4)
  dsimp only at h
  simpa only [ht, preparation_rate_cost] using h

/-- An explicit logarithmic guard pays the envelope. It depends on constants and
terminal exponent, not on a presumed target-error inequality. The budget estimate
is valid also at a truncated zero budget. -/
theorem preparation_rate_salary_le (B : BudgetData HP P) (M : ℕ)
    (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (ka : ℕ) (ht : r.terminal.rate = rate ka) (c : ℝ) (hc : 0 < c)
    (hcharge : Real.logb 2 c + 16 * (ka : ℝ) + 1 / 4 ≤
      4 * B.rankCharge * (if pilot then 40 else 4)) :
    let q := {r with task := .row 0 (if pilot then .pilotInput i else .input i)}
    c * (r.terminal.rate)⁻¹ ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  dsimp only
  have h := B.preparation_rate_salary_iff M pilot i r hr ka ht c
  dsimp only at h
  rw [h]
  rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1) hc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have hb := B.childBudget_precision_loss M
  have he : 4 * ((B.childBudget M : ℝ) - M) / (16 * B.slack) =
      -4 * (((M : ℝ) - B.childBudget M) / (16 * B.slack)) := by ring
  rw [he]
  linarith

/-- Once the terminal rate is too small, even dropping the negative budget loss
cannot pay this sufficient envelope. This does not lower-bound actual PREP error. -/
theorem preparation_rate_envelope_unpaid (B : BudgetData HP P) (M : ℕ)
    (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (ka : ℕ) (ht : r.terminal.rate = rate ka) (c : ℝ) (hc : 0 < c)
    (hsmall : 4 * B.rankCharge * (if pilot then 40 else 4) <
      Real.logb 2 c + 16 * (ka : ℝ)) :
    let q := {r with task := .row 0 (if pilot then .pilotInput i else .input i)}
    ¬ c * (r.terminal.rate)⁻¹ ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  dsimp only
  have h := B.preparation_rate_salary_iff M pilot i r hr ka ht c
  dsimp only at h
  rw [h]
  apply not_le.mpr
  rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1) hc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
  have hm : (B.childBudget M : ℝ) ≤ M := by exact_mod_cast Nat.sub_le M _
  have hs : 0 < (B.slack : ℝ) := by exact_mod_cast B.slack_pos
  have hd : 4 * ((B.childBudget M : ℝ) - M) / (16 * B.slack) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

/-- Every fixed positive envelope coefficient and fixed charge admits terminal
exponents beyond its salary, for both the pilot and actual rank gaps. Geometry and
budgets may subsequently grow; increasing common precisions does not repair the ratio. -/
theorem exists_preparation_rate_obstruction (c charge : ℝ) :
    ∃ ka₀ : ℕ, ∀ ka ≥ ka₀, ∀ pilot : Bool,
      4 * charge * (if pilot then 40 else 4) < Real.logb 2 c + 16 * (ka : ℝ) := by
  obtain ⟨ka₀, hk⟩ := exists_nat_gt (|160 * charge| + |16 * charge| + |Real.logb 2 c|)
  refine ⟨ka₀, ?_⟩
  intro ka hka pilot
  have hcast : (ka₀ : ℝ) ≤ ka := by exact_mod_cast hka
  have hlog := neg_abs_le (Real.logb 2 c)
  have hp := le_abs_self (160 * charge)
  have ha := le_abs_self (16 * charge)
  cases pilot <;> norm_num <;> linarith [abs_nonneg (160 * charge),
    abs_nonneg (16 * charge), abs_nonneg (Real.logb 2 c)]


/-- Actual successful PREP and its own successful input pay the original root
consumer under the explicit structural/rate guard. RAW and maximum are held fixed.
The coefficient is fixed at HP before geometry. This does not equate distinct calls
or supply recursive availability. At full terminal rate the guard has no rate cost. -/
theorem evaluate_preparation_rate_paid_root :
    ∃ c : ℝ, 0 < c ∧ ∀ (P : ℕ) [Fact P.Prime] (B : BudgetData HP P)
      (M : ℕ) (pilot : Bool) (i : Fin HP.k)
      (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
    r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i) →
    0 < B.requestPrecision M r → B.childBudget M < M →
    r.usage = r.terminal → 0 ≤ r.source.rate → 0 < r.terminal.rate →
    ∀ (A W : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ),
    let q := { r with task := .row 0 (if pilot then .pilotInput i else .input i) }
    0 < B.requestPrecision (B.childBudget M) q →
    B.evaluate (B.childBudget M) q = some (.row A) →
    B.evaluate M r = some (.row W) →
    rowNormPow 4 P q.source.rate
      (fun σ x => q.source.retains (channels B.padding) σ x)
      (fun σ y => q.usage.retains (channels B.padding) σ y)
      (fun σ x y => A σ x y - B.canonicalPreparationInput pilot i r x y) ≤
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 →
    ∀ (s u : Fin 3) (_hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P)),
    r.source = gridChannel s ks ss → r.usage = gridChannel u ku su →
    ∀ (ka : ℕ), r.terminal.rate = rate ka →
    Real.logb 2 c + 16 * (ka : ℝ) + 1 / 4 ≤
      4 * B.rankCharge * (if pilot then 40 else 4) →
    Admissible r →
    ∀ (raw : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
      (maximum : Environment P 3 → ZMod P → ℝ),
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    let output := fun prep => correctionRequest B.padding id r
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ raw prep maximum
    rootDistPow 4 P r.source.rate X U (output W)
      (output (B.incomingPreparation r
        (fun _ => B.canonicalPreparationInput pilot i r))) ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  obtain ⟨L, hL, hbias⟩ := evaluate_preparation_paid_bias (HP := HP)
  obtain ⟨C, hC, hroot⟩ := correctionRequest_normalizer_root_moment_le (HP := HP)
  let c := (C * L) ^ 4 + 1
  have hc : 0 < c := by dsimp only [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro P instP B M pilot i r hr hp hm hu hs hf A W q hqp hA hW hih
    a u hau ks ku ss su hsource husage ka ht hcharge hadm raw maximum X U output
  have hb := hbias P B M pilot i r hr hp hm hu hs hf A W hqp hA hW hih
    a u hau ks ku ss su hsource husage
  have hd := hroot P B r hadm hs hf raw W
    (B.incomingPreparation r (fun _ => B.canonicalPreparationInput pilot i r)) maximum
  apply hd.trans
  apply (mul_le_mul_of_nonneg_left hb (pow_nonneg hC 4)).trans
  have hcoef : C ^ 4 * (L / r.terminal.rate) ^ 4 ≤ c * (r.terminal.rate)⁻¹ ^ 4 := by
    rw [div_eq_mul_inv, mul_pow]
    dsimp only [c]
    rw [mul_pow]
    nlinarith [pow_nonneg (inv_nonneg.mpr hf.le) 4]
  have he := mul_le_mul_of_nonneg_right hcoef
    (by positivity : 0 ≤ ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4)
  rw [mul_assoc] at he
  exact he.trans (B.preparation_rate_salary_le M pilot i r hr ka ht c hc hcharge)


/-- A bounded terminal exponent admits one charge chosen before fields, budgets
and requests. At full rate take `cap = 0`; no source exponent restriction is needed. -/
theorem exists_preparation_bounded_rate_charge (c : ℝ) (cap lower : ℕ) :
    ∃ A₀ : ℕ, lower ≤ A₀ ∧ ∀ A ≥ A₀, ∀ ka ≤ cap, ∀ pilot : Bool,
      Real.logb 2 c + 16 * (ka : ℝ) + 1 / 4 ≤
        4 * (A : ℝ) * (if pilot then 40 else 4) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|Real.logb 2 c| + 16 * (cap : ℝ) + 1)
  refine ⟨max lower n, le_max_left _ _, ?_⟩
  intro A hA ka hka pilot
  have hnA : (n : ℝ) ≤ A := by exact_mod_cast (le_max_right lower n).trans hA
  have hkc : (ka : ℝ) ≤ cap := by exact_mod_cast hka
  cases pilot <;> norm_num <;> linarith [le_abs_self (Real.logb 2 c),
    abs_nonneg (Real.logb 2 c), (show (0 : ℝ) ≤ A from Nat.cast_nonneg A)]

/-- Existing joint depth guards coexist with an unpaid rate envelope. Fix a
terminal exponent beyond the fixed charge first, then grow `M = 2^N` and
`n = M/8+1`. The predecessor bounded-prime construction can choose fields after
these depths. This asserts scalar feasibility, not successful recursive histories. -/
theorem exists_joint_preparation_rate_obstruction (B : BudgetData HP P)
    (hslack : B.slack = 1) (allocation ks ka ku idMax : ℕ)
    (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (c : ℝ) (hc : 0 < c)
    (hsmall : 4 * B.rankCharge * (if pilot then 40 else 4) <
      Real.logb 2 c + 16 * (ka : ℝ)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let M := 2 ^ N
      let n := M / 8 + 1
      ks ≤ n ∧ 2 * ka ≤ n ∧ ku ≤ n ∧ idMax < 2 ^ n ∧
      B.slack * (1 + 4 * (n + ka)) < M ∧ M ≤ 32 * B.slack * n ∧
      16 * (B.slack : ℝ) * (2 * ((ka : ℝ) + ks) + B.rankCharge * r.task.rank +
        allocation + (Nat.log2 M + 1 : ℕ) + 3) ≤ M ∧
      0 < B.requestPrecision M r ∧
      (let q := {r with task := .row 0 (if pilot then .pilotInput i else .input i)}
      ¬ c * r.terminal.rate⁻¹ ^ 4 *
          ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 ≤
        ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4) := by
  obtain ⟨N₀, hg⟩ := exists_prefix_joint_depth_family allocation B hslack ks ka ku idMax r hs ht
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨hks, hka, hku, hid, hfit, homit, hprefix, hpos⟩ := hg N hN
  exact ⟨hks, hka, hku, hid, hfit, homit, hprefix, hpos,
    B.preparation_rate_envelope_unpaid (2 ^ N) pilot i r hr ka ht c hc hsmall⟩


/-- Fix a terminal exponent cap and all regularity/decoder constants before one
charge, then pay the actual root consumer at every field and budget. Full terminal
rates are the case `cap = 0`. All literal success, masks and positive own precision
hypotheses survive; no unrestricted-rate or recursive availability claim follows. -/
theorem evaluate_preparation_bounded_rate_paid_root (cap lower : ℕ) :
    ∃ A₀ : ℕ, lower ≤ A₀ ∧ ∀ charge ≥ A₀, ∀ (P : ℕ) [Fact P.Prime] (B : BudgetData HP P)
      (M : ℕ) (pilot : Bool) (i : Fin HP.k)
      (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
    B.rankCharge = (charge : ℝ) →
    r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i) →
    0 < B.requestPrecision M r → B.childBudget M < M →
    r.usage = r.terminal → 0 ≤ r.source.rate → 0 < r.terminal.rate →
    ∀ (A W : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ),
    let q := { r with task := .row 0 (if pilot then .pilotInput i else .input i) }
    0 < B.requestPrecision (B.childBudget M) q →
    B.evaluate (B.childBudget M) q = some (.row A) →
    B.evaluate M r = some (.row W) →
    rowNormPow 4 P q.source.rate
      (fun σ x => q.source.retains (channels B.padding) σ x)
      (fun σ y => q.usage.retains (channels B.padding) σ y)
      (fun σ x y => A σ x y - B.canonicalPreparationInput pilot i r x y) ≤
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 →
    ∀ (s u : Fin 3) (_hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P)),
    r.source = gridChannel s ks ss → r.usage = gridChannel u ku su →
    ∀ (ka : ℕ), r.terminal.rate = rate ka →
    ka ≤ cap →
    Admissible r →
    ∀ (raw : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
      (maximum : Environment P 3 → ZMod P → ℝ),
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    let output := fun prep => correctionRequest B.padding id r
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ raw prep maximum
    rootDistPow 4 P r.source.rate X U (output W)
      (output (B.incomingPreparation r
        (fun _ => B.canonicalPreparationInput pilot i r))) ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  obtain ⟨c, hc, hroot⟩ := evaluate_preparation_rate_paid_root (HP := HP)
  obtain ⟨A₀, hlower, hsalary⟩ := exists_preparation_bounded_rate_charge c cap lower
  refine ⟨A₀, hlower, ?_⟩
  intro charge hcharge P instP B M pilot i r hB hr hp hm hu hs hf A W q hqp hA hW hih
    a u hau ks ku ss su hsource husage ka ht hka hadm raw maximum
  apply hroot P B M pilot i r hr hp hm hu hs hf A W hqp hA hW hih
    a u hau ks ku ss su hsource husage ka ht _ hadm raw maximum
  rw [hB]
  exact hsalary charge hcharge ka hka pilot

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
