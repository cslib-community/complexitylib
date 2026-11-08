/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Analysis.SpecialFunctions.Hyperbolic
import CslibFrontier.Privacy.DifferentialPrivacy.AdvancedComposition
import CslibFrontier.Privacy.DifferentialPrivacy.RandomizedResponse

/-!
# Advanced composition: instances

* `k` adaptive rounds of randomized response, in the form of [DworkRoth2014, Theorem 3.20] and in
  the `tanh` form. Since `tanh (ln 3 / 2) = 1 / 2`, the linear term drops from `2 k ln 3` to
  `k ln 3 / 2`.
* A genuinely approximate round: randomized response together with a leak that releases a `true`
  input with probability `δ`. It is `(ln 3, δ)`-private but `(ε, 0)`-private for no `ε` when
  `δ > 0`, and `k` adaptive rounds add `k δ` to the failure probability.
* [DworkRoth2014, Corollary 3.21] with `k = 10000`, `δ' = e^{-32}`, `ε₀ = 1`: per-round privacy
  `1 / 1600` gives `(1, 10000 δ + e^{-32})`. Basic composition of the same rounds only gives
  `ε = 10000 / 1600 = 25 / 4`.
* The composition experiment against a randomized adaptive adversary, whose coin decides how it
  maps the challenge bit to a respondent's datum and whose next question depends on the previous
  answer.
-/

namespace CslibFrontierTests.Privacy.AdvancedComposition

open Cslib Cslib.Privacy
open scoped ENNReal

/-- Randomized response as a mechanism on one bit. -/
noncomputable abbrev rr : Bool → PMF Bool := fun truth => ProbComp.eval (randomizedResponse truth)

theorem tanh_log_three_div_two : Real.tanh (Real.log 3 / 2) = 1 / 2 := by
  rw [Real.tanh_half_eq_exp_sub_one_div, Real.exp_log (by norm_num)]
  norm_num

/-! ### Randomized response -/

/-- [DworkRoth2014, Theorem 3.20] for `k` rounds of randomized response (`e^{ln 3} - 1 = 2`). -/
example (k : ℕ) {δ' : ℝ} (hδ' : 0 < δ') :
    DifferentiallyPrivate (fun _ _ => True) (adaptiveComposition (fun _ : List Bool => rr) k)
      (Real.sqrt (2 * k * Real.log (1 / δ')) * Real.log 3 + k * Real.log 3 * 2)
      (k * 0 + ENNReal.ofReal δ') := by
  have := DifferentiallyPrivate.advancedComposition (fun _ _ _ => trivial)
    (M := fun _ : List Bool => rr) (Real.log_nonneg (by norm_num))
    (fun _ => differentiallyPrivate_randomizedResponse) k hδ'
  rw [Real.exp_log (by norm_num)] at this
  exact this.mono (le_of_eq (by ring)) le_rfl

/-- The `tanh` form for randomized response: the linear term is `k ln 3 / 2`. -/
example (k : ℕ) {δ' : ℝ} (hδ' : 0 < δ') :
    DifferentiallyPrivate (fun _ _ => True) (adaptiveComposition (fun _ : List Bool => rr) k)
      (Real.sqrt (2 * k * Real.log (1 / δ')) * Real.log 3 + k * Real.log 3 / 2)
      (k * 0 + ENNReal.ofReal δ') := by
  have := DifferentiallyPrivate.advancedComposition_sqrt (fun _ _ _ => trivial)
    (M := fun _ : List Bool => rr) (Real.log_nonneg (by norm_num))
    (fun _ => differentiallyPrivate_randomizedResponse) k hδ'
  rw [tanh_log_three_div_two] at this
  exact this.mono (le_of_eq (by ring)) le_rfl

/-! ### A genuinely approximate round -/

/-- A coin showing `true` with probability `δ`. -/
noncomputable def coin (δ : ℝ≥0∞) (hδ : δ ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun r => if r then δ else 1 - δ) (by
    simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
    exact add_tsub_cancel_of_le hδ)

/-- Releases a `true` input with probability `δ`, and `false` otherwise. -/
noncomputable def leak (δ : ℝ≥0∞) (hδ : δ ≤ 1) (b : Bool) : PMF Bool :=
  if b then coin δ hδ else PMF.pure false

theorem differentiallyPrivate_leak (δ : ℝ≥0∞) (hδ : δ ≤ 1) :
    DifferentiallyPrivate (fun _ _ => True) (leak δ hδ) 0 δ := by
  rw [DifferentiallyPrivate.iff_tsum_tsub_le]
  intro x y _
  cases x <;> cases y <;>
    simp only [leak, coin, tsum_bool, PMF.ofFintype_apply, PMF.pure_apply, Real.exp_zero,
      ENNReal.ofReal_one, one_mul, ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false,
      tsub_self, add_zero, tsub_zero, zero_tsub, zero_le]
  · rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hδ]
  · rw [tsub_eq_zero_of_le tsub_le_self, zero_add]

/-- Randomized response released together with the `δ`-leak of the same bit. -/
noncomputable def leakyRR (δ : ℝ≥0∞) (hδ : δ ≤ 1) (b : Bool) : PMF (Bool × Bool) := do
  let r₁ ← rr b
  let r₂ ← leak δ hδ b
  return (r₁, r₂)

theorem differentiallyPrivate_leakyRR (δ : ℝ≥0∞) (hδ : δ ≤ 1) :
    DifferentiallyPrivate (fun _ _ => True) (leakyRR δ hδ) (Real.log 3) δ := by
  have := differentiallyPrivate_randomizedResponse.prod (differentiallyPrivate_leak δ hδ)
  rw [add_zero, zero_add] at this
  exact this

theorem leakyRR_apply_true_true (δ : ℝ≥0∞) (hδ : δ ≤ 1) (b : Bool) :
    leakyRR δ hδ b (true, true) = rr b true * leak δ hδ b true := by
  simp only [leakyRR, Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
    PMF.bind_apply, PMF.pure_apply, tsum_bool, Prod.mk.injEq, Bool.true_eq_false, and_false,
    and_true, ite_false, ite_true, mul_zero, zero_add, mul_one]

/-- For `δ > 0` the leaky mechanism is `(ε, 0)`-private for no `ε`. -/
example (δ : ℝ≥0∞) (hδ : δ ≤ 1) (hδ0 : δ ≠ 0) (ε : ℝ) :
    ¬ DifferentiallyPrivate (fun _ _ => True) (leakyRR δ hδ) ε 0 := by
  rw [DifferentiallyPrivate.iff_apply_le]
  intro h
  have := h (x := true) (y := false) trivial (true, true)
  simp only [leakyRR_apply_true_true, leak, coin, ite_true, Bool.false_eq_true, ite_false,
    PMF.pure_apply, Bool.true_eq_false, mul_zero, PMF.ofFintype_apply, nonpos_iff_eq_zero,
    mul_eq_zero] at this
  rw [rr, eval_randomizedResponse_apply] at this
  simp only [ite_true] at this
  exact this.elim (by norm_num) hδ0

/-- `k` adaptive rounds of the leaky mechanism add `k δ` to the failure probability. -/
example (δ : ℝ≥0∞) (hδ : δ ≤ 1) (k : ℕ) {δ' : ℝ} (hδ' : 0 < δ') :
    DifferentiallyPrivate (fun _ _ => True)
      (adaptiveComposition (fun _ : List (Bool × Bool) => leakyRR δ hδ) k)
      (Real.sqrt (2 * k * Real.log (1 / δ')) * Real.log 3 + k * Real.log 3 / 2)
      (k * δ + ENNReal.ofReal δ') := by
  have := DifferentiallyPrivate.advancedComposition_sqrt (fun _ _ _ => trivial)
    (M := fun _ : List (Bool × Bool) => leakyRR δ hδ) (Real.log_nonneg (by norm_num))
    (fun _ => differentiallyPrivate_leakyRR δ hδ) k hδ'
  rw [tanh_log_three_div_two] at this
  exact this.mono (le_of_eq (by ring)) le_rfl

/-! ### Corollary 3.21 with concrete parameters -/

theorem log_one_div_exp_neg_32 : Real.log (1 / Real.exp (-32)) = 32 := by
  rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]

theorem sqrt_eq_800 : Real.sqrt (2 * (10000 : ℕ) * Real.log (1 / Real.exp (-32))) = 800 := by
  rw [log_one_div_exp_neg_32, Real.sqrt_eq_iff_mul_self_eq] <;> norm_num

/-- Per-round privacy `1 / 1600` makes `10000` adaptive rounds `(1, 10000 δ + e^{-32})`-private. -/
example {D R : Type} {Adj : D → D → Prop} (hAdj : ∀ ⦃x y⦄, Adj x y → Adj y x)
    {M : List R → D → PMF R} {δ : ℝ≥0∞}
    (h : ∀ history, DifferentiallyPrivate Adj (M history) (1 / 1600) δ) :
    DifferentiallyPrivate Adj (adaptiveComposition M 10000) 1
      (10000 * δ + ENNReal.ofReal (Real.exp (-32))) := by
  have := DifferentiallyPrivate.advancedComposition_of_target hAdj (M := M) (ε₀ := 1) (δ := δ)
    10000 zero_le_one (Real.exp_pos _) (by rw [log_one_div_exp_neg_32]; norm_num)
    (fun history => by
      rw [sqrt_eq_800, show (1 : ℝ) / (2 * 800) = 1 / 1600 by norm_num]
      exact h history)
  simpa only [Nat.cast_ofNat] using this

/-- Basic composition of the same rounds gives only `ε = 25 / 4`. -/
example {D R : Type} {Adj : D → D → Prop} {M : List R → D → PMF R} {δ : ℝ≥0∞}
    (h : ∀ history, DifferentiallyPrivate Adj (M history) (1 / 1600) δ) :
    DifferentiallyPrivate Adj (adaptiveComposition M 10000) (25 / 4) (10000 * δ) := by
  have := DifferentiallyPrivate.adaptiveComposition (ε := fun _ => 1 / 1600) (δ := fun _ => δ)
    (fun history => h history) 10000
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  exact this.mono (le_of_eq (by norm_num)) le_rfl

/-! ### The composition experiment -/

/-- A randomized adaptive adversary: its coin `ω` decides whether the respondent's datum is the
challenge bit or its negation, and after a `true` answer it negates once more. Every round runs
randomized response, so the adversary's view is private in the challenge bit. -/
example (k : ℕ) {δ' : ℝ} (hδ' : 0 < δ') :
    DifferentiallyPrivate (fun _ _ => True)
      (fun b : Bool => do
        let ω ← Probability.PMF.uniformOfFintype Bool
        let view ← adaptiveComposition
          (fun history b => rr (if ω = (history.head? == some true) then b else !b)) k b
        return (ω, view))
      (Real.sqrt (2 * k * Real.log (1 / δ')) * Real.log 3 +
        k * Real.log 3 * (Real.exp (Real.log 3) - 1))
      (k * 0 + ENNReal.ofReal δ') :=
  DifferentiallyPrivate.advancedComposition_experiment (Probability.PMF.uniformOfFintype Bool)
    (fun ω history b => if ω = (history.head? == some true) then b else !b) (fun _ _ => rr)
    (Real.log_nonneg (by norm_num)) (fun _ _ => differentiallyPrivate_randomizedResponse)
    (fun _ _ => ⟨trivial, trivial⟩) k hδ'

end CslibFrontierTests.Privacy.AdvancedComposition
