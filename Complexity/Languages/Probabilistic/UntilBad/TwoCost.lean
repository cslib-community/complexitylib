/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.UntilBad
import Complexity.Probability.PMF.Event

/-!
# Accumulating bad-event probability with two query costs

A stateful oracle may have two independently bounded kinds of calls. One cost charges calls
against a growing bad-event budget; the other charges a fixed error. This extends the single-cost
bound in `Complexity/Languages/Probabilistic/UntilBad.lean` without introducing a cryptographic
protocol dependency.

## Main results

* `Cslib.OracleComp.toOuterMeasure_bad_le_two`: bound the probability of a bad final state by
  `k₁ * (budget s + k₁ * δ₁ + k₂ * δ₂) + k₂ * ε` for two query-cost budgets `k₁` and `k₂`.
-/

@[expose] public section

namespace Cslib.OracleComp

open scoped ENNReal

/-- **Two-channel accumulated bad-state probability**: let each call `q` from a good state `¬bad s`
turn bad with probability at most `cost₁ q * budget s + cost₂ q * ε`, and raise `budget` by at most
`cost₁ q * δ₁ + cost₂ q * δ₂`. Then a program with `IsCostBounded cost₁ program k₁` and
`IsCostBounded cost₂ program k₂` reaches a bad state from `s` with probability at most
`k₁ * (budget s + k₁ * δ₁ + k₂ * δ₂) + k₂ * ε`. -/
theorem toOuterMeasure_bad_le_two {ι σ β : Type} {spec : ι → Type}
    {handler : (q : ι) → StateT σ PMF (spec q)} {bad : σ → Prop}
    (cost₁ cost₂ : ι → ℕ) (budget : σ → ℝ≥0∞) (δ₁ δ₂ ε : ℝ≥0∞)
    (hstep : ∀ q s, ¬bad s →
      (handler q s).toOuterMeasure {x | bad x.2} ≤ cost₁ q * budget s + cost₂ q * ε)
    (hgrow : ∀ q s, ¬bad s → ∀ x ∈ (handler q s).support, ¬bad x.2 →
      budget x.2 ≤ budget s + cost₁ q * δ₁ + cost₂ q * δ₂)
    {program : OracleComp spec β} {k₁ k₂ : ℕ}
    (hk₁ : IsCostBounded cost₁ program k₁) (hk₂ : IsCostBounded cost₂ program k₂)
    {s : σ} (hs : ¬bad s) :
    ((OracleComp.interpret handler program).run s).toOuterMeasure {x | bad x.2} ≤
      (k₁ : ℝ≥0∞) * (budget s + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂) + (k₂ : ℝ≥0∞) * ε := by
  induction hk₁ generalizing s k₂ with
  | pure a k₁ =>
    simp only [run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.toOuterMeasure_pure_apply, ite_eq_right (show (a, s) ∉ {x : β × σ | bad x.2} from hs)]
    exact zero_le
  | liftBind q cont k₁ _ ih =>
    classical
    obtain ⟨hle₂, hcont₂⟩ := IsCostBounded.liftBind_iff.mp hk₂
    simp only [run_interpret_bind, run_interpret_query,
      Probability.PMF.monad_bind_eq_bind, PMF.toOuterMeasure_bind_apply]
    set B : ℝ≥0∞ := budget s + ((k₁ + cost₁ q : ℕ) : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂
    set K : ℝ≥0∞ := (k₁ : ℝ≥0∞) * B + ((k₂ - cost₂ q : ℕ) : ℝ≥0∞) * ε
    have hterm (y : spec q × σ) : (handler q s) y *
        ((OracleComp.interpret handler (cont y.1)).run y.2).toOuterMeasure {x | bad x.2} ≤
        (handler q s) y * ({x : spec q × σ | bad x.2}.indicator 1 y + K) := by
      by_cases hmem : y ∈ (handler q s).support
      · refine mul_le_mul_of_nonneg_left ?_ zero_le
        by_cases hy : bad y.2
        · have : y ∈ {x : spec q × σ | bad x.2} := hy
          rw [Set.indicator_of_mem this, Pi.one_apply]
          exact (Probability.PMF.toOuterMeasure_le_one _ _).trans le_self_add
        · have : y ∉ {x : spec q × σ | bad x.2} := hy
          rw [Set.indicator_of_notMem this, zero_add]
          refine (ih y.1 (hcont₂ y.1) hy).trans ?_
          simp only [K, B]
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le) le_rfl
          calc budget y.2 + (k₁ : ℝ≥0∞) * δ₁ + ((k₂ - cost₂ q : ℕ) : ℝ≥0∞) * δ₂
              ≤ budget s + (cost₁ q : ℝ≥0∞) * δ₁ + (cost₂ q : ℝ≥0∞) * δ₂ +
                  (k₁ : ℝ≥0∞) * δ₁ + ((k₂ - cost₂ q : ℕ) : ℝ≥0∞) * δ₂ :=
                add_le_add (add_le_add (hgrow q s hs y hmem hy) le_rfl) le_rfl
            _ = budget s + ((k₁ + cost₁ q : ℕ) : ℝ≥0∞) * δ₁ +
                  (((k₂ - cost₂ q) + cost₂ q : ℕ) : ℝ≥0∞) * δ₂ := by
                simp only [Nat.cast_add]
                ring
            _ = budget s + ((k₁ + cost₁ q : ℕ) : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂ := by
                rw [Nat.sub_add_cancel hle₂]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hmem, zero_mul, zero_mul]
    calc ∑' y, (handler q s) y *
          ((OracleComp.interpret handler (cont y.1)).run y.2).toOuterMeasure {x | bad x.2}
        ≤ ∑' y, (handler q s) y * ({x : spec q × σ | bad x.2}.indicator 1 y + K) :=
          tsum_le_tsum hterm
      _ = (handler q s).toOuterMeasure {x | bad x.2} + K := by
          simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            PMF.toOuterMeasure_apply]
          congr 1
          refine tsum_congr fun y => ?_
          by_cases hy : y ∈ {x : spec q × σ | bad x.2}
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Pi.one_apply, mul_one]
          · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
      _ ≤ ((cost₁ q : ℝ≥0∞) * B + (cost₂ q : ℝ≥0∞) * ε) + K := by
          refine add_le_add ((hstep q s hs).trans ?_) le_rfl
          gcongr
          simp only [B]
          exact le_self_add.trans le_self_add
      _ = ((k₁ + cost₁ q : ℕ) : ℝ≥0∞) * B + (k₂ : ℝ≥0∞) * ε := by
          simp only [K]
          have hsub : (cost₂ q : ℝ≥0∞) * ε + ((k₂ - cost₂ q : ℕ) : ℝ≥0∞) * ε = (k₂ : ℝ≥0∞) * ε := by
            rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hle₂]
          have hadd : (cost₁ q : ℝ≥0∞) * B + (k₁ : ℝ≥0∞) * B = ((k₁ + cost₁ q : ℕ) : ℝ≥0∞) * B := by
            rw [← add_mul, add_comm (cost₁ q : ℝ≥0∞), ← Nat.cast_add]
          rw [← hsub, ← hadd]
          ring

end Cslib.OracleComp
