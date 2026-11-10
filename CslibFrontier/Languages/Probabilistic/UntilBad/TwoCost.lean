/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.UntilBad
import CslibFrontier.Probability.PMF.Event

/-!
# Accumulating bad-event probability with two query costs

A stateful oracle may have two independently bounded kinds of calls, where each channel can charge
against its own growing bad-event budget (`toOuterMeasure_bad_le_two_budgets`), or where one
channel charges against a growing budget and the other charges a fixed error
(`toOuterMeasure_bad_le_two`). This extends the single-cost bound in
`CslibFrontier/Languages/Probabilistic/UntilBad.lean` without introducing a cryptographic protocol
dependency.

## Main results

* `Cslib.OracleComp.toOuterMeasure_bad_le_two_budgets`: bound the probability of a bad final state
  by `k₁ * (budget₁ s + k₁ * δ₁₁ + k₂ * δ₁₂) + k₂ * (budget₂ s + k₁ * δ₂₁ + k₂ * δ₂₂)` for two
  query-cost budgets `k₁` and `k₂` with growing per-channel budgets `budget₁` and `budget₂`.
* `Cslib.OracleComp.toOuterMeasure_bad_le_two`: specialization when the second channel charges a
  constant per-call error `ε`.
-/

@[expose] public section

namespace Cslib.OracleComp

open scoped ENNReal

/-- **Two-channel accumulated bad-state probability with two growing budgets**: let each call `q`
from a good state `¬bad s` turn bad with probability at most
`cost₁ q * budget₁ s + cost₂ q * budget₂ s`, raising `budget₁` by at most
`cost₁ q * δ₁₁ + cost₂ q * δ₁₂` and `budget₂` by at most `cost₁ q * δ₂₁ + cost₂ q * δ₂₂`. Then a
program with `IsCostBounded cost₁ program k₁` and `IsCostBounded cost₂ program k₂`, started in a
good state `s`, ends in a bad state with probability at most
`k₁ * (budget₁ s + k₁ * δ₁₁ + k₂ * δ₁₂) + k₂ * (budget₂ s + k₁ * δ₂₁ + k₂ * δ₂₂)`. -/
theorem toOuterMeasure_bad_le_two_budgets {ι σ β : Type} {spec : ι → Type}
    {handler : (q : ι) → StateT σ PMF (spec q)} {bad : σ → Prop}
    (cost₁ cost₂ : ι → ℕ) (budget₁ budget₂ : σ → ℝ≥0∞) (δ₁₁ δ₁₂ δ₂₁ δ₂₂ : ℝ≥0∞)
    (hstep : ∀ q s, ¬bad s →
      (handler q s).toOuterMeasure {x | bad x.2} ≤ cost₁ q * budget₁ s + cost₂ q * budget₂ s)
    (hgrow₁ : ∀ q s, ¬bad s → ∀ x ∈ (handler q s).support, ¬bad x.2 →
      budget₁ x.2 ≤ budget₁ s + cost₁ q * δ₁₁ + cost₂ q * δ₁₂)
    (hgrow₂ : ∀ q s, ¬bad s → ∀ x ∈ (handler q s).support, ¬bad x.2 →
      budget₂ x.2 ≤ budget₂ s + cost₁ q * δ₂₁ + cost₂ q * δ₂₂)
    {program : OracleComp spec β} {k₁ k₂ : ℕ}
    (hk₁ : IsCostBounded cost₁ program k₁) (hk₂ : IsCostBounded cost₂ program k₂)
    {s : σ} (hs : ¬bad s) :
    ((OracleComp.interpret handler program).run s).toOuterMeasure {x | bad x.2} ≤
      (k₁ : ℝ≥0∞) * (budget₁ s + (k₁ : ℝ≥0∞) * δ₁₁ + (k₂ : ℝ≥0∞) * δ₁₂) +
        (k₂ : ℝ≥0∞) * (budget₂ s + (k₁ : ℝ≥0∞) * δ₂₁ + (k₂ : ℝ≥0∞) * δ₂₂) := by
  induction hk₁ generalizing s k₂ with
  | pure a k₁ =>
    simp only [run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.toOuterMeasure_pure_apply, ite_eq_right (show (a, s) ∉ {x : β × σ | bad x.2} from hs)]
    exact zero_le
  | liftBind q cont k₁ _ ih =>
    classical
    obtain ⟨hle₂, hcont₂⟩ := IsCostBounded.liftBind_iff.mp hk₂
    -- One budget step: the growth bound for `q` and the remaining `(k₁, k₂ - cost₂ q)` calls add
    -- up to the budget for `(k₁ + cost₁ q, k₂)` calls. Shared by both channels below.
    have hbudget (b : σ → ℝ≥0∞) (δ δ' : ℝ≥0∞) (t : σ)
        (hb : b t ≤ b s + (cost₁ q : ℝ≥0∞) * δ + (cost₂ q : ℝ≥0∞) * δ') :
        b t + (k₁ : ℝ≥0∞) * δ + ((k₂ - cost₂ q : ℕ) : ℝ≥0∞) * δ' ≤
          b s + ((k₁ + cost₁ q : ℕ) : ℝ≥0∞) * δ + (k₂ : ℝ≥0∞) * δ' :=
      calc b t + (k₁ : ℝ≥0∞) * δ + ((k₂ - cost₂ q : ℕ) : ℝ≥0∞) * δ'
          ≤ b s + (cost₁ q : ℝ≥0∞) * δ + (cost₂ q : ℝ≥0∞) * δ' +
              (k₁ : ℝ≥0∞) * δ + ((k₂ - cost₂ q : ℕ) : ℝ≥0∞) * δ' :=
            add_le_add (add_le_add hb le_rfl) le_rfl
        _ = b s + ((k₁ + cost₁ q : ℕ) : ℝ≥0∞) * δ +
              (((k₂ - cost₂ q) + cost₂ q : ℕ) : ℝ≥0∞) * δ' := by
            simp only [Nat.cast_add]
            ring
        _ = b s + ((k₁ + cost₁ q : ℕ) : ℝ≥0∞) * δ + (k₂ : ℝ≥0∞) * δ' := by
            rw [Nat.sub_add_cancel hle₂]
    simp only [run_interpret_bind, run_interpret_query,
      Probability.PMF.monad_bind_eq_bind, PMF.toOuterMeasure_bind_apply]
    set B₁ : ℝ≥0∞ := budget₁ s + ((k₁ + cost₁ q : ℕ) : ℝ≥0∞) * δ₁₁ + (k₂ : ℝ≥0∞) * δ₁₂
    set B₂ : ℝ≥0∞ := budget₂ s + ((k₁ + cost₁ q : ℕ) : ℝ≥0∞) * δ₂₁ + (k₂ : ℝ≥0∞) * δ₂₂
    set K : ℝ≥0∞ := (k₁ : ℝ≥0∞) * B₁ + ((k₂ - cost₂ q : ℕ) : ℝ≥0∞) * B₂
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
          simp only [K, B₁, B₂]
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le)
            (mul_le_mul_of_nonneg_left ?_ zero_le)
          · exact hbudget budget₁ δ₁₁ δ₁₂ y.2 (hgrow₁ q s hs y hmem hy)
          · exact hbudget budget₂ δ₂₁ δ₂₂ y.2 (hgrow₂ q s hs y hmem hy)
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hmem, zero_mul, zero_mul]
    calc ∑' y, (handler q s) y *
          ((OracleComp.interpret handler (cont y.1)).run y.2).toOuterMeasure {x | bad x.2}
        ≤ ∑' y, (handler q s) y * ({x : spec q × σ | bad x.2}.indicator 1 y + K) :=
          tsum_le_tsum hterm
      _ = (handler q s).toOuterMeasure {x | bad x.2} + K := by
          simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator]
      _ ≤ ((cost₁ q : ℝ≥0∞) * B₁ + (cost₂ q : ℝ≥0∞) * B₂) + K := by
          refine add_le_add ((hstep q s hs).trans ?_) le_rfl
          refine add_le_add ?_ ?_
          · gcongr
            simp only [B₁]
            exact le_self_add.trans le_self_add
          · gcongr
            simp only [B₂]
            exact le_self_add.trans le_self_add
      _ = ((k₁ + cost₁ q : ℕ) : ℝ≥0∞) * B₁ + (k₂ : ℝ≥0∞) * B₂ := by
          simp only [K]
          have hsub :
              (cost₂ q : ℝ≥0∞) * B₂ + ((k₂ - cost₂ q : ℕ) : ℝ≥0∞) * B₂ = (k₂ : ℝ≥0∞) * B₂ := by
            rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hle₂]
          have hadd :
              (cost₁ q : ℝ≥0∞) * B₁ + (k₁ : ℝ≥0∞) * B₁ = ((k₁ + cost₁ q : ℕ) : ℝ≥0∞) * B₁ := by
            rw [← add_mul, add_comm (cost₁ q : ℝ≥0∞), ← Nat.cast_add]
          rw [show (cost₁ q : ℝ≥0∞) * B₁ + (cost₂ q : ℝ≥0∞) * B₂ +
                ((k₁ : ℝ≥0∞) * B₁ + ((k₂ - cost₂ q : ℕ) : ℝ≥0∞) * B₂) =
              ((cost₁ q : ℝ≥0∞) * B₁ + (k₁ : ℝ≥0∞) * B₁) +
                ((cost₂ q : ℝ≥0∞) * B₂ + ((k₂ - cost₂ q : ℕ) : ℝ≥0∞) * B₂) by ring,
            hadd, hsub]

/-- **Two-channel accumulated bad-state probability**: let each call `q` from a good state `¬bad s`
turn bad with probability at most `cost₁ q * budget s + cost₂ q * ε`, and raise `budget` by at most
`cost₁ q * δ₁ + cost₂ q * δ₂`. Then a program with `IsCostBounded cost₁ program k₁` and
`IsCostBounded cost₂ program k₂`, started in a good state `s`, ends in a bad state with probability
at most
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
  simpa only [mul_zero, add_zero] using
    toOuterMeasure_bad_le_two_budgets cost₁ cost₂ budget (fun _ => ε) δ₁ δ₂ 0 0 hstep hgrow
      (fun _ _ _ _ _ _ => by simp) hk₁ hk₂ hs

end Cslib.OracleComp
