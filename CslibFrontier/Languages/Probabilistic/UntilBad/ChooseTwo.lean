/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.UntilBad
public import Mathlib.Data.Nat.Choose.Basic
import CslibFrontier.Probability.PMF.Event

/-!
# Triangular union bounds for linearly growing bad-event sets

When each oracle call from a good state `s` triggers a bad state with probability proportional to an
integer state size `size s` (`size s * δ`) and grows `size` by at most `1` per call, summing over an
`n`-query adaptive execution yields the triangular birthday sum
`size s + (size s + 1) + ⋯ + (size s + n - 1) = n * size s + n.choose 2` rather than the rectangular
bound `n * (size s + n)` of `OracleComp.toOuterMeasure_bad_le`.

More generally (`toOuterMeasure_bad_choose_two_cost_le`), when calls carry two separate cost budgets
`cost₁` (charging bad-event probability `(cost₁ q * size s) * δ` and growing `size`) and `cost₂`
(growing `size` without risking a bad transition, such as passive random-oracle queries alongside
programming steps), an adaptive program with budgets `k₁` and `k₂` reaches a bad state with
probability at most `(k₁ * size s + k₁ * k₂ + k₁.choose 2) * δ`.

## Main results

* `Cslib.OracleComp.toOuterMeasure_bad_choose_two_cost_le`: two-cost triangular union bound
  `(k₁ * size s + k₁ * k₂ + k₁.choose 2) * δ`.
* `Cslib.OracleComp.toOuterMeasure_bad_choose_two_of_isCostBounded`: single-cost triangular union
  bound `(n * size s + n.choose 2) * δ`.
* `Cslib.OracleComp.toOuterMeasure_bad_choose_two_le`: unit-cost `IsQueryBounded` specialization
  `(n * size s + n.choose 2) * δ`.
-/

public section

namespace Cslib.OracleComp

open scoped ENNReal

/-- **Two-cost triangular accumulated probability of a bad state.** Suppose each call `q` from a
good state `s` (`¬bad s`) turns bad with probability at most `(cost₁ q * size s) * δ`, and every
good supported transition increases `size` by at most `cost₁ q + cost₂ q`. Then any adaptive program
satisfying `IsCostBounded cost₁ program k₁` and `IsCostBounded cost₂ program k₂` reaches a bad state
from `s` with probability at most `(k₁ * size s + k₁ * k₂ + k₁.choose 2) * δ`. -/
theorem toOuterMeasure_bad_choose_two_cost_le {ι σ α : Type} {spec : ι → Type}
    {handler : (q : ι) → StateT σ PMF (spec q)} {bad : σ → Prop}
    (cost₁ cost₂ : ι → ℕ) (size : σ → ℕ) (δ : ℝ≥0∞)
    (hstep : ∀ q s, ¬bad s →
      (handler q s).toOuterMeasure {x | bad x.2} ≤ (cost₁ q * size s : ℕ) * δ)
    (hgrow : ∀ q s, ¬bad s → ∀ x ∈ (handler q s).support, ¬bad x.2 →
      size x.2 ≤ size s + cost₁ q + cost₂ q)
    {program : OracleComp spec α} {k₁ k₂ : ℕ}
    (hk₁ : IsCostBounded cost₁ program k₁) (hk₂ : IsCostBounded cost₂ program k₂)
    {s : σ} (hs : ¬bad s) :
    ((interpret handler program).run s).toOuterMeasure {x | bad x.2} ≤
      (k₁ * size s + k₁ * k₂ + k₁.choose 2 : ℕ) * δ := by
  induction hk₁ generalizing s k₂ with
  | pure a k₁ =>
    simp only [run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.toOuterMeasure_pure_apply, ite_eq_right (show (a, s) ∉ {x : α × σ | bad x.2} from hs)]
    exact zero_le
  | liftBind q cont a _ ih =>
    classical
    obtain ⟨hc₂, hcont₂⟩ := IsCostBounded.liftBind_iff.mp hk₂
    simp only [run_interpret_bind, run_interpret_query,
      Probability.PMF.monad_bind_eq_bind, PMF.toOuterMeasure_bind_apply]
    set M : ℕ := a * (size s + cost₁ q + cost₂ q) + a * (k₂ - cost₂ q) + a.choose 2
    set K : ℝ≥0∞ := (M : ℝ≥0∞) * δ
    have hterm (y : spec q × σ) :
        (handler q s) y *
          ((interpret handler (cont y.1)).run y.2).toOuterMeasure {x | bad x.2} ≤
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
          simp only [K, M]
          gcongr
          exact hgrow q s hs y hmem hy
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hmem, zero_mul, zero_mul]
    have hchoose : a.choose 2 + a * cost₁ q ≤ (a + cost₁ q).choose 2 := by
      suffices ∀ c, a.choose 2 + a * c ≤ (a + c).choose 2 from this (cost₁ q)
      intro c
      induction c with
      | zero => simp
      | succ d ihd =>
        rw [show a + (d + 1) = (a + d) + 1 by omega, Nat.choose_succ_succ' (a + d) 1,
          Nat.choose_one_right, show (1 + 1 : ℕ) = 2 from rfl, Nat.mul_succ]
        omega
    have hnat : cost₁ q * size s + M ≤
        (a + cost₁ q) * size s + (a + cost₁ q) * k₂ + (a + cost₁ q).choose 2 := by
      have hk₂_split : a * cost₂ q + a * (k₂ - cost₂ q) = a * k₂ := by
        rw [← Nat.mul_add, Nat.add_sub_of_le hc₂]
      have hk₂_mono : a * k₂ ≤ (a + cost₁ q) * k₂ := Nat.mul_le_mul_right k₂ (Nat.le_add_right _ _)
      have hexp : cost₁ q * size s + M =
          (a + cost₁ q) * size s + (a * cost₂ q + a * (k₂ - cost₂ q)) +
            (a.choose 2 + a * cost₁ q) := by
        dsimp only [M]
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
        omega
      omega
    calc ∑' y, (handler q s) y *
          ((interpret handler (cont y.1)).run y.2).toOuterMeasure {x | bad x.2}
        ≤ ∑' y, (handler q s) y * ({x : spec q × σ | bad x.2}.indicator 1 y + K) :=
          tsum_le_tsum hterm
      _ = (handler q s).toOuterMeasure {x | bad x.2} + K := by
          simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator]
      _ ≤ (cost₁ q * size s : ℕ) * δ + K := add_le_add (hstep q s hs) le_rfl
      _ = ((cost₁ q * size s + M : ℕ) : ℝ≥0∞) * δ := by
          simp only [K, ← add_mul, Nat.cast_add]
      _ ≤ ((a + cost₁ q) * size s + (a + cost₁ q) * k₂ + (a + cost₁ q).choose 2 : ℕ) * δ := by
          gcongr

/-- **Cost-weighted triangular accumulated probability of a bad state.** Suppose each call `q` from
a good state `s` turns bad with probability at most `(cost q * size s) * δ` and increases `size` by
at most `cost q`. Then a program with `IsCostBounded cost program n` reaches a bad state from `s`
with probability at most `(n * size s + n.choose 2) * δ`. -/
theorem toOuterMeasure_bad_choose_two_of_isCostBounded {ι σ α : Type} {spec : ι → Type}
    {handler : (q : ι) → StateT σ PMF (spec q)} {bad : σ → Prop}
    (cost : ι → ℕ) (size : σ → ℕ) (δ : ℝ≥0∞)
    (hstep : ∀ q s, ¬bad s →
      (handler q s).toOuterMeasure {x | bad x.2} ≤ (cost q * size s : ℕ) * δ)
    (hgrow : ∀ q s, ¬bad s → ∀ x ∈ (handler q s).support, ¬bad x.2 →
      size x.2 ≤ size s + cost q)
    {program : OracleComp spec α} {n : ℕ} (hn : IsCostBounded cost program n)
    {s : σ} (hs : ¬bad s) :
    ((interpret handler program).run s).toOuterMeasure {x | bad x.2} ≤
      (n * size s + n.choose 2 : ℕ) * δ := by
  simpa only [mul_zero, add_zero] using
    toOuterMeasure_bad_choose_two_cost_le cost (fun _ => 0) size δ hstep
      (fun q s hs x hmem hx => by simpa only [add_zero] using hgrow q s hs x hmem hx)
      hn (IsCostBounded.of_forall_cost_eq_zero (fun _ => rfl) program) hs

/-- **Triangular accumulated probability of a bad state.** If each oracle call from a good state `s`
turns bad with probability at most `size s * δ` and increases `size` by at most `1`, then an
adaptive program making at most `n` queries reaches a bad state from `s` with probability at most
`(n * size s + n.choose 2) * δ`. -/
theorem toOuterMeasure_bad_choose_two_le {ι σ α : Type} {spec : ι → Type}
    {handler : (q : ι) → StateT σ PMF (spec q)} {bad : σ → Prop}
    (size : σ → ℕ) (δ : ℝ≥0∞)
    (hstep : ∀ q s, ¬bad s → (handler q s).toOuterMeasure {x | bad x.2} ≤ size s * δ)
    (hgrow : ∀ q s, ¬bad s → ∀ x ∈ (handler q s).support, ¬bad x.2 → size x.2 ≤ size s + 1)
    {program : OracleComp spec α} {n : ℕ} (hn : IsQueryBounded program n)
    {s : σ} (hs : ¬bad s) :
    ((interpret handler program).run s).toOuterMeasure {x | bad x.2} ≤
      (n * size s + n.choose 2 : ℕ) * δ :=
  toOuterMeasure_bad_choose_two_of_isCostBounded (fun _ => 1) size δ
    (fun q s hs => by simpa only [one_mul, Nat.cast_id] using hstep q s hs)
    hgrow hn hs

end Cslib.OracleComp
