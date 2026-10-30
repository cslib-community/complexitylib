/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.QueryCount
public import Mathlib.Probability.ProbabilityMassFunction.Monad
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF

/-!
# Identical until bad

Two stateful oracle handlers are *identical until bad* when, from a good state, they give the same
probability to every answer that leads to a good state, and bad states are absorbing in both. Then
the two interpretations of any program give the same probability to every outcome with a good
final state (`IdenticalUntilBad.run_apply`). Consequently, an experiment that continues the run
accepts with the first handler at most as often as with the second, plus the probability of
reaching a bad state ([BonehShoup2023], Theorem 4.7, the difference lemma), with no bound on the
program's number of calls (`IdenticalUntilBad.bind_apply_le`). Both handlers reach a bad state with
the same probability (`IdenticalUntilBad.bad_eq`), so the two acceptance probabilities differ by
at most that probability (`IdenticalUntilBad.abs_sub_le`), and the bad event may be bounded in
whichever run is easier.

The probability of reaching a bad state is bounded by summing over the calls: if each call `q`
from a good state turns bad with probability at most `cost q · budget s`, and each call raises the
budget by at most `δ`, then a program making at most `n` calls, whose calls cost at most `k`,
reaches a bad state with probability at most `k · (budget s + n · δ)` (`toOuterMeasure_bad_le`).
This is the union bound for a growing collision set, such as a random oracle that is programmed,
at some calls only, at points that may already be defined.

## Main definitions

* `Cslib.OracleComp.IdenticalUntilBad`: two handlers that agree until a bad state.

## Main results

* `Cslib.OracleComp.IdenticalUntilBad.run_apply`: equal outcome probabilities at good states.
* `Cslib.OracleComp.IdenticalUntilBad.bind_apply_le`: the difference lemma.
* `Cslib.OracleComp.IdenticalUntilBad.bad_eq`, `Cslib.OracleComp.IdenticalUntilBad.abs_sub_le`:
  the bad event has the same probability under both handlers, and the two-sided difference
  lemma.
* `Cslib.OracleComp.toOuterMeasure_bad_le`: the accumulated probability of a bad state.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Theorem 4.7.
-/

@[expose] public section

namespace Cslib.OracleComp

open scoped ENNReal

variable {ι σ α : Type} {spec : ι → Type}

/-- Two stateful handlers agree until a bad state: from a good state they give equal probability
to every answer with a good next state, and bad states are absorbing for both. -/
structure IdenticalUntilBad (first second : (q : ι) → StateT σ PMF (spec q)) (bad : σ → Prop) :
    Prop where
  /-- From a good state, answers with good next states are equally likely. -/
  agree : ∀ q s, ¬bad s → ∀ a s', ¬bad s' → first q s (a, s') = second q s (a, s')
  /-- Bad states are absorbing for the first handler. -/
  absorb_first : ∀ q s, bad s → ∀ x ∈ (first q s).support, bad x.2
  /-- Bad states are absorbing for the second handler. -/
  absorb_second : ∀ q s, bad s → ∀ x ∈ (second q s).support, bad x.2

/-- A handler for which bad states are absorbing keeps every run from a bad state bad. -/
theorem bad_of_mem_support_run {handler : (q : ι) → StateT σ PMF (spec q)} {bad : σ → Prop}
    (habsorb : ∀ q s, bad s → ∀ x ∈ (handler q s).support, bad x.2)
    (program : OracleComp spec α) {s : σ} (hs : bad s) :
    ∀ x ∈ ((interpret handler program).run s).support, bad x.2 := by
  induction program using OracleComp.induction generalizing s with
  | pure a =>
    intro x hx
    simp only [run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff] at hx
    exact hx ▸ hs
  | query_bind q cont ih =>
    intro x hx
    simp only [run_interpret_bind, run_interpret_query,
      Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact ih y.1 (habsorb q s hs y hy) x hxy

namespace IdenticalUntilBad

variable {first second : (q : ι) → StateT σ PMF (spec q)} {bad : σ → Prop}

/-- Handlers that agree until a bad state give the same probability to every outcome whose final
state is good. -/
theorem run_apply (h : IdenticalUntilBad first second bad) (program : OracleComp spec α)
    (s : σ) (a : α) (s' : σ) (hs' : ¬bad s') :
    (interpret first program).run s (a, s') = (interpret second program).run s (a, s') := by
  induction program using OracleComp.induction generalizing s with
  | pure b => rfl
  | query_bind q cont ih =>
    simp only [run_interpret_bind, run_interpret_query,
      Probability.PMF.monad_bind_eq_bind, PMF.bind_apply]
    refine tsum_congr fun y => ?_
    by_cases hy : bad y.2
    · have hzero (handler : (q : ι) → StateT σ PMF (spec q))
          (habsorb : ∀ q s, bad s → ∀ x ∈ (handler q s).support, bad x.2) :
          (interpret handler (cont y.1)).run y.2 (a, s') = 0 :=
        (PMF.apply_eq_zero_iff _ _).mpr fun hmem =>
          hs' (bad_of_mem_support_run habsorb (cont y.1) hy _ hmem)
      rw [hzero first h.absorb_first, hzero second h.absorb_second, mul_zero, mul_zero]
    · by_cases hs : bad s
      · have hzero (handler : (q : ι) → StateT σ PMF (spec q))
            (habsorb : ∀ q s, bad s → ∀ x ∈ (handler q s).support, bad x.2) :
            handler q s y = 0 :=
          (PMF.apply_eq_zero_iff _ _).mpr fun hmem => hy (habsorb q s hs y hmem)
        rw [hzero first h.absorb_first, hzero second h.absorb_second, zero_mul, zero_mul]
      · rw [show y = (y.1, y.2) from rfl, h.agree q s hs y.1 y.2 hy, ih y.1 y.2]

/-- **The difference lemma** ([BonehShoup2023], Theorem 4.7): any experiment continuing the run
of a program accepts with the first handler at most as often as with the second, plus the
probability of reaching a bad state with the first. -/
theorem bind_apply_le (h : IdenticalUntilBad first second bad) (program : OracleComp spec α)
    (s : σ) {β : Type} (next : α × σ → PMF β) (b : β) :
    ((interpret first program).run s).bind next b ≤
      ((interpret second program).run s).bind next b +
        ((interpret first program).run s).toOuterMeasure {x | bad x.2} := by
  classical
  simp only [PMF.bind_apply, PMF.toOuterMeasure_apply]
  rw [← tsum_add]
  refine tsum_le_tsum fun x => ?_
  by_cases hx : bad x.2
  · have hbad : x ∈ {x : α × σ | bad x.2} := hx
    rw [Set.indicator_of_mem hbad]
    calc ((interpret first program).run s) x * next x b
        ≤ ((interpret first program).run s) x * 1 :=
          mul_le_mul_of_nonneg_left (PMF.coe_le_one _ _) zero_le
      _ ≤ _ := by rw [mul_one]; exact le_add_self
  · have hgood : x ∉ {x : α × σ | bad x.2} := hx
    rw [Set.indicator_of_notMem hgood, add_zero, show x = (x.1, x.2) from rfl,
      h.run_apply program s x.1 x.2 hx]

/-- Identical until bad is symmetric. -/
theorem symm (h : IdenticalUntilBad first second bad) : IdenticalUntilBad second first bad where
  agree q s hs a s' hs' := (h.agree q s hs a s' hs').symm
  absorb_first := h.absorb_second
  absorb_second := h.absorb_first

/-- A run gives the bad states and the good states total probability one. -/
private theorem toOuterMeasure_bad_add_good (p : PMF (α × σ)) :
    p.toOuterMeasure {x | bad x.2} + p.toOuterMeasure {x | ¬bad x.2} = 1 := by
  classical
  simp only [PMF.toOuterMeasure_apply]
  rw [← tsum_add, ← p.tsum_coe]
  refine tsum_congr fun x => ?_
  by_cases hx : bad x.2
  · rw [Set.indicator_of_mem (show x ∈ {x : α × σ | bad x.2} from hx),
      Set.indicator_of_notMem (show x ∉ {x : α × σ | ¬bad x.2} from fun h => h hx), add_zero]
  · rw [Set.indicator_of_notMem (show x ∉ {x : α × σ | bad x.2} from hx),
      Set.indicator_of_mem (show x ∈ {x : α × σ | ¬bad x.2} from hx), zero_add]

/-- Handlers that agree until a bad state reach a bad state with the same probability. -/
theorem bad_eq (h : IdenticalUntilBad first second bad) (program : OracleComp spec α) (s : σ) :
    ((interpret first program).run s).toOuterMeasure {x | bad x.2} =
      ((interpret second program).run s).toOuterMeasure {x | bad x.2} := by
  have hgood : ((interpret first program).run s).toOuterMeasure {x | ¬bad x.2} =
      ((interpret second program).run s).toOuterMeasure {x | ¬bad x.2} := by
    simp only [PMF.toOuterMeasure_apply]
    refine tsum_congr fun x => ?_
    by_cases hx : bad x.2
    · rw [Set.indicator_of_notMem (show x ∉ {x : α × σ | ¬bad x.2} from fun h => h hx),
        Set.indicator_of_notMem (show x ∉ {x : α × σ | ¬bad x.2} from fun h => h hx)]
    · rw [Set.indicator_of_mem (show x ∈ {x : α × σ | ¬bad x.2} from hx),
        Set.indicator_of_mem (show x ∈ {x : α × σ | ¬bad x.2} from hx),
        show x = (x.1, x.2) from rfl, h.run_apply program s x.1 x.2 hx]
  have hfirst := toOuterMeasure_bad_add_good (bad := bad) ((interpret first program).run s)
  have hsecond := toOuterMeasure_bad_add_good (bad := bad) ((interpret second program).run s)
  rw [hgood] at hfirst
  exact (ENNReal.add_left_inj (Probability.PMF.toOuterMeasure_ne_top _ _)).mp
    (hfirst.trans hsecond.symm)

/-- **The difference lemma, two-sided** ([BonehShoup2023], Theorem 4.7): any experiment continuing
the run of a program accepts with probabilities, under the two handlers, that differ by at most the
probability of reaching a bad state, which is the same under both. -/
theorem abs_sub_le (h : IdenticalUntilBad first second bad) (program : OracleComp spec α)
    (s : σ) {β : Type} (next : α × σ → PMF β) (b : β) :
    |(((interpret first program).run s).bind next b).toReal -
        (((interpret second program).run s).bind next b).toReal| ≤
      (((interpret first program).run s).toOuterMeasure {x | bad x.2}).toReal := by
  have hle := h.bind_apply_le program s next b
  have hle' := h.symm.bind_apply_le program s next b
  rw [← h.bad_eq] at hle'
  have hbad := Probability.PMF.toOuterMeasure_ne_top ((interpret first program).run s)
    {x | bad x.2}
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, hbad⟩) hle
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, hbad⟩) hle'
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) hbad] at h1 h2
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end IdenticalUntilBad

/-- **The accumulated probability of a bad state.** Let each call `q` from a good state turn bad
with probability at most `cost q · budget s`, and raise the budget by at most `δ`. Then a program
making at most `n` calls, whose calls cost at most `k`, reaches a bad state from a good state with
probability at most `k · (budget s + n · δ)`. -/
theorem toOuterMeasure_bad_le {handler : (q : ι) → StateT σ PMF (spec q)} {bad : σ → Prop}
    (cost : ι → ℕ) (budget : σ → ℝ≥0∞) (δ : ℝ≥0∞)
    (hstep : ∀ q s, ¬bad s → (handler q s).toOuterMeasure {x | bad x.2} ≤ cost q * budget s)
    (hgrow : ∀ q s, ¬bad s → ∀ x ∈ (handler q s).support, ¬bad x.2 →
      budget x.2 ≤ budget s + δ)
    {program : OracleComp spec α} {n k : ℕ} (hn : IsQueryBounded program n)
    (hk : IsCostBounded cost program k) {s : σ} (hs : ¬bad s) :
    ((interpret handler program).run s).toOuterMeasure {x | bad x.2} ≤
      k * (budget s + n * δ) := by
  induction hn generalizing s k with
  | pure a n =>
    simp only [run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.toOuterMeasure_pure_apply, ite_eq_right (show (a, s) ∉ {x : α × σ | bad x.2} from hs)]
    exact zero_le
  | liftBind q cont n _ ih =>
    classical
    obtain ⟨hle, hcont⟩ := IsCostBounded.liftBind_iff.mp hk
    simp only [run_interpret_bind, run_interpret_query,
      Probability.PMF.monad_bind_eq_bind, PMF.toOuterMeasure_bind_apply]
    set K : ℝ≥0∞ := (k - cost q : ℕ) * (budget s + δ + n * δ)
    have hterm (y : spec q × σ) : (handler q s) y *
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
          refine (ih y.1 (hcont y.1) hy).trans ?_
          simp only [K]
          gcongr
          exact hgrow q s hs y hmem hy
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hmem, zero_mul, zero_mul]
    calc ∑' y, (handler q s) y * ((interpret handler (cont y.1)).run y.2).toOuterMeasure
          {x | bad x.2}
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
      _ ≤ cost q * (budget s + (n + 1 : ℕ) * δ) +
            (k - cost q : ℕ) * (budget s + (n + 1 : ℕ) * δ) := by
          refine add_le_add ((hstep q s hs).trans ?_) (le_of_eq ?_)
          · gcongr
            exact le_self_add
          · simp only [K, Nat.cast_add, Nat.cast_one]
            ring
      _ = k * (budget s + (n + 1 : ℕ) * δ) := by
          rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hle]

end Cslib.OracleComp
