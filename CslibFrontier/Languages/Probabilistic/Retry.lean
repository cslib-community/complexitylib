/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.QueryCount.Expected
public import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Probability.PMF.EventBind

/-!
# Bounded retries and independent coordinates

`OracleComp.retry good program fuel` runs `program` at most `fuel` times and returns the first
result satisfying `good`, or `none` when every run fails. It is the bounded form of a Las Vegas
loop: an oracle program is a finite tree of calls, so "repeat until success" is represented by its
truncation after `fuel` runs, and the truncation is visible as the `none` outcome. Checking `good`
is local computation and makes no call.

When one run fails with probability `q` (under answer distributions `h`, as in
`OracleComp.evalWith`):

* the loop fails with probability exactly `q ^ fuel` (`OracleComp.evalWith_retry_none`);
* it returns a good result `a` with probability `P(a) (1 + q + ⋯ + q ^ (fuel - 1))`, where `P(a)`
  is the probability that one run returns `a` (`OracleComp.evalWith_retry_some`);
* its expected cost is `c (1 + q + ⋯ + q ^ (fuel - 1))` for a run of expected cost `c`
  (`OracleComp.expectedCost_retry`), so at most `2 c` for every fuel when `q ≤ 1 / 2`
  (`OracleComp.expectedCost_retry_le_two_mul`): the expected number of runs is at most `2`.

`OracleComp.pi` runs a family of programs one after the other and collects their results. Over an
arbitrary interface its expected cost is the sum of the expected costs
(`OracleComp.expectedCost_pi`), and the probability that some coordinate is bad is at most the sum
of the probabilities (`OracleComp.toOuterMeasure_evalWith_pi_exists_le`, a union bound). These
complement the support and law statements of `CslibFrontier.Languages.Probabilistic.Vector`.

## Main definitions

* `Cslib.OracleComp.retry`: at most `fuel` runs, returning the first good result.

## Main results

* `Cslib.OracleComp.mem_supportWith_retry`: a returned result is good and a result of one run.
* `Cslib.OracleComp.evalWith_retry_none`: the loop fails with probability `q ^ fuel`.
* `Cslib.OracleComp.evalWith_retry_some`: the loop returns a good result `a` with probability
  `P(a) (1 + q + ⋯ + q ^ (fuel - 1))`, where `P(a)` is the probability that one run returns `a`.
* `Cslib.OracleComp.expectedCost_retry`, `Cslib.OracleComp.expectedCost_retry_le_two_mul`: the
  expected cost of the loop is a geometric sum, at most twice a run when `q ≤ 1 / 2`.
* `Cslib.OracleComp.expectedCost_pi`, `Cslib.OracleComp.toOuterMeasure_evalWith_pi_exists_le`:
  expected cost and union bound for `OracleComp.pi`.
-/

public section

open scoped ENNReal

namespace Cslib.OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α : Type v}

/-- Run `program` at most `fuel` times and return the first result satisfying `good`, or `none`
when all `fuel` runs fail. Checking `good` makes no call. -/
@[expose] def retry (good : α → Prop) [DecidablePred good] (program : OracleComp spec α) :
    ℕ → OracleComp spec (Option α)
  | 0 => pure none
  | fuel + 1 => do
    let a ← program
    if good a then pure (some a) else retry good program fuel

section Retry

variable (good : α → Prop) [DecidablePred good] (program : OracleComp spec α)

@[simp] theorem retry_zero : retry good program 0 = pure none := rfl

theorem retry_succ (fuel : ℕ) :
    retry good program (fuel + 1) =
      program >>= fun a => if good a then pure (some a) else retry good program fuel := rfl

variable {good program} in
/-- A result returned by the loop satisfies `good` and is a possible result of one run. -/
theorem mem_supportWith_retry {possible : (q : ι) → Set (spec q)} {fuel : ℕ} {a : α}
    (ha : some a ∈ supportWith possible (retry good program fuel)) :
    good a ∧ a ∈ supportWith possible program := by
  induction fuel with
  | zero => simp at ha
  | succ fuel ih =>
    rw [retry_succ, mem_supportWith_bind_iff] at ha
    obtain ⟨b, hb, hab⟩ := ha
    by_cases hgood : good b
    · simp only [hgood, ↓reduceIte, supportWith_pure, Set.mem_singleton_iff,
        Option.some.injEq] at hab
      subst hab
      exact ⟨hgood, hb⟩
    · simp only [hgood, ↓reduceIte] at hab
      exact ih hab

variable (h : (q : ι) → PMF (spec q))

/-- The loop fails exactly when all its runs fail, with probability `q ^ fuel`, where `q` is the
probability that one run fails. -/
theorem evalWith_retry_none (fuel : ℕ) :
    evalWith h (retry good program fuel) none =
      (evalWith h program).toOuterMeasure {a | ¬ good a} ^ fuel := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
    rw [retry_succ, evalWith_bind, PMF.bind_apply, pow_succ', ← ih, PMF.toOuterMeasure_apply,
      ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    by_cases hgood : good a
    · simp [hgood]
    · simp [hgood]

/-- A run failing with probability at most `q` makes the loop fail with probability at most
`q ^ fuel`. -/
theorem evalWith_retry_none_le {q : ℝ≥0∞}
    (hfail : (evalWith h program).toOuterMeasure {a | ¬ good a} ≤ q) (fuel : ℕ) :
    evalWith h (retry good program fuel) none ≤ q ^ fuel := by
  rw [evalWith_retry_none]
  gcongr

/-- The loop returns `a` with probability `P(a) (1 + q + ⋯ + q ^ (fuel - 1))` when `a` is good,
and never otherwise, where `P(a)` is the probability that one run returns `a` and `q` is the
probability that one run fails. -/
theorem evalWith_retry_some (fuel : ℕ) (a : α) :
    evalWith h (retry good program fuel) (some a) =
      (if good a then evalWith h program a else 0) *
        ∑ i ∈ Finset.range fuel, (evalWith h program).toOuterMeasure {a | ¬ good a} ^ i := by
  classical
  induction fuel with
  | zero => simp
  | succ fuel ih =>
    have hterm : ∀ b, evalWith h program b *
        evalWith h (if good b then pure (some b) else retry good program fuel) (some a) =
        (if b = a then (if good a then evalWith h program a else 0) else 0) +
          {x | ¬ good x}.indicator (evalWith h program) b *
            evalWith h (retry good program fuel) (some a) := by
      intro b
      by_cases hb : good b
      · by_cases hba : b = a
        · subst hba
          simp [hb]
        · simp [hb, hba, Ne.symm hba]
      · by_cases hba : b = a
        · subst hba
          simp [hb]
        · simp [hb, hba]
    rw [retry_succ, evalWith_bind, PMF.bind_apply]
    refine (tsum_congr hterm).trans ?_
    rw [tsum_add, tsum_ite_eq, ENNReal.tsum_mul_right, ← PMF.toOuterMeasure_apply, ih,
      Finset.sum_range_succ', pow_zero]
    simp only [pow_succ', ← Finset.mul_sum]
    ring

variable (cost : ι → ℝ≥0∞)

/-- One more allowed run costs a run, plus the remaining loop when the run fails. -/
theorem expectedCost_retry_succ (fuel : ℕ) :
    expectedCost h cost (retry good program (fuel + 1)) =
      expectedCost h cost program +
        (evalWith h program).toOuterMeasure {a | ¬ good a} *
          expectedCost h cost (retry good program fuel) := by
  rw [retry_succ, expectedCost_bind, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
  congr 1
  refine tsum_congr fun a => ?_
  by_cases hgood : good a
  · simp [hgood]
  · simp [hgood]

/-- The expected cost of the loop is a geometric sum: a run of expected cost `c` failing with
probability `q` gives `c (1 + q + ⋯ + q ^ (fuel - 1))`. -/
theorem expectedCost_retry (fuel : ℕ) :
    expectedCost h cost (retry good program fuel) =
      expectedCost h cost program *
        ∑ i ∈ Finset.range fuel, (evalWith h program).toOuterMeasure {a | ¬ good a} ^ i := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
    rw [expectedCost_retry_succ, ih, Finset.sum_range_succ', pow_zero]
    simp only [pow_succ', ← Finset.mul_sum]
    ring

/-- **Expected cost of a retry loop.** If one run fails with probability at most `1 / 2`, the loop
costs at most twice a run in expectation, whatever the fuel. -/
theorem expectedCost_retry_le_two_mul
    (hfail : (evalWith h program).toOuterMeasure {a | ¬ good a} ≤ 2⁻¹) (fuel : ℕ) :
    expectedCost h cost (retry good program fuel) ≤ 2 * expectedCost h cost program := by
  rw [expectedCost_retry, mul_comm 2]
  gcongr
  calc ∑ i ∈ Finset.range fuel, (evalWith h program).toOuterMeasure {a | ¬ good a} ^ i
      ≤ ∑ i ∈ Finset.range fuel, (2⁻¹ : ℝ≥0∞) ^ i := by gcongr
    _ ≤ ∑' i, (2⁻¹ : ℝ≥0∞) ^ i := sum_le_tsum _
    _ = 2 := by rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]

end Retry

section Partial

variable {β : Type v} (h : (q : ι) → PMF (spec q))

/-- **Union bound for sequenced partial programs.** A partial program followed, on success, by a
partial continuation fails with probability at most the failure probability of the first program
plus a bound on the failure probability of every continuation. -/
theorem evalWith_bind_elim_none_le (program : OracleComp spec (Option α))
    (next : α → OracleComp spec (Option β)) {c : ℝ≥0∞}
    (hnext : ∀ a, evalWith h (next a) none ≤ c) :
    evalWith h (program >>= fun o => o.elim (pure none) next) none ≤
      evalWith h program none + c := by
  have hcompl : ({o | o.isSome} : Set (Option α))ᶜ = {none} := by
    ext o
    cases o <;> simp
  have key := Probability.PMF.toOuterMeasure_bind_failure_le (evalWith h program)
    (fun o => evalWith h (o.elim (pure none) next)) {o | o.isSome} {none} c fun o _ ho => by
      obtain ⟨a, rfl⟩ := Option.isSome_iff_exists.mp ho
      rw [PMF.toOuterMeasure_apply_singleton]
      exact hnext a
  rw [hcompl, PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton] at key
  rw [evalWith_bind]
  exact key

/-- The expected cost of a partial program followed, on success, by a continuation is at most the
expected cost of the first program plus a bound on the expected cost of every continuation. -/
theorem expectedCost_bind_elim_le (cost : ι → ℝ≥0∞) (program : OracleComp spec (Option α))
    (next : α → OracleComp spec (Option β)) {c : ℝ≥0∞}
    (hnext : ∀ a, expectedCost h cost (next a) ≤ c) :
    expectedCost h cost (program >>= fun o => o.elim (pure none) next) ≤
      expectedCost h cost program + c := by
  rw [expectedCost_bind]
  gcongr
  calc ∑' o, evalWith h program o * expectedCost h cost (o.elim (pure none) next)
      ≤ ∑' o, evalWith h program o * c := by
        refine tsum_le_tsum fun o => ?_
        gcongr
        cases o with
        | none => simp
        | some a => exact hnext a
    _ = c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Partial

section Pi

variable {m : ℕ} {β : Fin m → Type v}

variable (h : (q : ι) → PMF (spec q))

/-- The expected cost of running a family of programs is the sum of their expected costs. -/
theorem expectedCost_pi (cost : ι → ℝ≥0∞) (programs : (i : Fin m) → OracleComp spec (β i)) :
    expectedCost h cost (pi programs) = ∑ i, expectedCost h cost (programs i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pi_succ, expectedCost_bind, Fin.sum_univ_succ]
    congr 1
    simp only [expectedCost_map, ih, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **Union bound** for a family of programs: the probability that some coordinate is bad is at
most the sum over the coordinates of the probability that it is bad. -/
theorem toOuterMeasure_evalWith_pi_exists_le (programs : (i : Fin m) → OracleComp spec (β i))
    (bad : (i : Fin m) → β i → Prop) :
    (evalWith h (pi programs)).toOuterMeasure {r | ∃ i, bad i (r i)} ≤
      ∑ i, (evalWith h (programs i)).toOuterMeasure {a | bad i a} := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pi_succ, evalWith_bind, Fin.sum_univ_succ]
    refine Probability.PMF.toOuterMeasure_bind_le_add _ _ {a | bad 0 a} _ _ fun a _ ha => ?_
    rw [evalWith_map, PMF.toOuterMeasure_map_apply]
    have hsub : (Fin.cons a : ((j : Fin m) → β j.succ) → (i : Fin (m + 1)) → β i) ⁻¹'
          {r | ∃ i, bad i (r i)} ⊆ {r | ∃ j, bad j.succ (r j)} := by
      rintro r ⟨i, hi⟩
      cases i using Fin.cases with
      | zero => exact (ha (by simpa using hi)).elim
      | succ j => exact ⟨j, by simpa using hi⟩
    exact (MeasureTheory.measure_mono hsub).trans (ih _ _)

end Pi

end Cslib.OracleComp
