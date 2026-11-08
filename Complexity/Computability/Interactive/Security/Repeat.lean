/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Interactive.Security
public import Complexity.Languages.Probabilistic.Repeat

/-!
# Statistical error under independent repetition

Independent repetitions add their all-events statistical-distance bounds. The sample space
may be infinite, including encoded cryptographic transcripts. Deterministic postprocessing
then uses `CloseTo.map`.

## Main results

* `Cslib.Probability.CloseTo.iid`: independent product distributions.
* `Cslib.Probability.CloseTo.iid_replicate`: ideal independent draws versus repeated programs.
* `Cslib.Probability.CloseTo.eval_replicate`: repeated probabilistic programs.
-/

public section

namespace Cslib.Probability.CloseTo

open scoped ENNReal

/-- `k` independent draws from `ε`-close distributions are `(k * ε)`-close, without finiteness
assumptions on the sample space. -/
theorem iid {α : Type} {μ ν : PMF α} {ε : ℝ≥0∞} (h : CloseTo μ ν ε) (k : ℕ) :
    CloseTo (PMF.iid μ k) (PMF.iid ν k) (k * ε) := by
  induction k with
  | zero =>
    simp only [PMF.iid, Nat.cast_zero, zero_mul, CloseTo.refl]
  | succ k ih =>
    rw [PMF.iid, PMF.iid, PMF.monad_bind_eq_bind, PMF.monad_bind_eq_bind,
      Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm (k * ε) ε]
    refine CloseTo.bind h fun a _ => ?_
    exact ih.map (@Fin.cons k (fun _ => α) a)

/-- `k` independent draws from `μ` collected as a list are `(k * ε)`-close to
`OracleComp.replicate k prog` whenever `μ` is `ε`-close to `ProbComp.eval prog`. -/
theorem iid_replicate {α : Type} {μ : PMF α} {prog : ProbComp α} {ε : ℝ≥0∞}
    (h : CloseTo μ (ProbComp.eval prog) ε) (k : ℕ) :
    CloseTo ((PMF.iid μ k).map List.ofFn) (ProbComp.eval (OracleComp.replicate k prog))
      (k * ε) := by
  rw [ProbComp.eval_replicate_iid]
  exact (h.iid k).map List.ofFn

/-- `k` independent runs of two `ProbComp` programs whose single-run laws are `ε`-close are
`(k * ε)`-close. -/
theorem eval_replicate {α : Type} {prog₁ prog₂ : ProbComp α} {ε : ℝ≥0∞}
    (h : CloseTo (ProbComp.eval prog₁) (ProbComp.eval prog₂) ε) (k : ℕ) :
    CloseTo (ProbComp.eval (OracleComp.replicate k prog₁))
      (ProbComp.eval (OracleComp.replicate k prog₂)) (k * ε) := by
  rw [ProbComp.eval_replicate_iid]
  exact h.iid_replicate k

end Cslib.Probability.CloseTo

namespace Cslib.Interactive.CloseTo

export Cslib.Probability.CloseTo (iid iid_replicate eval_replicate)

end Cslib.Interactive.CloseTo
