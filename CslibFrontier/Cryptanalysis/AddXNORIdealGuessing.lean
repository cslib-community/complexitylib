/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORIdealVerificationCovering
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic.Linarith

/-!
# Hidden-word guessing in the valid stopped cut coupling

Good final-state equality transfers the joint candidate/hidden-word guessing event, without
using the source's false frontier-sampler law. This does not by itself assert that every
successful non-planted candidate forces a collision; `PlantedUniqueness.accepted_eq` proves that
on collision-free complete ledgers.

## Main results

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Guessing.stopped_guess_eq`: equality of the
  stopped guessing mass.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Guessing.independent_guess`: exact hidden-word guessing.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Guessing.stopped_guess_le`: the changed-world
  stopped guess costs at most `2^(-q)` in the valid cut coupling.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain.Guessing

open Probability OracleComp RandomPermutation
open scoped ENNReal

/-- Guessing the specified word without setting the flag has the same law in both worlds.
The event retains the candidate, rather than replacing it by verification acceptance. -/
theorem stopped_guess_eq {q : ℕ} {Word : Type} [DecidableEq Word]
    (perms changed : Label q → Equiv.Perm Word) (bits : Operators q)
    (program : ProbOracleComp (Spec q Word) (Operators q)) :
    ((ProbOracleComp.runWith (Visible.handler true perms changed) program (((), []), false)).map
        (fun (candidate, _, flag) => decide (candidate = bits) && !flag)) true =
      ((ProbOracleComp.runWith (Visible.handler false perms changed) program (((), []), false)).map
        (fun (candidate, _, flag) => decide (candidate = bits) && !flag)) true := by
  classical
  simp only [PMF.map_apply]
  apply tsum_congr
  rintro ⟨candidate, state, flag⟩
  cases flag <;> simp only [Bool.not_false, Bool.and_true, Bool.not_true, Bool.and_false,
    Bool.true_eq_false, ↓reduceIte]
  rw [(Visible.identicalUntilBad perms changed).run_apply program (((), []), false)
    candidate (state, false) (by simp [FlagBad])]

/-- Any independent candidate distribution guesses the uniform full word with probability
exactly `2^(-q)`, including candidates computed from adaptive oracle observations. -/
theorem independent_guess (q : ℕ) (candidates : PMF (Operators q)) :
    ((PMF.uniformOfFintype (Operators q)).bind fun bits =>
      candidates.map (fun candidate => decide (candidate = bits))) true = 1 / 2 ^ q := by
  classical
  have hc (candidate : Operators q) :
      ((PMF.uniformOfFintype (Operators q)).map
        (fun bits => decide (candidate = bits))) true = 1 / 2 ^ q := by
    simp [PMF.map_apply, PMF.uniformOfFintype_apply, Operators]
  have he : ((PMF.uniformOfFintype (Operators q)).bind fun bits =>
      candidates.map (fun candidate => decide (candidate = bits))) =
      candidates.bind fun candidate => (PMF.uniformOfFintype (Operators q)).map
        (fun bits => decide (candidate = bits)) := by
    simp only [PMF.map]
    exact PMF.bind_comm _ _ _
  rw [he, PMF.bind_apply]
  simp only [hc, ENNReal.tsum_mul_right, candidates.tsum_coe, one_mul]

/-- The valid changed-world stopped guessing event costs at most the exact hidden-word
mass. The oracle program sees no hidden bits; only the final event tests them. -/
theorem stopped_guess_le {q : ℕ} {Word : Type} [DecidableEq Word]
    (perms : Label q → Equiv.Perm Word) (seed target : Word) (k : Fin q)
    (program : ProbOracleComp (Spec q Word) (Operators q)) :
    ((PMF.uniformOfFintype (Operators q)).bind fun bits =>
      (ProbOracleComp.runWith
        (Visible.handler false perms ((sourceCut bits k).splice perms seed target)) program
        (((), []), false)).map
          (fun (candidate, _, flag) => decide (candidate = bits) && !flag)) true ≤ 1 / 2 ^ q := by
  classical
  have hstep (bits : Operators q) :
      ((ProbOracleComp.runWith
        (Visible.handler false perms ((sourceCut bits k).splice perms seed target)) program
        (((), []), false)).map
          (fun (candidate, _, flag) => decide (candidate = bits) && !flag)) true ≤
      ((interpret (Family.probEval perms) program).map
        (fun candidate => decide (candidate = bits))) true := by
    rw [← stopped_guess_eq]
    have h := Probability.PMF.map_true_mono
      (ProbOracleComp.runWith
        (Visible.handler true perms ((sourceCut bits k).splice perms seed target)) program
        (((), []), false))
      (E := fun (candidate, _, flag) => decide (candidate = bits) && !flag)
      (F := fun outcome => decide (outcome.1 = bits)) (fun ⟨candidate, state, flag⟩ _ he => by
        cases flag
        · simpa using he
        · simp at he)
    have hh := congrArg (PMF.map (fun candidate => decide (candidate = bits)))
      (Visible.output_law true perms ((sourceCut bits k).splice perms seed target) program)
    simp only [PMF.map_comp, Function.comp_def] at hh
    rw [hh] at h
    exact h
  rw [← independent_guess q (interpret (Family.probEval perms) program)]
  simp only [PMF.bind_apply]
  exact tsum_le_tsum (fun bits => mul_le_mul_of_nonneg_left (hstep bits) zero_le)

end Cslib.Cryptanalysis.AddXNOR.IdealChain.Guessing
