/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.GeneratorReindex
import Complexity.Crypto.Computational.UniformChoice
import Complexity.Tactic.PPT

/-! Nonmonotone schedules, short seeds, exact suffix preservation and uniform calibration. -/

namespace ComplexityTests.GeneratorReindex

open Cslib Cslib.Crypto Cslib.BitString Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

-- A polynomial schedule may decrease; every value still exceeds its parameter.
private def schedule (n : ℕ) : ℕ := if n % 2 = 0 then n + 3 else n + 1

example : schedule 1 < schedule 0 := by decide

example : ∀ n, n + 1 ≤ schedule n := by
  intro n
  unfold schedule
  split_ifs <;> lia

example : GeneratorReindex.parameter schedule 0 = 0 := by decide
example : GeneratorReindex.parameter schedule 3 = 1 := by decide
example : GeneratorReindex.parameter schedule 4 = 3 := by decide

example : ComputableInPolyTime (GeneratorReindex.parameter schedule) encUnary encUnary := by
  apply GeneratorReindex.isPolyTime_parameter
  · unfold schedule
    fun_prop
  · fun_prop

-- Short inputs use the explicit fallback; later inputs retain every unused suffix bit.
example : GeneratorReindex.generate schedule (fun _ seed => seed ++ [true]) [] =
    [false] := by decide

example : GeneratorReindex.generate schedule (fun _ seed => seed ++ [true]) [true, false] =
    [true, false, false] := by decide

example : GeneratorReindex.generate schedule (fun _ seed => seed ++ [true])
    [false, true, false] = [false, true, true, false] := by decide

example (seed : List Bool) :
    (GeneratorReindex.generate schedule (fun _ seed => seed ++ [true]) seed).length =
      seed.length + 1 :=
  GeneratorReindex.length_generate (fun _ _ h => by simp [h]) seed

example : ComputableInPolyTime
    (GeneratorReindex.generate schedule (fun _ seed => seed ++ [true])) encBits encBits := by
  apply GeneratorReindex.isPolyTime_generate
  · unfold schedule
    fun_prop
  · fun_prop

example (real ideal challenge : ℕ → ProbComp Bool)
    (hreal : IsPPTOn encUnary encBool real)
    (hideal : IsPPTOn encUnary encBool ideal)
    (hchallenge : IsPPTOn encUnary encBool challenge) :
    IsPPTOn encUnary encBool (fun n => calibratedTest (real n) (ideal n) (challenge n)) := by
  fail_if_success (clear hreal; ppt)
  fail_if_success (clear hideal; ppt)
  fail_if_success (clear hchallenge; ppt)
  ppt

-- Opposite signed gaps do not cancel: calibration orients both tests consistently.
private def signedTest (index : ℕ) (word : List Bool) : ProbComp Bool :=
  pure (if index = 0 then word.headD false else !word.headD false)

example : Game.advantage
    (ProbComp.eval (pure [true] >>=
      UniformChoice.test 1 (pure [true]) (pure [false]) signedTest))
    (ProbComp.eval (pure [false] >>=
      UniformChoice.test 1 (pure [true]) (pure [false]) signedTest)) =
    1 := by
  rw [UniformChoice.advantage_eq]
  change (∑ i : Fin 2, _) / 2 = 1
  norm_num [Fin.sum_univ_two, signedTest, Game.advantage, Game.succProbability,
    ProbComp.eval_bind, ProbComp.eval_pure]

-- One bound controls every allowed index without a program computing the chosen index.
example (adversary : ℕ → ℕ → List Bool → ProbComp Bool)
    (hadversary : IsPPTOn (encPair (encPair encUnary encUnary) encBits) encBool
      (fun p => adversary p.1.1 p.1.2 p.2)) :
    ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n index, index ≤ n + 2 →
      Game.advantage (ProbComp.eval (sampleList n >>= adversary n index))
        (ProbComp.eval (sampleList n >>= adversary n index)) ≤ ε n := by
  apply ComputationallyIndistinguishable.uniform_bound
    (ComputationallyIndistinguishable.refl _) (by ppt) (by ppt) (.of_tidy (by fun_prop))
      adversary hadversary

-- The uniform test accepts captured data and a computed challenge in ordinary functional form.
example : IsPPTOn (encPair encUnary encBits) encBool (fun p =>
    UniformChoice.test (p.1 + p.2.length) (sampleList p.1) (pure p.2)
      (fun index word => pure (decide (index ≤ word.length))) p.2.reverse) := by
  ppt

end ComplexityTests.GeneratorReindex
