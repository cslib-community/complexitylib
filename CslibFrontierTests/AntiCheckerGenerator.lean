/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.MCSP.AntiChecker.Generator
import CslibFrontier.Computability.MCSP.AntiChecker.Oracle.PolyTime

/-!
# Tests for the anti-checker generator

Under `NP ⊆ P/poly`, the generator with a `P/poly` oracle builds an anti-checker for every hard
function. Under any oracle its samples are correctly labelled, and under the empty oracle one round
picks the default input. The measures are checked at small parameters, and the anti-checker
parameters against their polynomial bounds.
-/

namespace CslibFrontierTests.AntiCheckerGenerator

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.MCSP Cslib.MCSP.AntiChecker
  Cslib.Complexity Turing.MultiTapeTM

-- Under `NP ⊆ P/poly`, one `P/poly` oracle makes the generator choose an anti-checker for every
-- function that needs more gates than `n` circuits with at most `s` gates and their majority.
example (hNP : NP encBits ⊆ PPolyOn encBits) {n : ℕ} (hn : 0 < n) (s : ℕ) :
    ∃ O ∈ PPoly, ∀ f : BooleanFunction n,
      n * s + complexity interpretation (single (strictMajority n)) <
          complexity interpretation (single f) →
        IsAntiChecker (computableFunctions n s) f
          {x | x ∈ (samplesOf ((generator n s (antiCheckerPower n s) (antiCheckerRounds n s)).eval
            (oracleInterpretation O) (MCSP.truthTable n f))).map Prod.fst} := by
  obtain ⟨O, hO, h⟩ := exists_mem_PPoly_agrees_antiCheckerOracle hNP
  exact ⟨O, hO, fun f hf => isAntiChecker_samplesOf_generator hn h hf⟩

-- Whatever the oracle, every sample is labelled by `f`.
example (O : Language Bool) (n s ℓ R : ℕ) (f : BooleanFunction n) :
    ∀ p ∈ samplesOf ((generator n s ℓ R).eval (oracleInterpretation O) (MCSP.truthTable n f)),
      p.2 = f p.1 :=
  fun _ hp => snd_eq_of_mem_samplesOf_eval_generator O n s ℓ R f hp

-- Under the empty oracle no query is accepted, so one round picks the default input.
example (n s ℓ : ℕ) (f : BooleanFunction n) :
    samplesOf ((generator n s ℓ 1).eval (oracleInterpretation 0) (MCSP.truthTable n f)) =
      [(default, f default)] := by
  have hnone : ∀ P u, queryOracle (0 : Language Bool) n s ℓ P u = false := fun P u => by
    rw [Bool.eq_false_iff, ne_eq, queryOracle_eq_true_iff]
    exact Language.notMem_zero _
  have hfind : (BitString.enum n).find? (fun _ => false) = none := List.find?_eq_none.2 (by simp)
  rw [samplesOf_eval_generator]
  simp [greedy, AntiChecker.step, AntiChecker.select, hnone, hfind]

-- Two rounds on one input: `2 (2 + 2 (3 + 5)) = 36` gates, `2 · 2 = 4` oracle gates, at most two
-- oracle gates on a path, and fan-in at most the length of a query with two samples.
example (s ℓ : ℕ) : (generator 1 s ℓ 2).size = 36 := by
  norm_num [size_generator]

example (s ℓ : ℕ) : (generator 1 s ℓ 2).program.cost OracleOp.queryWeight = 4 := by
  norm_num [cost_generator]

example (s ℓ : ℕ) : (generator 1 s ℓ 2).depthWith OracleOp.queryWeight ≤ 2 :=
  depthWith_generator_le 1 s ℓ 2

example (s ℓ : ℕ) : (generator 1 s ℓ 2).FanInAtMost (2 * (1 + s + ℓ + 2) + 4 + 2 * 9) :=
  fanInAtMost_generator 1 s ℓ 2

-- With the anti-checker parameters, the oracle gates on a path and the fan-in are polynomial in
-- `n + s`.
example (n s : ℕ) :
    (generator n s (antiCheckerPower n s) (antiCheckerRounds n s)).depthWith
        OracleOp.queryWeight ≤ 610 * (n + s + 1) ^ 4 :=
  (depthWith_generator_le _ _ _ _).trans (antiCheckerRounds_le n s)

example (n s : ℕ) :
    (generator n s (antiCheckerPower n s) (antiCheckerRounds n s)).FanInAtMost
      (5000 * (n + s + 1) ^ 5) :=
  (fanInAtMost_generator _ _ _ _).mono (queryLength_antiChecker_le n s)

end CslibFrontierTests.AntiCheckerGenerator
