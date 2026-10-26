/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.PseudorandomFunction.RandomOracle
import Complexity.Tactic.PPT

namespace ComplexityTests.PseudorandomFunction

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

-- The parameterized predicate has concrete uniform witnesses with unbounded auxiliary input.
example : IsOraclePPT (Operation := Unit) encBits (fun n word =>
    pure (List.replicate n false ++ word.reverse)) := by fun_prop

example : IsOraclePPT (Operation := Bool) encBool (fun n word =>
    pure (decide (word.length ≤ n))) := by fun_prop

-- The ideal game has a PPT realization for every certified adaptive adversary.
example {adversary : OracleDistinguisher} (h : IsOraclePPT encBool adversary) :
    IsPPT encBool (fun n _ => prfIdealGame adversary n) := isPPT_prfIdealGame h

private noncomputable def repeatQuery (n : ℕ) (_ : List Bool) : WordOracleComp Unit Bool := do
  let word ← ProbOracleComp.sample (BitString.sampleList n)
  let first ← ProbOracleComp.query ((), word)
  let bit ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let second ← ProbOracleComp.query ((), word)
  return (first == second) && bit

-- A private random query gets a consistent answer; intervening private randomness stays fresh.
example (n : ℕ) : ProbComp.eval (prfIdealGame repeatQuery n) = PMF.uniformOfFintype Bool := by
  simp only [prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbOracleComp.eval_interpret]
  simpa [repeatQuery, OracleComp.interpret_bind, ProbOracleComp.interpret_sample] using
    (show OracleComp.interpret ProbComp.unifOracle (ProbComp.uniform Bool) =
      PMF.uniformOfFintype Bool from ProbComp.eval_uniform Bool)

-- The same exact law holds for the executable list cache.
example (n : ℕ) :
    ProbComp.eval (prfIdealGame repeatQuery n) =
      ProbComp.eval (Prod.fst <$> (OracleComp.interpret
        (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
          (fun request => cachedRandomFunctionOracle n request.2)) (repeatQuery n [])).run []) :=
  prfIdealGame_eq_cached repeatQuery n

-- Malformed words neither sample an answer nor alter even a preassigned cache.
example (cache : List (List Bool × List Bool)) :
    cachedRandomFunctionOracle 2 [] cache = pure ([], cache) := by
  simp [cachedRandomFunctionOracle]

-- Duplicate preassigned keys use their first entry and do not resample.
example : cachedRandomFunctionOracle 1 [false] [([false], [true]), ([false], [false])] =
    pure ([true], [([false], [true]), ([false], [false])]) := by
  simp [cachedRandomFunctionOracle, memoize]

-- A purported family must produce valid-width answers, even if it has a trivial evaluator.
example : ¬ PseudorandomFunction (fun _ _ => []) := by
  intro h
  have := h.length_eq [false] [false] rfl
  simp at this

end ComplexityTests.PseudorandomFunction
