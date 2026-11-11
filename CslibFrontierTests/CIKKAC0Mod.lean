/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.UniformLearning.CIKK.AC0Mod
import CslibFrontier.Computability.Circuit.Boolean.ACC0.Gadgets

/-! Usage checks for learning AC⁰[2] with the rank property: the class-form theorem specializes to
parity, and the query bounds instantiate at a fixed depth. -/

namespace CslibFrontierTests.CIKKAC0Mod

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded
  Cslib.Circuits.Boolean.Razborov Cslib.MachineLearning.UniformLearning Finset

/-- **Parity.** One `MOD₂` gate computes parity, so the learner at depth `1` and size `1` learns
`parity n` with error `2^{-e}` and confidence `1 - 2^{-h}`. -/
example (e h n : ℕ) :
    (cikkLearner n (cikkAC0Len 1 e n 1 (cikkAC0Gap 1 e n 1)) e (cikkAC0Gap 1 e n 1) h
        (truthTableTest (rankProperty sliceLevel (cikkAC0Len 1 e n 1 (cikkAC0Gap 1 e n 1))))).Learns
      (cikkSeed n (cikkAC0Len 1 e n 1 (cikkAC0Gap 1 e n 1)) e (cikkAC0Gap 1 e n 1) h)
      {parity n} (1 / 2 ^ e) (1 / 2 ^ h) := by
  refine (learns_cikkLearner_rankTest 1 e h n 1).mono ?_ le_rfl le_rfl
  rintro _ rfl
  exact ⟨parityOnCircuit univ, fun x => funext fun o => eval_parityOnCircuit _ x o, by simp,
    by simp⟩

/-- **Quasi-polynomially many queries at depth `0`.** With `M = 2^{e+10} (3e + 42)` and
`B = ⌊log₂ (M² (s + 6 (n + 1)² + 3))⌋ + 1`, the learner for depth-`0` targets makes at most
`(h + 1) 2 ^ (12 · 2^{840} B^{14} + 6 e + 59)` queries. -/
example (e h n s : ℕ) :
    (cikkLearner n (cikkAC0Len 0 e n s (cikkAC0Gap 0 e n s)) e (cikkAC0Gap 0 e n s) h
        (truthTableTest (rankProperty sliceLevel
          (cikkAC0Len 0 e n s (cikkAC0Gap 0 e n s))))).QueriesAtMost
      ((h + 1) * 2 ^ (12 * (2 ^ 840 *
        (Nat.log 2 ((2 ^ (e + 10) * (3 * e + 42)) ^ 2 * (s + 6 * (n + 1) ^ 2 + 3)) + 1) ^ 14) +
          6 * e + 59)) := by
  have h := queriesAtMost_cikkLearner_rankTest_le 0 e h n s
  rwa [show 2 * (0 + 7) * (5 * (0 + 7) + 25) = 840 from rfl, show 2 * (0 + 7) = 14 from rfl]
    at h

end CslibFrontierTests.CIKKAC0Mod
