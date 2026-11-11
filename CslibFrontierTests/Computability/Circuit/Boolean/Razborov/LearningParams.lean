/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Boolean.Razborov.LearningParams

/-!
# Tests for the parameters of the CIKK learner for AC⁰[2]

How the learner's correctness proof (M6.8b2 of #4451) consumes
`CslibFrontier.Computability.Circuit.Boolean.Razborov.LearningParams`: the fixed point gives the
density margin `2 ^ (ℓ + 2) ≤ 2 ^ g`, the rejection lemma applies to any generator circuit of
depth at most `d + 7` and size at most `S(g)`, and the bound on `g` specializes to explicit
constants at a fixed depth.
-/

public section

namespace CslibFrontierTests.Computability.Circuit.Boolean.Razborov.LearningParams

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Razborov
open Cslib.MachineLearning.UniformLearning

/-- The density margin: with the rank test accepting half of the truth tables, the fixed point
leaves the factor `2 ^ (ℓ + 1)` the learner's density hypothesis asks for. -/
example (d e n s : ℕ) :
    2 ^ (cikkAC0Len d e n s (cikkAC0Gap d e n s) + 1) * 2 ≤ 2 ^ cikkAC0Gap d e n s := by
  rw [← pow_succ]
  exact Nat.pow_le_pow_right (by norm_num) (cikkAC0Len_add_two_le_cikkAC0Gap d e n s)

/-- The rejection, at the advantage exponent `g = cikkAC0Gap d e n s`. -/
example {d e n s : ℕ}
    {G : Circuit Unbounded.extSignature (cikkAC0Len d e n s (cikkAC0Gap d e n s)) 1}
    (hGd : G.depth ≤ d + 7)
    (hGs : G.size ≤ cikkK e (cikkAC0Gap d e n s) * s +
      6 * (cikkK e (cikkAC0Gap d e n s) * n + cikkK e (cikkAC0Gap d e n s)) ^ 2 + 3)
    {f : BooleanFunction (cikkAC0Len d e n s (cikkAC0Gap d e n s))}
    (hG : G.Computes (Unbounded.extInterpretation (modGate 2)) (single f)) :
    f ∉ rankProperty sliceLevel (cikkAC0Len d e n s (cikkAC0Gap d e n s)) :=
  notMem_rankProperty_cikkAC0Len_of_computes hGd hGs hG

/-- At depth `0`, `g ≤ 2 ^ 840 · B ^ 14`. -/
example (e n s : ℕ) :
    cikkAC0Gap 0 e n s ≤ 2 ^ 840 *
      (Nat.log 2 ((2 ^ (e + 10) * (3 * e + 42)) ^ 2 * (s + 6 * (n + 1) ^ 2 + 3)) + 1) ^ 14 := by
  have h := cikkAC0Gap_le 0 e n s
  rwa [show 2 * (0 + 7) * (5 * (0 + 7) + 25) = 840 from rfl, show 2 * (0 + 7) = 14 from rfl]
    at h

end CslibFrontierTests.Computability.Circuit.Boolean.Razborov.LearningParams
