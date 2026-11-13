/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Probabilistic.CoinOfDigits

/-!
# Tests for biased-coin samplers (Arora–Barak 2007 draft, Lemmas 7.14 and 7.15)

Exercises the public interfaces of `CslibFrontier.Probability.DDGTree.Biased`,
`CslibFrontier.Probability.DDGTree.Digits` and
`CslibFrontier.Computability.Probabilistic.CoinOfDigits`: von Neumann extraction at bias `1/3`
(exactly `9/2` expected flips), the failure at bias `0`, the digit sampler at bias `1` (digits
`0.111⋯`) and `1/2`, and the machine-level corollary for a constant digit function.
-/

public section

namespace Cslib.Tests.BiasedCoinSamplers

open scoped ENNReal unitInterval
open Cslib.Probability Cslib.Probability.DDGTree Turing.MultiTapeTM

/-- The bias `1/3`. -/
noncomputable def third : I := ⟨1 / 3, by norm_num, by norm_num⟩

/-- Von Neumann's tree outputs a fair bit from a `1/3`-coin. -/
example : vonNeumann.GeneratesWith (PMF.coin third) (PMF.uniformOfFintype Bool) :=
  vonNeumann_generatesWith_coin (by norm_num [third]) (by norm_num [third])

/-- At bias `1/3` it reads exactly `1 / ((1/3)(2/3)) = 9/2` flips in expectation. -/
example : vonNeumann.expectedFlipsWith (PMF.coin third) = ENNReal.ofReal (9 / 2) := by
  rw [expectedFlipsWith_coin_vonNeumann (by norm_num [third]) (by norm_num [third])]
  norm_num [third]

/-- The fair-coin run is the general run on the uniform coin. -/
example (T : DDGTree Bool) (n : ℕ) : T.run n = T.runWith (PMF.uniformOfFintype Bool) n :=
  run_eq_runWith T n

/-- At bias `0` no coin-reading tree produces a fair bit. -/
example : ¬ ∃ T : DDGTree Bool, T.GeneratesWith (PMF.coin 0) (PMF.uniformOfFintype Bool) := by
  rw [exists_generatesWith_coin_iff]
  simp

/-- The digit sampler at `ρ = 1` uses the expansion `0.111⋯` and always outputs `true`. -/
example : (coinOfDigits fun _ => true).Generates (PMF.coin 1) :=
  coinOfDigits_generates (by
    simpa using (hasSum_geometric_two' (1 : ℝ)).congr_fun fun i => by
      simp [pow_succ, div_eq_mul_inv])

/-- Whatever the bias, the digit sampler reads exactly two fair bits in expectation. -/
example (d : ℕ → Bool) : (coinOfDigits d).expectedFlips = 2 :=
  expectedFlips_coinOfDigits d

/-- A constant digit function is polynomial-time, so its sampler has finite expected digit-machine
time. -/
example : ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
    ComputableInTimeAndSpaceOfLength (fun _ : ℕ => true) encUnary encBool t s ∧
    (coinOfDigits fun _ => true).expectedCostWith (PMF.uniformOfFintype Bool)
        (fun n => (t n + 1 : ℕ)) = ∑' n, ((t n + 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ n ∧
    (coinOfDigits fun _ => true).expectedCostWith (PMF.uniformOfFintype Bool)
        (fun n => (t n + 1 : ℕ)) < ⊤ :=
  exists_digitTime_expectedCostWith_coinOfDigits_lt_top (ComputableInPolyTime.const true)

end Cslib.Tests.BiasedCoinSamplers
