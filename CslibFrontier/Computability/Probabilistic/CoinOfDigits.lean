/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Probability.DDGTree.Digits

/-!
# Expected digit-machine time of the biased-coin sampler

[Arora and Barak, Lemma 7.14] simulates a coin of bias `ρ` from fair coins in expected `O(1)` time
when the `i`-th binary digit of `ρ` is computable in time polynomial in `i`. Here the digits
`d : ℕ → Bool` are computed by a binary multitape machine from the unary index (`encUnary`)
within a polynomially bounded time `t`, as `Turing.MultiTapeTM.ComputableInPolyTime` provides.
The digit-comparison tree `Cslib.Probability.DDGTree.coinOfDigits d` computes digit `n` exactly
when it reads fair bit number `n + 1`. Charging that flip `t n + 1` (the machine's time bound
plus one comparison), the expected total cost is `∑ₙ (t n + 1) 2⁻ⁿ`, a finite constant that
depends only on `t`.

This bounds the expected sum of the digit machine's time bounds over the digits that the sampler
consults. The comparison loop itself is not compiled to a Turing machine; its control costs are the
unit charge per flip.

## Main results

* `Cslib.Probability.DDGTree.exists_digitTime_expectedCostWith_coinOfDigits_lt_top`: some
  polynomial time bound of a digit machine has finite expected total charge.
* `Cslib.Probability.DDGTree.coinOfDigits_spec_of_computableInPolyTime`: exact law, two expected
  fair bits and finite expected digit-machine time, together.
-/

public section

open scoped ENNReal
open Turing.MultiTapeTM

namespace Cslib.Probability.DDGTree

/-- **Expected constant time** ([Arora and Barak, Lemma 7.14]): if the binary digits `d` are
computable in polynomial time from the unary index, some machine computes digit `n` within a
polynomially bounded time `t n`, and charging fair bit number `n + 1` with `t n + 1` gives the
digit-comparison sampler a finite expected total cost `∑ₙ (t n + 1) 2⁻ⁿ`. -/
theorem exists_digitTime_expectedCostWith_coinOfDigits_lt_top {d : ℕ → Bool}
    (hd : ComputableInPolyTime d encUnary encBool) :
    ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      ComputableInTimeAndSpaceOfLength d encUnary encBool t s ∧
      (coinOfDigits d).expectedCostWith (PMF.uniformOfFintype Bool) (fun n => (t n + 1 : ℕ)) =
        ∑' n, ((t n + 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ n ∧
      (coinOfDigits d).expectedCostWith (PMF.uniformOfFintype Bool) (fun n => (t n + 1 : ℕ)) <
        ⊤ := by
  obtain ⟨t, s, ht, hs, h⟩ := hd
  have ht1 : PolynomiallyBounded fun n => t n + 1 := by
    obtain ⟨C, k, hC⟩ := polynomiallyBounded_iff_le.mp ht
    refine polynomiallyBounded_iff_le.mpr ⟨C + 1, k, fun n => ?_⟩
    have : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos n)
    nlinarith [hC n]
  exact ⟨t, s, ht, hs, h, expectedCostWith_coinOfDigits d _,
    expectedCostWith_coinOfDigits_lt_top d ht1⟩

/-- **Arora–Barak Lemma 7.14**, collected: for a binary expansion `d` of `ρ ∈ [0, 1]` whose digits
are computable in polynomial time from the unary index, the digit-comparison tree generates the coin
of bias `ρ` from fair bits, reads exactly two fair bits in expectation, and has finite expected
digit-machine time `∑ₙ (t n + 1) 2⁻ⁿ`. -/
theorem coinOfDigits_spec_of_computableInPolyTime {d : ℕ → Bool} {ρ : unitInterval}
    (hρ : HasSum (fun i => if d i then (2⁻¹ : ℝ) ^ (i + 1) else 0) ρ)
    (hd : ComputableInPolyTime d encUnary encBool) :
    (coinOfDigits d).Generates (PMF.coin ρ) ∧ (coinOfDigits d).expectedFlips = 2 ∧
      ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
        ComputableInTimeAndSpaceOfLength d encUnary encBool t s ∧
        (coinOfDigits d).expectedCostWith (PMF.uniformOfFintype Bool)
            (fun n => (t n + 1 : ℕ)) < ⊤ := by
  obtain ⟨t, s, ht, hs, h, -, hlt⟩ := exists_digitTime_expectedCostWith_coinOfDigits_lt_top hd
  exact ⟨coinOfDigits_generates hρ, expectedFlips_coinOfDigits d, t, s, ht, hs, h, hlt⟩

end Cslib.Probability.DDGTree
