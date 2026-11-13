/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Pseudoentropy.ExtractionSchedule
public import CslibFrontier.Crypto.Computational.Pseudoentropy.Seed

/-!
# The repetition schedule of a seed realization

Label extraction from a sampler repeats it
`ExtractionSchedule.count n (length n) (inverseSlack n)` times, where `length n` is the sampler's
seed length, and reserves two entropy slacks of
`ExtractionSchedule.slack n (length n) (inverseSlack n)` bits. This module names both quantities for
a `SeedRealization`, so extraction statements do not restate the schedule's arguments.

## Main definitions

* `Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.sampleCount`,
  `Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.sampleSlack`: the repetition count
  and entropy slack of the extraction schedule for a seed realization.

## Main results

* `Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.isPolyTime_sampleCount`: the
  repetition count is available in unary with polynomial cost.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization

open Turing.MultiTapeTM

variable {pair : SamplablePair} (seed : SeedRealization pair)

/-- The number of samples extraction draws at parameter `n` with slack parameter
`inverseSlack n`: `ExtractionSchedule.count` at the seed length. -/
abbrev sampleCount (inverseSlack : ℕ → ℕ) (n : ℕ) : ℕ :=
  ExtractionSchedule.count n (seed.length n) (inverseSlack n)

/-- The entropy slack extraction reserves (twice) at parameter `n` with slack parameter
`inverseSlack n`: `ExtractionSchedule.slack` at the seed length. -/
abbrev sampleSlack (inverseSlack : ℕ → ℕ) (n : ℕ) : ℕ :=
  ExtractionSchedule.slack n (seed.length n) (inverseSlack n)

/-- The repetition count is available in unary with polynomial cost. -/
theorem isPolyTime_sampleCount {inverseSlack : ℕ → ℕ}
    (hslack : ComputableInPolyTime inverseSlack encUnary encUnary) :
    ComputableInPolyTime (seed.sampleCount inverseSlack) encUnary encUnary :=
  ExtractionSchedule.isPolyTime_count .id' seed.length_isPolyTime hslack

end Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization
