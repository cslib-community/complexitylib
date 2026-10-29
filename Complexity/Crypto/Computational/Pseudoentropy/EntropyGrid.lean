/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.ExtractionSchedule
public import Complexity.Probability.UniformNat
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Probabilistic.UniformNat
import Mathlib.Algebra.Order.Floor.Ring
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Tactic.PolyTime.Init

/-!
# An expanding grid of entropy guesses

A dyadic grid guesses the observation entropy and the conditional label entropy. Every guess
assigns enough total digest bits to expand, including incorrect guesses. Rounding the true
entropies down gives a candidate satisfying all three extraction budgets whenever the prediction
gap covers four grid steps. The entropy-dependent choice appears only in the existence proof.

The grid and its output lengths use ordinary unary arithmetic. Their polynomial-time
certificates apply to arbitrary captured inputs, so later reductions can enumerate the family.

## Main definitions

* `size`, `observationBits`, `labelBits`, `remainingBits`: the executable grid and digest lengths.
* `Valid`: the entropy budgets required of a successful candidate.

## Main results

* `expands`: every candidate expands, including inaccurate guesses.
* `exists_valid`: a sufficiently large prediction gap guarantees a valid grid entry.
* `isPolyTime_scale`, `isPolyTime_observationBits`, `isPolyTime_labelBits`,
  `isPolyTime_remainingBits`, `isPolyTime_numerator`: grid parameters and digest lengths are
  computable in polynomial time.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, final proof of Theorem 1.
  [Holenstein2006].
  The constants below accommodate our repetition schedule and binary-matrix extractors.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using typed polynomial-time certificates.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.EntropyGrid

open Probability Turing.MultiTapeTM

/-- Enumerate an observation guess up to the seed entropy and a label guess below one. -/
def size (sourceBits bound : ℕ) : ℕ :=
  (dyadicSize bound * sourceBits + 1) * dyadicSize bound

/-- The grid is nonempty, including when the source has no seed bits. -/
@[simp] theorem size_pos (sourceBits bound : ℕ) : 0 < size sourceBits bound :=
  Nat.mul_pos (by lia) (dyadicSize_pos bound)

/-- One unit is the two-slack reserve in the extraction schedule. -/
def scale (n sourceBits bound : ℕ) : ℕ :=
  2 * ExtractionSchedule.slack n sourceBits (dyadicSize bound - 1)

/-- Digest length for the observation source, with a zero floor. -/
def observationBits (n sourceBits bound index : ℕ) : ℕ :=
  scale n sourceBits bound * (2 * (index / dyadicSize bound) - 1)

/-- Digest length for the hidden labels, using part of the pseudoentropy surplus. -/
def labelBits (n sourceBits bound index : ℕ) : ℕ :=
  scale n sourceBits bound * (2 * (index % dyadicSize bound) + 7)

/-- Digest length for the saved seed after revealing both components. -/
def remainingBits (n sourceBits bound index : ℕ) : ℕ :=
  scale n sourceBits bound *
    (2 * (dyadicSize bound * sourceBits -
      (index / dyadicSize bound + index % dyadicSize bound + 2)) - 1)

/-- The soft-mask density numerator, four grid steps above the label guess. -/
def numerator (bound index : ℕ) : ℕ := index % dyadicSize bound + 4

/-- The grid has polynomially many entries. -/
theorem isPolyTime_size {α : Type} {input : α ↪ List Bool} {sourceBits bound : α → ℕ}
    (hsource : ComputableInPolyTime sourceBits input encUnary)
    (hbound : ComputableInPolyTime bound input encUnary) :
    ComputableInPolyTime (fun a => size (sourceBits a) (bound a)) input encUnary := by
  have hdyadic := ComputableInPolyTime.unary_dyadicSize.comp hbound
  unfold size
  exact ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' hdyadic hsource)
      (ComputableInPolyTime.const 1))
    hdyadic

/-- The common slack unit is uniformly efficient. -/
theorem isPolyTime_scale {α : Type} {input : α ↪ List Bool} {n sourceBits bound : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hsource : ComputableInPolyTime sourceBits input encUnary)
    (hbound : ComputableInPolyTime bound input encUnary) :
    ComputableInPolyTime (fun a => scale (n a) (sourceBits a) (bound a)) input encUnary := by
  unfold scale
  exact ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
    (ExtractionSchedule.isPolyTime_slack hn hsource
      (ComputableInPolyTime.unary_sub'
        (ComputableInPolyTime.unary_dyadicSize.comp hbound)
        (ComputableInPolyTime.const 1)))

attribute [program_certificate] isPolyTime_size isPolyTime_scale

/-- The observation digest length is uniformly efficient in the candidate index. -/
theorem isPolyTime_observationBits {α : Type} {input : α ↪ List Bool}
    {n sourceBits bound index : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hsource : ComputableInPolyTime sourceBits input encUnary)
    (hbound : ComputableInPolyTime bound input encUnary)
    (hindex : ComputableInPolyTime index input encUnary) :
    ComputableInPolyTime
      (fun a => observationBits (n a) (sourceBits a) (bound a) (index a)) input encUnary := by
  have hdyadic := ComputableInPolyTime.unary_dyadicSize.comp hbound
  unfold observationBits
  exact ComputableInPolyTime.unary_mul' (isPolyTime_scale hn hsource hbound)
    (ComputableInPolyTime.unary_sub'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
        (ComputableInPolyTime.unary_div.comp (hindex.prod hdyadic)))
      (ComputableInPolyTime.const 1))

/-- The label digest length is uniformly efficient in the candidate index. -/
theorem isPolyTime_labelBits {α : Type} {input : α ↪ List Bool}
    {n sourceBits bound index : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hsource : ComputableInPolyTime sourceBits input encUnary)
    (hbound : ComputableInPolyTime bound input encUnary)
    (hindex : ComputableInPolyTime index input encUnary) :
    ComputableInPolyTime
      (fun a => labelBits (n a) (sourceBits a) (bound a) (index a)) input encUnary := by
  have hdyadic := ComputableInPolyTime.unary_dyadicSize.comp hbound
  unfold labelBits
  exact ComputableInPolyTime.unary_mul' (isPolyTime_scale hn hsource hbound)
    (ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
        (ComputableInPolyTime.unary_mod.comp (hindex.prod hdyadic)))
      (ComputableInPolyTime.const 7))

/-- The retained-seed digest length is uniformly efficient in the candidate index. -/
theorem isPolyTime_remainingBits {α : Type} {input : α ↪ List Bool}
    {n sourceBits bound index : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hsource : ComputableInPolyTime sourceBits input encUnary)
    (hbound : ComputableInPolyTime bound input encUnary)
    (hindex : ComputableInPolyTime index input encUnary) :
    ComputableInPolyTime
      (fun a => remainingBits (n a) (sourceBits a) (bound a) (index a)) input encUnary := by
  have hdyadic := ComputableInPolyTime.unary_dyadicSize.comp hbound
  have hq := ComputableInPolyTime.unary_div.comp (hindex.prod hdyadic)
  have hr := ComputableInPolyTime.unary_mod.comp (hindex.prod hdyadic)
  unfold remainingBits
  exact ComputableInPolyTime.unary_mul' (isPolyTime_scale hn hsource hbound)
    (ComputableInPolyTime.unary_sub'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
        (ComputableInPolyTime.unary_sub'
          (ComputableInPolyTime.unary_mul' hdyadic hsource)
          (ComputableInPolyTime.unary_add'
            (ComputableInPolyTime.unary_add' hq hr)
            (ComputableInPolyTime.const 2))))
      (ComputableInPolyTime.const 1))

/-- The requested density is uniformly efficient in the candidate index. -/
theorem isPolyTime_numerator {α : Type} {input : α ↪ List Bool} {bound index : α → ℕ}
    (hbound : ComputableInPolyTime bound input encUnary)
    (hindex : ComputableInPolyTime index input encUnary) :
    ComputableInPolyTime (fun a => numerator (bound a) (index a)) input encUnary := by
  have hdyadic := ComputableInPolyTime.unary_dyadicSize.comp hbound
  unfold numerator
  exact ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mod.comp (hindex.prod hdyadic))
    (ComputableInPolyTime.const 4)

attribute [program_certificate]
  isPolyTime_observationBits isPolyTime_labelBits isPolyTime_remainingBits isPolyTime_numerator

/-- No candidate asks for zero soft-mask mass. -/
theorem numerator_pos (bound index : ℕ) : 0 < numerator bound index := by
  unfold numerator
  lia

/-- The integer unit is positive even at security parameter zero. -/
theorem scale_pos (n sourceBits bound : ℕ) : 0 < scale n sourceBits bound := by
  unfold scale ExtractionSchedule.slack
  positivity

/-- The repetition count is exactly two units per grid step. -/
theorem count_eq (n sourceBits bound : ℕ) :
    ExtractionSchedule.count n sourceBits (dyadicSize bound - 1) =
      2 * scale n sourceBits bound * dyadicSize bound := by
  have h := dyadicSize_pos bound
  unfold ExtractionSchedule.count scale ExtractionSchedule.slack
  rw [Nat.sub_add_cancel (by lia : 1 ≤ dyadicSize bound)]
  ring

/-- All candidates expand, whether or not their entropy guesses are accurate. -/
theorem expands (n sourceBits bound index : ℕ) :
    ExtractionSchedule.count n sourceBits (dyadicSize bound - 1) * sourceBits <
      observationBits n sourceBits bound index + labelBits n sourceBits bound index +
        remainingBits n sourceBits bound index := by
  have hround (total first second : ℕ) :
      2 * total < (2 * first - 1) + (2 * second + 7) +
        (2 * (total - (first + second + 2)) - 1) := by lia
  have h := Nat.mul_lt_mul_of_pos_left
    (hround (dyadicSize bound * sourceBits) (index / dyadicSize bound)
      (index % dyadicSize bound)) (scale_pos n sourceBits bound)
  rw [count_eq]
  unfold observationBits labelBits remainingBits
  nlinarith only [h]

/-- The label budget holds exactly for every candidate, independent of entropy assumptions. -/
theorem label_budget (n sourceBits bound index : ℕ) :
    (labelBits n sourceBits bound index : ℝ) + scale n sourceBits bound =
      ExtractionSchedule.count n sourceBits (dyadicSize bound - 1) *
        ((numerator bound index : ℝ) / dyadicSize bound) := by
  have hD : (dyadicSize bound : ℝ) ≠ 0 := by exact_mod_cast (dyadicSize_pos bound).ne'
  rw [count_eq]
  unfold labelBits numerator
  push_cast
  field_simp
  ring

/-- The entropy assumptions required of a useful entry. Indexing and expansion are separate
from security: inaccurate entries are still total expanding programs. -/
structure Valid (n sourceBits bound index : ℕ)
    (observationEntropy labelEntropy gap : ℝ) : Prop where
  /-- The entry lies in the enumerated grid. -/
  index_lt : index < size sourceBits bound
  /-- The requested mask density is at most one. -/
  numerator_le : numerator bound index ≤ dyadicSize bound
  /-- The prediction gap pays for the increased label density. -/
  density_le : (numerator bound index : ℝ) / dyadicSize bound ≤ labelEntropy + gap
  /-- The first extractor respects the observation entropy. -/
  observation_budget : observationBits n sourceBits bound index = 0 ∨
    (observationBits n sourceBits bound index : ℝ) + scale n sourceBits bound ≤
      ExtractionSchedule.count n sourceBits (dyadicSize bound - 1) * observationEntropy
  /-- The last extractor respects the entropy left in the saved sampler seed. -/
  remaining_budget : remainingBits n sourceBits bound index = 0 ∨
    (remainingBits n sourceBits bound index : ℝ) + scale n sourceBits bound ≤
      ExtractionSchedule.count n sourceBits (dyadicSize bound - 1) *
        (sourceBits - observationEntropy - labelEntropy)

private theorem rounded_budget (unit guess : ℕ) {entropy : ℝ}
    (hguess : (guess : ℝ) ≤ entropy) :
    unit * (2 * guess - 1) = 0 ∨
      ((unit * (2 * guess - 1) : ℕ) : ℝ) + unit ≤ 2 * unit * entropy := by
  by_cases hzero : guess = 0
  · simp [hzero]
  · right
    rw [Nat.cast_mul, Nat.cast_sub (by lia : 1 ≤ 2 * guess)]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hguess (Nat.cast_nonneg unit)]

/-- Rounding both true entropies down supplies a valid candidate. Four grid steps of
pseudoentropy suffice; no algorithm for computing either entropy is assumed. -/
theorem exists_valid (n sourceBits bound : ℕ) {observationEntropy labelEntropy gap : ℝ}
    (hobservation : 0 ≤ observationEntropy) (hlabel : 0 ≤ labelEntropy)
    (htotal : observationEntropy + labelEntropy ≤ sourceBits)
    (hgap : 4 / (dyadicSize bound : ℝ) ≤ gap)
    (hone : labelEntropy + gap ≤ 1) :
    ∃ index, Valid n sourceBits bound index observationEntropy labelEntropy gap := by
  let D := dyadicSize bound
  let first := ⌊(D : ℝ) * observationEntropy⌋₊
  let second := ⌊(D : ℝ) * labelEntropy⌋₊
  have hD : 0 < D := dyadicSize_pos bound
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hfirst : (first : ℝ) ≤ D * observationEntropy := Nat.floor_le (by positivity)
  have hsecond : (second : ℝ) ≤ D * labelEntropy := Nat.floor_le (by positivity)
  have hfirst_lt : D * observationEntropy < (first : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsecond_lt : D * labelEntropy < (second : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfirst_le : first ≤ D * sourceBits := by
    exact_mod_cast hfirst.trans (mul_le_mul_of_nonneg_left
      (show observationEntropy ≤ (sourceBits : ℝ) by linarith) hDr.le)
  have hgap' : (4 : ℝ) ≤ gap * D := (div_le_iff₀ hDr).mp hgap
  have hsecond_le : second + 4 ≤ D := by
    have h := mul_le_mul_of_nonneg_left hone hDr.le
    exact_mod_cast (show (second : ℝ) + 4 ≤ D by nlinarith)
  have hsecond_mod : second < D := by lia
  have hquot : (first * D + second) / D = first := by
    rw [Nat.mul_comm first D, Nat.mul_add_div hD, Nat.div_eq_of_lt hsecond_mod, Nat.add_zero]
  have hrem : (first * D + second) % D = second := by simp [Nat.mod_eq_of_lt hsecond_mod]
  refine ⟨first * D + second, ?_⟩
  constructor
  · unfold size
    change first * D + second < (D * sourceBits + 1) * D
    nlinarith [Nat.mul_le_mul_right D hfirst_le]
  · simpa only [numerator, ← show D = dyadicSize bound from rfl, hrem] using hsecond_le
  · simp only [numerator, ← show D = dyadicSize bound from rfl, hrem, Nat.cast_add,
      Nat.cast_ofNat]
    apply (div_le_iff₀ hDr).mpr
    nlinarith
  · rw [count_eq]
    simp only [observationBits, ← show D = dyadicSize bound from rfl, hquot]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
      rounded_budget (scale n sourceBits bound) first hfirst
  · rw [count_eq]
    simp only [remainingBits, ← show D = dyadicSize bound from rfl, hquot, hrem]
    have hremaining : ((D * sourceBits - (first + second + 2) : ℕ) : ℝ) ≤
        D * (sourceBits - observationEntropy - labelEntropy) := by
      by_cases hsmall : first + second + 2 ≤ D * sourceBits
      · rw [Nat.cast_sub hsmall]
        push_cast
        nlinarith
      · rw [Nat.sub_eq_zero_of_le (by lia)]
        push_cast
        exact mul_nonneg hDr.le (by linarith)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
      rounded_budget (scale n sourceBits bound) _ hremaining

end Cslib.Crypto.Pseudoentropy.EntropyGrid
