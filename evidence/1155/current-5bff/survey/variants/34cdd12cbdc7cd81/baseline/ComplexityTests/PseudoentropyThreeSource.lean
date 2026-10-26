/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Pseudoentropy.EntropyGrid
import Complexity.Crypto.Computational.Pseudoentropy.ThreeSource.Seeded
import Complexity.Tactic.PPT

/-!
Entropy budgets, captured programs, exact seed accounting, and executable three-source clients.
-/

namespace ComplexityTests.PseudoentropyThreeSource

open Cslib Cslib.Probability Cslib.BitString Cslib.Crypto.Pseudoentropy Turing.MultiTapeTM

-- The plain efficiency contract is inhabited independently of entropy/security assumptions.
example : ThreeSource.Efficient (fun _ => 1) (fun _ => 2) (fun _ => 3) (fun _ => 4)
    (fun _ _ => 5) (fun _ _ => 6) (fun _ _ => 7) (fun _ _ => 8) := by
  constructor <;> fun_prop

-- Runtime divisors, including zero, use the same total quotient/remainder certificate.
example : ComputableInPolyTime (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2))
    (encPair encUnary encUnary) (encPair encUnary encUnary) :=
  .of_tidy ComputableTidilyInPolyTime.unary_divMod

example : ComputableInPolyTime
    (fun p : Bool × ℕ × ℕ => (p.2.1 / p.2.2, p.2.1 % p.2.2))
    (encPair encBool (encPair encUnary encUnary)) (encPair encUnary encUnary) := by fun_prop

example : ComputableInPolyTime (fun n : ℕ => (n / 0, n % 0))
    encUnary (encPair encUnary encUnary) := by polytime

-- All three lengths compose with ordinary computed parameters and indices.
example : ComputableInPolyTime (fun p : ℕ × ℕ =>
    (EntropyGrid.observationBits p.1 (p.1 + 1) p.2 (p.1 + p.2),
      EntropyGrid.labelBits p.1 (p.1 + 1) p.2 (p.1 + p.2),
      EntropyGrid.remainingBits p.1 (p.1 + 1) p.2 (p.1 + p.2)))
    (encPair encUnary encUnary) (encPair encUnary (encPair encUnary encUnary)) := by polytime

-- This is a concrete instance of every numerical field in Valid, with three positive digests.
-- It is an entropy-budget example, not an assumption that a positive-gap pair exists.
example : EntropyGrid.Valid 0 2 4 64 1 0 (1 / 2) := by
  have hsize : dyadicSize 4 = 8 := by decide
  constructor <;> norm_num [EntropyGrid.size, EntropyGrid.numerator,
    EntropyGrid.observationBits, EntropyGrid.remainingBits, EntropyGrid.scale,
    ExtractionSchedule.count, ExtractionSchedule.slack, hsize]

example : 0 < EntropyGrid.observationBits 0 2 4 64 ∧
    0 < EntropyGrid.labelBits 0 2 4 64 ∧ 0 < EntropyGrid.remainingBits 0 2 4 64 := by decide

-- Even an inaccurate or out-of-range guess expands; validity is a separate security condition.
example (n seedBits bound index : ℕ) :
    ExtractionSchedule.count n seedBits (dyadicSize bound - 1) * seedBits <
      EntropyGrid.observationBits n seedBits bound index +
        EntropyGrid.labelBits n seedBits bound index +
          EntropyGrid.remainingBits n seedBits bound index :=
  EntropyGrid.expands n seedBits bound index

-- An arbitrary evaluator may capture the parameter; the theorem charges every call and hash.
example (evaluate : ℕ → List Bool → List Bool × Bool)
    (hevaluate : ComputableInPolyTime (fun p => evaluate p.1 p.2)
      (encPair encUnary encBits) (encPair encBits encBool)) :
    ComputableInPolyTime (fun p : ℕ × List Bool =>
      ThreeSource.generate (p.1 + 1) p.1 p.1 1 1 1 (evaluate p.1) p.2)
      (encPair encUnary encBits) encBits := by
  fail_if_success (clear hevaluate; polytime)
  polytime

example (source : ℕ → ProbComp ((List Bool × Bool) × List Bool))
    (hsource : IsPPTOn encUnary (encPair (encPair encBits encBool) encBits) source) :
    IsPPTOn (encPair encBool encUnary) encBits (fun p : Bool × ℕ =>
      ThreeSource.extract (p.2 + 1) p.2 p.2 1 1 1 (source p.2)) := by ppt

-- A second spelling exposes the complete sampled pipeline to the same automation.
example (source : ℕ → ProbComp ((List Bool × Bool) × List Bool))
    (hsource : IsPPTOn encUnary (encPair (encPair encBits encBool) encBits) source) :
    IsPPTOn encUnary encBits (fun n => do
      let samples ← OracleComp.replicate (n + 1) (source n)
      let third ← extractWordSeeds (n + 1) n 1 samples
      let middle ← extractWordLabels (n + 1) 1 third.1
      let front ← ThreeSource.finish n 1 middle
      return front ++ (third.2.1 ++ third.2.2)) := by ppt

private def evaluate (seed : List Bool) : List Bool × Bool :=
  (seed.take 1, seed.getD 1 false)

private theorem observation_bound (seed : List Bool) : (evaluate seed).1.length ≤ 1 := by
  simpa only [evaluate, List.length_take] using Nat.min_le_left 1 seed.length

-- Two sampler bits and matrix keys of lengths 2, 1, and 3 give an eight-bit seed.
example : ThreeSource.seedLength 1 2 1 1 1 1 = 8 := rfl
example : ThreeSource.outputLength 1 2 1 1 1 1 = 9 := rfl

example :
    (uniformList 8).map (ThreeSource.generate 1 2 1 1 1 1 evaluate) =
      ProbComp.eval (ThreeSource.extract 1 2 1 1 1 1 (do
        let seed ← sampleList 2
        return (evaluate seed, seed))) :=
  ThreeSource.eval_generate 1 2 1 1 1 1 evaluate (fun seed _ => observation_bound seed)

example (seed : List Bool) (hseed : seed.length = 8) :
    (ThreeSource.generate 1 2 1 1 1 1 evaluate seed).length = 9 :=
  ThreeSource.length_generate 1 2 1 1 1 1 evaluate
    (fun seed _ => observation_bound seed) hseed

-- Small deterministic executions include malformed input and zero output components.
example : ThreeSource.generate 1 2 1 1 1 1 evaluate (List.replicate 8 false) =
    List.replicate 9 false := by decide

example : ThreeSource.generate 1 2 1 1 1 1 evaluate
    [true, false, true, false, true, true, false, true] =
      [true, false, true, true, true, false, true, false, true] := by decide

example : ThreeSource.generate 1 2 1 1 1 1 evaluate [] = [false, false, false] := by decide

example : ThreeSource.generate 1 2 1 0 0 0 evaluate [true, false] = [] := by decide

end ComplexityTests.PseudoentropyThreeSource
