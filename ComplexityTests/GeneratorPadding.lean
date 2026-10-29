/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Pseudoentropy.ThreeSource.Padding
import Complexity.Tactic.PPT

/-!
Common-length padding, arbitrary certified callbacks, and indexed entropy-grid clients.
-/

namespace ComplexityTests.GeneratorPadding

open Cslib Cslib.Probability Cslib.BitString Cslib.Crypto Cslib.Crypto.Pseudoentropy
  Turing.MultiTapeTM

-- A polynomial bound holds for every allowed index without computing an index selector.
example : ∃ c d : ℕ, ∀ n i, i < n + 1 → (n + i) ^ 2 ≤ c * (n + 1) ^ d :=
  ComputableTidilyInPolyTime.indexed_polynomial_bound (by polytime) (by fun_prop)

-- The grid parameters and entry index may all depend on the ordinary functional input.
example : ComputableInPolyTime (fun p : ℕ × ℕ =>
    (EntropyGrid.seedLength p.1 (p.1 + 1) (p.2 + 1) p.1 p.2,
      EntropyGrid.outputLength p.1 (p.1 + 1) (p.2 + 1) p.1 p.2))
    (encPair encUnary encUnary) (encPair encUnary encUnary) := by polytime

example : ComputableInPolyTime (fun p : ℕ × List Bool =>
    EntropyGrid.generate p.1 2 1 3 p.1 (fun seed => (seed.take 1, seed.getD 1 false)) p.2)
    (encPair encUnary encBits) encBits := by polytime

example (generator : ℕ → List Bool → List Bool)
    (hgenerator : ComputableInPolyTime (fun p => generator p.1 p.2)
      (encPair encUnary encBits) encBits) :
    ComputableInPolyTime (fun p : ℕ × List Bool =>
      GeneratorPadding.generate p.1 (p.1 + 3) (generator p.1) p.2)
      (encPair encUnary encBits) encBits := by
  fail_if_success (clear hgenerator; polytime)
  polytime

-- The same slicing program also works through the framed list encoding.
example : ComputableInPolyTime (fun seed : List Bool =>
    ((seed.take 2 ++ [true]) ++ seed.drop 2).take 5) (encList encBool) encBits := by polytime

example (adversary : ℕ → List Bool → ProbComp Bool)
    (hadversary : IsPPTOn (encPair encUnary encBits) encBool
      (fun p => adversary p.1 p.2)) :
    IsPPTOn (encPair encUnary encBits) encBool (fun p : ℕ × List Bool =>
      GeneratorPadding.test p.1 (p.1 + 3) (adversary p.1) p.2) := by
  fail_if_success (clear hadversary; ppt)
  ppt

example (adversary : ℕ → List Bool → ProbComp Bool)
    (hadversary : IsPPTOn (encPair encUnary encBits) encBool
      (fun p => adversary p.1 p.2)) :
    IsPPTOn (encPair encUnary encBits) encBool (fun p : ℕ × List Bool => do
      let padding ← sampleList ((p.1 + 3) - p.1)
      adversary p.1 ((p.2 ++ padding).take (p.1 + 4))) := by ppt

private def extend (seed : List Bool) : List Bool := seed ++ [true]

private theorem extend_expands (seed : List Bool) : seed.length < (extend seed).length := by
  simp [extend]

-- This concrete expanding function is for accounting tests, with no security assumption.
example (seed : List Bool) (hseed : seed.length = 4) :
    (GeneratorPadding.generate 2 4 extend seed).length = 5 :=
  GeneratorPadding.length_generate (by decide)
    (fun seed h => by simpa only [h] using extend_expands seed) hseed

example : GeneratorPadding.generate 2 4 extend [false, true, true, false] =
    [false, true, true, true, false] := by decide

example : GeneratorPadding.generate 2 2 extend [true, false] = [true, false, true] := by decide

example : GeneratorPadding.generate 0 0 extend [] = [true] := by decide

example : GeneratorPadding.generate 2 4 extend [] = [true] := by decide

example : (uniformList 4).map (GeneratorPadding.generate 2 4 extend) =
    ((uniformList 2).map extend).bind (fun word =>
      (uniformList 2).map (fun padding => (word ++ padding).take 5)) :=
  GeneratorPadding.generate_distribution extend (by decide)

-- The complete output may be observed; the reduction preserves its advantage exactly.
example (adversary : List Bool → ProbComp Bool) :
    Game.advantage
      (((uniformList 4).map (GeneratorPadding.generate 2 4 extend)).bind
        (fun word => ProbComp.eval (adversary word)))
      ((uniformList 5).bind (fun word => ProbComp.eval (adversary word))) =
    Game.advantage
      (((uniformList 2).map extend).bind
        (fun word => ProbComp.eval (GeneratorPadding.test 2 4 adversary word)))
      ((uniformList 3).bind
        (fun word => ProbComp.eval (GeneratorPadding.test 2 4 adversary word))) :=
  GeneratorPadding.advantage_eq extend adversary (by decide) (by decide)

-- Every entry of a concrete polynomial-size grid fits one increasing efficient schedule.
example : ∃ common : ℕ → ℕ, ComputableInPolyTime common encUnary encUnary ∧
    StrictMono common ∧ (∀ n, n + 1 ≤ common n) ∧
    ∀ n index, index < EntropyGrid.size (n + 1) (16 * (n + 7)) →
      EntropyGrid.seedLength n (n + 1) 2 (16 * (n + 7)) index ≤ common n := by
  obtain ⟨common, hcommon, hmono, hself, hbound⟩ :=
    EntropyGrid.exists_common_seedLength
      (sourceBits := fun n => n + 1) (observationBound := fun _ => 2)
      (densityBound := fun n => 16 * (n + 7)) (by polytime) (by polytime) (by polytime)
  exact ⟨common, hcommon, hmono, hself, hbound⟩

end ComplexityTests.GeneratorPadding
