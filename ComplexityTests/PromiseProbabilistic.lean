/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BPP.Amplification
import Complexity.Computability.Complexity.Classes.Promise.Randomized
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Tests for probabilistic promise classes (`PromiseBPP`, `PromiseRP`, `PromiseCoRP`),
`probability_sampleList_verifier`, error amplification (`SolvesWithBoundedError.repeatMajority`) on
a genuinely partial promise problem, and randomized one-sided promise reductions (`RPReducible`,
`RPReducibleWithError`). -/

namespace ComplexityTests.PromiseProbabilistic

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-! ### Nonvacuous concrete instances -/

/-- A concrete `PromiseRP` solver using a real 1-bit coin flip: on `true`,
`V (b, r) = b && r.headD false` accepts `[true]` and rejects `[false]` (acceptance probability
`1 / 2`); on `false`, it rejects both coins (acceptance probability `0`). -/
example : PromiseProblem.ofSet ({true} : Set Bool) ∈ PromiseRP encBool := by
  refine ⟨1, fun p : Bool × List Bool => p.1 && p.2.headD false, by fun_prop,
    fun a => ⟨fun ha => ?_, fun ha r => ?_⟩⟩
  · obtain rfl : a = true := ha
    generalize hk : (1 : Polynomial ℕ).eval (encBool true).length = k
    rw [Polynomial.eval_one] at hk
    subst hk
    decide
  · have hfalse : a = false := by
      cases a
      · rfl
      · exfalso; exact ha rfl
    subst hfalse
    rfl

/-- A concrete randomized `RPReducible` reduction whose soundness on the no-instance `false` is
strictly between `2 / 3` and `1`: reading 2 random bits `r`,
`f (b, r) = b || (r.headD false && r.tail.headD false)` maps `true` exclusively to `true` (all 4
seeds) and maps `false` to `false` on 3 out of 4 seeds (soundness `3 / 4 ∈ (2 / 3, 1)`). -/
example : PromiseProblem.RPReducible encBool encBool
    (PromiseProblem.ofSet ({true} : Set Bool))
    (PromiseProblem.ofSet ({true} : Set Bool)) := by
  rw [PromiseProblem.rpReducible_iff_exists_seeded]
  refine ⟨2, fun p : Bool × List Bool => p.1 || (p.2.headD false && p.2.tail.headD false),
    by fun_prop, fun a ha r => ?_, fun a ha => ?_⟩
  · obtain rfl : a = true := ha
    simp
  · have hfalse : a = false := by
      cases a
      · rfl
      · exfalso; exact ha rfl
    subst hfalse
    generalize hk : (2 : Polynomial ℕ).eval (encBool false).length = k
    rw [Polynomial.eval_ofNat] at hk
    subst hk
    simp only [PromiseProblem.no_ofSet, Set.mem_compl_iff, Set.mem_singleton_iff]
    decide

/-- Edge case `s ≤ 0`: when `s a = 0`, even the constant yes-map `fun _ => pure true` (which maps
the no-instance `false` into the no-set `{false}` with probability `0`) satisfies
`RPReducibleWithError`. -/
example : PromiseProblem.RPReducibleWithError encBool encBool (fun _ => 0)
    (PromiseProblem.ofSet ({true} : Set Bool))
    (PromiseProblem.ofSet ({true} : Set Bool)) := by
  refine ⟨fun _ => pure true, (ComputableInPolyTime.const true).isPPTOn,
    fun a _ b hb => ?_, fun _ _ => ENNReal.toReal_nonneg⟩
  simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hb
  exact hb

/-! ### Error amplification on a genuinely partial promise problem -/

/-- A genuinely partial promise problem on bit strings (`yes = {[true]}`, `no = {[false]}`),
leaving `[]` outside the promise. -/
def partialSingletonBit : PromiseProblem (List Bool) where
  yes := {[true]}
  no := {[false]}
  disjoint := by simp

/-- The promise of `partialSingletonBit` is a proper subset of `Set.univ` (`[]` is outside the
promise). -/
example : partialSingletonBit.yes ∪ partialSingletonBit.no ≠ Set.univ := by
  intro h
  have hmem : ([] : List Bool) ∈ partialSingletonBit.yes ∪ partialSingletonBit.no :=
    h ▸ Set.mem_univ []
  simp [partialSingletonBit] at hmem

/-- A 1-bit verifier that returns the first input bit when present and falls back to the first
random bit on `[]`. -/
def partialVerifier (p : List Bool × List Bool) : Bool :=
  p.1.headD (p.2.headD false)

/-- On the out-of-promise input `[]`, `partialVerifier` accepts with probability `1 / 2`, violating
the `2 / 3` bounded-error margin on both sides. -/
example :
    Pr[(fun w => partialVerifier ([], w)) <$> BitString.sampleList 1] = 1 / 2 := by
  rw [probability_sampleList_verifier]
  have hcard : acceptCount partialVerifier [] 1 = 1 := by decide
  rw [hcard]
  norm_num

/-- Despite accepting the out-of-promise instance `[]` with probability `1 / 2`, `partialVerifier`
solves `partialSingletonBit` with bounded error. -/
theorem solvesWithBoundedError_partialSingletonBit :
    partialSingletonBit.SolvesWithBoundedError encBits 1 partialVerifier := by
  intro a
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · obtain rfl : a = [true] := ha
    dsimp only [BoundedErrorAt]
    generalize hk : (1 : Polynomial ℕ).eval (encBits [true]).length = k
    rw [Polynomial.eval_one] at hk
    subst hk
    decide
  · obtain rfl : a = [false] := ha
    dsimp only [BoundedErrorAt]
    generalize hk : (1 : Polynomial ℕ).eval (encBits [false]).length = k
    rw [Polynomial.eval_one] at hk
    subst hk
    decide

/-- Majority amplification (`SolvesWithBoundedError.repeatMajority`) reduces the error on
`partialSingletonBit` to `2 ^ (-q(n))` without requiring any margin outside the promise. -/
example (q : Polynomial ℕ) :
    partialSingletonBit.SolvesWithErrorExponent encBits q (12 * q * 1)
      (repeatMajority encBits (6 * q) 1 partialVerifier) :=
  solvesWithBoundedError_partialSingletonBit.repeatMajority q

end ComplexityTests.PromiseProbabilistic
