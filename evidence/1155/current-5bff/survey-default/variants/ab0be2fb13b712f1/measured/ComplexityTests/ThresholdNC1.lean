/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Boolean.ModMajority
public import Complexity.Computability.Circuit.Boolean.ThresholdNC1
public import Complexity.Computability.Circuit.Boolean.Smolensky.Majority
public import Complexity.Foundations.Data.Nat.PolynomialBound.Log


import Diag1155.Measure
/-!
# Threshold simulation regression tests

Concrete majority families satisfy the polynomial size and fan-in hypotheses. Boundary inputs
cover the carry-save and modular-to-majority milestones.
-/


diag1155_install
@[expose] public section

namespace ComplexityTests.ThresholdNC1

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

example : AC0Mod 3 ⊂ TC0 :=
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  Smolensky.AC0Mod_ssubset_TC0 (by decide)

example : Language.ofSlices majority ∈ NC 1 := majority_mem_NC_one

example : (majorityDeMorganCircuit 3).eval interpretation ![true, false, true] 0 = true ∧
    (majorityDeMorganCircuit 3).eval interpretation ![false, false, true] 0 = false := by
  simp only [eval_majorityDeMorganCircuit]
  decide

-- Empty majority is true under the library's inclusive cutoff convention; an impossible
-- cutoff is false, including on an empty input.
example : (majorityDeMorganCircuit 0).eval interpretation Fin.elim0 0 = true := by
  simp only [eval_majorityDeMorganCircuit]
  decide

example : (thresholdDeMorganCircuit 0 1).eval interpretation Fin.elim0 0 = false := by
  simp only [eval_thresholdDeMorganCircuit]
  decide

example : (thresholdDeMorganCircuit 3 4).eval interpretation ![true, true, true] 0 = false := by
  simp only [eval_thresholdDeMorganCircuit]
  decide

example : PolynomiallyBounded (fun n => Nat.clog 2 (n ^ 3 + 1)) := by fun_prop

theorem majority_family (n : ℕ) :
    ∃ C : Circuit Unbounded.extSignature n 1,
      C.Computes (Unbounded.extInterpretation majority)
        (single ((Language.ofSlices majority).slice n)) ∧
      C.depth ≤ 1 * (Nat.log 2 n + 1) ^ 0 ∧ C.size ≤ 1 ∧ C.FanInAtMost n := by
  refine ⟨Circuit.oneGate (.gate n) id, ?_, ?_, le_rfl, ?_⟩
  · intro x
    funext j
    rw [Language.slice_ofSlices]
    rfl
  · simp
  · exact ⟨trivial, le_rfl⟩

-- Both transport theorems have a nonconstant language instance at every input length.
example : Language.ofSlices majority ∈ NC 1 :=
  mem_NC_succ_of_majority_fanInAtMost (i := 0) (s := fun _ => 1) (F := id)
    (by fun_prop) (by fun_prop) majority_family

example : Language.ofSlices majority ∈ NC 1 := by
  apply mem_NC_succ_of_threshold_fanInAtMost (i := 0) (c := 1) (s := fun _ => 1)
    (F := id) (by fun_prop) (by fun_prop)
  intro n
  obtain ⟨C, hc, hd, hs, hf⟩ := majority_family n
  exact ⟨C.mapOp Threshold.ofMajority, hc.mapOp,
    by simpa using hd, by simpa using hs, by simpa using hf⟩

end ComplexityTests.ThresholdNC1

