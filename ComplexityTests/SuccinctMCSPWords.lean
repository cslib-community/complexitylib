/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.MCSP.SuccinctNP.Words

/-!
# Tests: a binary NP language for succinct MCSP

The same binary `NP` language accepts an encoded zero-gate identity instance and rejects an
encoded contradictory sample set. The identity membership is witnessed by an explicit circuit
certificate, while every certificate for the contradictory instance is rejected.
-/

namespace ComplexityTests.SuccinctMCSPWords

open Cslib Cslib.Circuits.Boolean Cslib.Complexity Turing.MultiTapeTM

private def identityInstance : SuccinctMCSP.Instance :=
  ⟨1, {(![false], false), (![true], true)}, 0⟩

private def contradictoryInstance : SuccinctMCSP.Instance :=
  ⟨1, {(![false], false), (![false], true)}, 0⟩

private theorem contradictory_not_mem : contradictoryInstance ∉ SuccinctMCSP :=
  SuccinctMCSP.notMem_of_mem_samples (y := ![false]) (by decide) (by decide)

-- Extract one binary NP language and test both sides of its agreement with succinct MCSP.
example : ∃ L : Language Bool, (L : Set (List Bool)) ∈ NP encBits ∧
    SuccinctMCSP.enc identityInstance ∈ L ∧
    SuccinctMCSP.enc contradictoryInstance ∉ L := by
  obtain ⟨L, hL, hagree⟩ := SuccinctMCSP.exists_language_mem_NP
  refine ⟨L, hL, (hagree _).mp ?_, fun h => contradictory_not_mem ((hagree _).mpr h)⟩
  exact SuccinctMCSP.mem_of_verifier_eq_true
    (w := certificate 1 0 [] 0) (by decide)

-- Soundness rules out every certificate, including words longer than the prescribed NP bound.
example (w : List Bool) : SuccinctMCSP.verifier (contradictoryInstance, w) = false :=
  Bool.eq_false_iff.mpr fun hw =>
    contradictory_not_mem (SuccinctMCSP.mem_of_verifier_eq_true hw)

end ComplexityTests.SuccinctMCSPWords
