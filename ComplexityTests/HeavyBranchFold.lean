/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.GenericRAM.Native.HeavyBranchFold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Tests for heavy-variable branching and streaming common-zero accumulation

Kernel-checked (`decide`, `fun_prop`, and `ComputableInO`) regression tests for
`Cslib.GenericRAM.HeavyBranchFold` (§5.5 of [OpenAI2026ETH]).
-/

namespace Cslib.GenericRAM.HeavyBranchFold.Tests

open Cslib Cslib.BitString Cslib.Complexity Cslib.GenericRAM Cslib.GenericRAM.HeavyBranchFold
open Turing.MultiTapeTM

/-- 4-variable sparse `𝔽₂` system `{x₁ + x₁x₃ = 0, x₀x₃ + x₂x₃ + x₀x₁x₃ = 0}` with heavy variables
`heavyVarList 4 1 sys4 = [1, 3]` (incidence `2`) and free variables `[0, 2]` (incidence `1`). -/
private def sys4 : List (List (List ℕ)) := [[[1], [1, 3]], [[0, 3], [2, 3], [0, 1, 3]]]

example : varDegree 0 sys4 = 1 ∧ varDegree 1 sys4 = 2 ∧
    varDegree 2 sys4 = 1 ∧ varDegree 3 sys4 = 2 ∧ heavyVarList 4 1 sys4 = [1, 3] := by decide

-- All 4 branches on `S = [1, 3]`: `.tautology 2` (`4`), `.contradiction` (`0`),
-- `.reduced 2 [[[0], [1]]]` (`2`, relabeling `[0, 2] ↦ [0, 1]`), `.reduced 2 [[[1]]]` (`2`, mod-2).
example :
    prepareBranch 4 [1, 3] (lowBits 2 0) sys4 = .tautology 2 ∧
    branchRootCount (prepareBranch 4 [1, 3] (lowBits 2 0) sys4) = 4 ∧
    prepareBranch 4 [1, 3] (lowBits 2 1) sys4 = .contradiction ∧
    branchRootCount (prepareBranch 4 [1, 3] (lowBits 2 1) sys4) = 0 ∧
    prepareBranch 4 [1, 3] (lowBits 2 2) sys4 = .reduced 2 [[[0], [1]]] ∧
    branchRootCount (prepareBranch 4 [1, 3] (lowBits 2 2) sys4) = 2 ∧
    prepareBranch 4 [1, 3] (lowBits 2 3) sys4 = .reduced 2 [[[1]]] ∧
    branchRootCount (prepareBranch 4 [1, 3] (lowBits 2 3) sys4) = 2 := by decide

-- Streaming `BooleanFold` count matches `rootCount` and `SparseEquations.commonZeroCount` (`= 8`).
example : rootCount 4 sys4 = 8 ∧
    commonZeroCount Finset.univ (fun i : Fin sys4.length => toFinsetEquation 4 sys4[i]) = 8 ∧
    streamBranches rootCount (4, [1, 3], sys4) = (4, (2, ((4, [1, 3], sys4), 8))) ∧
    countByBranching rootCount (4, [1, 3], sys4) = rootCount 4 sys4 := by decide

/-- Poison-value oracle testing short-circuiting and reduced-system invariants (`b₀ = 1, k = 1`). -/
private def strictReducedOracle4 (n' : ℕ) (sys' : List (List (List ℕ))) : ℕ :=
  if n' == 2 && !sys'.isEmpty && decide ([] ∉ sys') && decide ([[]] ∉ sys') &&
      decide (varDegree 0 sys' ≤ 1 && varDegree 1 sys' ≤ 1) &&
      sys'.all (fun eq => eq.all fun m => decide (m.length ≤ 1)) then
    rootCount n' sys'
  else 999999

example : countByBranching strictReducedOracle4 (4, [1, 3], sys4) = 8 := by decide

/-- 5-variable cubic sparse `𝔽₂` system branched on `S = [1, 3]` (`[0, 2, 4] ↦ [0, 1, 2]`). -/
private def sys5 : List (List (List ℕ)) :=
  [[[0, 1, 4], [1, 2], []], [[2, 3, 4]], [[0, 3], [3, 4]]]

example : relabelFreeVar [1, 3] 0 = 0 ∧ relabelFreeVar [1, 3] 2 = 1 ∧
    relabelFreeVar [1, 3] 4 = 2 ∧
    prepareBranch 5 [1, 3] [false, false] sys5 = .contradiction ∧
    prepareBranch 5 [1, 3] [false, true] sys5 = .contradiction ∧
    prepareBranch 5 [1, 3] [true, false] sys5 = .reduced 3 [[[0, 2], [1], []]] ∧
    prepareBranch 5 [1, 3] [true, true] sys5 =
      .reduced 3 [[[0, 2], [1], []], [[1, 2]], [[0], [2]]] ∧
    rootCount 5 sys5 = 6 ∧ countByBranching rootCount (5, [1, 3], sys5) = 6 ∧
    streamBranches rootCount (3, [], [[[0, 1]]]) = (1, (0, ((3, [], [[[0, 1]]]), 6))) := by decide

-- Compositional `ComputableInPolyTime` checks (`@[fun_prop]`).
example : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × List (List (List ℕ)) =>
      let S := heavyVarList p.1.1 p.1.2 p.2
      prepareBranch p.1.1 S (List.replicate S.length true) p.2)
    (encPair (encPair encUnary encNat) (encList (encList (encList encNat))))
    encBranchOutcome := by fun_prop

example : ComputableInPolyTime
    (fun p : List ℕ × (List Bool × List (List ℕ)) =>
      relabelEquation p.1 (substituteEquation p.1 p.2.1 p.2.2))
    (encPair (encList encNat) (encPair encBits (encList (encList encNat))))
    (encList (encList encNat)) := by fun_prop

-- Uniform `ComputableInO` streaming instantiation with polynomial workspace (`no 2 ^ |S|` factor).
private noncomputable def zeroSolverCert :
    NativeCertificate (fun _ : ℕ × List (List (List ℕ)) => 0)
      (encPair encUnary (encList (encList (encList encNat)))) encNat :=
  NativeCertificate.const 0

example :
    let Q_solver := fun inp : BranchInput => (encBranchInput inp).length
    ComputableInO (countByBranching (fun _ _ => 0)) encBranchInput encNat
      (fun inp => stepOverhead (encBranchInput inp).length +
        (2 ^ inp.2.1.length + 1) * (stepOverhead (encBranchInput inp).length + Q_solver inp))
      (fun inp => stepOverhead (encBranchInput inp).length + Q_solver inp) ∧
    PolyBounded (fun inp => (encBranchInput inp).length)
      (fun inp => stepOverhead (encBranchInput inp).length + Q_solver inp) :=
  ⟨countByBranching_computableInO zeroSolverCert _ _
      (fun _ _ _ _ _ _ => Nat.zero_le _)
      (fun _ _ _ _ _ hred => length_enc_reduced_le hred)
      (fun _ _ _ _ _ hred => length_enc_reduced_le hred),
    polyBounded_branchWorkspace PolyBounded.self⟩

end Cslib.GenericRAM.HeavyBranchFold.Tests
