/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module

public import Complexity.Init
import Complexity.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceCounter

/-! # Concrete Nonvacuity Tests for `BoundedIncidenceCounter` -/

set_option linter.privateModule false

namespace Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.Tests

open Cslib Cslib.Complexity.SubexponentialSAT.SparsePolyCounter
open Cslib.Complexity.BranchedSparseCNFCounter Turing.MultiTapeTM

example : ReplacementParams.auxDim 2 < 2 := auxDim_lt_self_of_two_le (by decide)
example : ReplacementParams.auxDim 16384 < 16384 := auxDim_lt_self_of_two_le (by decide)

private def malformedBranchInput : BranchEvalInput := ((0, 1), (0, 0, 0, 0), (1, 1, 2, 0), [])
private def validEmptySysBranchInput : BranchEvalInput := ((1, 1), (1, 1, 1, 1), (1, 1, 2, 0), [])

example : validBranchEvalParams malformedBranchInput = false := by decide +kernel
example : evalBoundedIncidenceBranch malformedBranchInput = 0 := by decide +kernel
example : evalBoundedIncidenceBranch validEmptySysBranchInput ≤ 2 ^ 1 :=
  evalBoundedIncidenceBranch_le_two_pow validEmptySysBranchInput

example : ComputableInO evalBoundedIncidenceBranch encBranchEvalInput encNat
    boundedIncidenceBranchCertificate.time boundedIncidenceBranchCertificate.space :=
  boundedIncidenceBranchCertificate.computes

example : ∃ C d : ℕ, ∀ x : BranchEvalInput,
    boundedIncidenceBranchCertificate.space x ≤ C * ((encBranchEvalInput x).length + 1) ^ d :=
  polyBounded_boundedIncidenceBranchCertificate_space.exists_le

example : ∃ N₀_br C_br d_br A_br : ℕ, ∀ n' : ℕ, ∀ sys' : List (List (List ℕ)),
    checkBranchFeasible 16384 (n', sys') = true → N₀_br ≤ n' →
    sysMaxDegree sys' ≤ 3 → sys'.length ≤ 4 * n' →
    branchMaxFactorIncidence n' sys' ≤ 4 * Nat.clog 2 n' ^ 2 →
    branchMaxFactorWidth n' sys' ≤ 4 * Nat.clog 2 n' ^ 2 →
    (boundedIncidenceBranchCertificate.time (prepareBranchEvalInput (n', sys')) : ℝ) ≤
      (C_br : ℝ) * ((encPair encUnary (encList (encList (encList encNat))) (n', sys')).length +
        1 : ℝ) ^ d_br * (2 : ℝ) ^ ((A_br : ℝ) * interpolationScale n') :=
  exists_boundedIncidenceBranchCertificate_time_bound 16384 3 2 4

example : BranchPolylogTimeBound 16384 boundedIncidenceBranchCertificate :=
  branchPolylogTimeBound_boundedIncidenceBranchCertificate 16384

private theorem branchBound16384 (n' : ℕ) (eqs' : List (List (List ℕ)))
    (_ : checkBranchFeasible 16384 (n', eqs') = true) :
    evalBoundedIncidenceBranch (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n' :=
  evalBoundedIncidenceBranch_le_two_pow (prepareBranchEvalInput (n', eqs'))

example : ∃ N₀_leaf N₀_top C_t d_t A_t : ℕ, 1 ≤ A_t ∧
    ∀ x : (Unit × ℕ) × Logic.PL.CNF ℕ, x.2.length ≤ leafOccBound 3 x.1.2 * x.1.2 + 1 →
      ((branchedSparseCNFDeclaredCertificate 3 N₀_leaf N₀_top 16384
          boundedIncidenceBranchCertificate branchBound16384).time x : ℝ) ≤
        (C_t : ℝ) * ((encPair (encPair Universal.encUnit encUnary) encCNF x).length + 1 : ℝ) ^
          d_t * (2 : ℝ) ^ ((A_t : ℝ) * interpolationScale x.1.2) ∧
      ((branchedSparseCNFLeafCertificate 3 N₀_leaf N₀_top 16384
          boundedIncidenceBranchCertificate branchBound16384).time x : ℝ) ≤
        (C_t : ℝ) * ((encPair (encPair Universal.encUnit encUnary) encCNF x).length + 1 : ℝ) ^
          d_t * (2 : ℝ) ^ ((A_t : ℝ) * interpolationScale x.1.2) :=
  exists_branchedSparseCNF_time_bound 3 16384 boundedIncidenceBranchCertificate branchBound16384
    polyBounded_boundedIncidenceBranchCertificate_space
    (branchPolylogTimeBound_boundedIncidenceBranchCertificate 16384)

end Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.Tests
