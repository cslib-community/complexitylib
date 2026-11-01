/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Init
import Complexity.Computability.PolyTime.BooleanAnalysis.IncidenceBranching
import Complexity.Computability.GenericRAM.Native.ExhaustiveCountFallback
import Complexity.Computability.PolyTime.BooleanAnalysis.SparsePolyCounter

/-! # Tests for the high-incidence branching of Lemma D.2 -/

set_option linter.privateModule false

namespace Cslib.Complexity.SubexponentialSAT.IncidenceBranching.Tests

open Cslib Cslib.Complexity Cslib.GenericRAM Cslib.Complexity.SubexponentialSAT.IncidenceBranching
open Turing.MultiTapeTM

/-- `x₀ + x₁ = 0`, `x₀ x₁ = 0`, `x₀ x₂ = 0`: variable `0` lies in all three scopes and
`N₀ = 6`. -/
private def sys : List (List (List ℕ)) := [[[0], [1]], [[0, 1]], [[0, 2]]]

-- On `16` variables, `λ = 4`, so `D* = max{1, ⌈6/16⌉} ⌈√4⌉ = 2` and only variable `0` is above it.
example : threshold 16 sys = 2 ∧ branchVars 16 sys = [0] := by decide +kernel

-- On `5` variables, `D* = ⌈6/5⌉ ⌈√3⌉ = 4`, and nothing is above it.
example : threshold 5 sys = 4 ∧ branchVars 5 sys = [] := by decide +kernel

/-- The system satisfies the hypotheses of Lemma D.2 with `k = 2` and `c = 1` on `16` variables. -/
private theorem isSparseSystem_sys : IsSparseSystem 2 1 16 sys :=
  ⟨by decide, SparsePolyCounter.checkCanonicalSystem_eq_true_iff.mp (by decide), by decide,
    by decide +kernel, by decide⟩

-- `D* ≤ λ ^ (c + 2)`, since `c k = 2 ≤ λ = 4`.
example : threshold 16 sys ≤ Nat.clog 2 16 ^ 3 :=
  threshold_le_pow isSparseSystem_sys (by norm_num) (by decide)

-- Fixing `x₀ = 0` leaves `x₁ = 0` on the `15` relabeled free variables.
private theorem isReducedBranch_false : IsReducedBranch 16 sys 15 [[[0]]] :=
  ⟨[false], by decide +kernel, by decide +kernel⟩

-- Fixing `x₀ = 1` leaves `1 + x₁ = 0`, `x₁ = 0`, `x₂ = 0`, relabeled.
example : IsReducedBranch 16 sys 15 [[[], [0]], [[0]], [[1]]] :=
  ⟨[true], by decide +kernel, by decide +kernel⟩

-- The branching instance: since `16 ≥ 5` and `2 ^ ((c + 1) k) = 16 ≤ 16`, the branch satisfies the
-- branch solver's hypotheses with constant `2 c + 4 = 6`, and keeps half of the variables.
example : IsSparseBranch 2 6 15 [[[0]]] ∧ 16 ≤ 2 * 15 :=
  isSparseBranch_of_isReducedBranch isSparseSystem_sys (by norm_num) (by norm_num)
    isReducedBranch_false

/-- `x₀ + x₁ = 0`, `x₀ x₁ + x₂ = 0`, `x₀ x₂ = 0` on `7` variables: `D* = 2` and variable `0` is in
three scopes. Both of its values leave a reduced branch, and the system has `2 ^ 4 = 16` common
zeros, all with `x₀ = x₁ = x₂ = 0`. -/
private def sys7 : List (List (List ℕ)) := [[[0], [1]], [[0, 1], [2]], [[0, 2]]]

example : branchVars 7 sys7 = [0] ∧
    HeavyBranchFold.prepareBranch 7 [0] [false] sys7 = .reduced 6 [[[0]], [[1]]] ∧
    HeavyBranchFold.prepareBranch 7 [0] [true] sys7 =
      .reduced 6 [[[], [0]], [[0], [1]], [[1]]] := by
  decide +kernel

/-- The exhaustive counter, as a branch solver. -/
private def exhaustive (n' : ℕ) (sys' : List (List (List ℕ))) : ℕ :=
  ExhaustiveCountFallback.countSystemExhaustive (n', sys')

-- The counter with the exhaustive branch solver returns the count.
example : count exhaustive 7 sys7 = 16 := by decide +kernel

private theorem exhaustive_eq (n' : ℕ) (sys' : List (List (List ℕ))) :
    exhaustive n' sys' = HeavyBranchFold.rootCount n' sys' :=
  SparsePolyCounter.countSystemExhaustive_eq_rootCount n' sys'

-- Exactness through any solver that is exact on reduced branches.
example : count exhaustive 7 sys7 = HeavyBranchFold.rootCount 7 sys7 :=
  count_eq_rootCount (by decide) fun n' sys' _ => exhaustive_eq n' sys'

-- The resource interface accepts an actual solver certificate: the exhaustive counter is bounded
-- by `2 ^ n'`, so the counter has a certificate charging `2 ^ |S| + 1` solver calls in time and
-- one in space.
example : ∃ K : ℕ, ∃ cs : NativeCertificate (fun p : ℕ × List (List (List ℕ)) =>
      count exhaustive p.1 p.2) (encPair encUnary (encList (encList (encList encNat)))) encNat,
    ∀ (n : ℕ) (sys : List (List (List ℕ))) (R Q : ℕ),
      (∀ n' sys', IsReducedBranch n sys n' sys' →
        ExhaustiveCountFallback.countSystemExhaustiveCertificate.time (n', sys') ≤ R ∧
          ExhaustiveCountFallback.countSystemExhaustiveCertificate.space (n', sys') ≤ Q) →
      cs.time (n, sys) ≤ (2 ^ (branchVars n sys).length + 1) *
          (K * ((encPair encUnary (encList (encList (encList encNat))) (n, sys)).length + 1) ^ K +
            R) ∧
        cs.space (n, sys) ≤
          K * ((encPair encUnary (encList (encList (encList encNat))) (n, sys)).length + 1) ^ K +
            Q := by
  obtain ⟨K, hK⟩ := exists_count_certificate
  exact ⟨K, hK exhaustive ExhaustiveCountFallback.countSystemExhaustiveCertificate
    fun n' sys' => (exhaustive_eq n' sys').trans_le (HeavyBranchFold.rootCount_le_two_pow n' sys')⟩

end Cslib.Complexity.SubexponentialSAT.IncidenceBranching.Tests
