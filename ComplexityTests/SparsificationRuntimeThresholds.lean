/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingPolyTime

/-!
# Tests for sparsification certificates with runtime thresholds
-/

namespace ComplexityTests.SparsificationRuntimeThresholds

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification Turing.MultiTapeTM

/-- Two clauses sharing the heart `x₁`. -/
abbrev ψ : CNF ℕ := [[(1, true), (2, true)], [(1, true), (3, true)]]

/-- The runtime parameter matters: with base `1` the heart `x₁` is heavy, with base `100` the
formula is sparse. -/
example : isSparse (countingThreshold 1) 2 ψ = false := by decide

example : isSparse (countingThreshold 100) 2 ψ = true := by decide

/-- The two counting steps for base `1` add the heart, or the petals and the negated heart. -/
example : countingNext (countingThreshold 1) 2 ψ false = [[(1, true)]] := by decide

/-- Width zero has no candidate hearts, and the empty formula is sparse, for every base. -/
example (M : ℕ) : isSparse (countingThreshold M) 0 ψ = true := by
  simp [isSparse, candidates, hearts, heavy]

example (M : ℕ) : isSparse (countingThreshold M) 2 ([] : CNF ℕ) = true := by
  simp [isSparse, candidates]

/-- A composition with a computed base: one machine branches on a formula with base `M` and then
tests the resulting child for sparseness with base `2 * M`, for every runtime `M` in binary. -/
example : ComputableInPolyTime
    (fun x : ℕ × CNF ℕ =>
      isSparse (countingThreshold (2 * x.1)) 2 (countingNext (countingThreshold x.1) 2 x.2 true))
    (encPair encNat (encList (encList (encPair encNat encBool)))) encBool := by
  have hs := computableInPolyTime_isSparse_countingThreshold encNat 2
  have hn := computableInPolyTime_countingNext_countingThreshold encNat 2
  have harg : ComputableInPolyTime
      (fun x : ℕ × CNF ℕ => (x.1, x.2, true))
      (encPair encNat (encList (encList (encPair encNat encBool))))
      (encPair encNat (encPair (encList (encList (encPair encNat encBool))) encBool)) := by
    fun_prop
  have hchild : ComputableInPolyTime
      (fun x : ℕ × CNF ℕ => countingNext (countingThreshold x.1) 2 x.2 true)
      (encPair encNat (encList (encList (encPair encNat encBool))))
      (encList (encList (encPair encNat encBool))) := by
    simpa only [Function.comp_def] using hn.comp harg
  have hbase : ComputableInPolyTime (fun x : ℕ × CNF ℕ => 2 * x.1)
      (encPair encNat (encList (encList (encPair encNat encBool)))) encNat := by
    fun_prop
  simpa only [Function.comp_def] using hs.comp (hbase.prod hchild)

/-- A runtime parameter of another type: a pair `(M, a)` selecting the thresholds `M ^ j + a`. -/
example : ComputableInPolyTime
    (fun x : (ℕ × ℕ) × CNF ℕ => isSparse (fun j => x.1.1 ^ j + x.1.2) 2 x.2)
    (encPair (encPair encNat encNat) (encList (encList (encPair encNat encBool)))) encBool := by
  refine computableInPolyTime_isSparseWith encNat (θ := fun (p : ℕ × ℕ) j => p.1 ^ j + p.2) ?_ 2
  fun_prop

end ComplexityTests.SparsificationRuntimeThresholds
