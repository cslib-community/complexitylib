/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import Complexity.Computability.PolyTime.CNF.CardinalityInterval
meta import Complexity.Computability.PolyTime.CNF.CardinalityInterval
meta import Complexity.Computability.Circuit.Boolean.FunctionalCNF

/-! # Actual functional size-test writing

Small tests enumerate original inputs only, then compute their unique gate trace. They never
search the auxiliary cube. Production correctness is the functional extension theorem.
-/

public section

open Cslib.Logic.PL Cslib.Circuits.Boolean Turing.MultiTapeTM

set_option linter.hashCommand false

/-- Test-only materialization of the actual deterministic gate trace. -/
@[expose] def intervalTestValues (n lo hi seed : ℕ) : List Bool :=
  let (gs, _) := CardinalityInterval.generate (n, lo, hi)
  Cslib.Circuits.evalCode interpretation false
    (List.ofFn (fun i : Fin n => Nat.testBit seed i.val)) gs

/-- Test-only input enumeration; gate variables are determined, never enumerated. -/
@[expose] def intervalTestCount (n lo hi : ℕ) : ℕ :=
  (List.range (2 ^ n)).countP fun seed =>
    let vals := intervalTestValues n lo hi seed
    (CardinalityInterval.formula (n, lo, hi)).eval (vals.getD · false)

/-- info: (1, 0, 3, 6, 8, 0) -/
#guard_msgs in
#eval (intervalTestCount 0 0 0, intervalTestCount 0 1 0,
  intervalTestCount 3 1 1, intervalTestCount 3 1 2,
  intervalTestCount 3 0 100, intervalTestCount 3 3 2)

/- Huge binary cutoffs are capped before generation: two constant gates, eight clauses. -/
/-- info: (2, 8, 0) -/
#guard_msgs in
#eval ((CardinalityInterval.generate (5, 2 ^ 512, 2 ^ 1024)).1.length,
  (CardinalityInterval.formula (5, 2 ^ 512, 2 ^ 1024)).length,
  intervalTestCount 2 (2 ^ 512) (2 ^ 1024))

example : ComputableInPolyTime CardinalityInterval.formula CardinalityInterval.encInput
    (encList (encList (encPair encNat encBool))) := CardinalityInterval.formula_polytime

example (n lo hi : ℕ) : (CardinalityInterval.circuit n lo hi).size ≤ 952 * (n + 1) :=
  CardinalityInterval.size_circuit n lo hi
