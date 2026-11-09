/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.PolyTime.CNF.WeightedComparison.Frontend
meta import CslibFrontier.Computability.PolyTime.CNF.WeightedComparison.Frontend
meta import CslibFrontier.Computability.Circuit.Boolean.FunctionalCNF

/-!
# Actual polynomial-weight functional comparison clients

Only tiny original inputs are enumerated. The actual generated full gate code is evaluated in
an array, then its complete CNF is checked on that deterministic trace. No auxiliary cube is
searched. `WeightedComparisonResources` checks the complete binary resource and distribution
continuation.
-/

public section

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.WeightedSum
open Cslib.Logic.PL

set_option linter.hashCommand false

/-- Execute every actual generated gate, retaining the complete trace for CNF checking. -/
@[expose] def weightedTrace (bits : List Bool) (code : List (Op × List ℕ)) : Array Bool :=
  code.foldl (fun vals line =>
    let (op, args) := line
    vals.push (match op with
      | .const b => b
      | .not => !(vals[args.getD 0 0]?.getD false)
      | .and => vals[args.getD 0 0]?.getD false && vals[args.getD 1 0]?.getD false
      | .or => vals[args.getD 0 0]?.getD false || vals[args.getD 1 0]?.getD false)) bits.toArray

/-- Tiny real-writer oracle, using the proved gate-list generator and array gate evaluation. -/
@[expose] def weightedCodeCount (n : ℕ) (code : List (Op × List ℕ) × List ℕ) : ℕ :=
  let f := FunctionalCNF.write (n, code, List.replicate code.2.length true)
  (List.range (2 ^ n)).countP fun seed =>
    let vals := weightedTrace (List.ofFn (fun i : Fin n => seed.testBit i.val)) code.1
    f.eval (fun i => vals[i]?.getD false)

/-- The original two-variable encoded upper/equality/strict comparison. -/
@[expose] def weightedExampleCode (op : Comparison) (target : ℤ) :=
  testCode op 1 ![2, 1] ![true, false] target

/-- Counts using nonunit weights and complementary literals on the actual original variables. -/
@[expose] def weightedExample (op : Comparison) (target : ℤ) : Circuit signature 2 1 :=
  test op 1 ![2, 1] ![true, false] target

/-- info: (2, 1, 2, 1, 1) -/
#guard_msgs in
#eval (weightedCodeCount 2 (weightedExampleCode .le 1),
  weightedCodeCount 2 (weightedExampleCode .eq 1),
  weightedCodeCount 2 (weightedExampleCode .ge 2),
  weightedCodeCount 2 (weightedExampleCode .lt 1),
  weightedCodeCount 2 (weightedExampleCode .gt 2))

/- Constant branches do not materialize enormous integer targets. -/
/-- info: (1, 4, 1, 0) -/
#guard_msgs in
#eval ((weightedExampleCode .le (2 ^ 1024)).1.length,
  weightedCodeCount 2 (weightedExampleCode .le (2 ^ 1024)),
  (weightedExampleCode .le (-(2 ^ 512))).1.length,
  weightedCodeCount 2 (weightedExampleCode .le (-(2 ^ 512))))

/- The declared zero-weight variable is free; no positive-weight premise excludes it. -/
/-- info: (2, 0) -/
#guard_msgs in
#eval (weightedCodeCount 2 (testCode .eq 1 ![0, 2] (fun _ => true) 2),
  weightedCodeCount 2 (testCode .eq 1 ![0, 2] (fun _ => true) 1))

/- Signed coefficients use their negative offset, with exact cancellation at the boundary. -/
/-- info: (2, 1, 2) -/
#guard_msgs in
#eval (weightedCodeCount 2 (testCode .eq 1 ![2, 2] ![true, false] 2),
  weightedCodeCount 2 (testCode .lt 1 ![2, 2] ![true, false] 2),
  weightedCodeCount 2 (testCode .eq 1 ![2, 0] ![false, true] 0))

/- Simultaneous tests share the same two original bits, not independent copies. -/
/-- info: (1, 0) -/
#guard_msgs in
#eval (weightedCodeCount 2 (jointCode (r := 2) (fun _ => .eq) 1
    ![![2, 1], ![1, 1]] ![![true, false], ![true, true]] ![1, 0]),
  weightedCodeCount 2 (jointCode (r := 2) (fun _ => .eq) 1
    ![![2, 1], ![1, 1]] ![![true, false], ![true, true]] ![1, 2]))

/- No test and no input each preserve exactly the empty assignment. -/
/-- info: (1, 1, 0) -/
#guard_msgs in
#eval (weightedCodeCount 0 (jointCode (n := 0) (r := 0) Fin.elim0 1 Fin.elim0 Fin.elim0 Fin.elim0),
  weightedCodeCount 0 (testCode (n := 0) .eq 1 Fin.elim0 Fin.elim0 0),
  weightedCodeCount 0 (testCode (n := 0) .gt 1 Fin.elim0 Fin.elim0 0))

example : (∑ q : Fin 4, (group ![3, 1, 0] 4 0 q).length) = 3 :=
  sum_group_lengths (by decide) _ _

example (x : Fin 2 → Bool) :
    signedValue ![2, -2] x =
      (value ![2, 2] ![true, false] x : ℤ) - 2 := by
  have hw : (fun i : Fin 2 => (![2, -2] i : ℤ).natAbs) = ![2, 2] := by decide
  have hp : (fun i : Fin 2 => decide (0 ≤ (![2, -2] i : ℤ))) = ![true, false] := by decide
  rw [signed_normalization, hw, hp]
  simp [negativeOffset, sub_eq_add_neg]

example (op : Comparison) (target : ℤ) (x : Fin 2 → Bool) :
    (weightedExample op target).eval interpretation x =
      fun _ => decide (op.Holds (value ![2, 1] ![true, false] x) target) :=
  eval_test op 1 _ _ _ target (by intro i; fin_cases i <;> decide)

example (op : Comparison) (target : ℤ) :
    (weightedExample op target).size ≤ comparisonBudget 1 * 3 :=
  size_test_linear op 1 _ _ _

example (x : Fin 2 → Bool) (σ : ℕ → Bool) (hin : ∀ i : Fin 2, σ i = x i) :
    (formula .eq 1 ![2, 1] ![true, false] 1).eval σ = true ↔
      (∀ j : Fin (2 + (test .eq 1 ![2, 1] ![true, false] 1).size), σ j =
        FunctionalCNF.wireValues (test .eq 1 ![2, 1] ![true, false] 1) x j) ∧
      (value ![2, 1] ![true, false] x : ℤ) = 1 :=
  eval_formula_iff .eq 1 ![2, 1] ![true, false] x 1
    (by intro i; fin_cases i <;> decide) σ hin

/- Actual binary frames admit the source promise and reject wrong lengths/huge coefficients. -/
/-- info: (true, false, false, true) -/
#guard_msgs in
#eval (BinaryFrontend.admit 1 (2, ([(2, true), (1, false)], -1)),
  BinaryFrontend.admit 1 (2, ([(2 ^ 512, true), (1, false)], 0)),
  BinaryFrontend.admit 1 (2, ([(0, true)], 0)),
  BinaryFrontend.admit 1 (0, ([], -(2 ^ 512))))

example : BinaryFrontend.build .eq 1
    (BinaryFrontend.ofData ![2, 1] ![true, false] 1) =
      formula .eq 1 ![2, 1] ![true, false] 1 := BinaryFrontend.build_ofData _ _ _ _ _
