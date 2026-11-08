/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import Complexity.Computability.Complexity.FineGrained.VCOneCountingResources
public import ComplexityTests.PaperEndpoints.VCOne
meta import Complexity.Computability.PolyTime.CNF.VCOneDispatch
meta import Complexity.Computability.PolyTime.CNF.ExactOnePlan
meta import ComplexityTests.PaperEndpoints.VCOne

/-! # Actual table dispatcher: original counts, all branch shapes and complete resources

Exhaustive counting below is a small test oracle only. The production theorem instantiates the
proved sharp native counter and never enumerates the original assignment cube.
-/

public section

open Cslib.Logic.PL Cslib.Logic.PL.VCOne Turing.MultiTapeTM

set_option linter.hashCommand false

/-- Exhaustive small test oracle, excluded from every production algorithm. -/
@[expose] def tableBrute (n : ℕ) (q : CNF ℕ) : ℕ :=
  (List.range (2 ^ n)).countP fun x => q.eval (Nat.testBit x)

/-- Test-only execution of a tagged output using the exhaustive oracle. -/
@[expose] def tableReadback : WeightedRow.BinaryPlan.Output → ℕ
  | .inl a => a
  | .inr (n, (qf, qt)) => tableBrute n qf - tableBrute n qt

/-- info: (1, 0, 1, 0) -/
#guard_msgs in
#eval (tableReadback (ExactOne.BinaryPlan.compile (0, ([], []))),
  tableReadback (ExactOne.BinaryPlan.compile (0, ([[]], []))),
  tableReadback (ExactOne.BinaryPlan.compile (1, ([], [[(0, true)]]))),
  tableReadback (ExactOne.BinaryPlan.compile (1, ([], [[(0, true), (0, false)], []]))))

/- No constraints writes a binary count rather than enumerating 2^256 assignments. -/
/-- info: (true, 257) -/
#guard_msgs in
#eval let p := ExactOne.BinaryPlan.compile (256, ([], []))
      (p.isLeft, (encNat (p.getLeft?.getD 0)).length)

/- Contradiction, full-rank Boolean candidate, fractional candidate, and inconsistent rows. -/
/-- info: (0, 1, 0, 0) -/
#guard_msgs in
#eval (tableReadback (ExactOne.BinaryPlan.compile (3, ([[]], []))),
  tableReadback (ExactOne.BinaryPlan.compile (2, ([], [[(0, true)], [(1, false)]]))),
  tableReadback (ExactOne.BinaryPlan.compile (3, ([],
    [[(0, true), (1, true)], [(0, true), (2, true)], [(1, true), (2, true)]]))),
  tableReadback (ExactOne.BinaryPlan.compile (2, ([], [[(0, true)], [(0, false)]]))))

/- Rank zero retains the side formula and unused bits; a deficient row writes both path queries. -/
/-- info: (false, 4, false, 3) -/
#guard_msgs in
#eval let a := ExactOne.BinaryPlan.compile (3, ([[(0, true)]], []))
      let b := ExactOne.BinaryPlan.compile (3, ([], [[(0, true), (1, true), (2, true)]]))
      (a.isLeft, tableReadback a, b.isLeft, tableReadback b)

/- Original overlapping tables have opposite signs on shared columns and one unused declared bit. -/
/-- info: (false, 4) -/
#guard_msgs in
#eval let p := BinaryFrontend.compile
        (tablePayload (fun _ : Fin 2 => 3) overlapScope overlapTable)
      (p.isLeft, tableReadback p)

/- Empty table, zero-width tautology, no tables, and two contradictory overlapping tables. -/
/-- info: (0, 32, 32, 0) -/
#guard_msgs in
#eval (tableReadback (BinaryFrontend.compile (5, [(0, [], [])])),
  tableReadback (BinaryFrontend.compile (5, [(0, [[]], [])])),
  tableReadback (BinaryFrontend.compile (5, [])),
  tableReadback (BinaryFrontend.compile (3,
    [(3, [[false, false, true], [false, true, false], [true, false, false]], [0, 1, 2]),
      (3, [[true, true, false], [true, false, true], [false, true, true]], [0, 1, 2])])))

example : ComputableInPolyTime BinaryFrontend.compile encTablePayload
    ExactOne.BinaryPlan.encOutput := BinaryFrontend.compile_polytime

example : WeightedRow.BinaryPlan.WithinBudget 5 1
    (BinaryFrontend.compile (tablePayload (fun _ : Fin 2 => 3) overlapScope overlapTable)) :=
  BinaryFrontend.compile_withinBudget _ _ _ (fun i => oneTable_dimension (i == 0))

open Classical in
/-- Original-count client uses the actual constructor, with no supplied rank or output. -/
example : WeightedRow.BinaryPlan.Output.count
    (BinaryFrontend.compile (tablePayload (fun _ : Fin 2 => 3) overlapScope overlapTable)) =
      Fintype.card {x : Fin 5 → Bool // Satisfies (fun _ : Fin 2 => 3)
        overlapScope overlapTable x} :=
  BinaryFrontend.compile_count _ _ _ (fun i => oneTable_dimension (i == 0))

open Classical in
/-- The resource theorem supplies one actual algorithm, exact original counts, and uniform
polynomial space/time constants over all promised tables, not just the test fixtures. -/
example : ∃ count : (ℕ × List BinaryFrontend.Table) → ℕ,
    ∃ cs : Cslib.GenericRAM.NativeCertificate count encTablePayload encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encTablePayload x).length + 1) ^ e) ∧
      ∀ {r m : ℕ} (w : Fin m → ℕ) (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
        (R : (i : Fin m) → Finset (Fin (w i) → Bool)) (_hR : ∀ i, DimensionOne (R i)),
        let x := tablePayload w scope R
        count x = Fintype.card {σ : Fin r → Bool // Satisfies w scope R σ} ∧
          cs.time x ≤ C * ((encTablePayload x).length + 1) ^ e *
            2 ^ (A * Nat.logLogSqrtLogScale r) := BinaryFrontend.exists_count_sharp_certificate
