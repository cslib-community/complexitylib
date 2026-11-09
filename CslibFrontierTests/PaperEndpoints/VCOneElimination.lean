/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.VCOneElimination
public import CslibFrontierTests.PaperEndpoints.VCOne
public import CslibFrontierTests.PaperEndpoints.ExactOneElimination
meta import CslibFrontierTests.PaperEndpoints.VCOne
meta import CslibFrontierTests.PaperEndpoints.ExactOneElimination
meta import CslibFrontier.Logics.Propositional.CNF.VCOneElimination
meta import Mathlib.Data.Fintype.Basic
meta import Mathlib.Data.Fintype.Sum
meta import Mathlib.Data.Fintype.Pi
meta import Mathlib.Data.Fintype.Card
meta import Mathlib.Data.Finset.Insert

/-! Execute the full table-to-plan compiler on actual overlapping table inputs. -/

public section

open Cslib.Logic.PL Cslib.Logic.PL.VCOne

set_option linter.hashCommand false

/- Two overlapping tables derive two original equations, then execute elimination
and compile two queries. Both values of the unused fifth bit are counted. -/
/-- info: (2, 4) -/
#guard_msgs in
#eval ((equationList (fun _ : Fin 2 => 3) overlapTable).length,
  (tablePlan (fun _ => 3) overlapScope overlapTable).execute (fun _ => bruteCount))

open scoped Classical in
/-- The same executed plan has the exact original global count. -/
example : (tablePlan (fun _ : Fin 2 => 3) overlapScope overlapTable).value =
    Fintype.card {x : Fin 5 → Bool // Satisfies (fun _ : Fin 2 => 3)
      overlapScope overlapTable x} :=
  tablePlan_correct _ _ _ (fun t => oneTable_dimension (t == 0))

/-- Its syntax bounds use five global bits, despite overlapping local scopes. -/
example : (tablePlan (fun _ : Fin 2 => 3) overlapScope overlapTable).Budget 5 :=
  tablePlan_budget _ _ _

/- Empty zero-width tables reject, while the singleton zero-width table allows
both assignments on one declared global bit. -/
/-- info: (0, 2) -/
#guard_msgs in
#eval ((tablePlan (fun _ : Fin 1 => 0)
    (fun _ => Function.Embedding.ofIsEmpty : (i : Fin 1) → Fin 0 ↪ Fin 1)
    (fun _ => (∅ : Finset (Fin 0 → Bool)))).execute (fun _ => bruteCount),
  (tablePlan (fun _ : Fin 1 => 0)
    (fun _ => Function.Embedding.ofIsEmpty : (i : Fin 1) → Fin 0 ↪ Fin 1)
    (fun _ => ({fun _ => false} : Finset (Fin 0 → Bool)))).execute (fun _ => bruteCount))

/- A 32-coordinate scope given by just two explicit tuples. This executes local
listing, finite row numbering and the global compiler without forming 2^32 tuples. -/
/-- info: 0 -/
#guard_msgs in
#eval (equationList (fun _ : Fin 1 => 32) (fun _ => wideTwoRows)).length

/- The wide no-equation branch emits a direct binary side query on the declared bits. -/
/-- info: (2, 32, 2048, 1) -/
#guard_msgs in
#eval shape (tablePlan (fun _ : Fin 1 => 32) (fun _ => Function.Embedding.refl _)
  (fun _ => wideTwoRows))

/-- info: 4 -/
#guard_msgs in
#eval (binaryTablePlan (fun _ : Fin 2 => 3) overlapScope overlapTable).execute
  (fun _ => bruteCount)

open scoped Classical in
/-- Binary selection composes with actual overlapping tables. -/
example : (binaryTablePlan (fun _ : Fin 2 => 3) overlapScope overlapTable).value =
    Fintype.card {x : Fin 5 → Bool // Satisfies (fun _ : Fin 2 => 3)
      overlapScope overlapTable x} :=
  binaryTablePlan_correct _ _ _ (fun t => oneTable_dimension (t == 0))

example : (binaryTablePlan (fun _ : Fin 2 => 3) overlapScope overlapTable).Budget 5 :=
  binaryTablePlan_budget _ _ _

/-- info: (5, 2, 2) -/
#guard_msgs in
#eval ((tablePayload (fun _ : Fin 2 => 3) overlapScope overlapTable).1,
  (tablePayload (fun _ : Fin 2 => 3) overlapScope overlapTable).2.length,
  (equationPayload (fun _ : Fin 2 => 3) overlapScope overlapTable).length)

/- The actual serialized plan declares five source and one auxiliary bit. -/
/-- info: 6 -/
#guard_msgs in
#eval match binaryTablePayload (fun _ : Fin 2 => 3) overlapScope overlapTable with
  | .inl _ => 0
  | .inr (n, _, _) => n

/-- Framing separates empty rows, empty tables, and differing declarations. -/
example : encTablePayload (0, [(0, [[]], [])]) ≠
    encTablePayload (0, [(0, [], [])]) := by decide

example : encPlanPayload (Sum.inl 0) ≠ encPlanPayload (Sum.inr (0, [], [])) := by decide

/-- Coordinate-volume bounds require the actual dimension promise. -/
example {a : ℕ} (R : Finset (Fin a → Bool)) (hR : DimensionOne R) :
    prefixCandidates R (List.finRange a) * (a + 1) * a ≤
      2 * a * (a + 1) * (a + 1) * a :=
  prefix_comparison_coordinates_le R hR

/-- Shared columns keep their individual signs; the unused column is explicit. -/
example : payloadRows 3 [[(0, true), (1, false)], [(0, false)]] =
    [[1, -1, 0], [-1, 0, 0]] := by decide

example : payloadRhs [[(0, true), (1, false)], [(0, false)]] = [0, 0] := by decide

example : payloadConsistent 1 [[(0, true)], [(0, false)]] = false := by decide

example : payloadConsistent 0 [[]] = false := by decide

example : payloadConsistent 3 [] = true := by decide

open Turing.MultiTapeTM in
example : ComputableInPolyTime (fun p : ℕ × List (List (ℕ × Bool)) =>
    payloadConsistent p.1 p.2) (encPair encUnary encSignedCNF) encBool :=
  payloadConsistent_polytime
