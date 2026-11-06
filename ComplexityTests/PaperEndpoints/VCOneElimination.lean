/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.VCOneElimination
public import ComplexityTests.PaperEndpoints.VCOne
public import ComplexityTests.PaperEndpoints.ExactOneElimination
meta import ComplexityTests.PaperEndpoints.VCOne
meta import ComplexityTests.PaperEndpoints.ExactOneElimination
meta import Complexity.Logics.Propositional.CNF.VCOneElimination
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
