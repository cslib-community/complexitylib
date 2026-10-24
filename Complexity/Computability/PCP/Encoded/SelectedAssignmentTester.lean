/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.AssignmentTester
public import Complexity.Computability.PCP.AssignmentTester.Selection
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Executable six-query assignment testing

The selected tester reuses the executable coefficient table and the shared five-check family.
Its coin string retains the original product coins together with a branch in `Fin 5`. Only the
selected branch's six padded queries are read. All supplied data are charged by the certificates;
as in `Encoded.AssignmentTester`, polynomial time is for each fixed alphabet, not uniformly in
the alphabet size.

## Main definitions

* `Cslib.PCP.Encoded.SelectedHadamardTester.localTest`: the executable selected tester.
* `Cslib.PCP.Encoded.SelectedHadamardTester.query`, `.accepts`: query and decision algorithms.

## Main results

* `Cslib.PCP.Encoded.SelectedHadamardTester.localTest_eq`: exact interpretation.
* `Cslib.PCP.Encoded.SelectedHadamardTester.isPolyTime_query`, `.isPolyTime_accepts`: efficiency
  certificates uniform in the supplied constraint, coins, and answers.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.SelectedHadamardTester

open Cslib.PCP.HadamardTester Turing.MultiTapeTM

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Select a check using executable quadratic coefficients. -/
def localTest (constraint : α → α → Bool) :
    LocalTest (Pos α) (Fin 5 × Rand α) (Fin 6) Bool :=
  LocalTest.mix (checks (Encoded.HadamardTester.equationCoeff constraint))

/-- The executable selected tester agrees exactly with the mathematical one. -/
theorem localTest_eq (constraint : α → α → Bool) :
    localTest constraint = selectedHadamardTester (fun a b ↦ constraint a b = true) := by
  simp only [localTest, Encoded.HadamardTester.equationCoeff_eq, selectedHadamardTester]

/-- Compute one of the six queries for the specified branch and product coins. -/
def query (constraint : α → α → Bool) (coins : Fin 5 × Rand α) (i : Fin 6) : Pos α :=
  (localTest constraint).query coins i

/-- Decide the selected check, ignoring padding answers. -/
def accepts (constraint : α → α → Bool) (coins : Fin 5 × Rand α)
    (answers : Fin 6 → Bool) : Bool :=
  @decide ((localTest constraint).Accepts coins answers) (by
    rcases coins with ⟨i, coins⟩
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ Fin.cases ?_
      (fun i ↦ Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ Fin.elim0 i) i) i) i) i) i
    all_goals
      unfold localTest LocalTest.mix checks LocalTest.comapRand LocalTest.padQueries
        LocalTest.reindexQueries LocalTest.map blrTest tensorTest equationTest inputTest
      dsimp
      infer_instance)

/-- Computed queries agree with the selected mathematical tester. -/
theorem query_eq (constraint : α → α → Bool) (coins : Fin 5 × Rand α) (i : Fin 6) :
    query constraint coins i =
      (selectedHadamardTester (fun a b ↦ constraint a b = true)).query coins i := by
  rw [query, localTest_eq]

/-- The executable decision expresses exactly the selected acceptance predicate. -/
@[simp]
theorem accepts_eq_true (constraint : α → α → Bool) (coins : Fin 5 × Rand α)
    (answers : Fin 6 → Bool) : accepts constraint coins answers = true ↔
      (selectedHadamardTester (fun a b ↦ constraint a b = true)).Accepts coins answers := by
  simp only [accepts, decide_eq_true_eq, localTest_eq]

/-- Query generation charges the runtime constraint, selected branch, and product coins. -/
@[fun_prop]
theorem isPolyTime_query (coinsEncoding : (Fin 5 × Rand α) ↪ List Bool)
    (queryEncoding : Fin 6 ↪ List Bool) (positionEncoding : Pos α ↪ List Bool) :
    ComputableInPolyTime
      (fun p : (α → α → Bool) × (Fin 5 × Rand α) × Fin 6 ↦ query p.1 p.2.1 p.2.2)
      (encPair (encPi (encPi encBool)) (encPair coinsEncoding queryEncoding)) positionEncoding :=
  ComputableInPolyTime.of_finite _

/-- Acceptance charges the full supplied input, including all six answers. -/
@[fun_prop]
theorem isPolyTime_accepts (coinsEncoding : (Fin 5 × Rand α) ↪ List Bool) :
    ComputableInPolyTime
      (fun p : (α → α → Bool) × (Fin 5 × Rand α) × (Fin 6 → Bool) ↦ accepts p.1 p.2.1 p.2.2)
      (encPair (encPi (encPi encBool)) (encPair coinsEncoding (encPi encBool))) encBool :=
  ComputableInPolyTime.of_finite _

end Cslib.PCP.Encoded.SelectedHadamardTester
