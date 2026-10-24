/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.AssignmentTester
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Executable Hadamard assignment testing

A constraint given as a Boolean table determines the same assignment tester as
`PCP.hadamardTester`, with executable queries and acceptance. Compatibility is decided by
enumerating the finitely many assignments to the two ends. The remaining query operations and
the five checks reuse the mathematical tester's computational definitions.

The alphabet is fixed independently of the runtime input. The finite input and output types
therefore give polynomial-time certificates for the explicit algorithms. These certificates do
not assert uniform polynomial dependence on the alphabet size, and no decoding choice occurs in
the executable definitions.

## Main definitions

* `Cslib.PCP.Encoded.HadamardTester.equationCoeff`: executable quadratic coefficients.
* `Cslib.PCP.Encoded.HadamardTester.localTest`: the five executable constituent tests.
* `Cslib.PCP.Encoded.HadamardTester.query`, `.accepts`: the actual queries and Boolean decision.

## Main results

* `Cslib.PCP.Encoded.HadamardTester.localTest_eq`: exact agreement with the mathematical tester.
* `Cslib.PCP.Encoded.HadamardTester.isPolyTime_query`, `.isPolyTime_accepts`: certificates with
  the constraint, coins, and replies supplied at runtime.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.HadamardTester

open Finset
open Cslib.PCP.HadamardTester Turing.MultiTapeTM
open scoped BigOperators

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Decide compatibility by checking every assignment to the two endpoint variables. -/
def compatible (constraint : α → α → Bool) (p q : Fin 2 × α) : Bool :=
  decide (∃ σ : Fin 2 → α, constraint (σ 0) (σ 1) = true ∧ σ p.1 = p.2 ∧ σ q.1 = q.2)

/-- The executable check expresses the original existential compatibility condition. -/
@[simp]
theorem compatible_eq_true (constraint : α → α → Bool) (p q : Fin 2 × α) :
    compatible constraint p q = true ↔
      Cslib.PCP.HadamardTester.Compatible (fun a b => constraint a b = true) p q := by
  simp [compatible, Cslib.PCP.HadamardTester.Compatible]

/-- The quadratic system of a Boolean constraint, computed by finite compatibility checks. -/
def equationCoeff (constraint : α → α → Bool) :
    (Fin 2 × α) × (Fin 2 × α) ⊕ Fin 2 → (Fin 2 × α) × (Fin 2 × α) → Bool :=
  Sum.elim (fun q => if compatible constraint q.1 q.2 then 0 else Pi.single q true)
    fun b => ∑ a, Pi.single ((b, a), (b, a)) true

/-- The executable coefficients agree exactly with the original quadratic system. -/
theorem equationCoeff_eq (constraint : α → α → Bool) :
    equationCoeff constraint =
      Cslib.PCP.HadamardTester.equationCoeff (fun a b => constraint a b = true) := by
  classical
  funext e
  cases e with
  | inl q => exact if_congr (compatible_eq_true constraint q.1 q.2) rfl rfl
  | inr b => rfl

/-- Run the existing five checks, supplying the executable quadratic coefficients. -/
def localTest (constraint : α → α → Bool) : LocalTest (Pos α) (Rand α) Query Bool :=
  Cslib.PCP.HadamardTester.test (equationCoeff constraint)

/-- Equality of the entire test transfers its existing completeness and soundness theorems. -/
theorem localTest_eq (constraint : α → α → Bool) :
    localTest constraint = hadamardTester (fun a b => constraint a b = true) := by
  simp only [localTest, equationCoeff_eq, hadamardTester]

/-- The queried proof position for a specified constraint, random string, and query number. -/
def query (constraint : α → α → Bool) (coins : Rand α) (i : Query) : Pos α :=
  (localTest constraint).query coins i

/-- The Boolean acceptance decision on the symbols claimed at the seventeen queries. -/
def accepts (constraint : α → α → Bool) (coins : Rand α) (answers : Query → Bool) : Bool :=
  @decide ((localTest constraint).Accepts coins answers) (by
    unfold localTest Cslib.PCP.HadamardTester.test LocalTest.and LocalTest.map
      blrTest tensorTest equationTest inputTest
    infer_instance)

/-- Every computed position is the position specified by the mathematical assignment tester. -/
theorem query_eq (constraint : α → α → Bool) (coins : Rand α) (i : Query) :
    query constraint coins i =
      (hadamardTester (fun a b => constraint a b = true)).query coins i := by
  rw [query, localTest_eq]

/-- The Boolean decision accepts exactly the answers accepted by the mathematical tester. -/
@[simp]
theorem accepts_eq_true (constraint : α → α → Bool) (coins : Rand α)
    (answers : Query → Bool) : accepts constraint coins answers = true ↔
      (hadamardTester (fun a b => constraint a b = true)).Accepts coins answers := by
  simp only [accepts, decide_eq_true_eq, localTest_eq]

/-- Fixed-alphabet query generation is uniform in the runtime constraint and random string. -/
@[fun_prop]
theorem isPolyTime_query (coinsEncoding : Rand α ↪ List Bool)
    (queryEncoding : Query ↪ List Bool) (positionEncoding : Pos α ↪ List Bool) :
    ComputableInPolyTime
      (fun p : (α → α → Bool) × Rand α × Query => query p.1 p.2.1 p.2.2)
      (encPair (encPi (encPi encBool)) (encPair coinsEncoding queryEncoding)) positionEncoding :=
  ComputableInPolyTime.of_finite _

/-- Fixed-alphabet acceptance charges the supplied constraint, coins, and all query answers. -/
@[fun_prop]
theorem isPolyTime_accepts (coinsEncoding : Rand α ↪ List Bool) :
    ComputableInPolyTime
      (fun p : (α → α → Bool) × Rand α × (Query → Bool) => accepts p.1 p.2.1 p.2.2)
      (encPair (encPi (encPi encBool)) (encPair coinsEncoding (encPi encBool))) encBool :=
  ComputableInPolyTime.of_finite _

end Cslib.PCP.Encoded.HadamardTester
