/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.CSP.Constant
import Complexity.Computability.Complexity.Problems.CSP.Majority

/-! Native tractability on concrete languages with inconsistent and empty-relation instances. -/

namespace ComplexityTests.CSPTractability

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

private def unary : Bool → ℕ := fun _ => 1
private def pin (b : Bool) (vs : List Bool) : Bool := vs == [b]
private def maybePin (b : Bool) (vs : List Bool) : Bool := if b then false else vs == [true]

private theorem pins_majority : CSP.HasPolymorphism unary pin (majority 3) := by
  intro R
  change Cslib.Logic.IsPolymorphism (majority 3)
    {a : Fin 1 → Bool | pin R (List.ofFn a) = true}
  have heq : {a : Fin 1 → Bool | pin R (List.ofFn a) = true} =
      {a : Fin 1 → Bool | CNF.eval a [[(0, R)]] = true} := by
    ext a
    simp [pin, List.ofFn_succ, CNF.eval, Clause.eval]
  rw [heq]
  exact CNF.isPolymorphism_majority (by simp)

-- A single fixed language can express both true and false pins, hence inconsistent instances,
-- and is nevertheless tractable under the common majority operation.
example : CSPSAT unary pin ∈ P (encCSP encBool encNat) :=
  CSPSAT.mem_P_of_majority encBool unary pin pins_majority

example : [(true, [0]), (false, [1])] ∈ CSPSAT unary pin := by
  refine ⟨by decide, fun n => n == 0, ?_⟩
  decide

example : [(true, [0]), (false, [0])] ∉ CSPSAT unary pin := by
  rintro ⟨_, σ, hσ⟩
  cases h : σ 0 <;> simp [CSP.eval, Constraint.eval, pin, h] at hσ

private theorem maybePin_true :
    CSP.HasPolymorphism unary maybePin (fun _ : Fin 1 → Bool => true) := by
  intro R a ha
  cases R with
  | false =>
    change maybePin false (List.ofFn (fun _ : Fin 1 => true)) = true
    decide
  | true => exact (Bool.false_ne_true (ha 0)).elim

-- A common unary constant still gives P when the language also contains an empty relation.
example : CSPSAT unary maybePin ∈ P (encCSP encBool encNat) :=
  CSPSAT.mem_P_of_constant encBool unary maybePin true maybePin_true

example : [(false, [2 ^ 80])] ∈ CSPSAT unary maybePin := by
  refine ⟨by decide, fun _ => true, ?_⟩
  decide

example : [(true, [0])] ∉ CSPSAT unary maybePin := by
  rintro ⟨_, _, hσ⟩
  exact Bool.false_ne_true hσ

end ComplexityTests.CSPTractability
