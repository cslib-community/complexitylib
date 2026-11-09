/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.CSP.Schaefer

/-!
# Full Boolean Schaefer regression tests

Every tractable arm is exercised on a concrete equality language. NAE supplies the hard arm.
The final theorem is also applied symbolically at unrestricted fixed arities and to an empty
alphabet. These tests use the original CSP syntax and native binary encoding.
-/

namespace CslibFrontierTests.Schaefer

open Cslib.Logic Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM

-- Arbitrary fixed arities: the client supplies no solver, gadget or clone theorem.
example {Rel : Type} [Finite Rel] (encRel : Rel ↪ List Bool)
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) :
    CSPSAT arity sem ∈ P (encCSP encRel encNat) ∨
      NPComplete (encCSP encRel encNat) (CSPSAT arity sem) :=
  CSPSAT.mem_P_or_npComplete encRel arity sem

private def eqArity (_ : Unit) : ℕ := 2
private def eqSem (_ : Unit) : List Bool → Bool
  | [x, y] => x == y
  | _ => false

private theorem eq_constant (b : Bool) :
    CSP.HasPolymorphism eqArity eqSem (fun _ : Fin 1 → Bool => b) := by
  unfold CSP.HasPolymorphism IsPolymorphism CSP.booleanRelation eqArity
  cases b <;> decide

private theorem eq_and : CSP.HasPolymorphism eqArity eqSem
    (fun a : Fin 2 → Bool => a 0 && a 1) := by
  unfold CSP.HasPolymorphism IsPolymorphism CSP.booleanRelation eqArity
  decide

private theorem eq_or : CSP.HasPolymorphism eqArity eqSem
    (fun a : Fin 2 → Bool => a 0 || a 1) := by
  unfold CSP.HasPolymorphism IsPolymorphism CSP.booleanRelation eqArity
  decide

private theorem eq_majority : CSP.HasPolymorphism eqArity eqSem (Cslib.majority 3) := by
  unfold CSP.HasPolymorphism IsPolymorphism CSP.booleanRelation eqArity
  decide

private theorem eq_parity : CSP.HasPolymorphism eqArity eqSem (Cslib.parity 3) := by
  unfold CSP.HasPolymorphism IsPolymorphism CSP.booleanRelation eqArity
  decide

example (encUnit : Unit ↪ List Bool) : CSPSAT eqArity eqSem ∈ P (encCSP encUnit encNat) :=
  CSPSAT.mem_P_of_hasSchaeferPolymorphism encUnit eqArity eqSem (.inl (eq_constant false))

example (encUnit : Unit ↪ List Bool) : CSPSAT eqArity eqSem ∈ P (encCSP encUnit encNat) :=
  CSPSAT.mem_P_of_hasSchaeferPolymorphism encUnit eqArity eqSem (.inr (.inl (eq_constant true)))

example (encUnit : Unit ↪ List Bool) : CSPSAT eqArity eqSem ∈ P (encCSP encUnit encNat) :=
  CSPSAT.mem_P_of_hasSchaeferPolymorphism encUnit eqArity eqSem (.inr (.inr (.inl eq_and)))

example (encUnit : Unit ↪ List Bool) : CSPSAT eqArity eqSem ∈ P (encCSP encUnit encNat) :=
  CSPSAT.mem_P_of_hasSchaeferPolymorphism encUnit eqArity eqSem
    (.inr (.inr (.inr (.inl eq_or))))

example (encUnit : Unit ↪ List Bool) : CSPSAT eqArity eqSem ∈ P (encCSP encUnit encNat) :=
  CSPSAT.mem_P_of_hasSchaeferPolymorphism encUnit eqArity eqSem
    (.inr (.inr (.inr (.inr (.inl eq_majority)))))

example (encUnit : Unit ↪ List Bool) : CSPSAT eqArity eqSem ∈ P (encCSP encUnit encNat) :=
  CSPSAT.mem_P_of_hasSchaeferPolymorphism encUnit eqArity eqSem
    (.inr (.inr (.inr (.inr (.inr eq_parity)))))

-- Equality has both satisfying and nonsatisfying tuples, including sparse/repeated scopes.
example : eqSem () [false, true] = false := by decide
example : eqSem () [true, true] = true := by decide
example : [((), [2 ^ 80, 2 ^ 80])] ∈ CSPSAT eqArity eqSem := by
  exact ⟨by decide, fun _ => false, rfl⟩
example : [((), [0])] ∉ CSPSAT eqArity eqSem := by
  intro h
  have := h.1 ((), [0]) (by simp)
  simp [eqArity] at this

private def naeArity (_ : Unit) : ℕ := 3
private def naeSem (_ : Unit) : List Bool → Bool
  | [x, y, z] => !((x == y) && (y == z))
  | _ => false

private theorem nae_missing : ¬ CSP.HasSchaeferPolymorphism naeArity naeSem := by
  unfold CSP.HasSchaeferPolymorphism CSP.HasPolymorphism IsPolymorphism
    CSP.booleanRelation naeArity
  simp only [Set.mem_ofPred_eq, not_or]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

example (encUnit : Unit ↪ List Bool) :
    NPComplete (encCSP encUnit encNat) (CSPSAT naeArity naeSem) :=
  (CSPSAT.schaefer_dichotomy encUnit naeArity naeSem).2 nae_missing

-- Empty alphabets satisfy the constant arm rather than creating a spurious hard language.
example (encEmpty : Empty ↪ List Bool) :
    CSPSAT (Empty.elim : Empty → ℕ) (fun r => r.elim) ∈ P (encCSP encEmpty encNat) :=
  CSPSAT.mem_P_of_hasSchaeferPolymorphism encEmpty _ _ (.inl fun r => r.elim)

end CslibFrontierTests.Schaefer
