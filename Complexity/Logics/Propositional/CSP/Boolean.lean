/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP
public import Complexity.Logics.Polymorphism
public import Complexity.Foundations.Data.BitString.Threshold
public import Complexity.Foundations.Data.BitString.Parity

/-!
# Fixed-arity Boolean constraint languages

The existing CSP syntax is retained. A language supplies `arity : Rel → ℕ` and the existing
list semantics `sem : Rel → List Bool → Bool`; only lists of the declared arity are used.
`CSP.WellFormed` checks this condition on every constraint. The language, including its arities
and truth tables, is fixed independently of the input instance [Chen2006CSP], Definitions
3.1–3.3. Relation symbols need not be finite for these semantic definitions.

`CSP.HasSchaeferPolymorphism` is the six-case Boolean criterion of [Chen2006CSP], Theorem 3.20.
The constants are **unary** operations: they preserve an empty relation vacuously. Empty and
nullary relations are allowed. This module defines the criterion, not its complexity dichotomy.

## Main definitions

* `Cslib.Logic.PL.CSP.WellFormed`, `Cslib.Logic.PL.CSP.validArity`: exact-arity condition and guard.
* `Cslib.Logic.PL.CSP.booleanRelation`: a relation on its declared finite set of coordinates.
* `Cslib.Logic.PL.CSP.HasPolymorphism`: a common polymorphism of all relations in a language.
* `Cslib.Logic.PL.CSP.HasSchaeferPolymorphism`: constants, AND, OR, majority or minority.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V J : Type*}

/-- Every constraint scope has the arity declared by its relation symbol. Repeated variables
are allowed and count as distinct positions in the scope. -/
@[expose] def WellFormed (arity : Rel → ℕ) (F : CSP Rel V) : Prop :=
  ∀ c ∈ F, c.2.length = arity c.1

/-- Executable exact-arity guard for an instance of a fixed constraint language. -/
@[expose] def validArity (arity : Rel → ℕ) (F : CSP Rel V) : Bool :=
  F.all fun (R, vs) => decide (vs.length = arity R)

/-- The exact-arity guard agrees with the semantic well-formedness condition. -/
@[simp] theorem validArity_eq_true_iff (arity : Rel → ℕ) (F : CSP Rel V) :
    validArity arity F = true ↔ WellFormed arity F := by
  simp [validArity, WellFormed, List.all_eq_true]

/-- The relation belonging to a symbol, evaluated only at its declared arity. -/
@[expose] def booleanRelation (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) (R : Rel) :
    Set (Fin (arity R) → Bool) :=
  {a | sem R (List.ofFn a) = true}

/-- A common coordinatewise polymorphism of a fixed Boolean constraint language. -/
@[expose] def HasPolymorphism (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (f : (J → Bool) → Bool) : Prop :=
  ∀ R, IsPolymorphism f (booleanRelation arity sem R)

/-- The six common-polymorphism cases of Boolean Schaefer: unary false, unary true, binary
AND, binary OR, ternary majority and ternary parity (minority). -/
@[expose] def HasSchaeferPolymorphism (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) : Prop :=
  HasPolymorphism arity sem (fun _ : Fin 1 → Bool => false) ∨
  HasPolymorphism arity sem (fun _ : Fin 1 → Bool => true) ∨
  HasPolymorphism arity sem (fun a : Fin 2 → Bool => a 0 && a 1) ∨
  HasPolymorphism arity sem (fun a : Fin 2 → Bool => a 0 || a 1) ∨
  HasPolymorphism arity sem (Cslib.majority 3) ∨
  HasPolymorphism arity sem (Cslib.parity 3)

/-- A unary constant preserves precisely those nonempty relations containing its constant
tuple. Empty relations impose no condition, unlike preservation by a nullary constant. -/
theorem hasPolymorphism_const_iff (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) (b : Bool) :
    HasPolymorphism arity sem (fun _ : Fin 1 → Bool => b) ↔
      ∀ R, (booleanRelation arity sem R).Nonempty →
        (fun _ => b) ∈ booleanRelation arity sem R := by
  constructor
  · intro h R ⟨a, ha⟩
    exact h R (fun _ => a) (fun _ => ha)
  · intro h R a ha
    exact h R ⟨a 0, ha 0⟩

end Cslib.Logic.PL.CSP
