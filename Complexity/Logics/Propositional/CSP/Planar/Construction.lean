/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Planar.RelationMinor

/-!
# Finite ordered relation constructions

`RelationMinor.Construction` is a finite syntax tree of the ordered operations needed in
[DvorakKupec2015], Lemmas 2–3, printed pp. 437–438. Its leaves are the existing language
relations. A pin, disequality merge or flip carries the construction enabling that operation;
thus none is silently adjoined to the language. The only conjunction constructor is binary
intersection, the specific two-digon construction of Lemma 3. There is no arbitrary all-port
conjunction or identification.

The syntax records operations on the existing relations, with exact intermediate semantics.
An interpreter must justify its individual operations in the intended geometric model.
In particular this module proves no geometric planarity or runtime theorem.

## Main definitions

* `Cslib.Logic.PL.CSP.RelationMinor.Construction`: finite ordered construction trees.
* `Cslib.Logic.PL.CSP.RelationMinor.Trace.construction`: interpret a trace using enabling trees.
-/

public section

namespace Cslib.Logic.PL.CSP.RelationMinor

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {m n : ℕ}

/-- Finite ordered derivations from language symbols, recording the enabling pin or
disequality construction at every step where one is needed. -/
inductive Construction (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) :
    {n : ℕ} → Set (Fin n → Bool) → Type where
  /-- One original language constraint, with its original port order. -/
  | atom (r : Rel) : Construction arity sem (booleanRelation arity sem r)
  /-- Delete one port existentially. -/
  | project {n : ℕ} {R : Set (Fin (n + 1) → Bool)}
      (c : Construction arity sem R) (j : Fin (n + 1)) :
      Construction arity sem (project R j)
  /-- Restrict the first adjacent pair to equality and immediately delete the first port. -/
  | equalDrop {n : ℕ} {R : Set (Fin (n + 2) → Bool)}
      (c : Construction arity sem R) : Construction arity sem (adjacent R false)
  /-- Restrict the first adjacent pair to disequality, then delete its first port. -/
  | differentDrop {n : ℕ} {R : Set (Fin (n + 2) → Bool)}
      (c : Construction arity sem R) (d : Construction arity sem disequality) :
      Construction arity sem (adjacent R true)
  /-- Pin one port using an already constructed unary relation, then delete it. -/
  | cofactor {n : ℕ} {R : Set (Fin (n + 1) → Bool)}
      (c : Construction arity sem R) (j : Fin (n + 1)) (b : Bool)
      (p : Construction arity sem (pin b)) : Construction arity sem (cofactor R j b)
  /-- Twist one coordinate using an already constructed disequality relation. -/
  | flip {n : ℕ} {R : Set (Fin n → Bool)}
      (c : Construction arity sem R) (j : Fin n) (d : Construction arity sem disequality) :
      Construction arity sem (twist R (Pi.single j true))
  /-- Rotate the port list cyclically by one position. -/
  | rotate {n : ℕ} {R : Set (Fin (n + 1) → Bool)}
      (c : Construction arity sem R) : Construction arity sem (rotate R)
  /-- The binary intersection on the two bounded digons of three parallel edges. -/
  | binaryMeet {R S : Set (Fin 2 → Bool)} (c : Construction arity sem R)
      (d : Construction arity sem S) : Construction arity sem (R ∩ S)

/-- Availability means that a finite construction tree exists. This is a semantic existence
statement, without a uniform algorithm or a runtime bound. -/
abbrev Available (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (R : Set (Fin n → Bool)) : Prop := Nonempty (Construction arity sem R)

/-- Interpret an actual minor trace using actual constructions of its starting relation,
disequality and the two pins. Each cofactor or flip records its enabling construction. -/
def Trace.construction {n : ℕ} {R : Set (Fin m → Bool)} {S : Set (Fin n → Bool)}
    (trace : Trace R S) (c : Construction arity sem R)
    (d : Construction arity sem disequality) (p : ∀ b, Construction arity sem (pin b)) :
    Construction arity sem S :=
  match trace with
  | .refl => c
  | .project t j => .project (t.construction c d p) j
  | .cofactor t j b => .cofactor (t.construction c d p) j b (p b)
  | .flip (n := k) (S := U) t j =>
      Construction.flip (n := k) (R := U) (Trace.construction (n := k) (S := U) t c d p) j d

end Cslib.Logic.PL.CSP.RelationMinor
