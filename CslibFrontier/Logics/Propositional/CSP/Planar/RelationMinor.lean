/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Boolean
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Ordered Boolean relation minors

Relations are the sets of tuples used by `CSP.booleanRelation`. Deletion uses `Fin.succAbove`,
so surviving ports retain their order. `RelationMinor.Trace` records each projection, cofactor,
and single-coordinate twist separately. It does not assert geometric planarity: pins and
disequality must be supplied when interpreting these traces as gadgets.

The adjacent operations combine a restriction of the first two ports with **immediate** deletion
of the first port. They are the operations of [DvorakKupec2015], Lemma 2, printed p. 437, with
this deletion made explicit. There is no arbitrary identification or all-port intersection.

## Main definitions

* `Cslib.Logic.PL.CSP.RelationMinor.project`: ordered existential deletion.
* `Cslib.Logic.PL.CSP.RelationMinor.cofactor`: pinning and ordered deletion.
* `Cslib.Logic.PL.CSP.RelationMinor.twist`: coordinatewise translation of a relation.
* `Cslib.Logic.PL.CSP.RelationMinor.adjacent`: adjacent restriction and immediate deletion.
* `Cslib.Logic.PL.CSP.RelationMinor.Trace`: finite ordered minor traces.
-/

public section

namespace Cslib.Logic.PL.CSP.RelationMinor

variable {m n : ℕ}

/-- Delete one coordinate existentially, retaining the order of all other coordinates. -/
@[expose] def project (R : Set (Fin (n + 1) → Bool)) (j : Fin (n + 1)) :
    Set (Fin n → Bool) := {x | ∃ b, j.insertNth b x ∈ R}

/-- Fix one coordinate to `b` and immediately delete it. -/
@[expose] def cofactor (R : Set (Fin (n + 1) → Bool)) (j : Fin (n + 1)) (b : Bool) :
    Set (Fin n → Bool) := {x | j.insertNth b x ∈ R}

/-- Translate by a bit string. Since every bit string is its own inverse, this is both the
image and the inverse image under translation. -/
@[expose] def twist (R : Set (Fin n → Bool)) (t : Fin n → Bool) :
    Set (Fin n → Bool) := {x | x + t ∈ R}

/-- Restrict the first two adjacent coordinates to equality (`different = false`) or
disequality (`different = true`), then immediately delete the first coordinate. -/
@[expose] def adjacent (R : Set (Fin (n + 2) → Bool)) (different : Bool) :
    Set (Fin (n + 1) → Bool) := {x | Fin.cons (x 0 ^^ different) x ∈ R}

/-- Cyclically rotate the ports by one position; no arbitrary permutation is allowed. -/
@[expose] def rotate (R : Set (Fin (n + 1) → Bool)) : Set (Fin (n + 1) → Bool) :=
  {x | (fun i => x (i + 1)) ∈ R}

/-- The unary pin relation, distinct from a unary constant *operation*. -/
@[expose] def pin (b : Bool) : Set (Fin 1 → Bool) := {x | x 0 = b}

/-- Ordered binary disequality. -/
@[expose] def disequality : Set (Fin 2 → Bool) := {x | x 0 ≠ x 1}

/-- Ordered binary NAND: its unique missing row is `11`. -/
@[expose] def nand : Set (Fin 2 → Bool) := {x | ¬(x 0 = true ∧ x 1 = true)}

instance (b : Bool) : DecidablePred (· ∈ pin b) := fun x =>
  inferInstanceAs (Decidable (x 0 = b))

instance : DecidablePred (· ∈ disequality) := fun x =>
  inferInstanceAs (Decidable (x 0 ≠ x 1))

instance : DecidablePred (· ∈ nand) := fun x =>
  inferInstanceAs (Decidable (¬(x 0 = true ∧ x 1 = true)))

instance (R : Set (Fin (n + 1) → Bool)) [DecidablePred (· ∈ R)] (j : Fin (n + 1)) :
    DecidablePred (· ∈ project R j) := fun x =>
  inferInstanceAs (Decidable (∃ b, j.insertNth b x ∈ R))

instance (R : Set (Fin (n + 1) → Bool)) [DecidablePred (· ∈ R)] (j : Fin (n + 1))
    (b : Bool) : DecidablePred (· ∈ cofactor R j b) := fun x =>
  inferInstanceAs (Decidable (j.insertNth b x ∈ R))

instance (R : Set (Fin n → Bool)) [DecidablePred (· ∈ R)] (t : Fin n → Bool) :
    DecidablePred (· ∈ twist R t) := fun x =>
  inferInstanceAs (Decidable (x + t ∈ R))

instance (R : Set (Fin (n + 2) → Bool)) [DecidablePred (· ∈ R)] (d : Bool) :
    DecidablePred (· ∈ adjacent R d) := fun x =>
  inferInstanceAs (Decidable (Fin.cons (x 0 ^^ d) x ∈ R))

instance (R : Set (Fin (n + 1) → Bool)) [DecidablePred (· ∈ R)] :
    DecidablePred (· ∈ rotate R) := fun x =>
  inferInstanceAs (Decidable ((fun i => x (i + 1)) ∈ R))

/-- A finite sequence of projections, cofactors and one-coordinate twists, with the
intermediate relation and its arity recorded at each step. Cofactors require pins and flips
require disequality when a trace is interpreted geometrically. -/
inductive Trace (R : Set (Fin m → Bool)) : {n : ℕ} → Set (Fin n → Bool) → Type where
  /-- The empty trace. -/
  | refl : Trace R R
  /-- Append an existential deletion. -/
  | project {n : ℕ} {S : Set (Fin (n + 1) → Bool)} (trace : Trace R S) (j : Fin (n + 1)) :
      Trace R (project S j)
  /-- Append a pin and deletion. -/
  | cofactor {n : ℕ} {S : Set (Fin (n + 1) → Bool)} (trace : Trace R S)
      (j : Fin (n + 1)) (b : Bool) : Trace R (cofactor S j b)
  /-- Append a twist of just one port. -/
  | flip {n : ℕ} {S : Set (Fin n → Bool)} (trace : Trace R S) (j : Fin n) :
      Trace R (twist S (Pi.single j true))

/-- Concatenate two finite ordered traces. -/
def Trace.trans {R : Set (Fin m → Bool)} {S : Set (Fin n → Bool)}
    (a : Trace R S) {k : ℕ} {T : Set (Fin k → Bool)} (b : Trace S T) : Trace R T :=
  match b with
  | .refl => a
  | .project b j => .project (a.trans b) j
  | .cofactor b j v => .cofactor (a.trans b) j v
  | .flip b j => .flip (a.trans b) j

/-- Consecutive translations combine by addition in the Boolean cube. -/
theorem twist_twist (R : Set (Fin n → Bool)) (s t : Fin n → Bool) :
    twist (twist R s) t = twist R (s + t) := by
  ext x
  change (x + t) + s ∈ R ↔ x + (s + t) ∈ R
  rw [add_assoc, add_comm t s]

/-- A mask twist expands to finitely many single-port twists. -/
noncomputable def Trace.translate {R : Set (Fin m → Bool)} {S : Set (Fin n → Bool)}
    (trace : Trace R S) (t : Fin n → Bool) : Trace R (twist S t) := by
  classical
  have build (s : Finset (Fin n)) :
      Nonempty (Trace R (twist S (∑ i ∈ s, Pi.single i true))) := by
    induction s using Finset.induction_on with
    | empty => simpa [twist] using (show Nonempty (Trace R S) from ⟨trace⟩)
    | @insert i s hi ih =>
      obtain ⟨tr⟩ := ih
      simpa only [Finset.sum_insert hi, twist_twist, add_comm] using
        (show Nonempty _ from ⟨tr.flip i⟩)
  have ht : (∑ i ∈ (Finset.univ.filter fun i => t i = true), Pi.single i true) = t := by
    ext j
    by_cases hj : t j = true
    · rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp [hj]
      · intro i _ hi
        simp [Ne.symm hi]
      · simp [hj]
    · have hj' : t j = false := by cases h : t j <;> simp_all
      rw [hj', Finset.sum_apply]
      change _ = (0 : Bool)
      apply Finset.sum_eq_zero
      intro i hi
      have hne : j ≠ i := by
        intro heq
        subst i
        exact hj (Finset.mem_filter.mp hi).2
      simp [hne]
  exact Classical.choice (by simpa only [ht] using build (Finset.univ.filter fun i => t i = true))

/-- Deleting a feasible tuple gives a feasible projected tuple. -/
theorem remove_mem_project {R : Set (Fin (n + 1) → Bool)} {a : Fin (n + 1) → Bool}
    (ha : a ∈ R) (j : Fin (n + 1)) : j.removeNth a ∈ project R j := by
  refine ⟨a j, ?_⟩
  rwa [(Fin.insertNth_eq_iff).mpr ⟨rfl, rfl⟩]

/-- A tuple satisfying the pin survives in its cofactor. -/
theorem remove_mem_cofactor {R : Set (Fin (n + 1) → Bool)} {a : Fin (n + 1) → Bool}
    (ha : a ∈ R) (j : Fin (n + 1)) : j.removeNth a ∈ cofactor R j (a j) := by
  change j.insertNth (a j) (j.removeNth a) ∈ R
  rwa [(Fin.insertNth_eq_iff).mpr ⟨rfl, rfl⟩]

/-- A zero projection of a relation missing zero has only its unit-vector lift. -/
theorem single_mem_of_zero_mem_project {R : Set (Fin (n + 1) → Bool)}
    (hzero : (0 : Fin (n + 1) → Bool) ∉ R) (j : Fin (n + 1))
    (h : (0 : Fin n → Bool) ∈ project R j) : Pi.single j true ∈ R := by
  obtain ⟨b, hb⟩ := h
  have hi (b : Bool) : j.insertNth b (0 : Fin n → Bool) = (Pi.single j b : Fin (n + 1) → Bool) := by
    apply (Fin.insertNth_eq_iff).mpr
    constructor
    · simp
    · ext i
      simp [Fin.removeNth]
  cases b
  · exact False.elim (hzero (by simpa [hi, ← Bool.zero_eq_false] using hb))
  · simpa only [hi] using hb

end Cslib.Logic.PL.CSP.RelationMinor
