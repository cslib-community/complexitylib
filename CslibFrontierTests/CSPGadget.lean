/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.PolyTime.CSP.Gadget

/-! Fixed-gadget regression tests: actual existential ports, repeated source variables,
freshness across constraints, a large binary name, malformed scopes and nullary relations. -/

open Cslib.Logic Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM

namespace CSPGadgetTests

private abbrev targetArity : Bool → ℕ := fun r => if r then 0 else 2

private def targetSem (r : Bool) (v : List Bool) : Bool :=
  if r then false else match v with
  | [a, b] => a != b
  | _ => false

private abbrev sourceArity : Unit → ℕ := fun _ => 2

private def sourceSem (_ : Unit) : List Bool → Bool
  | [a, b] => a == b
  | _ => false

private def equalityGadget (_ : Unit) :
    PPGadget targetArity targetSem (booleanRelation sourceArity sourceSem ()) where
  numAux := 1
  body := [⟨false, [Sum.inl 0, Sum.inr 0]⟩, ⟨false, [Sum.inr 0, Sum.inl 1]⟩]
  wellFormed := by simp [WellFormed, targetArity]
  correct := by
    intro a
    constructor
    · intro ha
      refine ⟨fun _ => !a 0, ?_⟩
      have heq : a 0 = a 1 := by simpa [booleanRelation, sourceArity, sourceSem] using ha
      cases h : a 0 <;> simp [eval, Constraint.eval, targetSem, ← heq, h]
    · rintro ⟨b, hb⟩
      cases ha0 : a 0 <;> cases ha1 : a 1 <;> cases hb0 : b 0 <;>
        simp_all [eval, Constraint.eval, targetSem, booleanRelation, sourceArity, sourceSem]

private abbrev templates := fun r => (equalityGadget r).template

example : replaceGadgets 1 templates [⟨(), [7, 7]⟩, ⟨(), [7, 2^100]⟩] =
    [⟨false, [14, 1]⟩, ⟨false, [1, 14]⟩,
      ⟨false, [14, 3]⟩, ⟨false, [3, 2 * 2^100]⟩] := by decide

example : (replaceGadgets 1 templates [⟨(), [7, 7]⟩]).Satisfiable targetSem ↔
    Satisfiable sourceSem ([⟨(), [7, 7]⟩] : CSP Unit ℕ) :=
  satisfiable_replaceGadgets_iff equalityGadget 1 (by intro r; rfl)
    _ (by simp [WellFormed, sourceArity])

private def reject : CSP Bool ℕ := [⟨true, []⟩]

private theorem reject_unsatisfiable : ¬ reject.Satisfiable targetSem := by
  simp [Satisfiable, reject, eval, Constraint.eval, targetSem]

example : replaceGadgetsGuarded sourceArity 1 templates reject [⟨(), [7]⟩] = reject := by
  decide

example : ¬ (replaceGadgetsGuarded sourceArity 1 templates reject
    [⟨(), [7]⟩]).Satisfiable targetSem := by
  rw [satisfiable_replaceGadgetsGuarded_iff equalityGadget 1 (by intro r; rfl)
    reject reject_unsatisfiable]
  simp [WellFormed, sourceArity]

example (encUnit : Unit ↪ List Bool) :
    ComputableInPolyTime (replaceGadgetsGuarded sourceArity 1 templates reject)
      (Cslib.Complexity.encCSP encUnit encNat) (Cslib.Complexity.encCSP encBool encNat) :=
  Cslib.Complexity.CSP.computableInPolyTime_replaceGadgetsGuarded _ _ _ _ _ _

-- A malformed reject target works without any hypothesis about its Boolean semantics.
example (F : CSP Unit ℕ) :
    (WellFormed targetArity (replaceGadgetsGuarded sourceArity 1 templates
        (malformedReject targetArity false) F) ∧
      (replaceGadgetsGuarded sourceArity 1 templates
        (malformedReject targetArity false) F).Satisfiable targetSem) ↔
      WellFormed sourceArity F ∧ F.Satisfiable sourceSem :=
  wellFormed_satisfiable_replaceGadgetsGuarded_iff equalityGadget 1 (by intro r; rfl)
    _ (fun h => not_wellFormed_malformedReject _ _ h.1) F

private def unequalSem (_ : Unit) : List Bool → Bool := targetSem false

private def unequalGadget (_ : Unit) :
    PPGadget targetArity targetSem (booleanRelation sourceArity unequalSem ()) where
  numAux := 0
  body := [⟨false, [Sum.inl 0, Sum.inl 1]⟩]
  wellFormed := by simp [WellFormed, targetArity]
  correct := by
    intro a
    simp [booleanRelation, unequalSem, eval, Constraint.eval]

-- A well-formed unsatisfiable instance stays unsatisfiable, including the B = 0 case.
example : ¬ (replaceGadgets 0 (fun r => (unequalGadget r).template)
    [⟨(), [7, 7]⟩]).Satisfiable targetSem := by
  rw [satisfiable_replaceGadgets_iff unequalGadget 0 (by intro r; rfl)
    _ (by simp [WellFormed, sourceArity])]
  simp [Satisfiable, eval, Constraint.eval, unequalSem, targetSem]

-- Empty conjunctions require no allocation and remain satisfiable.
example : (replaceGadgets 0 (fun r => (unequalGadget r).template) []).Satisfiable targetSem :=
  ⟨fun _ => false, rfl⟩

/-- A nontrivial separating relation meets the actual canonical construction's premises. -/
example : Nonempty (PPGadget targetArity targetSem
    (booleanRelation targetArity targetSem false)) := by
  apply exists_ppGadget_of_polymorphisms
  · exact ⟨![false, true], by simp [booleanRelation, targetSem]⟩
  · intro i j hij
    refine ⟨![false, true], by simp [booleanRelation, targetSem], ?_⟩
    fin_cases i <;> fin_cases j <;> simp_all
  · intro k hk f hf
    exact hf false

/-- The canonical construction also covers the nonempty nullary target. -/
example : Nonempty (PPGadget targetArity targetSem (Set.univ : Set (Fin 0 → Bool))) := by
  apply exists_ppGadget_of_polymorphisms
  · exact Set.univ_nonempty
  · intro i; exact Fin.elim0 i
  · intro k hk f hf a ha
    exact Set.mem_univ _

end CSPGadgetTests
