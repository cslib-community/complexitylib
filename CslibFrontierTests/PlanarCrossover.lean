/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/
import CslibFrontier.Computability.Complexity.Problems.SAT.Planar.CrossoverLayout
import CslibFrontier.Logics.Propositional.CNF.ImplicationCycle
import CslibFrontier.Logics.Propositional.CSP.Planar.Crossover

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Logic.PL.CNF.Crossover

-- The public fixed table keeps the existing cycle constructor's exact clause order.
example (v : Internal) : ring v = CNF.implicationCycle (List.ofFn (SplitVariable.copy v)) := rfl

example (v : Internal) : (ring v).eval (fun _ => true) = true :=
  (eval_ring_iff _ v).2 (fun _ => rfl)

-- A nonconstant local cycle is rejected, independently of which internal variable is split.
example : ∀ v : Internal, (ring v).eval (fun w => match w with
    | .copy _ i => i == 0
    | _ => false) = false := by decide +kernel

-- Opposite signals are equal within each pair; the two pairs remain independent.
example : Extends true true false false := (extends_iff _ _ _ _).2 ⟨rfl, rfl⟩
example : ¬ Extends true false false false := by
  rw [extends_iff]
  decide

-- The moved drawing modules still expose the same fixed geometric data.
example : incidenceRoutes.length = 154 := drawing_sizes.2
example (i : Fin 4) : (accessRoute i).length = 2 := rfl

/-!
Concrete clients of the finite Figure 1 gadgets. These do not assert a planar embedding.
-/

open Cslib.BitString Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Logic.PL.CSP.Crossover

-- Every one of the eight shapes satisfies the actual standardized condition.
example (p q r : Bool) : IsStandardizedInconsistent (standardizedRelation p q r) :=
  (isStandardizedInconsistent_iff _).mpr ⟨p, q, r, rfl⟩

-- Each bit independently controls its declared complementary pair.
example (p q r : Bool) :
    (![false, false, false, true] ∈ standardizedRelation p q r ↔ p = true) ∧
    (![false, false, true, false] ∈ standardizedRelation p q r ↔ q = true) ∧
    (![false, false, true, true] ∈ standardizedRelation p q r ↔ r = true) := by
  cases p <;> cases q <;> cases r <;> decide

example : figureOneARelation (standardizedRelation false false true) = cross :=
  figureOneARelation_standardized false false true

example : figureOneARelation (standardizedRelation true false false) = nearCross :=
  figureOneARelation_standardized true false false

example : figureOneARelation (standardizedRelation false true false) = nearCross :=
  figureOneARelation_standardized false true false

-- The explicitly targeted constructor is directly usable as a NEAR-CROSS gadget.
example : ∃ b, (figureOneAStandardized (standardizedRelation true false false)
    ((isStandardizedInconsistent_iff _).mpr ⟨true, false, false, rfl⟩)).body.eval
      (sem (standardizedRelation true false false))
      (Sum.elim ![false, false, false, true] b) = true := by
  apply (figureOneAStandardized _ _).correct _ |>.mp
  simp [standardizedRelation, cross, nearCross]

example : ![false, true, false, true] ∈ cross := by decide
example : ![false, false, false, true] ∉ cross := by decide
example : ![false, false, false, true] ∈ nearCross := by decide
example : ![true, true, true, false] ∈ nearCross := by decide
example : ![false, true, true, false] ∉ nearCross := by decide

-- A concrete CROSS boundary and its auxiliaries (m,mbar,v2bar) in Figure 1(a).
example : figureOneABody.eval (sem cross)
    (Sum.elim ![false, true, false, true] ![true, false, false]) = true := by decide

-- The extra NEAR-CROSS boundary has an actual witness, rather than only abstract existence.
example : ∃ b, figureOneABody.eval (sem (standardizedRelation true false false))
    (Sum.elim ![false, false, false, true] b) = true := by
  exact ⟨![true, false, true], by decide⟩

example : ¬ ∃ b, figureOneABody.eval (sem cross)
    (Sum.elim ![false, false, false, true] b) = true := by decide

-- A checked PPGadget client uses both the literal body and its correctness field.
example : ∃ b, figureOneB.body.eval nearSem
    (Sum.elim ![false, true, false, true] b) = true :=
  (figureOneB.correct _).mp (by decide)

example : figureOneB.body.eval nearSem
    (Sum.elim ![false, true, false, true] ![false]) = true := by decide

-- Figure 1(b) removes each of the two unwanted NEAR-CROSS tuples.
example : ¬ ∃ b, figureOneB.body.eval nearSem
    (Sum.elim ![false, false, false, true] b) = true := by decide

example : ¬ ∃ b, figureOneB.body.eval nearSem
    (Sum.elim ![true, true, true, false] b) = true := by decide

example : ¬ ∃ b, figureOneB.body.eval nearSem
    (Sum.elim ![false, true, true, false] b) = true := by decide

example : (figureOneA cross).numAux = 3 ∧ (figureOneA cross).body.length = 4 := by decide
example : figureOneB.numAux = 1 ∧ figureOneB.body.length = 2 := by decide
example : validArity arity figureOneABody = true := by decide
example : validArity (fun _ : Unit => 4) figureOneB.body = true := by decide

-- Interpretations reject both undersized and oversized scopes.
example : sem cross .relation [false, false, false] = false := by decide
example : sem cross .relation [false, false, false, false, false] = false := by decide
example : sem cross .disequality [false] = false := by decide
example : sem cross .disequality [false, true, false] = false := by decide
example : nearSem () [false, false, false] = false := by decide
example : nearSem () [false, false, false, false, false] = false := by decide
example : validArity arity [⟨Symbol.relation, ([0, 1, 2] : List ℕ)⟩] = false := by decide
