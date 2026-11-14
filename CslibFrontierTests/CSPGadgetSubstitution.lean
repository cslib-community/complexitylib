/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: candidate

import CslibFrontier.Computability.PolyTime.CSP.Gadget.CertifiedRotation
import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.BoundaryBlocks
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary

/-! Full-checker regressions for literal positional substitution and empty-alphabet rejection. -/

namespace CslibFrontierTests.CSPGadgetSubstitution

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity
open Cslib.Complexity.CSP Cslib.Complexity.CSP.OrderedBoundary
open Cslib.Complexity.CSP.GadgetRotation Turing.MultiTapeTM

private def atom (n : ℕ) := PPGadget.atom (arity := fun (_ : Unit) => n)
  (sem := fun (_ : Unit) (_ : List Bool) => true) ()

private def atomWitness (n : ℕ) : GadgetWitness (atom n) :=
  Witness.atom (fun (_ : Unit) => n) (fun (_ : Unit) (_ : List Bool) => true) ()

private def runAtom (n : ℕ) := compile (fun (_ : Unit) => n) 0
  (fun _ => (atom n).template)
  (fun _ => freeBoundaryBlocks (atom n) (atomWitness n))
  (fun _ => auxiliaryBoundaryBlocks (atom n) (atomWitness n))

-- Parallel incidences use separate source blocks, even at the same source variable.
example : runAtom 2 ([⟨(), [7, 7]⟩], ⟨[2, 3, 0, 1]⟩) =
    ([⟨(), [14, 14]⟩], ⟨[2, 3, 0, 1]⟩) := by decide +kernel

example : verifyRotationCertificate
    (runAtom 2 ([⟨(), [7, 7]⟩], ⟨[2, 3, 0, 1]⟩)).1
    (runAtom 2 ([⟨(), [7, 7]⟩], ⟨[2, 3, 0, 1]⟩)).2 = true := by decide +kernel

-- Duplicate records keep both constraint positions and their four-edge white cycle.
example : verifyRotationCertificate
    (runAtom 2 ([⟨(), [7, 7]⟩, ⟨(), [7, 7]⟩], ⟨[6, 3, 0, 1, 2, 7, 4, 5]⟩)).1
    (runAtom 2 ([⟨(), [7, 7]⟩, ⟨(), [7, 7]⟩], ⟨[6, 3, 0, 1, 2, 7, 4, 5]⟩)).2 = true := by
  decide +kernel

-- Degree five and a nontrivial supplied clockwise white rotation.
example : verifyRotationCertificate
    (runAtom 5 ([⟨(), [7, 7, 7, 7, 7]⟩], ⟨[8, 3, 0, 5, 2, 7, 4, 9, 6, 1]⟩)).1
    (runAtom 5 ([⟨(), [7, 7, 7, 7, 7]⟩], ⟨[8, 3, 0, 5, 2, 7, 4, 9, 6, 1]⟩)).2 = true := by
  decide +kernel

-- Sparse binary names never become a clock, including the full target checker.
example : verifyRotationCertificate
    (runAtom 2 ([⟨(), [2 ^ 250, 2 ^ 250]⟩], ⟨[2, 3, 0, 1]⟩)).1
    (runAtom 2 ([⟨(), [2 ^ 250, 2 ^ 250]⟩], ⟨[2, 3, 0, 1]⟩)).2 = true := by decide +kernel

example : runAtom 2 ([⟨(), [7, 7]⟩], ⟨[2 ^ 250, 3, 0, 1]⟩) =
    ([], ⟨[0]⟩) := by decide +kernel

example : verifyRotationCertificate
    (runAtom 2 ([⟨(), [7]⟩], ⟨[0, 1]⟩)).1
    (runAtom 2 ([⟨(), [7]⟩], ⟨[0, 1]⟩)).2 = false := by decide +kernel

-- The empty relation alphabet still admits total rejection of a malformed certificate.
example : compile (Empty.elim : Empty → ℕ) 0
    (Empty.elim : Empty → CSP Empty (Bool × ℕ))
    (Empty.elim : Empty → List (List ℕ)) (Empty.elim : Empty → List (List ℕ))
    ([], ⟨[2 ^ 250]⟩) = ([], ⟨[0]⟩) := by decide +kernel

example : verifyRotationCertificate ([] : CSP Empty ℕ) ⟨[0]⟩ = false := by decide

example : compile (Empty.elim : Empty → ℕ) 0
    (Empty.elim : Empty → CSP Empty (Bool × ℕ))
    (Empty.elim : Empty → List (List ℕ)) (Empty.elim : Empty → List (List ℕ))
    ([], ⟨[]⟩) = ([], ⟨[]⟩) := by decide +kernel

example : verifyRotationCertificate ([] : CSP Empty ℕ) ⟨[]⟩ = true := by decide

-- Nullary truth is a semantic condition, independent of accepted point components.
example : verifyRotationCertificate ([⟨(), []⟩] : CSP Unit ℕ) ⟨[]⟩ = true := by decide

example : CSP.Satisfiable (fun (_ : Unit) (_ : List Bool) => true)
    ([⟨(), []⟩] : CSP Unit ℕ) :=
  ⟨fun _ => false, by decide⟩

example : ¬ CSP.Satisfiable (fun (_ : Unit) (_ : List Bool) => false)
    ([⟨(), []⟩] : CSP Unit ℕ) := by
  rintro ⟨σ, hσ⟩
  simp [CSP.eval, Constraint.eval] at hσ

-- A reflected ternary constraint still fails the full ordered target checker.
example : Graph.RotationCertificate.verifyGenusZero
    (incidenceGraph ([⟨(), [0, 1, 2]⟩] : CSP Unit ℕ)) ⟨[0, 5, 2, 1, 4, 3]⟩ = true := by
  decide +kernel

example : verifyRotationCertificate ([⟨(), [0, 1, 2]⟩] : CSP Unit ℕ)
    ⟨[0, 5, 2, 1, 4, 3]⟩ = false := by decide +kernel

private def unusedPorts (b : Bool) : PPGadget (fun (_ : Unit) => 0)
    (fun _ _ => b) {_a : Fin 3 → Bool | b = true} where
  numAux := 2
  body := [⟨(), []⟩]
  wellFormed := by simp [WellFormed]
  correct _ := by
    simp only [Set.mem_ofPred_eq, CSP.eval, Constraint.eval, List.all_cons, List.all_nil,
      Bool.and_true]
    exact ⟨fun hb => ⟨fun _ => false, hb⟩, fun ⟨_, hb⟩ => hb⟩

private def unusedPortsWitness (b : Bool) : GadgetWitness (unusedPorts b) where
  certificate := ⟨[0, 3, 2, 5, 4, 1]⟩
  accepted := by
    change verify ([⟨(), []⟩] : CSP Unit (Fin 3 ⊕ Fin 2)) (List.ofFn Sum.inl)
      ⟨[0, 3, 2, 5, 4, 1]⟩ = true
    decide +kernel

example : freeBoundaryBlocks (unusedPorts false) (unusedPortsWitness false) = [[], [], []] := by
  decide +kernel

example : auxiliaryBoundaryBlocks (unusedPorts false) (unusedPortsWitness false) = [[], []] := by
  decide +kernel

private def runUnused (b : Bool) := compile (fun (_ : Unit) => 3) 2
  (fun _ => (unusedPorts b).template)
  (fun _ => freeBoundaryBlocks (unusedPorts b) (unusedPortsWitness b))
  (fun _ => auxiliaryBoundaryBlocks (unusedPorts b) (unusedPortsWitness b))
  ([⟨(), [7, 7, 7]⟩], ⟨[4, 3, 0, 5, 2, 1]⟩)

-- All free and auxiliary ports vanish, but the actual closed nullary body remains.
example : runUnused false = ([⟨(), []⟩], ⟨[]⟩) := by decide +kernel

example : verifyRotationCertificate (runUnused false).1 (runUnused false).2 = true := by
  decide +kernel

example : ¬ CSP.Satisfiable (fun (_ : Unit) (_ : List Bool) => false) (runUnused false).1 := by
  rintro ⟨σ, hσ⟩
  change false = true at hσ
  contradiction

example : verifyRotationCertificate (runUnused true).1 (runUnused true).2 = true := by
  decide +kernel

example : CSP.Satisfiable (fun (_ : Unit) (_ : List Bool) => true) (runUnused true).1 :=
  ⟨fun _ => false, by decide +kernel⟩

-- A non-atom body has two free unary constraints, a closed auxiliary component and a
-- nullary component. Free port 2 and auxiliary port 1 are unused. Its fixed table is explicit.
private def splitArity (r : Bool) : ℕ := if r then 0 else 1

private def splitPorts (b : Bool) : PPGadget splitArity (fun _ _ => b)
    (booleanRelation (fun (_ : Unit) => 3) (fun _ _ => b) ()) where
  numAux := 2
  body := [⟨false, [.inl 0]⟩, ⟨false, [.inl 1]⟩, ⟨false, [.inr 0]⟩, ⟨true, []⟩]
  wellFormed := by decide
  correct _ := by
    cases b <;> simp [booleanRelation, CSP.eval, Constraint.eval]

private def splitWitness (b : Bool) : GadgetWitness (splitPorts b) where
  certificate := ⟨[10, 1, 8, 3, 4, 5, 6, 9, 2, 11, 0, 7]⟩
  accepted := by
    change verify ([⟨false, [.inl 0]⟩, ⟨false, [.inl 1]⟩, ⟨false, [.inr 0]⟩, ⟨true, []⟩] :
      CSP Bool (Fin 3 ⊕ Fin 2)) (List.ofFn Sum.inl)
        ⟨[10, 1, 8, 3, 4, 5, 6, 9, 2, 11, 0, 7]⟩ = true
    decide +kernel

private def runSplit (b : Bool) := compile (fun (_ : Unit) => 3) 2
  (fun _ => (splitPorts b).template)
  (fun _ => freeBoundaryBlocks (splitPorts b) (splitWitness b))
  (fun _ => auxiliaryBoundaryBlocks (splitPorts b) (splitWitness b))
  ([⟨(), [2 ^ 250, 2 ^ 250, 2 ^ 250]⟩, ⟨(), [2 ^ 250, 2 ^ 250, 2 ^ 250]⟩],
    ⟨[4, 3, 6, 5, 2, 1, 10, 9, 0, 11, 8, 7]⟩)

example : runSplit false =
    ([⟨false, [2 * 2 ^ 250]⟩, ⟨false, [2 * 2 ^ 250]⟩, ⟨false, [1]⟩, ⟨true, []⟩,
      ⟨false, [2 * 2 ^ 250]⟩, ⟨false, [2 * 2 ^ 250]⟩, ⟨false, [5]⟩, ⟨true, []⟩],
      ⟨[2, 1, 6, 3, 4, 5, 8, 7, 0, 9, 10, 11]⟩) := by decide +kernel

example : verifyRotationCertificate (runSplit false).1 (runSplit false).2 = true := by
  decide +kernel

example : verifyRotationCertificate (runSplit true).1 (runSplit true).2 = true := by
  decide +kernel

example : ¬ (runSplit false).1.Satisfiable (fun (_ : Bool) (_ : List Bool) => false) := by
  rintro ⟨σ, hσ⟩
  change false = true at hσ
  contradiction

example : (runSplit true).1.Satisfiable (fun (_ : Bool) (_ : List Bool) => true) :=
  ⟨fun _ => false, by decide +kernel⟩

end CslibFrontierTests.CSPGadgetSubstitution
