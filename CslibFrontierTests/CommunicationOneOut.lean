/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Communication.Forcing
import CslibFrontier.Computability.Communication.OneOut
import Mathlib.Tactic

/-! Concrete forcing, steering and distinct-tuple clients for submission 865's prerequisites. -/

namespace CslibFrontierTests.CommunicationOneOut
open Cslib.Communication Protocol

/-- All four output pairs are different leaf occurrences. The original messages are constant;
steering must replace them to meet the two input-dependent goals. -/
def tree : Protocol Bool Bool (Bool × Bool) :=
  .alice (fun _ => false)
    (.bob (fun _ => false) (.output (false, false)) (.output (false, true)))
    (.bob (fun _ => false) (.output (true, false)) (.output (true, true)))

example (x y : Bool) :
    (tree.steer (fun x z => z.1 = x) (fun y z => z.2 = y)).run x y = (x, y) := by
  have h := run_steer tree (fun x z => z.1 = x) (fun y z => z.2 = y) x y
    (by cases x <;> simp [tree, CanForce]) (by cases y <;> simp [tree, CanForce])
  exact Prod.ext h.1 h.2

example : tree.depth = 2 := rfl
example : ¬ tree.CanForce true (fun z => z.2 = true) := by simp [tree, CanForce]
example : tree.CanForce false (fun z => z.2 = true) := by simp [tree, CanForce]

example : OneOut.Relation (fun x y z : Fin 2 => x = z ∧ y = z)
    (Function.Embedding.refl _) (Function.Embedding.refl _) ⟨0, 0⟩ := ⟨rfl, rfl⟩

example : ¬ OneOut.Relation (fun x y z : Fin 2 => x = z ∧ y = z)
    (Function.Embedding.refl _) (Function.Embedding.refl _) ⟨0, 1⟩ := by
  simp [OneOut.Relation]

/-- Equal output values do not identify the two leaf occurrences. -/
example :
    ((Protocol.alice id (.output false) (.output false) : Protocol Bool Bool Bool).labelLeaves.run
      false false) ≠
    ((Protocol.alice id (.output false) (.output false) : Protocol Bool Bool Bool).labelLeaves.run
      true false) := by
  simp [labelLeaves]

/-- No indexed output exists when there are no instances. -/
example (z : OneOut.Answer 0 Bool) : False := Fin.elim0 z.index

end CslibFrontierTests.CommunicationOneOut
