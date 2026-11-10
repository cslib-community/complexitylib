/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Finite

/-! Finite dispatch retains an unbounded captured word and admits empty tags. -/

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

-- The finite tag is fixed, but the selected word can grow without bound.
example : ComputableInSpace (fun p : Bool × List Bool => if p.1 then p.2 else [])
    (encPair encBool encBits) encBits (fun p => (encPair encBool encBits p).length) := by
  have hbranches (choice : Bool) : ComputableInSpace
      (fun p : Bool × List Bool => if choice then p.2 else [])
      (encPair encBool encBits) encBits (fun p => (encPair encBool encBits p).length) := by
    cases choice
    · exact budget_const [] (.refl _)
    · exact snd encBool encBits
  exact finite_cases (fst encBool encBits) hbranches

private def encEmpty : Empty ↪ List Bool := ⟨Empty.elim, fun value => value.elim⟩

example : ComputableInSpace (fun a : Empty => (Empty.elim a : Bool))
    encEmpty encBool (fun a => (encEmpty a).length) := by
  exact finite_cases (tagEncoding := encEmpty) (tag := fun a : Empty => a)
    (branch := fun choice _ => Empty.elim choice)
    (of_finite _) (fun choice => Empty.elim choice)
