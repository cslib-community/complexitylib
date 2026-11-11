/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.PebblingWords
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability

/-!
# Tests: pebble configuration words in space

The first difference, readiness and moves on concrete words for the path dependency map, in which
each positive index depends on its predecessor; and the space certificates of readiness, of a move,
of the stored values of the children and of the table updates instantiated on that map with a
pebble bound depending on a parameter, so that their hypotheses are satisfiable; and Savitch's
algorithm run on its moves.
-/

namespace CslibFrontierTests.SpacePebblingWords

open Cslib Cslib.Pebbling Cslib.Pebbling.Descending Turing.MultiTapeTM
  Turing.MultiTapeTM.ComputableInSpace

/-- The path dependency map: index `i` has the single child `i - 1`, for every parameter. -/
private def pathChild (_ : ℕ) (i : ℕ) (_ : Fin 1) : ℕ := i - 1

/-! ### Concrete words -/

example : diffIndex [true, false, true] [true, true, true] = 1 := by decide
example : diffIndex [true, false] [true, false] = 2 := by decide

-- Index `2` is ready once `1` carries a pebble; the source `0` always is.
example : ready (pathChild 0) [false, true, false] 2 = true := by decide
example : ready (pathChild 0) [false, false, false] 2 = false := by decide
example : ready (pathChild 0) [false, false, false] 0 = true := by decide

-- Placing a pebble on the ready index `2`, within two pebbles; not within one.
example : wordStep (ready (pathChild 0)) 2 [false, true, false] [false, true, true] = true := by
  decide
example : wordStep (ready (pathChild 0)) 1 [false, true, false] [false, true, true] = false := by
  decide
-- Index `2` is not ready on the empty configuration; and two bits may not flip at once.
example : wordStep (ready (pathChild 0)) 3 [false, false, false] [false, false, true] = false := by
  decide
example : wordStep (ready (pathChild 0)) 3 [false, false, false] [true, true, false] = false := by
  decide

/-! ### Certificates on the path map -/

/-- The child of the path map, in space linear in its arguments. -/
private theorem pathChild_inSpace (a : Fin 1) :
    ComputableInSpace (fun (p, i) => pathChild p i a) (encPair encNat encNat) encNat
      fun q => (encPair encNat encNat q).length :=
  budget_natPred (snd _ _)

/-- A pebble bound one above the parameter, in space linear in it. -/
private theorem succ_inSpace :
    ComputableInSpace (fun p : ℕ => p + 1) encNat encNat fun p => (encNat p).length :=
  budget_natSucc (budget_id (.refl _))

/-- Readiness on the path map, in linear space. -/
example : ComputableInSpace (fun (p, w, i) => ready (pathChild p) w i)
    (encPair encNat (encPair encBits encNat)) encBool
    fun (p, w, i) => (encPair encNat (encPair encBits encNat) (p, w, i)).length +
      (encPair encNat encNat (p, i)).length :=
  ready_inSpace pathChild_inSpace

/-- A move on the path map with `p + 1` pebbles, in linear space, as an edge test. -/
example : ∃ T, ComputableInO (fun (p, u, v) => wordStep (ready (pathChild p)) (p + 1) u v)
    (encPair encNat (encPair encBits encBits)) encBool T
    fun (p, u, v) => (encPair encNat (encPair encBits encBits) (p, u, v)).length +
      (encPair encNat encNat (p, diffIndex u v)).length + (encNat p).length :=
  (wordStep_inSpace pathChild_inSpace succ_inSpace).exists_inO

/-- Savitch's algorithm decides reachability along moves on the path map, in the space of its stack
plus the parameter and the space of the move test at the given width. -/
example {γ : Type} {encIn : γ ↪ List Bool} {par width depth : γ → ℕ} {src dst : γ → List Bool}
    {Tin Sin : γ → ℕ}
    (hin : ComputableInO (fun x => (par x, width x, depth x, src x, dst x)) encIn
      (Reachability.encArgs encNat) Tin Sin)
    (hsrc : ∀ x, (src x).length = width x) (hdst : ∀ x, (dst x).length = width x) :
    ∃ T, ComputableInO
      (fun x => Reachability.savitch (wordStep (ready (pathChild (par x))) (par x + 1))
        (width x) (depth x) (src x) (dst x))
      encIn encBool T fun x => Sin x + (depth x + 1) * (depth x + width x + 1) +
        (encNat (par x)).length + Reachability.edgeMax (fun (p, u, v) =>
          (encPair encNat (encPair encBits encBits) (p, u, v)).length +
            (encPair encNat encNat (p, diffIndex u v)).length + (encNat p).length)
          (par x) (width x) := by
  obtain ⟨_, hedge⟩ := (wordStep_inSpace pathChild_inSpace succ_inSpace).exists_inO
  exact ⟨_, Reachability.computableInO_savitch
    (edge := fun p u v => wordStep (ready (pathChild p)) (p + 1) u v) hedge hin hsrc hdst⟩

/-- The stored values of the children on the path map, in linear space. -/
example : ComputableInSpace
    (fun (p, t, i) => (List.finRange 1).map fun a => (t.lookup (pathChild p i a)).getD [])
    (encPair encNat (encPair encTable encNat)) (encList encBits)
    fun (p, t, i) => (encPair encNat (encPair encTable encNat) (p, t, i)).length +
      (encPair encNat encNat (p, i)).length :=
  childValues_inSpace pathChild_inSpace

/-! ### Table updates within a budget -/

section Table

variable {α : Type} {encIn : α ↪ List Bool} {Bs : α → ℕ} {t : α → List (ℕ × List Bool)}
  {i s : α → ℕ} {x : α → List Bool}

-- Inserting an entry, clearing an index and testing the size compose from the budget forms.
example (ht : ComputableInSpace t encIn encTable Bs) (hi : ComputableInSpace i encIn encNat Bs)
    (hx : ComputableInSpace x encIn encBits Bs) :
    ComputableInSpace (fun a => (i a, x a) :: t a) encIn encTable Bs :=
  budget_cons (budget_prod hi hx) ht

example (ht : ComputableInSpace t encIn encTable Bs) (hi : ComputableInSpace i encIn encNat Bs) :
    ComputableInSpace (fun a => (t a).filter fun q => q.1 != i a) encIn encTable Bs :=
  budget_erase ht hi

example (ht : ComputableInSpace t encIn encTable Bs) (hs : ComputableInSpace s encIn encNat Bs) :
    ComputableInSpace (fun a => decide ((t a).length < s a)) encIn encBool Bs :=
  budget_natLt (budget_length ht) hs

end Table

-- The stored value at an index, and the table cleared at it.
example : ([(3, [true]), (1, [false, true])].lookup 1).getD [] = [false, true] := by decide
example : ([(3, [true])].lookup 1).getD [] = [] := by decide
example : [(3, [true]), (1, [false, true])].filter (fun q => q.1 != 3) = [(1, [false, true])] := by
  decide

end CslibFrontierTests.SpacePebblingWords
