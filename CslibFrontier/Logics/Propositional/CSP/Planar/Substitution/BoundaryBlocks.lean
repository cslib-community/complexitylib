/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.Table
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Relabel

/-!
# Reading fixed substitution blocks from actual gadget boundary tables

The free-port block starts immediately after that port's structural probe dart. Auxiliary
blocks use the original body's first occurrence. Block entries are original local edge-list
positions, independent of later source variable names or coincidences. Unused auxiliary names
produce empty blocks. These are explicit scans of the supplied fixed table; they do not search
for a rotation. Preprocessing is static and nonuniform in the fixed gadget/language size.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph.RotationCertificate

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {n : ℕ} {R : Set (Fin n → Bool)}

/-- Re-encoding the gadget ports as the existing uniform Boolean/index template retains the
literal accepted boundary table and ordered free-port positions. -/
def templateBoundary (g : PPGadget arity sem R) (w : GadgetWitness g) :
    Witness g.template (List.ofFn (fun i : Fin n => (false, i.val))) := by
  let f : Fin n ⊕ Fin g.numAux → Bool × ℕ :=
    Sum.elim (fun i => (false, i.val)) (fun i => (true, i.val))
  have hi : Function.Injective f := by
    intro x y he
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Fin.ext (congrArg Prod.snd he))
      | inr y => exact False.elim (Bool.false_ne_true (congrArg Prod.fst he))
    | inr x =>
      cases y with
      | inl y => exact False.elim (Bool.false_ne_true (congrArg Prod.fst he).symm)
      | inr y => exact congrArg Sum.inr (Fin.ext (congrArg Prod.snd he))
  have ht := w.relabel f (fun _ _ _ _ he => hi he)
  simpa only [PPGadget.template, List.map_ofFn, Function.comp_def, f, Sum.elim_inl] using ht

/-- Local body edge positions in forward cyclic order after each free port's probe corner.
The reverse probe scope places port `i` at appended edge `bodyOccurrences+n-1-i`. -/
@[expose] def freeBoundaryBlocks (g : PPGadget arity sem R) (w : GadgetWitness g) :
    List (List ℕ) :=
  (List.finRange n).map fun i =>
    ((cycleWord w.certificate (2 * (g.body.vars.length + (n - 1 - i.val)))).tail).map (· / 2)

/-- Auxiliary corner cycles from the actual body restriction. Unused existential labels
remain in the gadget semantics but contribute no target darts. -/
@[expose] def auxiliaryBoundaryBlocks (g : PPGadget arity sem R) (w : GadgetWitness g) :
    List (List ℕ) :=
  (List.finRange g.numAux).map fun j =>
    if Sum.inr j ∈ g.body.vars then
      (cycleWord (bodyCertificate g.body w.certificate)
        (2 * g.body.vars.idxOf (Sum.inr j))).map (· / 2)
    else []

/-- Free block selection has exactly one entry for every actual declared free port. -/
theorem length_freeBoundaryBlocks (g : PPGadget arity sem R) (w : GadgetWitness g) :
    (freeBoundaryBlocks g w).length = n := by simp [freeBoundaryBlocks]

/-- Auxiliary block selection includes each declared existential index, including empty blocks. -/
theorem length_auxiliaryBoundaryBlocks (g : PPGadget arity sem R) (w : GadgetWitness g) :
    (auxiliaryBoundaryBlocks g w).length = g.numAux := by simp [auxiliaryBoundaryBlocks]

end Cslib.Complexity.CSP.GadgetRotation
