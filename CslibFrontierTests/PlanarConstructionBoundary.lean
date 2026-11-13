/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Construction

/-! Full original-language construction trees and their exact primitive bodies. The only
language symbol is one-in-three: neither pins nor disequality are added symbols. -/

namespace CslibFrontierTests.PlanarConstructionBoundary

open Cslib Cslib.BitString Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Logic.PL.CSP.RelationMinor Cslib.Complexity.CSP.OrderedBoundary

private abbrev arity : Unit → ℕ := fun _ => 3

private def sem (_ : Unit) : List Bool → Bool
  | [a, b, c] => (a && !b && !c) || (!a && b && !c) || (!a && !b && c)
  | _ => false

private abbrev relation : Set (Fin 3 → Bool) := booleanRelation arity sem ()

private def atomTree : Construction arity sem relation := .atom ()

private theorem falsePin_eq : project (adjacent relation false) 1 = pin false := by
  ext a
  unfold pin project adjacent relation booleanRelation
  decide +revert

private theorem truePin_eq : project (adjacent relation false) 0 = pin true := by
  ext a
  unfold pin project adjacent relation booleanRelation
  decide +revert

private def falseTree : Construction arity sem (pin false) :=
  falsePin_eq ▸ Construction.project (.equalDrop atomTree) 1

private def trueTree : Construction arity sem (pin true) :=
  truePin_eq ▸ Construction.project (.equalDrop atomTree) 0

private theorem unequal_eq : cofactor relation 2 false = disequality := by
  ext a
  unfold disequality cofactor relation booleanRelation
  decide +revert

private def unequalTree : Construction arity sem disequality :=
  unequal_eq ▸ Construction.cofactor atomTree 2 false falseTree

-- Every enabling recipe is a genuine subtree. This exercises all eight grammar branches.
private def binaryTree := Construction.binaryMeet
  (.differentDrop (.flip (.rotate atomTree) 2 unequalTree) unequalTree)
  (.project atomTree 1)

private noncomputable def binaryWitness : GadgetWitness binaryTree.gadget :=
  binaryTree.orderedWitness

example : verify binaryTree.gadget.body (List.ofFn Sum.inl)
    binaryWitness.certificate = true := binaryWitness.accepted

example : ∃ z, binaryTree.gadget.body.eval sem (Sum.elim ![false, true] z) = true :=
  (binaryTree.gadget.correct _).mp (by
    unfold adjacent twist rotate project relation booleanRelation
    decide)

example : ¬∃ z, binaryTree.gadget.body.eval sem (Sum.elim ![true, true] z) = true := by
  rw [← binaryTree.gadget.correct]
  unfold adjacent twist rotate project relation booleanRelation
  decide

example : ¬∃ z, binaryTree.gadget.body.eval sem (Sum.elim ![false, false] z) = true := by
  rw [← binaryTree.gadget.correct]
  unfold adjacent twist rotate project relation booleanRelation
  decide

private def closedTree := Construction.project
  (.cofactor binaryTree 1 true trueTree) 0

example : verify closedTree.gadget.body [] closedTree.orderedWitness.certificate = true :=
  closedTree.orderedWitness.accepted

example : ∃ z, closedTree.gadget.body.eval sem (Sum.elim Fin.elim0 z) = true :=
  (closedTree.gadget.correct _).mp (by
    unfold project cofactor adjacent twist rotate relation booleanRelation
    decide)

-- Explicit primitive recipes retain all row positions and auxiliary blocks, so these
-- kernel checks do not require computing the noncomputably selected witness tables.
private def falsePin : PPGadget arity sem (pin false) :=
  (((PPGadget.atom ()).equalDrop).project 1).retarget (by
    intro a
    exact Set.ext_iff.mp falsePin_eq a |>.symm)

private noncomputable def falseWitness : GadgetWitness falsePin :=
  let w := ((Witness.atom arity sem ()).equalDrop).project 1
  ⟨w.certificate, w.accepted⟩

private def unequal : PPGadget arity sem disequality :=
  ((PPGadget.atom ()).cofactor 2 false falsePin).retarget (by
    intro a
    exact Set.ext_iff.mp unequal_eq a |>.symm)

private noncomputable def unequalWitness : GadgetWitness unequal :=
  let w := (Witness.atom arity sem ()).cofactor 2 false falseWitness
  ⟨w.certificate, w.accepted⟩

private def flipped := (PPGadget.atom (arity := arity) (sem := sem) ()).flip 1 unequal

private noncomputable def flipWitness : GadgetWitness flipped :=
  (Witness.atom arity sem ()).flip 1 unequalWitness

example : flipped.body =
    ([⟨(), [.inl 0, .inr 0, .inl 2]⟩,
      ⟨(), [.inl 1, .inr 0, .inr 1]⟩, ⟨(), [.inr 1, .inr 1, .inr 2]⟩] :
      CSP Unit (Fin 3 ⊕ Fin 3)) := rfl

example : verify flipped.body (List.ofFn Sum.inl) flipWitness.certificate = true :=
  flipWitness.accepted

example : flipped.body.eval sem (Sum.elim ![true, true, false] ![false, false, true]) = true :=
  by decide +kernel

example : ∀ z, flipped.body.eval sem (Sum.elim ![true, false, true] z) = false := by
  decide +kernel

private def different := (PPGadget.atom (arity := arity) (sem := sem) ()).differentDrop unequal

example : different.body =
    ([⟨(), [.inr 0, .inl 0, .inl 1]⟩,
      ⟨(), [.inr 0, .inl 0, .inr 1]⟩, ⟨(), [.inr 1, .inr 1, .inr 2]⟩] :
      CSP Unit (Fin 2 ⊕ Fin 3)) := rfl

example : verify different.body (List.ofFn Sum.inl)
    ((Witness.atom arity sem ()).differentDrop unequalWitness).certificate = true :=
  ((Witness.atom arity sem ()).differentDrop unequalWitness).accepted

example : different.body.eval sem (Sum.elim ![true, false] ![false, false, true]) = true :=
  by decide +kernel

example : ∀ z, different.body.eval sem (Sum.elim ![true, true] z) = false := by decide +kernel

-- A reflected table is rejected on this actual ternary original-language atom.
example : verify (PPGadget.atom (arity := arity) (sem := sem) ()).body
    (List.ofFn Sum.inl) ⟨(List.range (atomBoundaryCertificate 3).successor.length).map
      (atomBoundaryCertificate 3).successor.idxOf⟩ = false := by decide +kernel

-- All free ports may be absent from the body. Probe darts, rather than invented isolate
-- darts or positive-occurrence hypotheses, still support every attachment branch.
private def emptyGadget (n : ℕ) : PPGadget arity sem (Set.univ : Set (Fin n → Bool)) where
  numAux := 0
  body := []
  wellFormed := by intro c hc; simp at hc
  correct a := by simp [CSP.eval]

private def emptyWitness (n : ℕ) : GadgetWitness (emptyGadget n) :=
  Witness.empty _ (List.nodup_ofFn.mpr Sum.inl_injective)

example : (emptyGadget 3).body.vars = [] := rfl

example : verify ((emptyGadget 3).flip 1 unequal).body (List.ofFn Sum.inl)
    ((emptyWitness 3).flip 1 unequalWitness).certificate = true :=
  ((emptyWitness 3).flip 1 unequalWitness).accepted

example : verify ((emptyGadget 2).differentDrop unequal).body (List.ofFn Sum.inl)
    ((emptyWitness 2).differentDrop unequalWitness).certificate = true :=
  ((emptyWitness 2).differentDrop unequalWitness).accepted

example : verify ((emptyGadget 1).cofactor 0 false falsePin).body []
    ((emptyWitness 1).cofactor 0 false falseWitness).certificate = true :=
  ((emptyWitness 1).cofactor 0 false falseWitness).accepted

example : ((emptyGadget 1).cofactor 0 false falsePin).body =
    ([⟨(), [.inr 0, .inr 0, .inr 1]⟩] : CSP Unit (Fin 0 ⊕ Fin 2)) := rfl

example : ((emptyGadget 1).cofactor 0 false falsePin).body.eval sem
    (Sum.elim Fin.elim0 ![false, true]) = true := by decide +kernel

example : verify ((emptyGadget 2).conj (emptyGadget 2)).body (List.ofFn Sum.inl)
    ((emptyWitness 2).binaryMeet (emptyWitness 2)).certificate = true :=
  ((emptyWitness 2).binaryMeet (emptyWitness 2)).accepted

example : verify ((emptyGadget 2).equalDrop).body (List.ofFn Sum.inl)
    (emptyWitness 2).equalDrop.certificate = true := (emptyWitness 2).equalDrop.accepted

-- An infinite original symbol type; five identical binary rows give degree five at
-- both free vertices. A nullary original symbol survives as a separate point component.
private abbrev countArity : ℕ → ℕ := id
private def countSem (_ : ℕ) (_ : List Bool) : Bool := true
private def repeatTree := Construction.binaryMeet
  (.atom (arity := countArity) (sem := countSem) 2)
  (.binaryMeet (.atom 2) (.binaryMeet (.atom 2) (.binaryMeet (.atom 2) (.atom 2))))

example : repeatTree.gadget.body = List.replicate 5 ⟨2, [.inl 0, .inl 1]⟩ := rfl

example : repeatTree.gadget.body.vars.count (.inl 0) = 5 := by decide +kernel

example : verify repeatTree.gadget.body (List.ofFn Sum.inl)
    repeatTree.orderedWitness.certificate = true := repeatTree.orderedWitness.accepted

example : repeatTree.gadget.body.eval countSem (Sum.elim ![false, true] Fin.elim0) = true :=
  by decide +kernel

private def nullTree : Construction countArity countSem
    (booleanRelation countArity countSem 0) := .atom 0

example : verify nullTree.gadget.body [] nullTree.orderedWitness.certificate = true :=
  nullTree.orderedWitness.accepted

end CslibFrontierTests.PlanarConstructionBoundary
