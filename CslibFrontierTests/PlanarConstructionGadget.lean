/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import CslibFrontier.Logics.Propositional.CSP.Planar.OneInThree.Gadget

/-! Original-language interpretation tests. The main language has just one ternary symbol:
one-in-three. Neither pins nor disequality are symbols of this language. -/

namespace CslibFrontierTests.PlanarConstructionGadget

open Cslib Cslib.BitString Cslib.Logic Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Logic.PL.CSP.RelationMinor Cslib.Logic.PL.CSP.NonSelfDual

private abbrev arity : Unit → ℕ := fun _ => 3

private instance (a : Fin 3 → Bool) : Decidable (a ∈ oneHotRelation (Fin 3)) :=
  inferInstanceAs (Decidable (∃ i : Fin 3, (fun j => decide (j = i)) = a))

private def sem (_ : Unit) : List Bool → Bool
  | [a, b, c] => decide (![a, b, c] ∈ oneHotRelation (Fin 3))
  | _ => false

private abbrev relation : Set (Fin 3 → Bool) := booleanRelation arity sem ()

private instance : DecidablePred (· ∈ relation) := fun a =>
  inferInstanceAs (Decidable (sem () (List.ofFn a) = true))

private theorem not_schaefer : ¬HasSchaeferPolymorphism arity sem := by
  intro h
  rcases h with h | h | h | h | h | h
  · have hh := h () (fun _ => ![true, false, false]) (by decide)
    exact Bool.false_ne_true hh
  · have hh := h () (fun _ => ![true, false, false]) (by decide)
    exact Bool.false_ne_true hh
  · have hh := h () ![![true, false, false], ![false, true, false]] (by decide)
    exact Bool.false_ne_true hh
  · have hh := h () ![![true, false, false], ![false, true, false]] (by decide)
    exact Bool.false_ne_true hh
  · have hh := h ()
      ![![true, false, false], ![false, true, false], ![false, false, true]] (by decide)
    exact Bool.false_ne_true hh
  · have hh := h ()
      ![![true, false, false], ![false, true, false], ![false, false, true]] (by decide)
    exact Bool.false_ne_true hh

private theorem not_complement : ¬HasPolymorphism arity sem
    (fun a : Fin 1 → Bool => !(a 0)) := by
  intro h
  have hh := h () (fun _ => ![true, false, false]) (by decide)
  exact Bool.false_ne_true hh

-- These are concrete recipes, independent of the noncomputable witness selection.
private def falsePin : PPGadget arity sem (pin false) :=
  (((PPGadget.atom ()).equalDrop).project 1).retarget (by
    unfold pin project adjacent booleanRelation
    decide)

private def truePin : PPGadget arity sem (pin true) :=
  (((PPGadget.atom ()).equalDrop).project 0).retarget (by
    unfold pin project adjacent booleanRelation
    decide)

private def unequal : PPGadget arity sem disequality :=
  ((PPGadget.atom ()).cofactor 2 false falsePin).retarget (by
    unfold disequality cofactor booleanRelation
    decide)

-- Exact atom order and adjacent identification, followed by the selected hidden port.
example : (PPGadget.atom (arity := arity) (sem := sem) ()).body =
    [((), [.inl 0, .inl 1, .inl 2])] := rfl

example : falsePin.body =
    ([((), [.inl 0, .inl 0, .inr 0])] : CSP Unit (Fin 1 ⊕ Fin 1)) := rfl

example : truePin.body =
    ([((), [.inr 0, .inr 0, .inl 0])] : CSP Unit (Fin 1 ⊕ Fin 1)) := rfl

example : unequal.body =
    ([((), [.inl 0, .inl 1, .inr 0]), ((), [.inr 0, .inr 0, .inr 1])] :
      CSP Unit (Fin 2 ⊕ Fin 2)) := rfl

-- Two occurrences require DIFFERENT witnesses: falsePin's hidden bit is true, whereas
-- truePin's hidden bit is false. A shared auxiliary would make this conjunction inconsistent.
private def oppositePins : PPGadget arity sem
    ({a : Fin 2 → Bool | a 0 = false} ∩ {a | a 1 = true}) :=
  (falsePin.relabelFree (fun _ => 0)).conj (truePin.relabelFree (fun _ => 1))

example : oppositePins.numAux = 2 := rfl

example : oppositePins.body =
    ([((), [.inl 0, .inl 0, .inr 0]), ((), [.inr 1, .inr 1, .inl 1])] :
      CSP Unit (Fin 2 ⊕ Fin 2)) := rfl

example : oppositePins.body.eval sem
    (Sum.elim ![false, true] ![true, false]) = true := by decide

example : ∀ b : Bool, oppositePins.body.eval sem
    (Sum.elim ![false, true] (fun _ => b)) = false := by decide

-- Projection keeps survivor order, including a deleted middle coordinate.
example : ((PPGadget.atom (arity := arity) (sem := sem) ()).project 1).body =
    ([((), [.inl 0, .inr 0, .inl 1])] : CSP Unit (Fin 2 ⊕ Fin 1)) := rfl

example : ((PPGadget.atom (arity := arity) (sem := sem) ()).relabelFree
    (fun i : Fin 3 => i + 1)).body = [((), [.inl 1, .inl 2, .inl 0])] := by decide

example : ((PPGadget.atom (arity := arity) (sem := sem) ()).flip 1 unequal).body =
    ([((), [.inl 0, .inr 0, .inl 2]),
      ((), [.inl 1, .inr 0, .inr 1]), ((), [.inr 1, .inr 1, .inr 2])] :
      CSP Unit (Fin 3 ⊕ Fin 3)) := rfl

example : ((PPGadget.atom (arity := arity) (sem := sem) ()).differentDrop unequal).body =
    ([((), [.inr 0, .inl 0, .inl 1]),
      ((), [.inr 0, .inl 0, .inr 1]), ((), [.inr 1, .inr 1, .inr 2])] :
      CSP Unit (Fin 2 ⊕ Fin 3)) := rfl

-- Exercise recursive interpretation, including binary intersection and enabling trees.
private def atomTree : Construction arity sem relation := .atom ()

example : (Construction.project atomTree 1).gadget.body =
    ([((), [.inl 0, .inr 0, .inl 1])] : CSP Unit (Fin 2 ⊕ Fin 1)) := rfl

example : (Construction.rotate atomTree).gadget.body =
    [((), [.inl 1, .inl 2, .inl 0])] := by decide

example : (Construction.binaryMeet (.project atomTree 0) (.project atomTree 2)).gadget.body =
    ([((), [.inr 0, .inl 0, .inl 1]), ((), [.inl 0, .inl 1, .inr 1])] :
      CSP Unit (Fin 2 ⊕ Fin 2)) := rfl

-- The endpoint theorem's hypotheses are realized by this SINGLE original symbol.
private noncomputable def derived : PPGadget arity sem (oneHotRelation (Fin 3)) :=
  Classical.choice (exists_oneHotGadget not_schaefer not_complement)

example : ∃ b, derived.body.eval sem (Sum.elim ![false, true, false] b) = true :=
  (derived.correct _).mp ⟨1, by decide⟩

example : ¬∃ b, derived.body.eval sem (Sum.elim ![false, false, false] b) = true := by
  rw [← derived.correct]
  decide

example : ¬∃ b, derived.body.eval sem (Sum.elim ![true, false, true] b) = true := by
  rw [← derived.correct]
  decide

private noncomputable def derivedUnequal : PPGadget arity sem disequality :=
  Classical.choice (exists_disequalityGadget not_schaefer)

example : ∃ b, derivedUnequal.body.eval sem (Sum.elim ![true, false] b) = true :=
  (derivedUnequal.correct _).mp (by decide)

example : ¬∃ b, derivedUnequal.body.eval sem (Sum.elim ![true, true] b) = true := by
  rw [← derivedUnequal.correct]
  decide

-- A concrete expanded triangle also tests macro order and fresh copies of a nonempty body.
private def nandGadget : PPGadget arity sem nand :=
  ((PPGadget.atom ()).project 2).retarget (by
    unfold nand project booleanRelation
    decide)

private def expanded : PPGadget arity sem (oneHotRelation (Fin 3)) :=
  triangleGadget (PPGadget.atom ()) nandGadget (by decide) (by decide)

example : expanded.numAux = 3 := rfl

example : expanded.body =
    ([((), [.inl 0, .inl 1, .inl 2]),
      ((), [.inl 0, .inl 1, .inr 0]),
      ((), [.inl 1, .inl 2, .inr 1]),
      ((), [.inl 2, .inl 0, .inr 2])] : CSP Unit (Fin 3 ⊕ Fin 3)) := rfl

example : expanded.body.eval sem (Sum.elim ![false, true, false] ![false, false, true]) =
    true := by decide

-- The repeated NAND template needs false on the first two auxiliary blocks and true on
-- the last: identifying the three copies' auxiliaries would reject this one-hot tuple.
example : ∀ b : Bool, expanded.body.eval sem
    (Sum.elim ![false, true, false] (fun _ => b)) = false := by decide

example : ∀ b, expanded.body.eval sem (Sum.elim ![true, false, true] b) = false := by decide

-- Nullary atoms and malformed-width guards are independent of the one-in-three language.
private abbrev nullaryArity : Bool → ℕ := fun _ => 0

private def nullarySem (r : Bool) : List Bool → Bool
  | [] => r
  | _ => false

example : (PPGadget.atom (arity := nullaryArity) (sem := nullarySem) true).body =
    [(true, [])] := rfl

example : ∃ b, (PPGadget.atom (arity := nullaryArity) (sem := nullarySem) true).body.eval
    nullarySem (Sum.elim Fin.elim0 b) = true := by decide

example : ¬∃ b, (PPGadget.atom (arity := nullaryArity) (sem := nullarySem) false).body.eval
    nullarySem (Sum.elim Fin.elim0 b) = true := by decide

example : validArity arity ([((), [0, 1])] : CSP Unit ℕ) = false := rfl
example : validArity nullaryArity ([(true, [0])] : CSP Bool ℕ) = false := rfl

end CslibFrontierTests.PlanarConstructionGadget
