/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Fusion.Consistency
import Mathlib.Tactic.FinCases

/-!
# Exact-consistency clients

A three-bit conjunction admits an exactly consistent semifilter, while the nonempty-set
semifilter gives a one-sided witness for the same complete literal family that is not exact.
-/

namespace CslibFrontierTests.FusionConsistency

open Cslib.Circuits.Fusion

private abbrev target : Set (Fin 3 → Bool) := {x | ∀ i, x i = true}
private abbrev point : target := ⟨fun _ => true, fun _ => rfl⟩
private abbrev inputs : Fin (3 + 3) → Set (Fin 3 → Bool) :=
  Fin.append (fun i => {x | x i = true}) (fun i => {x | x i = false})

private def generated : Semifilter ↥(targetᶜ) where
  toFun s := ∃ i : Fin 3, ∀ x : ↥(targetᶜ), x.val i = true → x ∈ s
  monotone' _ _ h hs := hs.imp fun _ hi x hx => h (hi x hx)
  map_top' := by simp
  map_bot' := propext (by
    change (∃ i : Fin 3, ∀ x : ↥(targetᶜ), x.val i = true → False) ↔ False
    decide)

private theorem generated_consistent :
    generated.IsConsistentWith Subtype.val point.val := by
  change ∀ (i : Fin 3) (b : Bool),
    (∃ j : Fin 3, ∀ x : ↥(targetᶜ), x.val j = true → x.val i = b) ↔ true = b
  decide

private def exactWitness : SemifilterWitness target inputs where
  point := point
  filter := generated
  admissible_filter := trivial
  above := by
    intro i h
    fin_cases i <;> exact (generated_consistent _ _).mpr h

private theorem exactWitness_exact : exactWitness.IsExact := by
  intro i
  fin_cases i <;> exact generated_consistent _ _

example (i : Fin (3 + 3)) : exactWitness.observe (inputs i) = inputs i :=
  exactWitness.observe_input exactWitness_exact i

private instance : Nonempty ↥(targetᶜ) := ⟨⟨fun _ => false, by decide⟩⟩

private def nonemptySets : Semifilter ↥(targetᶜ) where
  toFun s := s.Nonempty
  monotone' _ _ h hs := hs.mono h
  map_top' := by simp
  map_bot' := by simp

private def inexactWitness : SemifilterWitness target inputs where
  point := point
  filter := nonemptySets
  admissible_filter := trivial
  above := by
    change ∀ i : Fin (3 + 3), point.val ∈ inputs i →
      ∃ x : ↥(targetᶜ), x.val ∈ inputs i
    intro i h
    fin_cases i
    · exact ⟨⟨![true, false, false], by decide⟩, rfl⟩
    · exact ⟨⟨![false, true, false], by decide⟩, rfl⟩
    · exact ⟨⟨![false, false, true], by decide⟩, rfl⟩
    all_goals exact (Bool.noConfusion h)

example : ¬ inexactWitness.IsExact := by
  intro h
  have := (h 3).mp ⟨⟨fun _ => false, by decide⟩, rfl⟩
  exact Bool.noConfusion this

example : ¬ nonemptySets.IsConsistentWith Subtype.val point.val := by
  intro h
  have := (h 0 false).mp ⟨⟨fun _ => false, by decide⟩, rfl⟩
  exact Bool.noConfusion this

-- Even a nonempty exact witness class need not contain every one-sided witness.
example : Nonempty (SemifilterWitness target inputs) := ⟨exactWitness⟩

end CslibFrontierTests.FusionConsistency
