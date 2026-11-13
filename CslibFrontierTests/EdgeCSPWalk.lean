/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import CslibFrontier.Logics.Propositional.CSP.Edge.Augmenting
import Mathlib.Tactic.FinCases

/-! Concrete edge-CSP augmentations and rejection of final-only validity. -/

namespace CslibFrontierTests.EdgeCSPWalk

open Cslib Cslib.BitString Cslib.Logic.PL Cslib.Logic.PL.CSP

private def equalitySem (_ : Unit) : List Bool → Bool
  | [a, b] => a == b
  | _ => false

-- The identical constraint values retain two different positional identities.
private abbrev doubled : CSP Unit ℕ := [⟨(), [0, 1]⟩, ⟨(), [0, 1]⟩]
private def bad : doubled.OccurrenceLabeling Bool := fun o => o.1.val == 1
private def good : doubled.OccurrenceLabeling Bool := fun _ => false

private theorem doubled_edge : doubled.EdgeInstance := by
  unfold EdgeInstance
  decide

private theorem doubled_even : EdgeInstance.EvenConstraints equalitySem doubled := by
  intro i
  fin_cases i <;>
    exact {
      isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
      parity_eq := by decide }

private theorem bad_valid : ValidLabeling equalitySem bad := by
  intro i
  fin_cases i <;> rfl

private theorem good_valid : ValidLabeling equalitySem good := by
  intro i
  fin_cases i <;> rfl

example : defects bad = {0, 1} := by decide
example : defects good = ∅ := by decide
example : (defects bad).card = 2 := by decide
example : (defects good).card = 0 := by decide

-- Both constraints have the same local tuples as the paper's 00/11 example.
example : localTuple bad 0 = [false, false] ∧ localTuple bad 1 = [true, true] := by decide
example : (EdgeInstance.repair equalitySem good 4 bad).2 = 1 := by decide
example : (defects (EdgeInstance.repair equalitySem good 4 bad).1).card = 0 := by decide

private def summary (w : Walk doubled) : ℕ × ℕ × List (ℕ × ℕ) :=
  (w.start, w.finish, w.steps.map fun (o, p) => (o.1.val, p.1.val))

-- The deterministic scan starts at 1 when 0 is excluded, but ends at 0.
example : (EdgeInstance.augmentingWalk equalitySem bad good 0).map summary =
    some (1, 0, [(1, 1)]) := by decide
example : (EdgeInstance.augmentingWalk equalitySem bad good 1).map summary =
    some (0, 1, [(1, 1)]) := by decide
example : (EdgeInstance.augmentingWalk equalitySem bad good 0).map
    (fun w => (localTuple (w.flip bad) 0, localTuple (w.flip bad) 1)) =
      some ([false, false], [false, false]) := by decide

example : ∃ w : Walk doubled, w.IsAugmenting equalitySem bad ∧ w.start ≠ 0 ∧
    (defects (w.flip bad)).card = 0 := by
  obtain ⟨w, _, hw, hstart, _⟩ := doubled_edge.augmentingWalk_spec doubled_even
    bad_valid good_valid (by decide) 0
  refine ⟨w, hw, hstart, ?_⟩
  have hd := hw.card_defects_flip_add_two doubled_edge
  have hb : (defects bad).card = 2 := by decide
  omega

-- A two-step walk crosses an internally consistent variable.
private abbrev triangle : CSP Unit ℕ := [⟨(), [0, 1]⟩, ⟨(), [1, 2]⟩, ⟨(), [2, 0]⟩]
private def triangleBad : triangle.OccurrenceLabeling Bool := fun o => o.1.val != 0
private def triangleGood : triangle.OccurrenceLabeling Bool := fun _ => false

example : triangle.EdgeInstance := by unfold EdgeInstance; decide
example : (EdgeInstance.augmentingWalk equalitySem triangleBad triangleGood 1).map
    (fun w => (w.start, w.finish, w.steps.length, (defects (w.flip triangleBad)).card)) =
      some (0, 1, 2, 0) := by decide

-- A closed incidence trail is legal, but cannot be an f-walk with distinct endpoints.
private abbrev closed : Walk doubled :=
  ⟨0, [(⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩),
    (⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩, ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩)]⟩

example : closed.IsWalk := by
  constructor
  · simp only [Walk.Linked]
    decide
  · decide
example : closed.start = closed.finish := rfl
example : ¬ closed.IsFWalk equalitySem bad := fun h => h.2 rfl

-- Opposing unary singleton relations have different common parities. There is one unavoidable
-- defect, and there is no augmentation. Evenness does not mean that every local parity is zero.
private def unitSem (r : Bool) (xs : List Bool) : Bool := xs == [r]
private abbrev opposing : CSP Bool ℕ := [⟨false, [7]⟩, ⟨true, [7]⟩]
private def unitLabels : opposing.OccurrenceLabeling Bool := fun o => o.1.val == 1

private theorem opposing_edge : opposing.EdgeInstance := by
  unfold EdgeInstance
  decide
private theorem opposing_even : EdgeInstance.EvenConstraints unitSem opposing := by
  intro i
  fin_cases i <;>
    exact {
      isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
      parity_eq := by decide }
private theorem unit_valid : ValidLabeling unitSem unitLabels := by
  intro i
  fin_cases i <;> rfl

example : (defects unitLabels).card = 1 := by decide
example : ¬ ∃ w : Walk opposing, w.IsAugmenting unitSem unitLabels := by
  rintro ⟨w, hw⟩
  have hd := hw.card_defects_flip_add_two opposing_edge
  have hc : (defects unitLabels).card = 1 := by decide
  omega
example : EdgeInstance.augmentingWalk unitSem unitLabels unitLabels 7 = none := by decide
example (g : opposing.OccurrenceLabeling Bool) (hg : ValidLabeling unitSem g) :
    (defects g).card % 2 = 1 := by
  have hp := opposing_edge.card_defects_mod_two_eq opposing_even hg unit_valid
  exact hp
example : ¬ opposing.Satisfiable unitSem := by
  rintro ⟨σ, hσ⟩
  cases h : σ 7 <;> simp [CSP.eval, Constraint.eval, unitSem, h] at hσ

-- No occurrences in empty or nullary instances; nullary validity still matters.
private abbrev empty : CSP Bool ℕ := []
private abbrev nullary : CSP Bool ℕ := [⟨true, []⟩]
private def nullarySem (r : Bool) (_ : List Bool) : Bool := r

example (f : empty.OccurrenceLabeling Bool) : defects f = ∅ := by
  apply (defects_eq_empty_iff f).mpr
  intro o
  exact Fin.elim0 o.1
example : EdgeInstance.augmentingWalk nullarySem
    (F := empty) (fun _ => false) (fun _ => false) 0 = none := by decide
example : EdgeInstance.EvenConstraints nullarySem empty := fun i => Fin.elim0 i
example : EdgeInstance.EvenConstraints nullarySem nullary := by
  intro i
  fin_cases i
  exact {
    isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
    parity_eq := by decide }
example : (defects (F := nullary) (fun _ => false)).card = 0 := by decide
example : nullary.Satisfiable nullarySem := ⟨fun _ => false, rfl⟩
example : ¬ CSP.Satisfiable nullarySem ([⟨false, []⟩] : CSP Bool ℕ) := by
  rintro ⟨_, h⟩
  cases h

-- A real trail visits constraint position 0 twice. Its final flip is valid, but its first
-- variable-ended prefix is invalid: final validity is insufficient for an f-walk.
private def shortcutSem (r : Bool) : List Bool → Bool
  | [a, b, c, d] => !r && (a == c) && (b == d)
  | [a, b] => r && (a == b)
  | [a] => r && !a
  | _ => false
private abbrev shortcut : CSP Bool ℕ :=
  [⟨false, [0, 1, 2, 3]⟩, ⟨true, [1, 2]⟩, ⟨true, [0]⟩, ⟨true, [3]⟩]
private def shortcutLabels : shortcut.OccurrenceLabeling Bool := fun _ => false
private abbrev shortcutWalk : Walk shortcut :=
  ⟨0, [(⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩),
    (⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩),
    (⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩, ⟨⟨0, by decide⟩, ⟨3, by decide⟩⟩)]⟩

example : shortcut.EdgeInstance := by unfold EdgeInstance; decide
example : EdgeInstance.EvenConstraints shortcutSem shortcut := by
  intro i
  fin_cases i <;>
    exact {
      isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
      parity_eq := by decide }
example : shortcutWalk.IsWalk := by
  constructor
  · simp only [Walk.Linked]
    decide
  · decide
example : ValidLabeling shortcutSem shortcutLabels := by
  intro i
  fin_cases i <;> rfl
example : ValidLabeling shortcutSem (shortcutWalk.flip shortcutLabels) := by
  intro i
  fin_cases i <;> decide
example : shortcutWalk.start ≠ shortcutWalk.finish := by decide
example : Walk.InternallyConsistent shortcutLabels shortcutWalk.steps := by
  simp only [Walk.InternallyConsistent]
  decide
example : ¬ shortcutWalk.IsFWalk shortcutSem shortcutLabels := by
  intro hw
  have hv := hw.1.2.2.2.1
  have hfail : ¬ ValidLabeling shortcutSem
      (flipOn {⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩,
        ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩} shortcutLabels) := by
    intro h
    have h0 := h 0
    change false = true at h0
    cases h0
  exact hfail hv

end CslibFrontierTests.EdgeCSPWalk
