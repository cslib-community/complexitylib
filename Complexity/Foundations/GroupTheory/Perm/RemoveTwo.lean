/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate (Mathlib)

public import Complexity.Init
public import Mathlib.Logic.Equiv.Option

/-!
# First return after removing two permutation points

Removing the two `Option` points keeps the first retained successor. Permutation injectivity
rules out revisiting a deleted point before reaching a retained point, so at most three
successor steps are needed. The five possible directed paths are explicit, with no finite
carrier or equality-decision assumption. This is an original elementary reconstruction for
bounded rotation-certificate restriction.
-/

public section

namespace Equiv.Perm

/-- The five possible first-return paths through two removed points. In each case the
retained endpoint is exactly the twice-`removeNone` successor; the two three-step cases
preserve the order of visits to the removed points. -/
theorem removeNone_removeNone_paths {α : Type*} (f : Perm (Option (Option α))) (a : α) :
    let b := Equiv.removeNone (Equiv.removeNone f) a
    f (some (some a)) = some (some b) ∨
      (f (some (some a)) = none ∧ f none = some (some b)) ∨
      (f (some (some a)) = some none ∧ f (some none) = some (some b)) ∨
      (f (some (some a)) = none ∧ f none = some none ∧
        f (some none) = some (some b)) ∨
      (f (some (some a)) = some none ∧ f (some none) = none ∧
        f none = some (some b)) := by
  cases ha : f (some (some a)) with
  | none =>
    cases hb : f none with
    | none => cases f.injective (ha.trans hb.symm)
    | some t =>
      cases t with
      | some b =>
        have he : Equiv.removeNone (Equiv.removeNone f) a = b := by
          simp [Equiv.removeNone, Equiv.removeNoneAux, ha, hb]
        rw [he]
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | none =>
        cases hc : f (some none) with
        | none => cases f.injective (ha.trans hc.symm)
        | some s =>
          cases s with
          | none => cases f.injective (hb.trans hc.symm)
          | some b =>
            have he : Equiv.removeNone (Equiv.removeNone f) a = b := by
              simp [Equiv.removeNone, Equiv.removeNoneAux, ha, hb, hc]
            rw [he]
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  | some t =>
    cases t with
    | some b =>
      have he : Equiv.removeNone (Equiv.removeNone f) a = b := by
        simp [Equiv.removeNone, Equiv.removeNoneAux, ha]
      rw [he]
      exact Or.inl rfl
    | none =>
      cases hb : f (some none) with
      | none =>
        cases hc : f none with
        | none => cases f.injective (hb.trans hc.symm)
        | some s =>
          cases s with
          | none => cases f.injective (ha.trans hc.symm)
          | some b =>
            have he : Equiv.removeNone (Equiv.removeNone f) a = b := by
              simp [Equiv.removeNone, Equiv.removeNoneAux, ha, hb, hc]
            rw [he]
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))
      | some s =>
        cases s with
        | none => cases f.injective (ha.trans hb.symm)
        | some b =>
          have he : Equiv.removeNone (Equiv.removeNone f) a = b := by
            simp [Equiv.removeNone, Equiv.removeNoneAux, ha, hb]
          rw [he]
          exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

end Equiv.Perm
