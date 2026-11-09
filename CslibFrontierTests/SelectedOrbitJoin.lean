/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Foundations.GroupTheory.Perm.SelectedOrbitJoin

/-! Graph-free complete-orbit joins include fixed points and empty selections. -/

namespace CslibFrontierTests.SelectedOrbitJoin

open Equiv Equiv.Perm.SelectedOrbits

-- Two fixed points join into one selected orbit, in either successor convention.
example : Nat.card (OrbitOn (swap (0 : Fin 3) 1 * (1 : Perm (Fin 3))) (fun _ => True)) + 1 =
    Nat.card (OrbitOn (1 : Perm (Fin 3)) (fun _ => True)) := by
  simpa only [ite_true] using card_orbitOn_swap_mul_of_not_sameCycle (1 : Perm (Fin 3))
    (fun _ => True) (fun _ => Iff.rfl) 0 1 Iff.rfl
    (by intro h; have he := Perm.sameCycle_one.mp h; exact (by decide : (0 : Fin 3) ≠ 1) he)

example : Nat.card (OrbitOn ((1 : Perm (Fin 3)) * swap (0 : Fin 3) 1) (fun _ => False)) =
    Nat.card (OrbitOn (1 : Perm (Fin 3)) (fun _ => False)) := by
  simpa only [ite_false, Nat.add_zero] using card_orbitOn_mul_swap_of_not_sameCycle
    (1 : Perm (Fin 3)) (fun _ => False) (fun _ => Iff.rfl) 0 1 Iff.rfl
    (by intro h; have he := Perm.sameCycle_one.mp h; exact (by decide : (0 : Fin 3) ≠ 1) he)

example : Nat.card (OrbitOn (1 : Perm (Fin 3)) (fun i => i = 0 ∨ i = 1)) =
    Nat.card (OrbitOn (1 : Perm (Fin 3)) (· = 0)) +
      Nat.card (OrbitOn (1 : Perm (Fin 3)) (· = 1)) := by
  apply card_orbitOn_union _ _ _ (fun _ => Iff.rfl)
  intro t ht hs a ha
  exact (by decide : (0 : Fin 3) ≠ 1) ((ht a ha).symm.trans (hs a ha))

example : Nat.card (OrbitOn (sumCongr (1 : Perm Empty) (1 : Perm (Fin 1)))
      (Sum.elim (fun _ => False) (fun _ => True))) =
    Nat.card (OrbitOn (1 : Perm Empty) (fun _ => False)) +
      Nat.card (OrbitOn (1 : Perm (Fin 1)) (fun _ => True)) :=
  card_orbitOn_sum _ _ _ _

end CslibFrontierTests.SelectedOrbitJoin
