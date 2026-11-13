/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.WordGame

/-!
# Tests for potential bounds on alternating word games

A finite-state preparation writes a two-bit position. The round machine erases its second
cell and returns its head to the origin. Depending on the move bit it takes three or four
steps. The potential pays for the slower move as well as the three dispatch steps, on both
existential and universal positions. The identity update is a negative termination example.
-/

namespace CslibFrontierTests.WordGamePotential

open Turing Turing.MultiTapeTM Turing.MultiTapeATM Turing.MultiTapeATM.WordGame

private def prepare (u : Bool) : MultiTapeTM 1 Bool (Fin 3) :=
  .ofTr 0 fun q _ _ => match q.val with
    | 0 => ⟨0, fun _ => (some (some u), 1), none, some 1⟩
    | 1 => ⟨0, fun _ => (some (some false), -1), none, some 2⟩
    | _ => ⟨0, fun _ => (none, 0), none, none⟩

private def eraseSecond : MultiTapeTM 1 Bool (Fin 4) :=
  .ofTr 0 fun q _ work => match q.val with
    | 0 => ⟨0, fun _ => (none, 1), none, some 1⟩
    | 1 => ⟨0, fun _ => (some none, -1), none,
        some (if work 0 = some true then 2 else 3)⟩
    | 2 => ⟨0, fun _ => (none, 0), none, some 3⟩
    | _ => ⟨0, fun _ => (none, 0), none, none⟩

private def update : List Bool → List Bool := List.take 1

private def potential (w : List Bool) : ℕ := if 2 ≤ w.length then 7 else 0

private theorem reachable_shape (u : Bool) {w : List Bool}
    (h : Reach update [u, false] w) : w = [u, false] ∨ w = [u] := by
  induction h with
  | start => exact Or.inl rfl
  | @move v x r b h ih =>
    rcases ih with h | h
    · cases h
      exact Or.inr rfl
    · simp at h

private theorem prepare_run (u : Bool) :
    (prepare u).runFrom (Cfg.init (prepare u).q₀ []) 3 =
      wordsCfg [] none (Function.update (fun _ => []) 0 [u, false]) [] := by
  have hsingle : tapeOfList [u] = Function.update (fun _ => none) 0 (some u) := by
    simpa using tapeOfList_append_single ([] : List Bool) u
  have hpair : tapeOfList [u, false] = Function.update (tapeOfList [u]) 1 (some false) :=
    tapeOfList_append_single [u] false
  simp [MultiTapeTM.runFrom, Function.iterate_succ_apply', MultiTapeTM.step_of_state,
    MultiTapeTM.tr_ofTr, prepare, Action.apply, Cfg.init, wordsCfg, hpair, hsingle, funext_iff]

private theorem eraseSecond_run (u b : Bool) :
    eraseSecond.runFrom
      (wordsCfg [] (some eraseSecond.q₀) (Function.update (fun _ => []) 0 [u, b]) [])
      (if b then 4 else 3) =
      wordsCfg [] none (Function.update (fun _ => []) 0 [u]) [] := by
  have hpair : tapeOfList [u, b] = Function.update (tapeOfList [u]) 1 (some b) :=
    tapeOfList_append_single [u] b
  have herase : Function.update (tapeOfList [u, b]) 1 none = tapeOfList [u] := by
    rw [hpair, Function.update_idem]
    exact Function.update_eq_self_iff.mpr rfl
  have hread : tapeOfList [u, b] (1 : ℤ) = some b := rfl
  cases b <;>
    simp [MultiTapeTM.runFrom, Function.iterate_succ_apply', MultiTapeTM.step_of_state,
      MultiTapeTM.tr_ofTr, eraseSecond, Action.apply, Cfg.workTapeSymbols, wordsCfg,
      hread, herase, funext_iff]

/-- The same exact branch-time bound covers existential and universal starting positions. -/
example (u : Bool) : (wordGame (prepare u) eraseSecond 0).toPTM.toNTM.RunsInTime [] 12 := by
  apply runsInTime_wordGame_of_potential (U := update) potential (prepare_run u)
  intro v x r h b
  rcases reachable_shape u h with h | h
  · cases h
    refine ⟨if b then 4 else 3, eraseSecond_run u b, ?_⟩
    cases b <;> simp [potential, update]
  · simp at h

/-- Dropping the first symbol strictly decreases length, regardless of the player. -/
example (w : List Bool) : Ends List.tail w.length w :=
  Ends.of_potential List.length fun _ _ _ _ _ => by simp

/-- A terminal position needs no positive potential. -/
example : Ends id 0 [true] :=
  Ends.of_potential (fun _ => 0) fun u x r h _ => by
    have he : Ends id 0 (u :: x :: r) :=
      (show Ends id 0 [true] from trivial).of_reach h
    exact he.elim

/-- A self-loop cannot pay even the dispatch overhead with a natural-valued potential. -/
example : ¬ ∃ φ : List Bool → ℕ, ∀ b : Bool,
    3 + φ (id [false, b]) ≤ φ [false, false] := by
  rintro ⟨φ, h⟩
  have := h false
  simp only [id] at this
  omega

end CslibFrontierTests.WordGamePotential
