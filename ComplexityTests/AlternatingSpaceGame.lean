/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Alternation.SpaceGame
import Complexity.Computability.Complexity.Classes.Inclusions
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Tests: word games and `APSPACE`

The word game whose update drops the first symbol (`List.tail`) is worked out completely. A move
`b` at `u :: x :: r` leads to `b :: r`, so the mover chooses who moves next. The existential player
wins exactly at `[true]` and at the positions `false :: x :: r`: at `[false, x]` the move `true`
leads to `[true]`, and at a longer position the move `false` keeps the turn. A universal position
`true :: x :: r` is lost: at `[true, x]` the universal move `false` leads to `[false]`, and at a
longer position the universal move `true` keeps the turn. Every play ends within the length of the
position. With the identity as update, the play from `[false, false]` never ends.

The tail game is in `APSPACE` through `Cslib.Complexity.mem_APSPACE_of_wins`, with the initial
position the instance itself, and hence in `EXP` through `Cslib.Complexity.APSPACE_eq_EXP`.

In the circuit-value game on the tableau of any machine
(`Cslib.Circuits.Boolean.Tableau.ValueGame`), a claim about a wire is won exactly when the opposite
claim is lost, and the claims about input wires are decided by the input.
-/

namespace ComplexityTests.AlternatingSpaceGame

open Cslib.Complexity Turing.MultiTapeTM Turing.MultiTapeATM.WordGame

/-! ### The tail game -/

example : Wins List.tail [true] := .accept

example : ¬ Wins List.tail [] := by
  intro h
  cases h

example : ¬ Wins List.tail [false] := by
  intro h
  cases h

/-- At `[false, x]` the existential move `true` leads to `[true]`. -/
example (x : Bool) : Wins List.tail [false, x] := .existsMove true .accept

/-- At `[true, x]` the universal move `false` leads to `[false]`, which is lost. -/
example (x : Bool) : ¬ Wins List.tail [true, x] := by
  intro h
  cases h with
  | forallMove h => cases h false

/-- The existential player wins from every position `false :: x :: r` and loses from every
position `true :: x :: r`. -/
theorem wins_tail : ∀ (r : List Bool) (x : Bool),
    Wins List.tail (false :: x :: r) ∧ ¬ Wins List.tail (true :: x :: r)
  | [], _ => ⟨.existsMove true .accept, fun h => by cases h with | forallMove h => cases h false⟩
  | y :: r, _ => by
    obtain ⟨hwin, hlose⟩ := wins_tail r y
    exact ⟨.existsMove false hwin, fun h => by cases h with | forallMove h => exact hlose (h true)⟩

/-- **The tail game, solved.** -/
theorem wins_tail_iff (w : List Bool) :
    Wins List.tail w ↔ w = [true] ∨ ∃ x r, w = false :: x :: r := by
  refine ⟨fun h => ?_, ?_⟩
  · rcases w with _ | ⟨u, _ | ⟨x, r⟩⟩
    · cases h
    · cases u
      · cases h
      · exact .inl rfl
    · cases u
      · exact .inr ⟨x, r, rfl⟩
      · exact absurd h (wins_tail r x).2
  · rintro (rfl | ⟨x, r, rfl⟩)
    · exact .accept
    · exact (wins_tail r x).1

/-- Every play of the tail game ends within the length of the position. -/
theorem ends_tail : ∀ (n : ℕ) (w : List Bool), w.length ≤ n → Ends List.tail n w
  | _, [], _ => by simp [Ends]
  | _, [_], _ => by simp [Ends]
  | 0, _ :: _ :: _, h => by simp at h
  | n + 1, u :: x :: r, h => by
    simp only [Ends, List.tail_cons]
    exact fun b => ends_tail n (b :: r) (by simp at h ⊢; omega)

/-- With the identity as update, the play from `[false, false]` never ends. -/
example (n : ℕ) : ¬ Ends id n [false, false] := by
  induction n with
  | zero => simp [Ends]
  | succ n ih =>
    simp only [Ends, id]
    exact fun h => ih (h false)

/-- Positions reachable in the tail game are no longer than the initial one. -/
theorem length_le_of_reach {w₀ w : List Bool} (h : Reach List.tail w₀ w) :
    w.length ≤ w₀.length := by
  induction h with
  | start => exact le_rfl
  | move b _ ih => simp only [List.length_cons, List.tail_cons] at ih ⊢; omega

/-! ### Nonvacuity: the tail game is in `APSPACE` -/

/-- The tail game is in `APSPACE`, through the word game machine. -/
example : {w : List Bool | Wins List.tail w} ∈ APSPACE encBits :=
  mem_APSPACE_of_wins (I := id) (U := List.tail) (ℓ := List.length)
    ComputableInPolyTime.id'
    ComputableTidilyInPolyTime.bitsTail.computableInPolyTime
    (PolyBounded.of_forall_le 1 1 fun w => by simp)
    (fun _ _ h => length_le_of_reach h)
    (fun w => ⟨w.length, ends_tail _ w le_rfl⟩)
    (fun _ => Iff.rfl)

/-! ### Inversion -/

/-- In the tail game, the existential position `[false, x, y]` is won by moving to `[false, y]`. -/
example (x y : Bool) : Wins List.tail [false, x, y] :=
  wins_false_cons_cons_iff.mpr ⟨false, .existsMove true .accept⟩

example (x : Bool) : ¬ Wins List.tail [true, x] := by
  rw [wins_true_cons_cons_iff]
  exact fun h => absurd (wins_singleton_iff.mp (h false)) Bool.false_ne_true

/-! ### The circuit-value game on the tableau -/

section ValueGame

open Cslib.Circuits.Boolean.Tableau Cslib.Circuits.Boolean.Tableau.ValueGame

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : Turing.MultiTapeTM k Bool State)

/-- A claim about a tableau wire is won exactly when the opposite claim is lost. -/
example (x : List Bool) (T w : ℕ) (hw : w < x.length + numGates k State T) :
    Wins (update tm encClaim) (emit tm encClaim (x, T, w, true)) ↔
      ¬ Wins (update tm encClaim) (emit tm encClaim (x, T, w, false)) := by
  rw [wins_emit_iff x T w hw, wins_emit_iff x T w hw]
  cases val tm T x w <;> simp

/-- The true claim about an input wire is won, the false one lost. -/
example (x : List Bool) (T i : ℕ) (hi : i < x.length) :
    Wins (update tm encClaim) (emit tm encClaim (x, T, i, x[i])) ∧
      ¬ Wins (update tm encClaim) (emit tm encClaim (x, T, i, !x[i])) := by
  have hw : i < x.length + numGates k State T := by omega
  rw [wins_emit_iff x T i hw, wins_emit_iff x T i hw, val_input tm hi]
  simp

end ValueGame

/-! ### `APSPACE = EXP` -/

/-- `PSPACE ⊆ APSPACE`, through `EXP`. -/
example {α : Type} {enc : α ↪ List Bool} : PSPACE enc ⊆ APSPACE enc :=
  fun _ h => EXP_subset_APSPACE (PSPACE_subset_EXP h)

/-- The tail game is in `EXP`, through `APSPACE = EXP`. -/
example : {w : List Bool | Wins List.tail w} ∈ EXP encBits := by
  rw [← APSPACE_eq_EXP]
  exact mem_APSPACE_of_wins (I := id) (U := List.tail) (ℓ := List.length)
    ComputableInPolyTime.id'
    ComputableTidilyInPolyTime.bitsTail.computableInPolyTime
    (PolyBounded.of_forall_le 1 1 fun w => by simp)
    (fun _ _ h => length_le_of_reach h)
    (fun w => ⟨w.length, ends_tail _ w le_rfl⟩)
    (fun _ => Iff.rfl)

end ComplexityTests.AlternatingSpaceGame
