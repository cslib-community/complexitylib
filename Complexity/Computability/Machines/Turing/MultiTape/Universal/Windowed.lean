/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Machine

/-!
# Windowed simulation

In `n` steps, a head reads only cells within distance `n` of where it started. The windowed
simulation exploits this to simulate `n` steps on *windows*: for every tape, the zipper of the
cells within distance `n` of its head. It cuts the windows of radius `⌈n / 2⌉` around the heads,
simulates the first `⌈n / 2⌉` steps on them recursively, pastes the result back, and does the same
for the remaining `⌊n / 2⌋` steps. A single step is `Turing.MultiTapeTM.Universal.stepWith`.

Cutting and pasting take time linear in the window, so `n` steps take time `O(n log n)` for a
fixed machine; that cost analysis is in a separate module. This module defines the simulation and
proves that it computes the universal function.

A windowed configuration (`Turing.MultiTapeTM.Universal.Windowed.Win`) holds the state, then the
input window followed by the work windows. The `head` fields of the window zippers are not used.
Input cells are coded so that a step can be taken without the position of the input head:
`some 0` is the left end at position `0`, `some (a + 1)` the input symbol `a`, and `none` a blank
after the input.

## Main definitions

* `Turing.MultiTapeTM.Universal.Windowed.extract`, `.restore`: cutting windows and pasting them
  back.
* `Turing.MultiTapeTM.Universal.Windowed.wstep`: one step on windows.
* `Turing.MultiTapeTM.Universal.Windowed.sim`: the recursive simulation of `n` steps.
* `Turing.MultiTapeTM.Universal.Windowed.initWin`: the windows of the initial configuration.

## Main results

* `Turing.MultiTapeTM.Universal.Windowed.universal_eq_sim`: the windowed simulation of `t` steps
  from the radius-`t` windows of the initial configuration computes the universal function.
-/

public section

namespace Turing.MultiTapeTM.Universal.Windowed

/-- A windowed configuration: the state, then the input window followed by the work windows. -/
abbrev Win := Option ℕ × List Tape

/-- The cells of `t` within distance `r` of its head, as a zipper with head field `0`. -/
@[expose] def cut (r : ℕ) (t : Tape) : Tape := ⟨0, t.left.take r, t.right.take (r + 1)⟩

/-- The window `inner`, cut from `outer` with radius `r` and then run, with the cells of `outer`
beyond distance `r` of its head put back around it. -/
@[expose] def paste (r : ℕ) (outer inner : Tape) : Tape :=
  ⟨0, inner.left ++ outer.left.drop r, inner.right ++ outer.right.drop (r + 1)⟩

/-- The windows of radius `r`. -/
@[expose] def extract (r : ℕ) (w : Win) : Win := (w.1, w.2.map (cut r))

/-- The windows `inner`, extracted from `outer` with radius `r` and then run, pasted back. -/
@[expose] def restore (r : ℕ) (outer inner : Win) : Win :=
  (inner.1, List.zipWith (paste r) outer.2 inner.2)

/-- The input symbol of a coded input cell. -/
@[expose] def inSym (c : Option ℕ) : Option ℕ := c.bind fun v => if v = 0 then none else some (v - 1)

/-- A stand-in for the position of the input head on a coded input cell: `0` at the left end and
`1` elsewhere. `Turing.MultiTapeTM.Universal.moveInput` distinguishes only these cases. -/
@[expose] def inPos (c : Option ℕ) : ℕ := if c = some 0 then 0 else 1

/-- The input window, moved as the input head moved from `p` to `p'`. -/
@[expose] def moveIn (t : Tape) (p p' : ℕ) : Tape :=
  if p' = p + 1 then t.move .pos else if p' + 1 = p then t.move .neg else t

/-- One step on a windowed configuration, and the symbol it emits. -/
@[expose] def wstep (d : Desc) (w : Win) : Win × Option ℕ :=
  match w.2 with
  | [] => (w, none)
  | i :: ts =>
    (((stepWith d ⟨w.1, inPos i.read, ts⟩ (inSym i.read)).1.state,
      moveIn i (inPos i.read) (stepWith d ⟨w.1, inPos i.read, ts⟩ (inSym i.read)).1.inputPos ::
        (stepWith d ⟨w.1, inPos i.read, ts⟩ (inSym i.read)).1.workTapes),
      (stepWith d ⟨w.1, inPos i.read, ts⟩ (inSym i.read)).2)

/-- The number of steps of the first half of a block of `n` steps. -/
@[expose] def firstHalf (n : ℕ) : ℕ := n - n / 2

/-- The windowed simulation of `n` steps, and the symbols emitted. -/
@[expose] def sim (d : Desc) : ℕ → Win → Win × List ℕ
  | 0, w => (w, [])
  | 1, w => ((wstep d w).1, (wstep d w).2.toList)
  | n + 2, w =>
    let r₁ := sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)
    let w₁ := restore (firstHalf (n + 2)) w r₁.1
    let r₂ := sim d ((n + 2) / 2) (extract ((n + 2) / 2) w₁)
    (restore ((n + 2) / 2) w₁ r₂.1, r₁.2 ++ r₂.2)
termination_by n => n
decreasing_by all_goals first | omega | (simp only [firstHalf]; omega)

/-- The windows of the initial configuration on the input `x`: the input head on the first input
symbol, after the left end, and blank work tapes. -/
@[expose] def initWin (d : Desc) (x : List ℕ) : Win :=
  (some d.q₀, ⟨0, [some 0], x.map fun a => some (a + 1)⟩ :: List.replicate d.tapes ⟨0, [], []⟩)

/-- **The windowed simulation computes the universal function**: started from the radius-`t`
windows of the initial configuration, `t` windowed steps give the output and the halting status
after `t` steps. -/
theorem universal_eq_sim (d : Desc) (x : List ℕ) (t : ℕ) :
    universal (d, x, t) = ((sim d t (extract t (initWin d x))).2,
      (sim d t (extract t (initWin d x))).1.1.isNone) :=
  sorry

end Turing.MultiTapeTM.Universal.Windowed
