/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Windowed

/-!
# The size of windowed configurations

Encodings of windowed configurations and of the problems, solutions and saved data of the
divide-and-conquer form of the windowed simulation, and bounds on their sizes.

A windowed configuration satisfies `Turing.MultiTapeTM.Universal.Windowed.WInv D B h L` when its
state is at most `D`, it has at most `D + 1` windows, the heads of its windows are within `h` of
`0`, every window holds at most `L` cells and every cell is at most `B`. Its encoded length is then
at most `winBound D B h L`. The windowed simulation of `n` steps with a description of length at
most `B` preserves the bounds on the state and the cells, moves the heads by at most one, adds at
most `2 * n` cells to every window, and emits at most `n` symbols, each at most the length of the
description.

## Main definitions

* `Turing.MultiTapeTM.Universal.Windowed.eWin`: the encoding of windowed configurations.
* `Turing.MultiTapeTM.Universal.Windowed.cells`: the number of cells of a window.
* `Turing.MultiTapeTM.Universal.Windowed.WInv`: bounds on a windowed configuration.
* `Turing.MultiTapeTM.Universal.Windowed.winBound`: the resulting bound on its encoded length.

## Main results

* `Turing.MultiTapeTM.Universal.Windowed.length_eWin_le`: the size of a windowed configuration.
* `Turing.MultiTapeTM.Universal.Windowed.WInv.sim`: the bounds after the windowed simulation.
* `Turing.MultiTapeTM.Universal.Windowed.WInv.restore_sim`: the bounds after simulating on cut
  windows and pasting them back.
-/

public section

namespace Turing.MultiTapeTM.Universal.Windowed

/-! ### Encodings -/

/-- Windowed configurations: the state and the windows. -/
abbrev eWin : Win ↪ List Bool := encPair eSym (encList eTape)

/-- Problems of the divide-and-conquer simulation: the description, the number of steps in unary
and the windows. -/
abbrev Prob := Desc × ℕ × Win

/-- The encoding of problems. -/
abbrev eProb : Prob ↪ List Bool := encPair eDesc (encPair encUnary eWin)

/-- Solutions: the windows after the steps and the emitted symbols. -/
abbrev Sol := Win × List ℕ

/-- The encoding of solutions. -/
abbrev eSol : Sol ↪ List Bool := encPair eWin (encList encUnary)

/-- Saved data: the number of steps of the second half, the windows after the first half and the
symbols it emitted. -/
abbrev Saved := ℕ × Win × List ℕ

/-- The encoding of saved data. -/
abbrev eSaved : Saved ↪ List Bool := encPair encUnary (encPair eWin (encList encUnary))

/-! ### Bounds -/

/-- The number of cells of a window. -/
@[expose] def cells (t : Tape) : ℕ := t.left.length + t.right.length

/-- Bounds on a windowed configuration: the state is at most `D`, there are at most `D + 1`
windows, their heads are within `h` of `0`, they hold at most `L` cells each, and every cell is at
most `B`. -/
structure WInv (D B h L : ℕ) (w : Win) : Prop where
  state : w.1.getD 0 ≤ D
  tapes : w.2.length ≤ D + 1
  head : ∀ t ∈ w.2, t.head.natAbs ≤ h
  cells : ∀ t ∈ w.2, cells t ≤ L
  val : ∀ t ∈ w.2, ∀ o ∈ t.left ++ t.right, o.getD 0 ≤ B

/-- The bound on the encoded length of a windowed configuration satisfying `WInv D B h L`. -/
@[expose] def winBound (D B h L : ℕ) : ℕ :=
  2 * D + 3 + (D + 1) * (4 * h + 4 * L * (2 * B + 3) + 9)

/-- **The size of a windowed configuration.** -/
theorem length_eWin_le {D B h L : ℕ} {w : Win} (hw : WInv D B h L w) :
    (eWin w).length ≤ winBound D B h L :=
  sorry

/-- Weakening the bounds. -/
theorem WInv.mono {D B h L h' L' : ℕ} {w : Win} (hw : WInv D B h L w) (hh : h ≤ h')
    (hL : L ≤ L') : WInv D B h' L' w :=
  sorry

/-- Cutting windows of radius `r`: the heads are at `0` and every window holds at most `2 * r + 1`
cells, and at most as many as before. -/
theorem WInv.extract {D B h L : ℕ} {w : Win} (hw : WInv D B h L w) (r : ℕ) :
    WInv D B 0 (min L (2 * r + 1)) (Windowed.extract r w) :=
  sorry

/-- The windows of the initial configuration. -/
theorem winv_initWin (d : Desc) (x : List ℕ) :
    WInv (descLen d) (descLen d + listMax id x + 1) 0 (x.length + 1) (initWin d x) :=
  sorry

/-- The windowed simulation keeps the number of windows. -/
theorem length_sim (d : Desc) (n : ℕ) (w : Win) : (sim d n w).1.2.length = w.2.length :=
  sorry

/-- **The bounds after the windowed simulation** of `n` steps, for a description of length at most
`B`: the heads move by at most one and every window gains at most `2 * n` cells. -/
theorem WInv.sim {d : Desc} {B h L : ℕ} (hDB : descLen d ≤ B) {w : Win}
    (hw : WInv (descLen d) B h L w) (n : ℕ) :
    WInv (descLen d) B (h + 1) (L + 2 * n) (Windowed.sim d n w).1 :=
  sorry

/-- **The bounds after simulating on cut windows and pasting them back**: simulating `m` steps on
the windows of radius `r` and pasting the result back adds at most `2 * m` cells to every window,
and puts the heads at `0`. -/
theorem WInv.restore_sim {d : Desc} {B h L : ℕ} (hDB : descLen d ≤ B) {w : Win}
    (hw : WInv (descLen d) B h L w) (r m : ℕ) :
    WInv (descLen d) B 0 (L + 2 * m) (restore r w (Windowed.sim d m (Windowed.extract r w)).1) :=
  sorry

/-- The windowed simulation of `n` steps emits at most `n` symbols. -/
theorem length_sim_out (d : Desc) (n : ℕ) (w : Win) : (sim d n w).2.length ≤ n :=
  sorry

/-- The symbols emitted by the windowed simulation are at most the length of the description. -/
theorem le_of_mem_sim_out {d : Desc} {n : ℕ} {w : Win} {o : ℕ} (ho : o ∈ (sim d n w).2) :
    o ≤ descLen d :=
  sorry

/-- The size of the emitted symbols. -/
theorem length_encList_sim_out_le (d : Desc) (n : ℕ) (w : Win) :
    (encList encUnary (sim d n w).2).length ≤ n * (2 * descLen d + 1) :=
  sorry

/-- The windowed simulation of `n + 2` steps: the first half on cut windows, pasted back, then the
second half. -/
theorem sim_add_two (d : Desc) (n : ℕ) (w : Win) :
    sim d (n + 2) w =
      (restore ((n + 2) / 2) (restore (firstHalf (n + 2)) w
          (sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)).1)
        (sim d ((n + 2) / 2) (extract ((n + 2) / 2) (restore (firstHalf (n + 2)) w
          (sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)).1))).1,
        (sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)).2 ++
          (sim d ((n + 2) / 2) (extract ((n + 2) / 2) (restore (firstHalf (n + 2)) w
            (sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)).1))).2) :=
  sorry

end Turing.MultiTapeTM.Universal.Windowed
