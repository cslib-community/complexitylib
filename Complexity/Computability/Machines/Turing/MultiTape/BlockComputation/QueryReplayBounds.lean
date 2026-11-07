/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayAccess

/-!
# Storage of actual local replay runs

The conditional representation bound is discharged for every physical clock of replay from a
loaded view, including clocks after stopping. The original input contributes only its logarithm;
no caller-supplied bound on intermediate windows or heads remains.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay

variable {k : ℕ} {Q : Type}

private theorem runFrom_fixed {S : Type} (M : QueryMachine S) (w : List Bool) (s : S)
    (h : M.halted s = true) (n : ℕ) : M.runFrom w s n = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [QueryMachine.runFrom_succ, ih]; simp [QueryMachine.step, h]

/-- Once the exact replay duration is exhausted, the physical state stays fixed. -/
theorem runFrom_loadView_min (M : MultiTapeTM k Bool Q) (w : List Bool)
    (b : ℕ) (J : Option (Fin k) → ℤ) (v : View k Q b) (t : ℕ) :
    (machine M).runFrom w (loadView w.length b J v) t =
      (machine M).runFrom w (loadView w.length b J v) (min t b) := by
  by_cases ht : t ≤ b
  · rw [Nat.min_eq_left ht]
  · rw [Nat.min_eq_right (by omega)]
    conv_lhs => rw [show t = b + (t - b) by omega]
    rw [QueryMachine.runFrom_add]
    exact runFrom_fixed _ _ _ (halted_runFrom_loadView M b J v) _

variable [Finite Q]

/-- All physical replay clocks satisfy the explicit local-window encoding bound. This includes
malformed absolute input origins, whose loader follows the existing blank-boundary convention. -/
theorem length_runFrom_loadView_le (M : MultiTapeTM k Bool Q) (w : List Bool)
    (b : ℕ) [NeZero b] (J : Option (Fin k) → ℤ) (v : View k Q b) (t : ℕ) :
    (encConfig ((machine M).runFrom w (loadView w.length b J v) t)).length ≤
      1024 * (k + 1) *
        (b + Nat.log2 w.length + Nat.card (Option Q) +
          Nat.card MultiTapeNTM.ChoiceTable.OutputTrack + 1) := by
  rw [runFrom_loadView_min M w b J v t]
  let u := min t b
  let state := (machine M).runFrom w (loadView w.length b J v) u
  have hu : u ≤ b := Nat.min_le_right _ _
  have hrep := runFrom_loadView_represents (w := w) M b J v hu
  have hstart := loadView_represents (w := w) b J v
  have hwidth : state.width = b := width_runFrom M w _ u
  have hrem : state.remaining ≤ state.width := by
    rw [hwidth]
    change ((machine M).runFrom w (loadView w.length b J v) u).remaining ≤ b
    rw [remaining_runFrom]
    change b - u ≤ b
    omega
  have hin : state.inputPos ≤ state.inputLength + 1 := by
    rw [hrep.inputLength, hrep.inputPos]
    have hp := (M.runFrom (embedCfg (input := w) b J v.1 v.2) u).inputPos.isLt
    omega
  have hheads (h : Fin k) : state.heads h ≤ 3 * state.width := by
    have hdist := abs_le.mp
      (M.workTapePos_runFrom_abs_sub_le (embedCfg (input := w) b J v.1 v.2) u h)
    rw [hrep.heads h, hstart.heads h] at hdist
    have hr := ZMod.val_lt (v.1.2.1 (some h))
    rw [show (loadView w.length b J v).heads h = b + (v.1.2.1 (some h)).val from rfl]
      at hdist
    push_cast at hdist
    rw [hwidth]
    change ((machine M).runFrom w (loadView w.length b J v) u).heads h ≤ 3 * b
    omega
  have hcells (h : Fin k) : (state.cells h).length ≤ 3 * state.width := by
    rw [hwidth]
    change (((machine M).runFrom w (loadView w.length b J v) u).cells h).length ≤ 3 * b
    rw [length_cells_runFrom]
    simp [loadView]
  have hcodes (h : Fin k) (n : ℕ) (hn : n ∈ state.cells h) : n ≤ 2 := by
    have hc := cells_lt_three_runFrom M w (loadView w.length b J v)
      (cells_lt_three_loadView b J v) u h n hn
    omega
  have hb := length_encConfig_le state hrem hin hheads hcells hcodes
  rw [hwidth, hrep.inputLength] at hb
  exact hb

/-- Extracting any actual replay prefix retains only linear local-window data. The original
input length does not appear in the returned representation. -/
theorem length_rawResult_runFrom_loadView_le (M : MultiTapeTM k Bool Q) (w : List Bool)
    (b : ℕ) (J : Option (Fin k) → ℤ) (v : View k Q b) (t : ℕ) :
    (encRawResult (rawResult ((machine M).runFrom w (loadView w.length b J v) t))).length ≤
      128 * (k + 1) *
        (b + Nat.card (Option Q) + Nat.card MultiTapeNTM.ChoiceTable.OutputTrack + 1) := by
  let state := (machine M).runFrom w (loadView w.length b J v) t
  have hwidth : state.width = b := width_runFrom M w _ t
  have hcells (h : Fin k) : (state.cells h).length ≤ 3 * state.width := by
    rw [hwidth]
    change (((machine M).runFrom w (loadView w.length b J v) t).cells h).length ≤ 3 * b
    rw [length_cells_runFrom]
    simp [loadView]
  have hcodes (h : Fin k) (n : ℕ) (hn : n ∈ state.cells h) : n ≤ 2 := by
    have hc := cells_lt_three_runFrom M w (loadView w.length b J v)
      (cells_lt_three_loadView b J v) t h n hn
    omega
  have hb := length_encRawResult_le state hcells hcodes
  rw [hwidth] at hb
  exact hb

end Turing.MultiTapePTM.BlockComputation.QueryReplay
