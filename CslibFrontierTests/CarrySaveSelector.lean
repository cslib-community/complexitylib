/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.CarrySaveSelector

/-!
Native selector checks include a borrow through two zeros, bit-index underflow, arbitrary
pre-existing address length, header overwrite, and flag erasure with cursor reset.
-/

namespace CslibFrontierTests.CarrySaveSelector

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.CarrySaveSelector Cslib.BitString

private theorem lastCases_small {α : Type*} (last : α) (f : Fin 4 → α)
    (j : Fin 5) (h : j.val < 4) : Fin.lastCases last f j = f ⟨j.val, h⟩ := by
  have hj : j = (⟨j.val, h⟩ : Fin 4).castSucc := by apply Fin.ext; rfl
  conv_lhs => rw [hj, Fin.lastCases_castSucc]

private def store (height bits path : List Bool) (status : Bool) : Cfg 4 Bool Unit [] :=
  ⟨none, 0, ![tapeOfList height, tapeOfList bits, tapeOfList path, tapeOfList [status]],
    ![0, 0, (path.length : ℤ), 0], []⟩

/-- Twenty transitions suffice independently of the old path length. The previous true status
is overwritten, both counters decrease correctly, and the flag tape is ready for reuse. -/
example (path : List Bool) :
    let tm := complete (0 : Fin 4) 1 2 3 true 2
    let c := tm.runFrom
      (outCfg ((store [true, true] [false, false, true] path true).withState (some tm.q₀))) 20
    c.state = none ∧ c.workTapes (Fin.last 4) = tapeOfList [] ∧ c.workTapePos (Fin.last 4) = 0 ∧
      c.workTapes (3 : Fin 4).castSucc 0 = some false ∧ c.workTapePos (3 : Fin 4).castSucc = 0 ∧
      c.workTapes (0 : Fin 4).castSucc = tapeOfList [false, true] ∧
      c.workTapePos (0 : Fin 4).castSucc = 0 ∧
      c.workTapes (1 : Fin 4).castSucc = tapeOfList [false, true, false] ∧
      c.workTapePos (1 : Fin 4).castSucc = 0 ∧
      c.workTapes (2 : Fin 4).castSucc = tapeOfList (path ++ [true]) ∧
      c.workTapePos (2 : Fin 4).castSucc = (path.length : ℤ) + 1 ∧ c.output = [] := by
  have hr := runFrom_complete (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide) true 2
    (store [true, true] [false, false, true] path true) rfl
    [true, true] [false, false, true] path rfl rfl rfl rfl rfl rfl
  simp only [BinaryDecrement.zeros, BinaryDecrement.totalClock, decrement] at hr
  rw [resultFlags_contains_eq] at hr
  norm_num only [show (2 : Fin 3).val = 2 by decide] at hr
  simp only [outCfg_workTapes_castSucc, outCfg_workTapePos_castSucc] at hr
  dsimp only
  rw [hr]
  simp [store, Cfg.withState, outCfg, lastCases_small, lsbValue, decrement,
    Function.iterate_succ_apply]

/-- Shift two from index one returns an invalid status, but still clears all underflow flags. -/
example (path : List Bool) :
    let tm := complete (0 : Fin 4) 1 2 3 false 2
    let c := tm.runFrom
      (outCfg ((store [true] [true] path false).withState (some tm.q₀))) 18
    c.state = none ∧ c.workTapes (Fin.last 4) = tapeOfList [] ∧ c.workTapePos (Fin.last 4) = 0 ∧
      c.workTapes (3 : Fin 4).castSucc 0 = some true ∧
      c.workTapePos (3 : Fin 4).castSucc = 0 ∧ c.output = [] := by
  have hr := runFrom_complete (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide) false 2
    (store [true] [true] path false) rfl [true] [true] path rfl rfl rfl rfl rfl rfl
  simp only [BinaryDecrement.zeros, BinaryDecrement.totalClock, decrement] at hr
  rw [resultFlags_contains_eq] at hr
  norm_num only [show (2 : Fin 3).val = 2 by decide] at hr
  simp only [outCfg_workTapes_castSucc, outCfg_workTapePos_castSucc] at hr
  dsimp only
  rw [hr]
  simp [store, Cfg.withState, outCfg, lastCases_small, lsbValue]

/-- Zero shift succeeds with an empty bit-index word; no fictitious decrement is performed. -/
example (path : List Bool) :
    let tm := complete (0 : Fin 4) 1 2 3 true 0
    let c := tm.runFrom
      (outCfg ((store [true] [] path true).withState (some tm.q₀))) 8
    c.workTapes (1 : Fin 4).castSucc = tapeOfList [] ∧ c.workTapes (Fin.last 4) = tapeOfList [] ∧
      c.workTapePos (Fin.last 4) = 0 ∧ c.workTapes (3 : Fin 4).castSucc 0 = some false := by
  have hr := runFrom_complete (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide) true 0
    (store [true] [] path true) rfl [true] [] path rfl rfl rfl rfl rfl rfl
  simp only [BinaryDecrement.zeros, BinaryDecrement.totalClock, decrement] at hr
  rw [resultFlags_contains_eq] at hr
  norm_num only [show (0 : Fin 3).val = 0 by decide] at hr
  simp only [outCfg_workTapes_castSucc, outCfg_workTapePos_castSucc] at hr
  dsimp only
  rw [hr]
  simp [store, Cfg.withState, outCfg, lastCases_small, lsbValue]

/-- The source of carry port four has shift two and selects the first child's first word. -/
example : decodedResult [true, true] [false, false, true] [true] true 4 =
    some ⟨[true, false], 2, false, 2⟩ := by
  rw [decodedResult_eq_descend]
  decide

example : decodedResult [true] [true] [] true 4 = none := by
  rw [decodedResult_eq_descend]
  decide

example : decodedResult [] [true] [] false 0 = none := by
  rw [decodedResult_eq_descend]
  decide

end CslibFrontierTests.CarrySaveSelector
