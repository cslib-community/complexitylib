/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalTensor

/-! Views, embeddings and interval steps of a concrete choice-string run, with blocks of
length `2`. -/

namespace ComplexityTests.HPVIntervalTensors

open Turing MultiTapeMachine

/-- On one work tape, write the coin and move right on `true`, left on `false`. The input head
moves right on `true` too. -/
private def zigzag : MultiTapePTM 1 Bool Unit where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := if bit then 1 else 0,
      workTapes := fun _ => (some (some bit), if bit then 1 else -1),
      output := none, state := some () }
    Empty.elim Empty.elim

/-- Replays on upstream configurations, evaluated through the computable interpreter. -/
private theorem stepCoins_eq (coins : List Bool) (cfg : Cfg 1 Bool Unit [true, false]) :
    zigzag.stepCoins coins cfg =
      (zigzag.runClosedConfigFromCoins coins { tapes := cfg }).tapes :=
  (MultiTapePTM.tapes_runClosedConfigFromCoins zigzag coins { tapes := cfg }).symm

private def start : Cfg 1 Bool Unit [true, false] := Cfg.init () [true, false]

/-! ### Embedding a view keeps the window and forgets the rest -/

/-- The start configuration with marks in its window `[-2, 4)` (cell `3`) and outside it
(cell `5`). -/
private def marked : Cfg 1 Bool Unit [true, false] :=
  { start with workTapes := fun _ z => if z = 3 ∨ z = 5 then some false else none }

/-- The configuration embedded from the view of `marked`. -/
private noncomputable def markedView : Cfg 1 Bool Unit [true, false] :=
  embedCfg 2 (marked.blockIndex 2) (marked.blockControl 2)
    (marked.windowContents 2 (marked.blockIndex 2))

-- The mark in the window is kept.
example : markedView.workTapes 0 3 = some false :=
  (agreeOn_embedCfg_view marked).workTapes_eq 0 3 (by simp [Cfg.blockWindow, marked, start])

-- The mark outside the window is forgotten: block `2` is not part of the view.
example : markedView.workTapes 0 5 = none := by
  simp only [markedView, embedCfg, windowCell]
  rw [dite_eq_right (by decide)]

/-! ### Interval steps -/

/-- After `true, true` both heads have moved two cells to the right. -/
private noncomputable def after : Cfg 1 Bool Unit [true, false] :=
  zigzag.stepCoins [true, true] start

private theorem headPos_after : after.headPos = fun _ => 2 := by
  funext head
  cases head <;> (rw [after, stepCoins_eq]; rfl)

-- The interval wrote `true` into cells `0` and `1`: offsets `0` and `1` of the middle block.
example : after.windowContents 2 (start.blockIndex 2) 0 1 = fun _ => some true := by
  funext r
  fin_cases r <;> (rw [after, stepCoins_eq]; rfl)

/-- Both heads move one block to the right. -/
private theorem blockIndex_after (head : Option (Fin 1)) :
    after.blockIndex 2 head = start.blockIndex 2 head + ((1 : SignType) : ℤ) := by
  simp only [Cfg.blockIndex, headPos_after, Cfg.headPos_init, start]
  rfl

-- From the view of `start`, the interval step on `true, true` leaves the record and window of
-- the true replay and moves both blocks by `+1`.
example : zigzag.IntervalStep 2 [true, false] (start.blockIndex 2) (fun _ => 1)
    (start.blockControl 2) (start.windowContents 2 (start.blockIndex 2)) [true, true]
    (after.blockControl 2) (after.windowContents 2 (start.blockIndex 2)) :=
  (zigzag.intervalStep_view_iff 2 start (by decide) _ _ _).mpr ⟨rfl, rfl, blockIndex_after⟩

-- The schedule entry is checked: the step does not keep the work head in its block.
example : ¬ zigzag.IntervalStep 2 [true, false] (start.blockIndex 2) (fun _ => 0)
    (start.blockControl 2) (start.windowContents 2 (start.blockIndex 2)) [true, true]
    (after.blockControl 2) (after.windowContents 2 (start.blockIndex 2)) := by
  rw [zigzag.intervalStep_view_iff 2 start (by decide)]
  rintro ⟨-, -, h⟩
  have := (h (some 0)).symm.trans (blockIndex_after (some 0))
  simp at this

/-- An entry of the interval tensor counts at most the `4` bit strings of the interval. -/
example : zigzag.intervalCount 2 [true, false] (start.blockIndex 2) (fun _ => 1)
    (start.blockControl 2) (start.windowContents 2 (start.blockIndex 2))
    (after.blockControl 2) (after.windowContents 2 (start.blockIndex 2)) ≤ 4 :=
  zigzag.intervalCount_le 2 _ _ _ _ _ _ _

/-! ### Bits of an interval -/

-- With two intervals of two bits, interval `1` replays bits `2` and `3`.
example (y : Fin (2 * 2) → Bool) :
    zigzag.intervalStart 2 (List.ofFn y) start 2 =
      zigzag.stepCoins [y 2, y 3] (zigzag.intervalStart 2 (List.ofFn y) start 1) := by
  exact zigzag.intervalStart_succ_ofFn y start 1

end ComplexityTests.HPVIntervalTensors
