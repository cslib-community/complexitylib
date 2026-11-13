/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveDepthPrepare

namespace CslibFrontierTests.CarrySaveDepthPrepare

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Turing.MultiTapeATM.CarrySaveDepthPrepare

-- Three leaves require ceiling depth two. The real preparation writes both representations,
-- preserves the context, source count, precision and queried bit, and restores every head.
example : ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (k + 12) Bool S) (c d : ℕ),
    ∀ input : List Bool,
      let result := tm.runFrom
        ((initial k input [true, false] 3 5 2).withState (some tm.q₀)) (c * 3 ^ d)
      result.state = none ∧
        result.workTapes 0 = tapeOfList [false, true] ∧
        result.workTapes 4 = tapeOfList [true, true] ∧
        result.workTapes 1 = tapeOfList [false, true] ∧
        result.workTapes 6 = tapeOfList [true, false] ∧
        result.workTapes 7 = tapeOfList [true, true] ∧
        result.workTapes 8 = tapeOfList [true, false, true] ∧
        result.workTapePos = 0 ∧ result.inputPos = 0 ∧ result.output = [] := by
  obtain ⟨k, S, hS, tm, c, d, h⟩ := exists_root
  refine ⟨k, S, hS, tm, c, d, fun input => ?_⟩
  have hr := h input [true, false] 3 5 2
  change tm.runFrom ((initial k input [true, false] 3 5 2).withState (some tm.q₀))
    (c * 3 ^ d) = _ at hr
  dsimp only
  rw [hr]
  simp only [Cfg.withState_state, Cfg.withState_inputPos, Cfg.withState_output, true_and]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
  funext i
  simp [CarrySaveCountingRoot.initial, Cfg.withState, CarrySaveLeafLayout.initial_head,
    CarrySaveLeafLayout.heads]

-- The empty count has no unary or binary depth cells, but still runs the same finite native
-- preparation, including both host-head movements and all private cleanup.
example : ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (k + 12) Bool S) (c : ℕ),
    ∀ input : List Bool,
      tm.runFrom ((initial k input [false] 0 1 0).withState (some tm.q₀)) c =
        (initial k input [false] 0 1 0).withState none := by
  obtain ⟨k, S, hS, tm, c, d, h⟩ := exists_root
  refine ⟨k, S, hS, tm, c, fun input => ?_⟩
  simpa [CarrySaveCountingRoot.initial, initial, encNat_apply, encUnary_apply] using
    h input [false] 0 1 0

end CslibFrontierTests.CarrySaveDepthPrepare
