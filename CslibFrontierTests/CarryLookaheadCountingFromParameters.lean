/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingFromParameters
import CslibFrontierTests.CarryLookaheadCounting

/-!
The complete raw-parameter machine answers both bits of an empty count and a count with a carry,
including false claims, on arbitrary host input and arbitrarily long context. Its initial evaluator
block contains no precomputed count, width, height, frontier, header, status, or routing metadata.
-/

namespace CslibFrontierTests.CarryLookaheadCountingFromParameters

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Cslib Cslib.Circuits.Boolean.CarryLookahead.Query
open Turing.MultiTapeATM.CarryLookaheadCountingFromParameters

-- The entire evaluator block starts blank except for its separately supplied context.
example (scratch k r q : ℕ) (input context : List Bool) (a : CountingInput.Input)
    (i : Fin (CarryLookaheadCountingLayout.size k r q))
    (hi : i ≠ CarryLookaheadCountingInitialLayout.contextTape k r q) :
    (CarryLookaheadCountingPrepare.initial scratch k r q input context a).workTapes
      (CarryLookaheadCountingPrepare.evaluatorTapes scratch k r q i) = fun _ => none := by
  have hword : CarryLookaheadCountingPrepare.ambientWords scratch k r q context a {}
      (CarryLookaheadCountingPrepare.evaluatorTapes scratch k r q i) = [] := by
    change Fin.append _ _ ((Fin.natAdd scratch i).castAdd 2) = _
    rw [Fin.append_left, Fin.append_right,
      CarryLookaheadCountingInitialLayout.words_empty_of_ne_context k r q context i hi]
  simp only [CarryLookaheadCountingPrepare.initial, CarryLookaheadCountingPrepare.config,
    tapesCfg, Pi.zero_apply, sub_zero, hword, tapeOfList_nil]

-- One actual native machine prepares its own fields and handles both an empty count and a carry.
example : ∃ (scratch k r q : ℕ) (S : Type) (_ : Finite S)
    (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch k r q) Bool S)
    (cInit dInit c d cRoot dRoot : ℕ),
    ∀ (input context : List Bool) (filled : Bool) (bit : Fin 2) (claim : Bool),
      let a : CountingInput.Input := ⟨if filled then 2 else 0, ⟨2, bit.val, claim⟩⟩
      let start := (CarryLookaheadCountingPrepare.initial scratch k r q input context a).withState
        (some atm.toPTM.initial)
      atm.HaltsWithin (clock cInit dInit c d cRoot dRoot context a) start ∧
        (atm.AcceptsWithin (clock cInit dInit c d cRoot dRoot context a) start ↔
          (filled && (bit == 1)) = claim) := by
  obtain ⟨scratch, k, r, q, S, hS, atm, cInit, dInit, c, d, cRoot, dRoot, h⟩ :=
    exists_evaluator (fun _ => true) (ComputableInPolyTime.const true)
  refine ⟨scratch, k, r, q, S, hS, atm, cInit, dInit, c, d, cRoot, dRoot, ?_⟩
  intro input context filled bit claim
  have hrun := h input context (if filled then 2 else 0) 2 bit claim
  refine ⟨hrun.1, hrun.2.trans ?_⟩
  rw [CarryLookaheadCounting.count_bits]

end CslibFrontierTests.CarryLookaheadCountingFromParameters
