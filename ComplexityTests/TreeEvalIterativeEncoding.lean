/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of iterative controller encodings)

public import Complexity.Computability.TreeEval.Ary.IterativeEncoding

/-!
# Compact continuation encodings

A dirty two-coordinate bank and two suspended frames instantiate the charged representation.
The proofs use its real table encoding, not a separately asserted abstract storage cost.
-/

@[expose] public section

namespace ComplexityTests.TreeEvalIterativeEncoding

open Cslib.TreeEval Cslib.TreeEval.Ary Cslib.TreeEval.Ary.Iter

private instance : NeZero (7 : ℕ) := ⟨by decide⟩

def bank : Ary.State (ZMod 7) 2 2 := fun i j => (i.val + 2 * j.val + 1 : ℕ)

def frame : Frame (ZMod 7) 2 := ⟨1, 1, false, 3, 2⟩

def cfg : Cfg (ZMod 7) 2 2 := ⟨bank, [frame, frame], .call 5 1⟩

example : ControlBounds 2 3 cfg := by
  constructor
  · decide
  · intro fr hfr
    have h : fr = frame := by simpa only [cfg, List.mem_cons, List.not_mem_nil,
      or_false, or_self] using hfr
    subst fr
    decide

example : (encRegs (encField 7) bank).length ≤ 42 := by
  have h := length_encRegs_le (encField 7) bank (length_encField_le 7)
  norm_num at h ⊢
  exact h

example : (encCfg (encField 7) cfg).length ≤ 276 := by
  have hbounds : ControlBounds 2 3 cfg := by
    constructor
    · decide
    · intro fr hfr
      have h : fr = frame := by simpa only [cfg, List.mem_cons, List.not_mem_nil,
        or_false, or_self] using hfr
      subst fr
      decide
  have h := length_encCfg_le (encField 7) cfg (length_encField_le 7) hbounds
  norm_num [frameBits] at h ⊢
  exact h

/-- Binary indices retain their logarithmic length. -/
example : (encIndex 1024 ⟨1023, by decide⟩).length = 10 := by
  rw [length_encIndex]
  decide

end ComplexityTests.TreeEvalIterativeEncoding
