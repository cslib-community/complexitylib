/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the windowed universal simulation)

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Windowed

/-!
# The windowed universal simulation

A concrete machine checks one windowed step against the transition table, and the output of the
windowed simulation through `universal_eq_sim`. The size facts are instantiated on the initial
windows.
-/

@[expose] public section

namespace ComplexityTests.UniversalWindowed

open Turing.MultiTapeTM.Universal Turing.MultiTapeTM.Universal.Windowed

/-- On the input `[0, 1]`, read the symbol zero, emit seven, move right and write three on the
work tape, then halt on the missing transition. -/
def readZero : Desc where
  tapes := 1
  q₀ := 0
  table := [(⟨0, some 0, [none]⟩, ⟨.pos, [(some (some 3), .pos)], some 7, some 1⟩)]

-- One windowed step reads the coded input cell `some 1` as the input symbol zero.
example :
    (wstep readZero (initWin readZero [0, 1])).1.1 = some 1 ∧
      (wstep readZero (initWin readZero [0, 1])).2 = some 7 ∧
      ((wstep readZero (initWin readZero [0, 1])).1.2.map Tape.read) = [some 2, none] ∧
      ((wstep readZero (initWin readZero [0, 1])).1.2.map Tape.left) =
        [[some 1, some 0], [some 3]] := by
  decide

-- The windowed simulation of three steps emits the output of the machine.
example : (sim readZero 3 (extract 3 (initWin readZero [0, 1]))).2 = [7] ∧
    (sim readZero 3 (extract 3 (initWin readZero [0, 1]))).1.1 = none := by
  have h := universal_eq_sim readZero [0, 1] 3
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only at h₁ h₂
  refine ⟨h₁ ▸ by decide, Option.isNone_iff_eq_none.1 (h₂ ▸ by decide)⟩

example (n : ℕ) :
    (sim readZero n (extract n (initWin readZero [0, 1]))).1.2.length = 2 :=
  (length_sim _ _ _).trans rfl

end ComplexityTests.UniversalWindowed
