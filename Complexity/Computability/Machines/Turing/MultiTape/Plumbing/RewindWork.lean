/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Algebra.BigOperators.Fin
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
public import Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# The space of the work-tape-rewinding machine

The addition of Christian Reitwiessner's branch `crei/tidy-universal` to
`Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork`.

## Main results

* `Turing.MultiTapeTM.space_rewindWork_le`: the rewinding machine visits at most `p + 2` cells.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

-- vendored: `spaceUsed_rewindWork_le` in crei:crei/tidy-universal; `spaceUsed` is the space of a
-- run path since cslib #1133 and #1122
/-- The one-tape `rewindWork` machine visits at most `p + 2` cells: its head stays within
`[-1, p]`. -/
public theorem space_rewindWork_le (write : Option (Option Symbol))
    (ip : Fin (input.length + 2)) (t : ℤ → Option Symbol) (out : List Symbol) {w : List Symbol}
    (hw : t = tapeOfList w) {p : ℕ} (hp : p ≤ w.length) (n : ℕ) :
    (MultiTapeNTM.RunPath.ofDeterministic (rewindWork Symbol write)
        ⟨some (rewindWork Symbol write).q₀, ip, fun _ => t, fun _ => (p : ℤ), out⟩ n).space ≤
      p + 2 := by
  rw [MultiTapeNTM.RunPath.space, Fin.sum_univ_one]
  refine (spaceUsedByTape_le_card _ (S := .Icc (-1) (p : ℤ)) fun m _ => ?_).trans ?_
  · exact Finset.mem_Icc.2 (workTapePos_runFrom_rewindWork write ip t out hw hp m)
  · rw [Int.card_Icc]; omega

end Turing.MultiTapeTM
