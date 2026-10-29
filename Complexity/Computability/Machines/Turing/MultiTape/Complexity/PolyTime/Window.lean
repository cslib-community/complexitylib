/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Feature
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time enumeration of tape windows

The existing `Turing.windowList` enumerates `-T, …, T` from left to right. With the bound in
unary and the positions in signed unary, the same list is computable in polynomial time.

## Main results

* `Turing.computableInPolyTime_windowList`.
* `Turing.MultiTapeTM.ComputableInPolyTime.moveInputPosNat`: total input-head movement,
  including clipping when the supplied position exceeds the input boundary.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing

open MultiTapeTM ComputableInPolyTime

/-- Enumerate all tape positions within a unary distance of the origin, in signed unary. -/
@[fun_prop]
theorem computableInPolyTime_windowList :
    ComputableInPolyTime windowList encUnary (encList encInt) := by
  unfold windowList
  have hf : ComputableInPolyTime (fun p : ℕ × ℕ => (p.2 : ℤ) - p.1)
      (encPair encUnary encUnary) encInt :=
    ComputableTidilyInPolyTime.int_natCast_sub.computableInPolyTime.comp
      ((snd encUnary encUnary).prod (fst encUnary encUnary))
  exact mapWithInput (by fun_prop) hf

/-- Move and clamp a unary input-head position, including positions outside the input boundary. -/
@[fun_prop]
theorem MultiTapeTM.ComputableInPolyTime.moveInputPosNat (direction : SignType) :
    ComputableInPolyTime (fun p : ℕ × ℕ => Turing.moveInputPosNat p.1 p.2 direction)
      (encPair encUnary encUnary) encUnary := by
  have heq (n j : ℕ) : Turing.moveInputPosNat n j direction = min (n + 1)
      (match direction with | .zero => j | .neg => j - 1 | .pos => j + 1) := by
    cases direction <;> simp only [Turing.moveInputPosNat, SignType.cast] <;> lia
  simp_rw [heq]
  cases direction <;> fun_prop

end Turing
