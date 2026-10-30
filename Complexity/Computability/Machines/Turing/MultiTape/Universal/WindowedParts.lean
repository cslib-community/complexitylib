/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.WindowedBound

/-!
# The cost of cutting, pasting and stepping windows

Cutting windows (`Turing.MultiTapeTM.Universal.Windowed.extract`) and pasting them back
(`Turing.MultiTapeTM.Universal.Windowed.restore`) take time linear in the encoded windows for each
window, so time `O((K + 1) * N)` for `K` windows of total encoded length `N`; every operation on
the cells of a window is linear in their encoded length. A windowed step
(`Turing.MultiTapeTM.Universal.Windowed.wstep`) takes time cubic in the encoded description and
windows. Halving a number of steps in unary takes linear time.

## Main results

* `Turing.MultiTapeTM.Universal.Windowed.extract_inO`, `.restore_inO`: cutting and pasting.
* `Turing.MultiTapeTM.Universal.Windowed.wstep_inO`: a windowed step.
* `Turing.MultiTapeTM.Universal.Windowed.firstHalf_inO`, `.half_inO`: halving in unary.
-/

public section

namespace Turing.MultiTapeTM.Universal.Windowed

/-- **Cutting windows** of radius `r`, in time linear in the encoded windows for each window. -/
theorem extract_inO :
    ComputableInO (fun p : ℕ × Win => extract p.1 p.2) (encPair encUnary eWin) eWin
      (fun p => (p.2.2.length + 1) * ((encPair encUnary eWin p).length + 1))
      (fun p => (p.2.2.length + 1) * ((encPair encUnary eWin p).length + 1)) :=
  sorry

/-- **Pasting windows back**, in time linear in the encoded windows for each window. -/
theorem restore_inO :
    ComputableInO (fun p : ℕ × Win × Win => restore p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair eWin eWin)) eWin
      (fun p => (p.2.1.2.length + 1) * ((encPair encUnary (encPair eWin eWin) p).length + 1))
      (fun p => (p.2.1.2.length + 1) * ((encPair encUnary (encPair eWin eWin) p).length + 1)) :=
  sorry

/-- **A windowed step**, in time cubic in the encoded description and windows. -/
theorem wstep_inO :
    ComputableInO (fun p : Desc × Win => wstep p.1 p.2) (encPair eDesc eWin) (encPair eWin eSym)
      (fun p => ((encPair eDesc eWin p).length + 1) ^ 3)
      (fun p => ((encPair eDesc eWin p).length + 1) ^ 3) :=
  sorry

/-- The first half of a number of steps, in unary, in linear time. -/
theorem firstHalf_inO :
    ComputableInO firstHalf encUnary encUnary (fun n => (encUnary n).length)
      (fun n => (encUnary n).length) :=
  sorry

/-- Half a number of steps, rounded down, in unary, in linear time. -/
theorem half_inO :
    ComputableInO (· / 2) encUnary encUnary (fun n => (encUnary n).length)
      (fun n => (encUnary n).length) :=
  sorry

end Turing.MultiTapeTM.Universal.Windowed
