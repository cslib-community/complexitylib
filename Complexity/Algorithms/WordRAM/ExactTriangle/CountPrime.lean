/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.SourceBounds
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.TimeBound

/-!
# Complete native cyclic-Strassen modular triangle counter

One fixed 128-register standard WordRAM program counts the existing modular-zero triangles
from raw `(n,p)` headers and three canonical signed matrices. It computes residues, the
Morton table, padding and both cyclic-monomial matrices, executes the actual seven-product
recursion with an explicit stack, then reads and sums the selected coefficients. Its raw
count is register 70; caller arguments are registers 64 through 69. The callable variant takes
runtime matrix/workspace pointers and preserves original arrays and outside memory.

## Main results

* `exec`: actual complete caller execution from original signed arrays, allowing dirty scratch.
* `runs_input_subcubic`: actual initialized prefix and charged halt, exact raw count and
  `3704*(p+1)^2*(n+1)^2.81` instruction bound.
* `admissionWidth_le_log`: if `p,A≤(n+2)^κ`, physical width
  `(κ+24)*clog₂(n+2)` is sufficient and the original input fits.
* `bounded_reachable_polynomial`: every admitted wider prefix has words and memory support
  bounded by `(n+2)^(κ+25)`, independently of the selected physical width.

The n exponent is subcubic and the runtime p factor remains explicit. This is the concrete
counter prerequisite for prime selection, not prime enumeration/argmin, an aggregate
ExactTriangle solver or the ordinary 3SUM exponent 1.9992 endpoint.

## References

Selectively adapts the algorithm in Programs/Sec3/Theorem17/Hashing/{CountPrime,RingOps,
Strassen,StrassenTime,ZOrder,Count}.lean and its finite specification at
[Anthropic formal-math revision 16a5ce41304fcdaea4e0be7c132e1c361dc26da5](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp).
Credit is retained in adapted source modules. Native implementation, frames, fits, execution
and instruction constants are independently proved against existing standard WordRAM APIs;
no Light semantics or assumed machine simulation is imported.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- One actual initialized finite native program, exact modular count and charged subcubic
execution. The prefix and halting result belong to the same state. All setup, ring arithmetic,
indexing, copying, recursion/control/return, scan and halt instructions are included.
The modulus and original-weight bound determine admission; no intermediate certificate is input. -/
theorem runs_input_subcubic {W n p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hp : 0 < p)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n p A ≤ W) :
    InputFits W (inputWords n p values) ∧
    ∃ y t, Runs W (entryProgram.program Reg.result) (State.init (inputWords n p values))
        ⟨entryProgram.size, y⟩ t ∧
      Executes W (entryProgram.program Reg.result) (State.init (inputWords n p values))
        (y.regs Reg.result) (t + 1) ∧
      ((t + 1 : ℕ) : ℝ) ≤ 3704 * (p + 1 : ℝ) ^ 2 * (n + 1 : ℝ) ^ (281 / 100 : ℝ) ∧
      y.regs Reg.result = Cslib.Algorithms.ExactTriangle.countZeroMod
        (fun α β : Fin n => values.getD (α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (n * n + α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (2 * (n * n) + α.val * n + β.val) 0) p ∧
      y.Bounded W ∧
      ∀ d, d < 3 + 3 * (n * n) ∨ memoryEnd n p (Nat.clog 2 n) (3 + 3 * (n * n)) ≤ d →
        y.mem d = (Data.init (inputWords n p values) : Data 128).mem d := by
  obtain ⟨hi, y, t, ht, run, halt, result, bounded, frame⟩ := runs_input values hlen hp hv hW
  have hcast : ((t + 1 : ℕ) : ℝ) ≤ ((cost n p + 10 : ℕ) : ℝ) := by exact_mod_cast ht
  exact ⟨hi, y, t, run, halt, hcast.trans (cost_le_subcubic n p), result, bounded, frame⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
