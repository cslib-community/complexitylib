/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Sampling.F4
public import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native sampling and scalar arithmetic in the four-element field

The existing quadratic algebra is encoded by the standard pair encoding of its two Boolean
coordinates. Two fair-bit instructions followed by finite deterministic decoding supply a
strict-PPT sampler with the exact uniform law proved in the language module. Addition,
subtraction and multiplication have finite lookup-machine certificates under the same encoding.
The field is fixed: none of these finite-type certificates asserts uniform efficiency for
growing extension degrees.

## Main definitions

* `Cslib.F4.encoding`: the standard pair encoding of the two Boolean coordinates.

## Main results

* `Cslib.F4.isPPTOn_sample`: an unconditional strict fair-coin sampler certificate.
* `Cslib.F4.computableInPolyTime_add`, `Cslib.F4.computableInPolyTime_sub`,
  `Cslib.F4.computableInPolyTime_mul`: encoded scalar arithmetic certificates.
-/

public section

namespace Cslib.F4

open Probability Turing.MultiTapeTM

/-- Encode the two basis coordinates using the existing Boolean-pair encoding. -/
@[expose] def encoding : QuadraticAlgebra (ZMod 2) 1 1 ↪ List Bool :=
  equivBits.toEmbedding.trans (encPair encBool encBool)

/-- Sampling this fixed field uses exactly the distribution of two independent fair bits. -/
theorem isPPTOn_sample : IsPPTOn encUnit encoding (fun _ => sample) := by
  unfold sample
  apply (isPPTOn_uniform_bool encUnit).bind
  simpa only [bind_pure_comp] using
    (isPPTOn_uniform_bool encBool).map_with
      (ComputableInPolyTime.of_finite fun p : Bool × Bool => equivBits.symm p)

/-- Addition in the fixed four-element field has a finite lookup implementation. -/
theorem computableInPolyTime_add :
    ComputableInPolyTime (fun p : QuadraticAlgebra (ZMod 2) 1 1 ×
      QuadraticAlgebra (ZMod 2) 1 1 => p.1 + p.2) (encPair encoding encoding) encoding :=
  .of_finite _

/-- Subtraction in the fixed four-element field has a finite lookup implementation. -/
theorem computableInPolyTime_sub :
    ComputableInPolyTime (fun p : QuadraticAlgebra (ZMod 2) 1 1 ×
      QuadraticAlgebra (ZMod 2) 1 1 => p.1 - p.2) (encPair encoding encoding) encoding :=
  .of_finite _

/-- Multiplication in the fixed four-element field has a finite lookup implementation. -/
theorem computableInPolyTime_mul :
    ComputableInPolyTime (fun p : QuadraticAlgebra (ZMod 2) 1 1 ×
      QuadraticAlgebra (ZMod 2) 1 1 => p.1 * p.2) (encPair encoding encoding) encoding :=
  .of_finite _

end Cslib.F4
