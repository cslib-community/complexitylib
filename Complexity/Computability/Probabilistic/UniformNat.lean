/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.UniformNat
public import Complexity.Computability.Probabilistic.Sampling
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Tactic.PPT

/-!
# Sampling bounded indices in strict polynomial time

Each sampler uses a fixed number of fair bits. `sampleBinaryNat` takes a unary bit width and
returns the sampled value in binary. The bounded-index samplers instead saturate binary decoding
at a computed cap, so both their intermediate states and their unary outputs remain polynomially
bounded. The dyadic range is at most `2 * (bound + 1)`, including zero. No unbounded rejection
loop is used.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.unary_dyadicSize`: efficient unary range size.
* `Cslib.Probability.isPPTOn_sampleBinaryNat`: uniform sampling with binary output.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.sampleBinaryNat`: sample a computed bit width.
* `Cslib.Probability.isPPTOn_sampleModNat`: approximately uniform residues, for a computed bit width
  and modulus.
* `Cslib.Probability.isPPTOn_sampleDyadicIndex`: exact uniform sampling in the dyadic range.
* `Cslib.Probability.isPPTOn_sampleBoundedIndex`: capped sampling with a rejection sentinel.
* `Cslib.Probability.isPPTOn_sampleDyadicCoin`: exact capped dyadic probabilities.

## References

Adapted from Computability/Probabilistic/UniformNat.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the tidy machine calculus and shared bit folds.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Compute the dyadic range in unary via capped binary decoding. Its exponential expression
does not authorize exponential output: the proved linear cap supplies the implementation. -/
@[fun_prop]
theorem unary_dyadicSize : ComputableTidilyInPolyTime Cslib.Probability.dyadicSize
    encUnary encUnary := by
  change ComputableTidilyInPolyTime (fun n => Cslib.Probability.dyadicSize n) encUnary encUnary
  simp only [Cslib.Probability.dyadicSize_eq_boundedBinaryValue]
  fun_prop

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Compute the linearly capped dyadic range from a unary bound in plain polynomial time. -/
@[fun_prop]
theorem Turing.MultiTapeTM.ComputableInPolyTime.unary_dyadicSize :
    Turing.MultiTapeTM.ComputableInPolyTime Cslib.Probability.dyadicSize
      Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary :=
  Turing.MultiTapeTM.ComputableInPolyTime.of_tidy
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_dyadicSize

namespace Cslib.Probability

open ProbComp Turing.MultiTapeTM

/-- A unary bit width gives a uniformly strict PPT sampler with binary natural output. -/
theorem isPPTOn_sampleBinaryNat : IsPPTOn encUnary encNat sampleBinaryNat :=
  isPPTOn_sampleList.map ComputableTidilyInPolyTime.bitsBinaryValue

/-- An efficiently supplied unary bound gives a strict PPT exact dyadic sampler. -/
@[program_certificate]
theorem isPPTOn_sampleDyadicIndex {α : Type} {input : α ↪ List Bool} {bound : α → ℕ}
    (hbound : ComputableTidilyInPolyTime bound input encUnary) :
    IsPPTOn input encUnary (fun a => sampleDyadicIndex (bound a)) := by
  unfold sampleDyadicIndex
  ppt

/-- Efficient unary parameters give a strict PPT coin with the specified dyadic law. -/
@[program_certificate]
theorem isPPTOn_sampleDyadicCoin {α : Type} {input : α ↪ List Bool}
    {bound numerator : α → ℕ}
    (hbound : ComputableTidilyInPolyTime bound input encUnary)
    (hnumerator : ComputableTidilyInPolyTime numerator input encUnary) :
    IsPPTOn input encBool (fun a => sampleDyadicCoin (bound a) (numerator a)) := by
  have hcallback : ComputableInPolyTime
      (fun p : α × ℕ => decide (p.2 < numerator p.1)) (encPair input encUnary) encBool := by
    apply ComputableInPolyTime.of_tidy
    fun_prop
  simpa only [sampleDyadicCoin, bind_pure_comp] using
    (isPPTOn_sampleDyadicIndex hbound).map_with hcallback

/-- An efficiently supplied unary bound gives a strict PPT capped index sampler. -/
@[program_certificate]
theorem isPPTOn_sampleBoundedIndex {α : Type} {input : α ↪ List Bool} {bound : α → ℕ}
    (hbound : ComputableTidilyInPolyTime bound input encUnary) :
    IsPPTOn input encUnary (fun a => sampleBoundedIndex (bound a)) := by
  unfold sampleBoundedIndex
  ppt

end Cslib.Probability

/-- Sample a binary natural using an efficiently computed unary bit width. -/
@[fun_prop]
theorem Turing.MultiTapeTM.ComputableTidilyInPolyTime.sampleBinaryNat {α : Type}
    {input : α ↪ List Bool} {width : α → ℕ}
    (hwidth : ComputableTidilyInPolyTime width input encUnary) :
    Cslib.Probability.IsPPTOn input encNat
      (fun a => Cslib.ProbComp.sampleBinaryNat (width a)) :=
  Cslib.Probability.isPPTOn_sampleBinaryNat.preprocess (.of_tidy hwidth)

namespace Cslib.Probability

open ProbComp Turing.MultiTapeTM

/-- Approximately uniform residues: reducing a computed number of fair bits modulo a computed
modulus is uniformly strict PPT, with binary output. -/
theorem isPPTOn_sampleModNat {α : Type} {input : α ↪ List Bool} {width modulus : α → ℕ}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hmodulus : ComputableInPolyTime modulus input encNat) :
    IsPPTOn input encNat (fun a => sampleModNat (width a) (modulus a)) := by
  unfold sampleModNat
  exact (ComputableTidilyInPolyTime.sampleBinaryNat hwidth.tidy).map_with
    (.of_tidy (ComputableTidilyInPolyTime.binary_mod' (by fun_prop)
      (hmodulus.tidy.comp (by fun_prop))))

end Cslib.Probability
