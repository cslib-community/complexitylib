/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Probabilistic.Repeat
public import CslibFrontier.Languages.Probabilistic.CenteredBinomial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling

/-!
# Native centered binomial sampling

The actual two-count program has one strict fair-coin polynomial-time implementation for all
unary parameters `η`. Its signed output uses the binary integer encoding. The certificate
charges both blocks of independent trials, their counts, and signed subtraction.

## Main results

* `isPPTOn_sampleCenteredBinomial`: the unary-input, binary-output sampler certificate.
* `Turing.MultiTapeTM.ComputableInPolyTime.sampleCenteredBinomial`: composition with an
  efficiently computed unary parameter.

## References

* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, Section 4.2.2,
  Algorithm 8][NISTFIPS203]
-/

@[expose] public section

namespace Cslib.Probability

open ProbComp Turing.MultiTapeTM

/-- The centered-binomial program is uniformly strict PPT, with a unary parameter and binary
signed output. No fixed finite output type or finite-rank encoding is used. -/
theorem isPPTOn_sampleCenteredBinomial :
    IsPPTOn encUnary encIntBin sampleCenteredBinomial :=
  let e1 := encPair encUnary encUnary
  let hcount := (isPPTOn_uniform_bool encUnary).countTrue .id'
  let hcast := ComputableInPolyTime.unary_to_binary.trans .intBin_natCast
  let hsub := ((((ComputableInPolyTime.fst e1 encUnary).trans
    (.snd encUnary encUnary)).trans hcast).prod
    ((ComputableInPolyTime.snd e1 encUnary).trans hcast)).trans .intBin_sub
  hcount.bind_with ((hcount.preprocess (.fst encUnary encUnary)).bind_with hsub.isPPTOn)

end Cslib.Probability

/-- Sample a centered-binomial integer using an efficiently computed unary parameter. -/
@[fun_prop]
theorem Turing.MultiTapeTM.ComputableInPolyTime.sampleCenteredBinomial {α : Type}
    {input : α ↪ List Bool} {parameter : α → ℕ}
    (hparameter : ComputableInPolyTime parameter input encUnary) :
    Cslib.Probability.IsPPTOn input encIntBin
      (fun a => Cslib.ProbComp.sampleCenteredBinomial (parameter a)) :=
  Cslib.Probability.isPPTOn_sampleCenteredBinomial.preprocess hparameter
