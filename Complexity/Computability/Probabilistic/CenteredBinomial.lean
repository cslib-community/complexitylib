/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.CenteredBinomial
public import Complexity.Computability.Probabilistic.Repeat
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native centered binomial sampling

The actual two-count program has one strict fair-coin polynomial-time implementation for all
unary parameters `η`. Its signed output uses the binary integer encoding. The certificate
charges both blocks of independent trials, their counts, and signed subtraction.

## Main results

* `isPPTOn_sampleCenteredBinomial`: the unary-input, binary-output sampler certificate.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.sampleCenteredBinomial`: composition with an
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
    IsPPTOn encUnary encIntBin sampleCenteredBinomial := by
  have hcount : IsPPTOn encUnary encUnary
      (fun η => OracleComp.countTrue η (ProbComp.uniform Bool)) :=
    (isPPTOn_uniform_bool encUnary).countTrue .id'
  have hcast : ComputableTidilyInPolyTime (fun n : ℕ => (n : ℤ)) encUnary encIntBin :=
    ComputableTidilyInPolyTime.intBin_natCast.comp
      ComputableTidilyInPolyTime.unary_to_binary
  have hsub : ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℕ => (p.1.2 : ℤ) - p.2)
      (encPair (encPair encUnary encUnary) encUnary) encIntBin :=
    ComputableTidilyInPolyTime.intBin_sub.comp
      ((hcast.comp ((ComputableTidilyInPolyTime.fst _ _).snd')).prod
        (hcast.comp (ComputableTidilyInPolyTime.snd _ _)))
  have hsecond := (hcount.preprocess
    (ComputableInPolyTime.fst encUnary encUnary)).map_with
      (f := fun (p : ℕ × ℕ) (negative : ℕ) => (p.2 : ℤ) - negative) (.of_tidy hsub)
  unfold sampleCenteredBinomial
  apply hcount.bind_with
  simpa only [bind_pure_comp] using hsecond

end Cslib.Probability

/-- Sample a centered-binomial integer using an efficiently computed unary parameter. -/
@[fun_prop]
theorem Turing.MultiTapeTM.ComputableTidilyInPolyTime.sampleCenteredBinomial {α : Type}
    {input : α ↪ List Bool} {parameter : α → ℕ}
    (hparameter : ComputableTidilyInPolyTime parameter input encUnary) :
    Cslib.Probability.IsPPTOn input encIntBin
      (fun a => Cslib.ProbComp.sampleCenteredBinomial (parameter a)) :=
  Cslib.Probability.isPPTOn_sampleCenteredBinomial.preprocess
    (Turing.MultiTapeTM.ComputableInPolyTime.of_tidy hparameter)
