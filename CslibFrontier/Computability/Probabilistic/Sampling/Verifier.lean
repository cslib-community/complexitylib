/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Running a verifier on a sampled certificate

The program that samples a uniform word of length `p` evaluated at the encoded input length and
returns the verdict of a Boolean verifier `V` on the input and that word. This is the common first
step from verifier classes (`NP`, `BPP`, `PP`) to fair-coin machines: the program is uniformly
PPT, and the encoded output `[true]` is possible exactly when some word of the sampled length is
accepted.

## Main results

* `Cslib.Probability.isPPTOn_sampleVerify`: a polynomial-time verifier run on a sampled word of
  polynomial length is uniformly strict PPT.
* `Cslib.Probability.singleton_true_mem_support_sampleVerify_iff`: the encoded verdict `[true]`
  is possible exactly when some word of the sampled length is accepted.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- A polynomial-time verifier run on a uniformly sampled word whose length is a fixed polynomial
in the encoded input length is a uniform strict PPT program. -/
theorem isPPTOn_sampleVerify (p : Polynomial ℕ) {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    IsPPTOn enc encBool
      (fun a => (fun w => V (a, w)) <$> BitString.sampleList (p.eval (enc a).length)) :=
  IsPPTOn.of_seeded ((ComputableInPolyTime.unary_eval p).comp
    (ComputableInPolyTime.encoding_length enc)) hV

/-- Running `V` on a uniform word of length `n` can output the encoded verdict `[true]` exactly
when some word of length `n` is accepted. -/
theorem singleton_true_mem_support_sampleVerify_iff (V : α × List Bool → Bool) (a : α) (n : ℕ) :
    [true] ∈ ((ProbComp.eval ((fun w => V (a, w)) <$> BitString.sampleList n)).map
      encBool).support ↔ ∃ w : List Bool, w.length = n ∧ V (a, w) = true := by
  simp only [ProbComp.eval_map, BitString.eval_sampleList, PMF.map_comp, PMF.mem_support_map_iff,
    BitString.mem_support_uniformList_iff, Function.comp_apply, encBool_apply, List.cons.injEq,
    and_true]

end Cslib.Probability
