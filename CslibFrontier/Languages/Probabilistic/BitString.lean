/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Basic
public import CslibFrontier.Probability.BitString

/-!
# Sampling bit strings one fair bit at a time

`BitString.sampleList n` is an ordinary recursive program drawing `n` independent Boolean values.
Its distribution is the uniform law on lists of exactly that length. Computational efficiency is
certified separately in `Computability.Probabilistic.Sampling`.

## Main definitions

* `Cslib.BitString.sampleList`: sample a word using only fair Boolean choices.

## Main results

* `Cslib.BitString.eval_sampleList`: agreement with the finite uniform distribution.
* `Cslib.ProbComp.eval_bind_of_uniformList`: concatenate fixed-length seeds for sequential runs.

## References

Adapted from Cslib/Languages/Probabilistic/BitString.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the typed `PFunctor.FreeM` program interface.
-/

@[expose] public section

namespace Cslib.BitString

/-- Sample `n` independent fair bits, returned in sampling order. -/
noncomputable def sampleList : ℕ → ProbComp (List Bool)
  | 0 => pure []
  | n + 1 => do
    let bit ← ProbComp.uniform Bool
    return bit :: (← sampleList n)

/-- The operational fair-bit sampler has the finite uniform word distribution. -/
@[simp] theorem eval_sampleList (n : ℕ) : ProbComp.eval (sampleList n) = uniformList n := by
  induction n with
  | zero => simp [sampleList]
  | succ n ih => simp [sampleList, uniformList_succ, ih]

end Cslib.BitString

namespace Cslib.ProbComp

/-- Two fixed-length fair-bit seeds concatenate, including when the second program depends on
the first result. This is an exact distribution law, without an efficiency assertion. -/
theorem eval_bind_of_uniformList {α β : Type} (first second : ℕ)
    (program : ProbComp α) (next : α → ProbComp β)
    (evaluate : List Bool → α) (evaluateNext : α → List Bool → β)
    (hprogram : eval program = (BitString.uniformList first).map evaluate)
    (hnext : ∀ a, eval (next a) = (BitString.uniformList second).map (evaluateNext a)) :
    eval (do let a ← program; next a) =
      (BitString.uniformList (first + second)).map (fun tape =>
        evaluateNext (evaluate (tape.take first)) (tape.drop first)) := by
  rw [eval_bind, hprogram, PMF.bind_map]
  simp only [Function.comp_def, hnext]
  exact (BitString.uniformList_bind_split first second
    (fun front back => PMF.pure (evaluateNext (evaluate front) back))).symm

end Cslib.ProbComp
