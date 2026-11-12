/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Oracle
import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic

/-!
# `FP^A` outputs as canonical oracle replays

A function computable in polynomial time relative to an oracle language `A` is realized by one
finite oracle machine under one polynomial clock. Its encoded output is the replayed output of
that machine along the canonical instruction-indexed transcript of `A`'s replies
(`Turing.MultiTapePTM.oracleReplies`). Simulations of `FP^A` by guessed reply transcripts, such as
the lowness proofs for `NP ∩ coNP`, `UP ∩ coUP` and `#P` and the `P^NP ⊆ Σ₂` bound, start from
this fact.

## Main results

* `Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_replayOutput`: an `FP^A` output is
  the canonical replay of a fixed finite machine under a fixed polynomial clock.
-/

public section

namespace Cslib.Complexity

open _root_.Turing

variable {α β : Type} {A : Set (List Bool)} {enc : α ↪ List Bool} {output : β ↪ List Bool}

open Classical in
/-- **An `FP^A` output is a canonical oracle replay.** A function computable in polynomial time
relative to `A` has a finite oracle machine and a polynomial clock `p` such that, on every
instance, the encoded output is the replayed output of the machine along the canonical transcript
of `A`'s replies of length `p (|enc a|)`. -/
theorem ComputableInPolyTimeWithOracle.exists_replayOutput {f : α → β}
    (hf : ComputableInPolyTimeWithOracle A f enc output) :
    ∃ (k m : ℕ) (machine : MultiTapePTM k Bool (Fin m) Unit) (p : Polynomial ℕ),
      ∀ a, machine.replayOutput (enc a)
          (machine.oracleReplies (fun q => decide (q ∈ A)) (p.eval (enc a).length) (enc a)) =
        output (f a) := by
  obtain ⟨program, hcert, hprogram⟩ := hf
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  refine ⟨k, m, machine, Polynomial.C c * (Polynomial.X + 1) ^ d, fun a => ?_⟩
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  rw [machine.replayOutput_oracleReplies]
  exact (hrun a (languageOracle A)).trans (congrArg output (hprogram a))

end Cslib.Complexity
