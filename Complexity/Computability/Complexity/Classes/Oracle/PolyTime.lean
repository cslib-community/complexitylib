/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle.Deterministic
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation

/-!
# Polynomial time relative to an oracle in polynomial time

An oracle language decided in polynomial time adds nothing to polynomial time: `P^A = P` and
`NP^A = NP` for `A ∈ P` [Arora and Barak, Section 3.4][AroraBarak09].

A computation in polynomial time relative to `A` is the clocked run, with every coin fixed to
`false`, of a finite oracle machine (`Cslib.Probability.IsOraclePPTOn.exists_fin_run_pure_false`).
That run iterates one instruction on finite storage (`Turing.MultiTapePTM.answerStep`), which
answers a query with the decider of `A` on the pending request. Against an oracle computed in
polynomial time the instruction is polynomial-time
(`Turing.MultiTapePTM.computableTidilyInPolyTime_answerStep`), the storage grows by a bounded amount
per instruction, and the clock is polynomial, so the run is polynomial-time
(`Turing.MultiTapePTM.computableInPolyTime_run`,
`Cslib.Complexity.ComputableInPolyTimeWithOracle.computableInPolyTime`).

## Main results

* `Cslib.Complexity.ComputableInPolyTimeWithOracle.computableInPolyTime`: polynomial time
  relative to an oracle in `P` is polynomial time.
* `Cslib.Complexity.PWithOracle_eq_P`, `Cslib.Complexity.NPWithOracle_eq_NP`: `P^A = P` and
  `NP^A = NP` for `A ∈ P`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {A : Set (List Bool)}

open Classical in
/-- **Polynomial time relative to an oracle in `P` is polynomial time.** Relative to an oracle
language decided in polynomial time, a function computable in polynomial time relative to it is
computable in polynomial time: every query is answered by running the decider. -/
theorem ComputableInPolyTimeWithOracle.computableInPolyTime {f : α → β}
    {output : β ↪ List Bool} (hA : A ∈ P encBits)
    (hf : ComputableInPolyTimeWithOracle A f enc output) :
    ComputableInPolyTime f enc output := by
  obtain ⟨g, hg, hgA⟩ := hA
  have hg' : g = fun w => decide (w ∈ A) := funext fun w =>
    Bool.eq_iff_iff.mpr ⟨fun h => decide_eq_true ((hgA w).mpr h),
      fun h => (hgA w).mp (of_decide_eq_true h)⟩
  subst hg'
  obtain ⟨program, hcert, hprogram⟩ := hf
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  refine (machine.computableInPolyTime_run (input := enc) hg c d).of_enc_eq fun a => ?_
  rw [← hprogram a, ← hrun a (languageOracle A)]
  rfl

/-- **`P` relative to an oracle in `P` is `P`.** -/
theorem PWithOracle_eq_P (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    PWithOracle A enc = P enc :=
  Set.Subset.antisymm (fun _ ⟨f, hf, hL⟩ => ⟨f, hf.computableInPolyTime hA, hL⟩)
    (P_subset_PWithOracle A enc)

/-- **`NP` relative to an oracle in `P` is `NP`.** -/
theorem NPWithOracle_eq_NP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    NPWithOracle A enc = NP enc :=
  Set.Subset.antisymm
    (fun _ ⟨p, V, hV, hL⟩ => ⟨p, V, hV.computableInPolyTime hA, hL⟩)
    (NP_subset_NPWithOracle A enc)

end Cslib.Complexity
