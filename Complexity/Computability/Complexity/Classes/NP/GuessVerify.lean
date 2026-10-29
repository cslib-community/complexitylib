/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Nondeterministic
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.PPT.Clock
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# Guess and verify

Every problem in `Cslib.Complexity.NP` is decided in polynomial time by a nondeterministic
machine with a binary alphabet and finitely many states, which guesses a certificate and runs the
verifier on it: the inclusion of `NP` in nondeterministic polynomial time
[Arora and Barak, Theorem 2.6][AroraBarak09]. The converse, and hence the characterization of
`NP`, is in `Complexity.Computability.Complexity.Classes.NP.Nondeterministic`.

The machine is built from the PPT calculus and its clock compiler rather than by hand. For a
verifier `V` with certificates of length `p (enc a).length`, the probabilistic program that samples
a word of this length and returns the verdict of `V` is uniformly polynomial-time. The clock
compiler `Cslib.Probability.IsPPTOn.exists_halting_machine` turns it into a finite fair-coin
machine that actually halts on every branch within a polynomial clock. Its nondeterministic machine
`Turing.MultiTapePTM.toNTM` guesses the coins: its computation paths are exactly the coin
replays, so it accepts exactly when some certificate of the required length is accepted. It is
never stuck, so every branch actually halts within the bound.

## Main results

* `Cslib.Complexity.IsVerifier.exists_decidesInTime`: a verifier gives a fair-coin machine whose
  nondeterministic machine decides the problem within an explicit polynomial and is never stuck.
* `Cslib.Complexity.decidableInPolyTime_of_mem_NP`: `NP` problems are decidable in nondeterministic
  polynomial time.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Probability

variable {α : Type} {enc : α ↪ List Bool} {p : Polynomial ℕ} {V : α × List Bool → Bool}
  {A : Set α}

/-- **Guess and verify**, the inclusion of `NP` in nondeterministic polynomial time
[Arora and Barak, Theorem 2.6][AroraBarak09]. A polynomial-time verifier gives a finite fair-coin
machine whose nondeterministic machine decides the problem within the explicit polynomial
`c * ((enc a).length + 1) ^ d`. That machine is never stuck, so its branches
actually halt within the bound. -/
theorem IsVerifier.exists_decidesInTime
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (hA : IsVerifier enc p V A) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State) (c d : ℕ),
      machine.toNTM.DecidesInTime enc A (fun a => c * ((enc a).length + 1) ^ d) ∧
      ∀ input (cfg : Cfg k Bool State input), ∃ cfg', machine.toNTM.Step cfg cfg' := by
  -- guess a certificate of the required length, then verify it
  let program (a : α) : ProbComp Bool :=
    (fun w => V (a, w)) <$> BitString.sampleList (p.eval (enc a).length)
  have hcount : ComputableInPolyTime (fun a => p.eval (enc a).length) enc encUnary :=
    (ComputableInPolyTime.unary_eval p).comp (ComputableInPolyTime.encoding_length enc)
  have hprogram : IsPPTOn enc encBool program :=
    (hcount).sampleList.map_with hV
  obtain ⟨k, State, hfinite, machine, c, d, heval, hhalt⟩ := hprogram.exists_halting_machine
  refine ⟨k, State, hfinite, machine, c, d, fun a => ?_, fun _ => machine.exists_step_toNTM⟩
  have htime : machine.toNTM.RunsInTime (enc a) (c * ((enc a).length + 1) ^ d) :=
    machine.runsInTime_toNTM (hhalt (enc a))
  refine ⟨htime, ?_⟩
  rw [hA a, MultiTapeNTM.accepts_iff_exists_time_eq htime,
    machine.exists_computationPath_toNTM_iff (P := fun cfg => cfg.output = [true])]
  -- both sides say that `[true]` is a supported output
  have hsupport := congrArg (fun μ => [true] ∈ μ.support) (heval a)
  simp only [MultiTapePTM.runClosed_eq_map, ProbComp.eval_map, PMF.mem_support_map_iff,
    program, BitString.eval_sampleList, BitString.mem_support_uniformList_iff, encBool_apply,
    List.cons.injEq, and_true] at hsupport
  rw [← hsupport]
  constructor
  · rintro ⟨w, hw, hV⟩
    exact ⟨true, ⟨w, hw, hV⟩, rfl⟩
  · rintro ⟨b, ⟨w, hw, hV⟩, rfl⟩
    exact ⟨w, hw, hV⟩

/-- Problems in `NP` are decidable in polynomial time by nondeterministic machines with a binary
alphabet and finitely many states. -/
theorem decidableInPolyTime_of_mem_NP (h : A ∈ NP enc) :
    MultiTapeNTM.DecidableInPolyTime A enc := by
  obtain ⟨p, V, hV, hA⟩ := h
  obtain ⟨k, State, hfinite, machine, c, d, hdecides, -⟩ := hA.exists_decidesInTime hV
  exact ⟨_, .of_forall_le c d fun _ => le_rfl, k, State, hfinite, machine.toNTM, hdecides⟩

end Cslib.Complexity
