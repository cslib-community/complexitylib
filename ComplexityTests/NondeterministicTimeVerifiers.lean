/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Computability.Complexity.Classes.Time.Verifier
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.PairSampler

/-! The explicit-time verifier characterization of `NTIME` on concrete bounds. A deterministic
linear-time decider is a verifier with empty certificates, and a linear-time nondeterministic
problem survives the round trip through its linear-time verifier and guess and verify, at the
same linear bound. The sampler's output distribution is checked on a small input. -/

public section

namespace ComplexityTests.NondeterministicTimeVerifiers

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-- `c * n + c` in unary, within linear time and space. -/
private theorem computableInO_linear_unary (c : ℕ) :
    ComputableInO (fun x : List Bool => c * x.length + c) encBits encUnary
      (fun x => x.length) (fun x => x.length) := by
  induction c with
  | zero =>
    simpa using ComputableInO.const (encIn := encBits) (encMid := encUnary) 0
  | succ c ih =>
    have hstep := ComputableInO.lengthUnary.append
      (ComputableInO.const (encIn := encBits) (encMid := encUnary) 1)
      (g := fun x : List Bool => x.length + 1) (encOut := encUnary)
      fun x => by simp [encUnary_apply, List.replicate_add]
    have h := ih.append hstep (g := fun x : List Bool => (c + 1) * x.length + (c + 1))
      (encOut := encUnary) fun x => by
        simp only [encUnary_apply, ← List.replicate_add]
        congr 1
        ring
    exact h.mono 3 (fun x => by simp only [encBits_apply]; omega)
      (fun x => by simp only [encBits_apply]; omega)

/-- Guess and verify with empty certificates recovers deterministic linear time inside
nondeterministic linear time. -/
example {A : Set (List Bool)} (hA : A ∈ DTIME encBits fun n => n) :
    A ∈ NTIME encBits fun n => n := by
  have hV := (computableInO_indicator_of_mem_DTIME hA).comp (ComputableInO.fst encBits encBits)
  have h := setOf_exists_mem_NTIME (ℓ := fun _ => 0) (t := fun n => n) (C := 6)
    (ComputableInO.const (encIn := encBits) (encMid := encUnary) 0) hV fun x w hw => by
      simp only [List.length_eq_zero_iff] at hw
      subst hw
      simp only [encBits_apply, encPair_apply, List.length_append, length_frame,
        List.length_nil]
      omega
  have hset : {x : List Bool | ∃ w : List Bool, w.length = 0 ∧
      (indicator A ∘ Prod.fst) (x, w) = true} = A := by
    ext x
    simp [indicator]
  rwa [hset] at h

/-- **Round trip at linear time.** A problem in nondeterministic linear time has a linear-time
verifier, and guessing certificates of length `c * n + c` for it decides the problem in
nondeterministic linear time again. Both explicit-time hypotheses are satisfiable together. -/
theorem mem_NTIME_linear_of_verifier_roundTrip {A : Set (List Bool)}
    (hA : A ∈ NTIME encBits fun n => n) : A ∈ NTIME encBits fun n => n := by
  obtain ⟨V, c, hV, hmem⟩ := exists_verifier_of_mem_NTIME hA
  have h := setOf_exists_mem_NTIME (ℓ := fun x : List Bool => c * x.length + c)
    (t := fun n => n) (C := c + 4)
    (computableInO_linear_unary c) hV fun x w hw => by
      simp only [encBits_apply, encPair_apply, List.length_append, length_frame, hw]
      nlinarith
  have hset : {x : List Bool | ∃ w : List Bool, w.length = c * x.length + c ∧
      V (x, w) = true} = A := by
    ext x
    exact (hmem x _ le_rfl).symm
  rwa [hset] at h

/-- The sampler copies the framed word `[true]` and guesses a two-bit certificate. -/
example : ProbComp.eval (MultiTapePTM.pairSampler.runClosed 6 (frame [true] ++ [false, false])) =
    (BitString.uniformList 2).map (frame [true] ++ ·) := by
  simpa using MultiTapePTM.eval_pairSampler [true] [false, false]

end ComplexityTests.NondeterministicTimeVerifiers
