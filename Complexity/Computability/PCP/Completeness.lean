/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PCP
public import Mathlib.Data.Nat.Log
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Classes.PCP.NP
import Complexity.Computability.PCP.Encoded.GapTheorem
import Complexity.Computability.PCP.Encoded.Verifier.Reduction
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi

/-!
# The PCP theorem

Compose Cook–Levin's polynomial-time reduction with the concrete SAT-to-gap construction and
the encoded graph verifier. The fixed output alphabet has an explicit binary representation:
seven bits: one for the input label and six for the selected tester's claimed answers.
The construction uses logarithmic randomness, constantly many queries, perfect completeness and
soundness at most one half. Its enormous fixed parameters remain asymptotic construction constants.

Conversely, exhaustive checking of logarithmically many random bits has polynomial cost. A
certificate supplies the bits at all queried addresses, with repeated addresses sharing one bit.
This gives `NP = PCP(log n, 1)` for the library's deterministic-verifier definition of NP.

## Main results

* `Cslib.Complexity.NP_subset_PCP_log`: every problem in NP has such a PCP verifier.
* `Cslib.Complexity.NP_eq_PCP_log`: the class-level PCP theorem.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 11][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.PCP Cslib.PCP.Encoded HadamardTester Turing.MultiTapeTM
open ConstraintGraph.Amplification.Arithmetic

private def encodeLabel (label : GapAlphabet) : Fin (FinEnum.card (Fin 6) + 1) → Bool :=
  Fin.cases label.1 (fun i => label.2 (FinEnum.equiv.symm i))

private def decodeLabel (bits : Fin (FinEnum.card (Fin 6) + 1) → Bool) : GapAlphabet :=
  (bits 0, fun query => bits (FinEnum.equiv query).succ)

private theorem decode_encodeLabel : Function.LeftInverse decodeLabel encodeLabel := by
  intro label
  simp [decodeLabel, encodeLabel]

/-- Every NP language has a polynomial-time verifier with logarithmic randomness and constantly
many nonadaptive proof queries, perfect completeness, and soundness at most one half. -/
theorem NP_subset_PCP_log {Input : Type} (input : Input ↪ List Bool) :
    NP input ⊆ PCP (fun n => Nat.log 2 n + 1) (fun _ => 1) input := by
  intro A hA
  obtain ⟨reduce, hreduce, hmem⟩ := CookLevin.SAT_npHard input A hA
  have heval : ComputableTidilyInPolyTime
      (fun p : (GapAlphabet → GapAlphabet → Bool) × GapAlphabet × GapAlphabet => p.1 p.2.1 p.2.2)
      (encPair (encPi (encPi encBool))
        (encPair (encPair encBool (encPi encBool)) (encPair encBool (encPi encBool)))) encBool :=
    (Graph.isPolyTime_constraintTableEval (encPair encBool (encPi encBool))).tidy
  exact Graph.mem_PCP_of_gapReduction (FinEnum.card (Fin 6) + 1)
    encodeLabel decodeLabel decode_encodeLabel (isPolyTime_gapGraph hreduce) (.of_tidy heval)
    (fun x => wellFormed_gapGraph (reduce x))
    (fun x hx => (satisfiable_gapGraph_iff _).mpr ((hmem x).mp hx))
    (gap := gap) gap_pos
    (fun x hx => gap_le_unsatVal_gapGraph _ fun h => hx ((hmem x).mpr h))

/-- **The PCP theorem:** NP is exactly logarithmic-randomness, constant-query PCP, with perfect
completeness and soundness at most one half. -/
theorem NP_eq_PCP_log {Input : Type} (input : Input ↪ List Bool) :
    NP input = PCP (fun n => Nat.log 2 n + 1) (fun _ => 1) input :=
  Set.Subset.antisymm (NP_subset_PCP_log input) (PCP_log_subset_NP _)

end Cslib.Complexity
