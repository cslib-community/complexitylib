/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PCP
public import Mathlib.Data.Nat.Log
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Classes.PCP.NP
import CslibFrontier.Computability.PCP.Encoded.GapTheorem
import CslibFrontier.Computability.PCP.Encoded.Verifier.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi

/-!
# The PCP theorem

`NP = PCP(log n, 1)`: every problem in NP has a polynomial-time verifier that uses `O(log n)`
random bits and reads a constant number of proof bits, accepts some proof of every member on every
random string, and accepts every proof of a non-member on at most half of the random strings. NP
is the library's deterministic-verifier class.

## Proof overview

The inclusion `NP ⊆ PCP(log n, 1)` follows Dinur [Dinur2007]. Every stage after Cook–Levin is a
program on explicit constraint graphs (`Cslib.PCP.Encoded.Graph`), with a polynomial-time
certificate and an exact interpretation as a construction on mathematical constraint graphs
(`Cslib.PCP.ConstraintGraph`), where its soundness is proved.

1. **Cook–Levin** (`Cslib.Complexity.CookLevin.SAT_npHard`) reduces the problem to SAT.
2. **The constraint graph of a formula** (`Cslib.PCP.Encoded.Graph.ofCompactCNF`, after splitting
   clauses with `Cslib.Logic.PL.CNF.to3CNF`) has three edges per clause and the alphabet
   `Fin 3 → Bool`, and is satisfiable exactly when the formula is.
3. **Composition** (`Cslib.PCP.Encoded.Graph.composeSelectedEnumerated`) with the six-query
   Hadamard assignment tester brings the alphabet to the fixed `Cslib.PCP.SelectedAlphabet` of
   `128` symbols, losing at most a factor `840` of the value
   (`Cslib.PCP.ConstraintGraph.le_unsatVal_composeSelected`).
4. **Gap amplification** (`Cslib.PCP.Encoded.Graph.arithmeticAmplify`) runs `⌈log₂ |E|⌉` rounds.
   Each round preprocesses with the explicit arithmetic expanders
   (`Cslib.PCP.ConstraintGraph.preprocessWith`), powers along killed walks
   (`Cslib.PCP.RegularConstraintGraph.power`), and composes back to `SelectedAlphabet`; it doubles
   the value up to the fixed threshold `Cslib.PCP.ConstraintGraph.Amplification.Arithmetic.gap`
   (`Cslib.PCP.ConstraintGraph.min_le_div_unsatVal_power_preprocessWith`). Since an
   unsatisfiable graph with `|E|` edges has value at least `1 / |E|`, the rounds reach the threshold
   (`Cslib.PCP.ConstraintGraph.gap_le_of_min_two_pow_mul_le`). Stages 2 to 4 form
   `Cslib.PCP.Encoded.gapGraph`.
5. **The verifier** (`Cslib.PCP.Encoded.Graph.reductionVerifier`) builds the graph and checks a
   constant number of independently sampled edges, reading the labels of their ends from the proof,
   seven bits each: one for the input label and six for the selected tester's claimed answers. A
   single check rejects with probability at least half the value
   (`Cslib.PCP.Encoded.Graph.unsatVal_div_two_le_rejectProb`), so a constant number of repetitions
   brings the soundness error to one half (`Cslib.PCP.Encoded.Graph.mem_PCP_of_gapReduction`).

The converse inclusion (`Cslib.Complexity.PCP_log_subset_NP`) checks all polynomially many random
strings. Its certificate supplies the bits at all queried addresses, with repeated addresses
sharing one bit.

`Cslib.PCP.Dinur.gapGraph` in `CslibFrontier.Computability.PCP.GapTheorem` renders the same
argument noncomputably, with non-explicit expanders and smaller constants; the theorem here does
not use it. The fixed constants of the explicit construction are enormous, so the result is
asymptotic.

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

private def encodeLabel (label : SelectedAlphabet) : Fin (FinEnum.card (Fin 6) + 1) → Bool :=
  Fin.cases label.1 (fun i => label.2 (FinEnum.equiv.symm i))

private def decodeLabel (bits : Fin (FinEnum.card (Fin 6) + 1) → Bool) : SelectedAlphabet :=
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
  have heval : ComputableInPolyTime
      (fun p : (SelectedAlphabet → SelectedAlphabet → Bool) ×
        SelectedAlphabet × SelectedAlphabet => p.1 p.2.1 p.2.2)
      (encPair (encPi (encPi encBool))
        (encPair (encPair encBool (encPi encBool)) (encPair encBool (encPi encBool)))) encBool :=
    Graph.isPolyTime_constraintTableEval (encPair encBool (encPi encBool))
  exact Graph.mem_PCP_of_gapReduction (FinEnum.card (Fin 6) + 1)
    encodeLabel decodeLabel decode_encodeLabel (isPolyTime_gapGraph hreduce) heval
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
