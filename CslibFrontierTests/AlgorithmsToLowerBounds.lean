/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Complexity.Classes.AlgorithmsToLowerBounds
import CslibFrontier.Computability.Complexity.Classes.Time.BoundedExists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# A realized native algorithms-to-witness-circuits simulation

The decoder's two clauses require the two witness bits to be false and true respectively.
A zero-gate identity circuit is a satisfying witness. Its bounded description has one bit:
`[false]` selects its valid input wire; `[true]` selects a nonexistent wire and is rejected.

The native simulation below has no hypothetical algorithm or efficiency premise. Its SAT
algorithm applies the existing native bounded-search theorem to `CircuitSAT.verifier`. We use
the actual polynomial-time certificate compiler, compute the two possible SAT-query costs,
and verify the displayed combined bound. This tests the machine-level transfer as well as its
logic, without importing the broader class-inclusion hierarchy.
-/

-- Regression tests intentionally export no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.AlgorithmsToLowerBounds

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity
open Cslib.Complexity.AlgorithmsToLowerBounds
open Cslib.Circuits.Boolean.SuccinctVerifier Turing.MultiTapeTM

private def decoder : Circuit signature 1 6 := Circuit.wiring signature fun _ => 0

private def family (_ : List Bool) : Circuit signature 1 6 := decoder

example (x : List Bool) : x ∈ smallWitnessLanguage (r := fun _ => 1) family (fun _ => 0) := by
  refine ⟨Circuit.wiring signature id, by simp, ?_⟩
  rw [eval_toCNF_eq_true_iff]
  intro y
  rw [eval_clause_eq_true_iff]
  exact ⟨0, by simp [family, decoder]⟩

-- The compiler keeps the input width at one, even on the invalid description.
example (x : List Bool) :
    (certificateQuery (r := fun _ => 1) family (fun _ => 0) (x, [true])).1 = 1 := rfl

example (x : List Bool) :
    certificateQuery (r := fun _ => 1) family (fun _ => 0) (x, [true]) ∈ CircuitSAT :=
  mem_CircuitSAT_certificateCircuit_of_decode_eq_none (r := 1) decoder (by rfl)

-- All four native hypotheses of the transfer are realized: certificate-length computation,
-- query construction, SAT decision, and the combined time budget.
example : ∃ t : ℕ → ℕ,
    smallWitnessLanguage (r := fun _ => 1) family (fun _ => 0) ∈ NTIME encBits t := by
  obtain ⟨TV, SV, hTV, hSV, hV⟩ := CircuitSAT.computableInPolyTime_verifier.exists_computableInO
  obtain ⟨k, hsat⟩ := exists_computableInO_any_enumList hV hTV hSV
    (ComputableInPolyTime.encoding_length (encCircuit 1))
  have hspec (c : Σ n, Circuit signature n 1) :
      (BitString.enumList (encCircuit 1 c).length).any (fun w => CircuitSAT.verifier (c, w)) =
        true ↔ c ∈ CircuitSAT := by
    simpa only [List.any_eq_true, BitString.mem_enumList, Polynomial.eval_X] using
      (CircuitSAT.isVerifier c).symm
  have hbuildPoly : ComputableInPolyTime (certificateQuery (r := fun _ => 1) family (fun _ => 0))
      (encPair encBits encBits) (encCircuit 1) :=
    computableInPolyTime_certificateQuery
      (.const 1) (.const 1) (.const 0) (.const decoder.code)
  obtain ⟨d, _, hbuild⟩ := hbuildPoly.exists_degree
  have hℓ : ComputableInO (fun _ : List Bool => certLength 1 0) encBits encUnary
      (fun x => x.length) (fun x => x.length) := ComputableInO.const 1
  let cost (c : Σ n, Circuit signature n 1) : ℕ :=
    2 ^ (k * ((encCircuit 1 c).length + (encCircuit 1 c).length))
  let K := max (cost (certificateQuery (r := fun _ => 1) family (fun _ => 0) ([], [false])))
    (cost (certificateQuery (r := fun _ => 1) family (fun _ => 0) ([], [true])))
  let t : ℕ → ℕ := fun n => 2 * n + (2 * n + 3) ^ d + K
  refine ⟨t, smallWitnessLanguage_mem_NTIME (C := 1) hℓ hbuild.inO hsat hspec ?_⟩
  intro x w hw
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp (show w.length = 1 by simpa [certLength] using hw)
  have hcost : cost (certificateQuery (r := fun _ => 1) family (fun _ => 0) (x, [b])) ≤ K := by
    cases b
    · exact Nat.le_max_left _ _
    · exact Nat.le_max_right _ _
  have hpair : (encPair encBits encBits (x, [b])).length + 1 = 2 * x.length + 3 := by
    simp only [length_encPair, encBits_apply, List.length_cons, List.length_nil]
  change x.length + x.length +
    (((encPair encBits encBits (x, [b])).length + 1) ^ d +
      cost (certificateQuery (r := fun _ => 1) family (fun _ => 0) (x, [b]))) ≤ 1 * t x.length + 1
  rw [hpair]
  dsimp [t]
  omega

end CslibFrontierTests.AlgorithmsToLowerBounds
