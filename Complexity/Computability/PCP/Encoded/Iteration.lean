/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Size
public import Mathlib.Data.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Tactic.PolyTime

/-!
# Graph invariants and iteration size

A client-supplied invariant establishes well-formed endpoints, bounded descriptor lengths, and
constant-factor growth of the total number of vertices and edges. These properties give a bound
on every complete encoded graph throughout an iteration. The bound charges the initial state even
when the growth factor is zero, and includes the pair and list framing from the graph encoding.

For a ceiling-logarithmic number of rounds, the existing fixed-factor power certificate makes
this size bound polynomial in the original input encoding. Clients can pass it directly to the
existing iteration calculus; no new iteration rule or machine construction is needed.

## Main definitions

* `Cslib.PCP.Encoded.Graph.iterationSize`: a bound on all intermediate encoded graph sizes.

## Main results

* `Cslib.PCP.Encoded.Graph.iterate_length_encoding_le`: a preserved graph invariant supplies
  the full intermediate-state bound.
* `Cslib.PCP.Encoded.Graph.polyBounded_iterationSize_clog`: the bound is polynomial for a
  logarithmic number of rounds, including an efficiently computed initial graph.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Turing.MultiTapeTM

variable {C Input : Type} {enc : C ↪ List Bool} {input : Input ↪ List Bool}

/-- A graph-size invariant bounds the complete framed state throughout the loop. -/
def iterationSize (factor descriptorBound rounds : ℕ) (g : Graph C) : ℕ :=
  let size := max factor 1 ^ rounds * (g.vertices + g.edges.length)
  2 * size + 1 + size * (8 * size + 2 * descriptorBound + 5)

/-- The logarithmic-round state bound is polynomial in any efficiently computed initial graph.
Its fixed-factor power is computed by the existing charged logarithm/power certificate. -/
theorem polyBounded_iterationSize_clog {graph : Input → Graph C}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (factor descriptorBound : ℕ) :
    PolyBounded (fun x => (input x).length)
      (fun x => iterationSize factor descriptorBound (Nat.clog 2 (graph x).edges.length)
        (graph x)) := by
  apply ComputableInPolyTime.polyBounded
  unfold iterationSize
  fun_prop

/-- A preserved graph invariant with fixed linear cardinality growth and bounded descriptors
bounds every intermediate encoding, including the initial state and all list framing. -/
theorem iterate_length_encoding_le {step : Graph C → Graph C} {valid : Graph C → Prop}
    (factor descriptorBound : ℕ)
    (hvalid : ∀ g, valid g → valid (step g))
    (hwellFormed : ∀ g, valid g → g.WellFormed)
    (hdescriptors : ∀ g, valid g → ∀ edge ∈ g.edges,
      (enc edge.constraint).length ≤ descriptorBound)
    (hgrowth : ∀ g, valid g →
      (step g).vertices + (step g).edges.length ≤ factor * (g.vertices + g.edges.length))
    {g : Graph C} (hg : valid g) {i rounds : ℕ} (hi : i ≤ rounds) :
    (encoding enc (step^[i] g)).length ≤ iterationSize factor descriptorBound rounds g := by
  have htrace (k : ℕ) : valid (step^[k] g) ∧
      (step^[k] g).vertices + (step^[k] g).edges.length ≤
        max factor 1 ^ k * (g.vertices + g.edges.length) := by
    induction k with
    | zero => exact ⟨hg, by simp⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply', pow_succ', mul_assoc]
      exact ⟨hvalid _ ih.1, (hgrowth _ ih.1).trans
        (Nat.mul_le_mul (Nat.le_max_left _ _) ih.2)⟩
  have hs := (htrace i).2.trans (Nat.mul_le_mul_right (g.vertices + g.edges.length)
    (Nat.pow_le_pow_right (Nat.le_max_right factor 1) hi))
  have hv := (Nat.le_add_right (step^[i] g).vertices (step^[i] g).edges.length).trans hs
  have he := (Nat.le_add_left (step^[i] g).edges.length (step^[i] g).vertices).trans hs
  apply ((hwellFormed _ (htrace i).1).length_encoding_le enc descriptorBound
    (hdescriptors _ (htrace i).1)).trans
  dsimp only [iterationSize]
  gcongr

end Cslib.PCP.Encoded.Graph
