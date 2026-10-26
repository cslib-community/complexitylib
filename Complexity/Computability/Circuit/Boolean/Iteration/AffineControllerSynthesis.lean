/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Iteration.AffineController
import Complexity.Computability.Circuit.Boolean.ShannonSynthesis
import Mathlib.Tactic.Ring

/-!
# Synthesizing the coefficients of an affine controller

For an autonomous `q`-bit controller with a `p`-bit affine payload, every fixed iterate is
again a controller-selected affine map. Its `q` controller outputs and `p * (p + 1)` matrix
and offset coefficients are Boolean functions of only the controller input. Synthesizing
these coefficient functions before applying the affine map costs
`(q + p * (p + 1)) * L + p * (5 * (p + 1) + 1)` gates whenever every Boolean function on
`q` inputs has a circuit with at most `L` gates.

The finite Shannon bound gives `L = 27 * 2 ^ q / q` for `q ≥ 16`. In particular, when
`p = q`, this improves the existing `O(q ^ 2 * 2 ^ q)` bound from separate affine maps
for all controller states to `O(q * 2 ^ q)`. The hypotheses on the controller and affine
payloads are unchanged. Binary powering transfers the improvement to input-time iteration.

This combines the existing controller decomposition and classical Boolean synthesis.
It is a strengthening of the library's affine-controller bound; no
priority or optimality claim is made. All NOT, AND, OR and constant gates are charged,
while wiring and fanout are free. These are nonuniform circuit-size bounds, with no
bound on the time needed to construct the circuits or their coefficient tables.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.affineControllerSynthesisBudget`: the coefficient-table
  synthesis budget, parameterized by the scalar Boolean synthesis bound.

## Main results

* `Cslib.Circuits.Boolean.Iteration.controlled_affine_circuit_of_scalar_bound`: synthesize
  an arbitrary controller-selected affine map.
* `Cslib.Circuits.Boolean.Iteration.affine_controller_power_of_scalar_bound`: every fixed
  iterate satisfies the same budget.
* `Cslib.Circuits.Boolean.Iteration.affine_controller_power_shannon`: the finite bound
  using `27 * 2 ^ q / q` gates per coefficient, for `q ≥ 16`.
* `Cslib.Circuits.Boolean.Iteration.affine_controller_variable_time_of_scalar_bound`,
  `Cslib.Circuits.Boolean.Iteration.affine_controller_variable_time_shannon`: input-time bounds.

## References

* [S. Schlesinger, *Square-root circuit bounds for iterated functions*]
  [Schlesinger2026IteratedFunctions], for the existing affine-controller decomposition.
* [O. B. Lupanov, *On a Method of Circuit Synthesis*][Lupanov1958], for Boolean synthesis.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.BitString.LinearHash
open scoped BigOperators

variable {q p : ℕ}

/-- Synthesizing the controller output and affine coefficients at `L` gates each, followed
by one affine evaluation. -/
def affineControllerSynthesisBudget (q p L : ℕ) : ℕ :=
  (q + p * (p + 1)) * L + p * (5 * (p + 1) + 1)

/-- Compute a controller-selected affine map by synthesizing its scalar coefficients.
This accepts any size bound valid for all `q`-input Boolean functions. -/
theorem controlled_affine_circuit_of_scalar_bound (g : BitString q → BitString q)
    (a : BitString q → (BitString p →ᵃ[Bool] BitString p)) (L : ℕ)
    (hL : ∀ f : BooleanFunction q, ∃ c : Circuit signature q 1,
      c.Computes interpretation (single f) ∧ c.size ≤ L) :
    ∃ c : Circuit signature (q + p) (q + p),
      c.Computes interpretation (controlledBits g (fun u => a u)) ∧
      c.size ≤ affineControllerSynthesisBudget q p L := by
  let u : BitString (q + p) → BitString q := fun x i => x (Fin.castAdd p i)
  let v : BitString (q + p) → BitString p := fun x i => x (Fin.natAdd q i)
  have hscalar (f : BooleanFunction q) :
      Synthesis interpretation (inputs (q + p)) {fun x => f (u x)} L := by
    obtain ⟨c, hc, hs⟩ := hL f
    have h := Synthesis.circuit (I := interpretation) (s := inputs (q + p)) c
      (fun i x => u x i) (fun i => ⟨Fin.castAdd p i, rfl⟩)
    have he : c.eval interpretation = single f := funext hc
    simpa [he, wires, single] using h.mono Set.Subset.rfl Set.Subset.rfl hs
  have hrow (row : Fin p) :
      Synthesis interpretation (inputs (q + p)) {fun x => a (u x) (v x) row}
        ((p + 1) * (L + 5) + 1) := by
    let term (j : Fin (p + 1)) (x : BitString (q + p)) : Bool :=
      Fin.snoc (α := fun _ => Bool) (fun i => (affineMapSeed (a (u x))).1 row i * v x i)
        ((affineMapSeed (a (u x))).2 row) j
    have hterm (j : Fin (p + 1)) :
        Synthesis interpretation (inputs (q + p)) {term j} (L + 1) := by
      induction j using Fin.lastCases with
      | last =>
        simpa only [term, Fin.snoc_last] using
          (hscalar (fun z => (affineMapSeed (a z)).2 row)).mono
            Set.Subset.rfl Set.Subset.rfl (Nat.le_succ L)
      | cast i =>
        have hinput : Synthesis interpretation (inputs (q + p)) {fun x => v x i} 0 :=
          Synthesis.of_mem ⟨Fin.natAdd q i, rfl⟩
        simpa only [term, Fin.snoc_castSucc, Bool.mul_eq_and, Nat.add_zero] using
          (hscalar (fun z => (affineMapSeed (a z)).1 row i)).and hinput
    have hsum := Synthesis.sum (s := inputs (q + p))
      (Finset.univ : Finset (Fin (p + 1))) term (fun _ => L + 1) (fun j _ => hterm j)
    have he : (fun x : BitString (q + p) => ∑ j : Fin (p + 1), term j x) =
        fun x => a (u x) (v x) row := by
      funext x
      rw [Fin.sum_univ_castSucc]
      simp only [term, Fin.snoc_castSucc, Fin.snoc_last]
      change affineHash (affineMapSeed (a (u x))) (v x) row = _
      exact congrFun (affineHash_affineMapSeed (a (u x)) (v x)) row
    rw [he] at hsum
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul,
      Nat.add_assoc, show 1 + 4 = 5 by rfl] using hsum
  let cost : Fin (q + p) → ℕ := Fin.append (fun _ => L) (fun _ => (p + 1) * (L + 5) + 1)
  have hout (i : Fin (q + p)) :
      Synthesis interpretation (inputs (q + p))
        {fun x => controlledBits g (fun z => a z) x i} (cost i) := by
    induction i using Fin.addCases with
    | left i =>
      simpa only [cost, controlledBits, Fin.append_left, u] using hscalar (fun z => g z i)
    | right i =>
      simpa only [cost, controlledBits, Fin.append_right, u, v] using hrow i
  obtain ⟨c, hc, hs⟩ := (Synthesis.family _ cost hout).exists_circuit_outputs
  refine ⟨c, hc, hs.trans (le_of_eq ?_)⟩
  simp only [cost, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul,
    affineControllerSynthesisBudget]
  ring

/-- Every fixed iterate has the coefficient-synthesis bound, since the composed payload
map is affine for each initial controller state. -/
theorem affine_controller_power_of_scalar_bound (g : BitString q → BitString q)
    (a : BitString q → (BitString p →ᵃ[Bool] BitString p)) (L : ℕ)
    (hL : ∀ f : BooleanFunction q, ∃ c : Circuit signature q 1,
      c.Computes interpretation (single f) ∧ c.size ≤ L) (T : ℕ) :
    ∃ c : Circuit signature (q + p) (q + p),
      c.Computes interpretation ((controlledBits g (fun u => a u))^[T]) ∧
      c.size ≤ affineControllerSynthesisBudget q p L := by
  let family : Set (BitString p → BitString p) :=
    Set.range fun f : BitString p →ᵃ[Bool] BitString p => ⇑f
  have hclosed (u : BitString q) : controlledPayload g (fun z => a z) T u ∈ family :=
    controlledPayload_mem g (fun z => a z) family
      (show id ∈ family from ⟨AffineMap.id Bool (BitString p), rfl⟩)
      (fun _ ⟨f, hf⟩ _ ⟨h, hh⟩ => ⟨f.comp h, by simp only [← hf, ← hh]; rfl⟩)
      (fun z => ⟨a z, rfl⟩) T u
  choose b hb using hclosed
  obtain ⟨c, hc, hs⟩ := controlled_affine_circuit_of_scalar_bound (g^[T]) b L hL
  refine ⟨c, fun x => (hc x).trans ?_, hs⟩
  rw [controlledBits_iterate]
  simp only [controlledBits, hb]

/-- Finite coefficient synthesis for controllers of width at least 16. -/
theorem affine_controller_power_shannon (hq : 16 ≤ q) (g : BitString q → BitString q)
    (a : BitString q → (BitString p →ᵃ[Bool] BitString p)) (T : ℕ) :
    ∃ c : Circuit signature (q + p) (q + p),
      c.Computes interpretation ((controlledBits g (fun u => a u))^[T]) ∧
      c.size ≤ affineControllerSynthesisBudget q p (27 * 2 ^ q / q) :=
  affine_controller_power_of_scalar_bound g a _ (ShannonSynthesis.exists_circuit hq) T

/-- Conditional binary powers transfer any scalar synthesis bound to an input exponent. -/
theorem affine_controller_variable_time_of_scalar_bound (g : BitString q → BitString q)
    (a : BitString q → (BitString p →ᵃ[Bool] BitString p)) (L : ℕ)
    (hL : ∀ f : BooleanFunction q, ∃ c : Circuit signature q 1,
      c.Computes interpretation (single f) ∧ c.size ≤ L) (m : ℕ) :
    ∃ c : Circuit signature ((q + p) + m) (q + p),
      c.Computes interpretation (inputTimeIterate (controlledBits g (fun u => a u)) m) ∧
      c.size ≤ m * (affineControllerSynthesisBudget q p L + 4 * (q + p)) :=
  binary_powering (controlledBits g (fun u => a u)) m (affineControllerSynthesisBudget q p L)
    fun j _ => affine_controller_power_of_scalar_bound g a L hL (2 ^ j)

/-- An input exponent with `m` bits, using the finite Shannon coefficient bound. -/
theorem affine_controller_variable_time_shannon (hq : 16 ≤ q)
    (g : BitString q → BitString q)
    (a : BitString q → (BitString p →ᵃ[Bool] BitString p)) (m : ℕ) :
    ∃ c : Circuit signature ((q + p) + m) (q + p),
      c.Computes interpretation (inputTimeIterate (controlledBits g (fun u => a u)) m) ∧
      c.size ≤ m * (affineControllerSynthesisBudget q p (27 * 2 ^ q / q) + 4 * (q + p)) :=
  affine_controller_variable_time_of_scalar_bound g a _ (ShannonSynthesis.exists_circuit hq) m

end Cslib.Circuits.Boolean.Iteration
