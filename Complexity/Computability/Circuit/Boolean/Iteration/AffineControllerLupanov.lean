/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Iteration.AffineControllerSynthesis
public import Mathlib.Basic.Real.Basic
import Cslib.Computability.Circuit.Boolean.Lupanov
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Asymptotic coefficient synthesis for affine controllers

Applying Lupanov's scalar synthesis theorem to the controller output and the coefficients
of the composed affine payload gives, for every `ε > 0` and sufficiently large controller
width `q`, the fixed-power circuit bound

`(q + p * (p + 1)) * ((1 + ε) * 2 ^ q / q) + p * (5 * (p + 1) + 1)`.

The threshold on `q` is uniform in the payload width `p`, controller, affine maps and fixed
exponent. The final summand charges one matrix-vector multiplication and translation.
Binary powering gives the corresponding bound for an input exponent of `m` bits.

These are nonuniform circuit-size bounds in the same De Morgan model as
`affine_controller_power`; no construction-time bound or new synthesis theorem is claimed.
This applies the classical scalar synthesis bound to the existing affine-controller
decomposition; no priority claim is made.

## Main results

* `Cslib.Circuits.Boolean.Iteration.affine_controller_power_lupanov`: a fixed exponent.
* `Cslib.Circuits.Boolean.Iteration.affine_controller_variable_time_lupanov`: an input exponent.

## References

* [O. B. Lupanov, *On a Method of Circuit Synthesis*][Lupanov1958].
* [S. Schlesinger, *Square-root circuit bounds for iterated functions*]
  [Schlesinger2026IteratedFunctions], for the existing affine-controller decomposition.
-/

public section

namespace Cslib.Circuits.Boolean.Iteration

open Cslib.Circuits Cslib.Circuits.Boolean

private theorem scalar_floor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q ≥ q₀, ∀ f : BooleanFunction q,
      ∃ c : Circuit signature q 1,
        c.Computes interpretation (single f) ∧
        c.size ≤ ⌊(1 + ε) * (2 : ℝ) ^ q / q⌋₊ := by
  obtain ⟨q₀, hq₀⟩ := Lupanov.exists_circuit ε hε
  refine ⟨q₀, fun q hq f => ?_⟩
  obtain ⟨c, hc, hs⟩ := hq₀ q hq f
  exact ⟨c, hc, Nat.le_floor hs⟩

private theorem synthesisBudget_floor_le (q p : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (affineControllerSynthesisBudget q p ⌊R⌋₊ : ℝ) ≤
      (q + p * (p + 1) : ℕ) * R + (p * (5 * (p + 1) + 1) : ℕ) := by
  simp only [affineControllerSynthesisBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one]
  gcongr
  exact Nat.floor_le hR

/-- Lupanov synthesis gives an asymptotic coefficient of one for the controller-output
and affine-coefficient tables, uniformly in the payload width and fixed exponent. -/
theorem affine_controller_power_lupanov (ε : ℝ) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q ≥ q₀, ∀ p : ℕ, ∀ (g : BitString q → BitString q)
      (a : BitString q → (BitString p →ᵃ[Bool] BitString p)) (T : ℕ),
      ∃ c : Circuit signature (q + p) (q + p),
        c.Computes interpretation ((controlledBits g (fun u => a u))^[T]) ∧
        (c.size : ℝ) ≤ (q + p * (p + 1) : ℕ) * ((1 + ε) * (2 : ℝ) ^ q / q) +
          (p * (5 * (p + 1) + 1) : ℕ) := by
  obtain ⟨q₀, hq₀⟩ := scalar_floor_bound ε hε
  refine ⟨q₀, fun q hq p g a T => ?_⟩
  obtain ⟨c, hc, hs⟩ := affine_controller_power_of_scalar_bound g a _ (hq₀ q hq) T
  refine ⟨c, hc, (Nat.cast_le.mpr hs).trans ?_⟩
  exact synthesisBudget_floor_le q p _ (by positivity)

/-- The same asymptotic coefficient-synthesis bound at each conditional binary stage
computes an input exponent with `m` bits. -/
theorem affine_controller_variable_time_lupanov (ε : ℝ) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q ≥ q₀, ∀ p : ℕ, ∀ (g : BitString q → BitString q)
      (a : BitString q → (BitString p →ᵃ[Bool] BitString p)) (m : ℕ),
      ∃ c : Circuit signature ((q + p) + m) (q + p),
        c.Computes interpretation (inputTimeIterate (controlledBits g (fun u => a u)) m) ∧
        (c.size : ℝ) ≤ m * ((q + p * (p + 1) : ℕ) * ((1 + ε) * (2 : ℝ) ^ q / q) +
          (p * (5 * (p + 1) + 1) : ℕ) + (4 * (q + p) : ℕ)) := by
  obtain ⟨q₀, hq₀⟩ := scalar_floor_bound ε hε
  refine ⟨q₀, fun q hq p g a m => ?_⟩
  obtain ⟨c, hc, hs⟩ :=
    affine_controller_variable_time_of_scalar_bound g a _ (hq₀ q hq) m
  refine ⟨c, hc, (Nat.cast_le.mpr hs).trans ?_⟩
  simp only [Nat.cast_mul, Nat.cast_add]
  gcongr
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    synthesisBudget_floor_le q p ((1 + ε) * (2 : ℝ) ^ q / q) (by positivity)

end Cslib.Circuits.Boolean.Iteration
