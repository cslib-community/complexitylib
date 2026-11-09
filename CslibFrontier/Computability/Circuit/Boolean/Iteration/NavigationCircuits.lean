/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.ForestCircuits
import Mathlib.Tactic.Linarith

/-!
# Reachability and first-hitting-time circuits

Combining `forest_transient_circuit` with `checkpoint_depth_circuit`, `cycle_label_circuit`, and
`synthesis_navigation_given_flag` yields a Boolean circuit on pair inputs `z : BitString (n + n)`
returning both the reachability bit and the `(n + 1)`-bit first hitting time
`navigationBits f (inputLeft z) (inputRight z)` within `navigationBudget n c.size L` gates
(`navigation_circuit`), and within `13500000 * optimizedBudget n c.size (2 ^ n)` gates at the
balanced checkpoint parameter (`reachability_hitting_time`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.navigationBudget`: gate bound for the navigation circuit at
  checkpoint spacing `L`.

## Main results

* `Cslib.Circuits.Boolean.Iteration.navigation_circuit`: synthesizes `navigationBits` within
  `navigationBudget n c.size L` gates.
* `Cslib.Circuits.Boolean.Iteration.navigationBudget_le`: bounds `navigationBudget` by
  `4500000 * powerBudget n s (2 ^ n) L`.
* `Cslib.Circuits.Boolean.Iteration.reachability_hitting_time`: square-root-size circuit returning
  reachability and first hitting time.

## References

* Adapted from lean/Proofs/NavigationCircuits.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

attribute [local instance] lexOrder

variable {n : ℕ}

/-- Gate bound for the combined reachability and first-hitting-time circuit at spacing `L`. -/
def navigationBudget (n s L : ℕ) : ℕ :=
  2 + 4220000 * powerBudget n s (2 ^ n) L + 50 * (n + 4) ^ 2 + (49 * n + 138)

/-- **Reachability and first hitting time at spacing `L`.** Forest reachability plus depths, cycle
labels, and word arithmetic compute `navigationBits` within `navigationBudget n c.size L` gates. -/
theorem navigation_circuit (c : Circuit signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature (n + n) (1 + (n + 1)),
      out.Computes interpretation (fun z =>
        navigationBits (c.eval interpretation) (inputLeft z) (inputRight z)) ∧
      out.size ≤ navigationBudget n c.size L := by
  let f := c.eval interpretation
  obtain ⟨depth, hd, hds⟩ := checkpoint_depth_circuit c L hL hLN
  obtain ⟨label, hl, hls⟩ := cycle_label_circuit c L hL hLN
  obtain ⟨transient, htr, htrs⟩ := forest_transient_circuit c L hL hLN
  have hnav := synthesis_navigation_given_flag f depth hd label hl transient htr
  obtain ⟨out, hout, hsize⟩ := hnav.exists_circuit_outputs
  refine ⟨out, hout, hsize.trans ?_⟩
  unfold navigationBudget
  omega

/-- Every component of `navigationBudget` fits within `4500000 * powerBudget`. -/
theorem navigationBudget_le (n s L : ℕ) :
    navigationBudget n s L ≤ 4500000 * powerBudget n s (2 ^ n) L := by
  have hb : (n + 1) ^ 3 ≤ powerBudget n s (2 ^ n) L := by
    have hh := Nat.mul_le_mul_left ((n + 1) ^ 3) (show 1 ≤ L + 2 ^ n / L + 1 by lia)
    unfold powerBudget
    nlinarith
  have hfour : (n + 4) ^ 2 ≤ 16 * (n + 1) ^ 3 := by
    have h1 : (n + 4) ^ 2 ≤ 16 * (n + 1) ^ 2 := by
      have := Nat.pow_le_pow_left (show n + 4 ≤ 4 * (n + 1) by omega) 2
      nlinarith
    have h2 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
    nlinarith
  have hn1 : n + 1 ≤ (n + 1) ^ 3 := by nlinarith [Nat.zero_le (n ^ 2)]
  unfold navigationBudget
  nlinarith

/-- **Reachability and first hitting time**, with an explicit optimized gate bound. -/
theorem reachability_hitting_time (c : Circuit signature n n) :
    ∃ out : Circuit signature (n + n) (1 + (n + 1)),
      (∀ z, out.eval interpretation z 0 = true ↔
        ∃ t, (c.eval interpretation)^[t] (inputLeft z) = inputRight z) ∧
      (∀ z, out.eval interpretation z 0 = true →
        let t := (word fun i : Fin (n + 1) =>
          out.eval interpretation z (Fin.natAdd 1 i)).toNat
        (c.eval interpretation)^[t] (inputLeft z) = inputRight z ∧
          (∀ j < t, (c.eval interpretation)^[j] (inputLeft z) ≠ inputRight z) ∧
          t < 2 ^ n) ∧
      (out.size : ℝ) ≤ 13500000 * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨L, hL, hLN, ho⟩ := exists_powerBudget_le_optimizedBudget n c.size (2 ^ n) le_rfl
  obtain ⟨out, hout, hs⟩ := navigation_circuit c L hL hLN
  refine ⟨out, ?_, ?_, ?_⟩
  · intro z
    rw [hout z]
    exact navigationBits_flag _ _ _
  · intro z hz
    rw [hout z] at hz ⊢
    exact navigationBits_time _ _ _ ((navigationBits_flag _ _ _).mp hz)
  · have hs' : (out.size : ℝ) ≤
        4500000 * (powerBudget n c.size (2 ^ n) L : ℝ) := by
      exact_mod_cast hs.trans (navigationBudget_le n c.size L)
    linarith

end Cslib.Circuits.Boolean.Iteration
