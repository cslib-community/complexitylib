/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.ForestQuerySynthesis
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.NavigationSynthesis
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.Optimization
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Square-root-size reachability circuits via compressed checkpoint forests

Combining `synthesis_transient_forest_reachability` with `checkpoint_depth_circuit`,
`exists_forest_circuit_tables`, and `cycle_label_circuit` yields a Boolean circuit of size
`O(powerBudget n c.size (2 ^ n) L)` that decides reachability `∃ t, f^[t] x = y` for all pairs of
states `(x, y)` (`forest_reachability_circuit`). Optimizing the checkpoint spacing `L` yields the
square-root-size bound `O(optimizedBudget n c.size (2 ^ n))` (`forest_reachability_optimized`).

## Main results

* `Cslib.Circuits.Boolean.Iteration.forest_dictionary_cost_le`: bounds `dictionaryCost` by a
  constant multiple of `powerBudget`.
* `Cslib.Circuits.Boolean.Iteration.transientForestCost_le`: bounds `transientForestCost` by a
  constant multiple of `powerBudget`.
* `Cslib.Circuits.Boolean.Iteration.forest_transient_circuit`: decides reachability to transient
  targets within `4000000 * powerBudget n c.size (2 ^ n) L` gates.
* `Cslib.Circuits.Boolean.Iteration.forest_reachability_circuit`: decides general reachability
  within `4500000 * powerBudget n c.size (2 ^ n) L` gates.
* `Cslib.Circuits.Boolean.Iteration.forest_reachability_optimized`: decides general reachability
  within `13500000 * optimizedBudget n c.size (2 ^ n)` gates.

## References

* Adapted from lean/Proofs/ForestCircuits.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

attribute [local instance] lexOrder

variable {n : ℕ}

/-- Every shared dictionary lookup in the compressed-forest query fits within `powerBudget`. -/
theorem forest_dictionary_cost_le (n s v M Q L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n)
    (hv : v ≤ 4 * n + 5) (hM : M ≤ 2 * (2 ^ n / L)) (hQ : Q ≤ 2 * L + 2) :
    dictionaryCost n v M Q ≤ 1500000 * powerBudget n s (2 ^ n) L := by
  let N := 2 ^ n
  have hN : 1 ≤ N := Nat.one_le_two_pow
  have hMN : M ≤ 2 * N := hM.trans (Nat.mul_le_mul_left _ (Nat.div_le_self _ _))
  have hd : Nat.clog 2 (M + Q + 1) ≤ n + 3 := by
    apply Nat.clog_le_of_le_pow
    have hpow : 2 ^ (n + 3) = 8 * N := by
      dsimp [N]
      rw [pow_add]
      ring
    omega
  have hw : (Nat.clog 2 (M + Q + 1) + n + (1 + v) + 3) ^ 3 ≤ 1728 * (n + 1) ^ 3 := by
    have h1 : Nat.clog 2 (M + Q + 1) + n + (1 + v) + 3 ≤ 12 * (n + 1) := by omega
    calc (Nat.clog 2 (M + Q + 1) + n + (1 + v) + 3) ^ 3
        ≤ (12 * (n + 1)) ^ 3 := Nat.pow_le_pow_left h1 3
      _ = 1728 * (n + 1) ^ 3 := by ring
  have hr : M + Q + 1 ≤ 3 * (L + 2 ^ n / L + 1) := by lia
  have hb : (n + 1) ^ 3 * (L + 2 ^ n / L + 1) ≤ powerBudget n s (2 ^ n) L := by
    unfold powerBudget
    nlinarith
  unfold dictionaryCost
  calc 256 * (M + Q + 1) * (Nat.clog 2 (M + Q + 1) + n + (1 + v) + 3) ^ 3
      ≤ 256 * (3 * (L + 2 ^ n / L + 1)) * (1728 * (n + 1) ^ 3) := by gcongr
    _ = 1327104 * ((n + 1) ^ 3 * (L + 2 ^ n / L + 1)) := by ring
    _ ≤ 1500000 * powerBudget n s (2 ^ n) L := by nlinarith

/-- The transient compressed-forest query budget is bounded by `4000000 * powerBudget`. -/
theorem transientForestCost_le (n s d M E L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n)
    (hd : d ≤ 50000 * powerBudget n s (2 ^ n) L)
    (hM : M ≤ 2 * (2 ^ n / L)) (hE : E ≤ 2 * (2 ^ n / L)) :
    transientForestCost n s d M E L ≤ 4000000 * powerBudget n s (2 ^ n) L := by
  have hm := forest_dictionary_cost_le n s (n + 1 + (n + 1)) M (2 * L + 2) L
    hL hLN (by omega) hM le_rfl
  have he := forest_dictionary_cost_le n s (n + (n + 1 + (n + 1)) + (n + 3)) E (2 * L + 1) L
    hL hLN (by omega) hE (by omega)
  have hn1 : n + 1 ≤ (n + 1) ^ 3 := by nlinarith [Nat.zero_le (n ^ 2)]
  have hp : (2 * L + 1) * (41 * n + 41) + (24 * n + 50) + 2 ≤
      200 * ((n + 1) ^ 3 * (L + 2 ^ n / L + 1)) := by
    have h1 : (2 * L + 1) * (41 * n + 41) ≤
        (3 * (L + 2 ^ n / L + 1)) * (41 * (n + 1) ^ 3) :=
      Nat.mul_le_mul (by omega) (by nlinarith)
    have h2 : 24 * n + 50 + 2 ≤ 52 * ((n + 1) ^ 3 * (L + 2 ^ n / L + 1)) := by
      have hL1 : 1 ≤ L + 2 ^ n / L + 1 := by omega
      nlinarith
    nlinarith
  have hb : (n + 1) ^ 3 * (L + 2 ^ n / L + 1) ≤ powerBudget n s (2 ^ n) L := by
    unfold powerBudget
    nlinarith
  have hs : L * s ≤ powerBudget n s (2 ^ n) L := by
    unfold powerBudget
    nlinarith
  unfold transientForestCost
  nlinarith

/-- **Transient reachability.** For transient targets, reachability has the same checkpoint tradeoff
as a single fixed iterate. -/
theorem forest_transient_circuit (c : Circuit signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature (n + n) 1,
      (∀ z, 0 < transientDepth (c.eval interpretation) (inputRight z) →
        (out.eval interpretation z 0 = true ↔
          ∃ t, (c.eval interpretation)^[t] (inputLeft z) = inputRight z)) ∧
      out.size ≤ 4000000 * powerBudget n c.size (2 ^ n) L := by
  obtain ⟨depth, hd, hds⟩ := checkpoint_depth_circuit c L hL hLN
  obtain ⟨tables⟩ := exists_forest_circuit_tables (c.eval interpretation) L hL
  obtain ⟨out, hout, hsize⟩ := synthesis_transient_forest_reachability c L hL depth hd tables
  exact ⟨out, hout, hsize.trans (transientForestCost_le n c.size depth.size
    tables.markCount tables.edgeTable.count L hL hLN hds tables.markCount_le tables.edgeCount_le)⟩

/-- **General reachability.** Combining compressed-forest ancestry for transient targets with
canonical cycle representatives for periodic targets decides reachability for all pairs `(x, y)`
within `4500000 * powerBudget n c.size (2 ^ n) L` gates. -/
theorem forest_reachability_circuit (c : Circuit signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature (n + n) 1,
      (∀ z, out.eval interpretation z 0 = true ↔
        ∃ t, (c.eval interpretation)^[t] (inputLeft z) = inputRight z) ∧
      out.size ≤ 4500000 * powerBudget n c.size (2 ^ n) L := by
  let f := c.eval interpretation
  obtain ⟨depth, hd, hds⟩ := checkpoint_depth_circuit c L hL hLN
  obtain ⟨label, hl, hls⟩ := cycle_label_circuit c L hL hLN
  obtain ⟨transient, htr, htrs⟩ := forest_transient_circuit c L hL hLN
  have hnav := synthesis_navigation_given_flag f depth hd label hl transient htr
  have hflag : Synthesis interpretation (inputs (n + n))
      {fun z => navigationBits f (inputLeft z) (inputRight z) 0}
      (2 + 2 * depth.size + 2 * label.size + transient.size +
        50 * (n + 4) ^ 2 + (49 * n + 138)) := by
    refine hnav.mono Set.Subset.rfl ?_ le_rfl
    rintro _ rfl
    exact ⟨0, rfl⟩
  obtain ⟨out, hout, hsize⟩ := hflag.exists_circuit
  refine ⟨out, fun z => ?_, hsize.trans ?_⟩
  · rw [hout z]
    exact navigationBits_flag f (inputLeft z) (inputRight z)
  · have hb : (n + 1) ^ 3 ≤ powerBudget n c.size (2 ^ n) L := by
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
    nlinarith

/-- **Square-root reachability.** Optimizing the checkpoint parameter `L` gives a circuit of size at
most `13500000 * optimizedBudget n c.size (2 ^ n)` deciding reachability for all state pairs. -/
theorem forest_reachability_optimized (c : Circuit signature n n) :
    ∃ out : Circuit signature (n + n) 1,
      (∀ z, out.eval interpretation z 0 = true ↔
        ∃ t, (c.eval interpretation)^[t] (inputLeft z) = inputRight z) ∧
      (out.size : ℝ) ≤ 13500000 * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨L, hL, hLN, hopt⟩ := exists_powerBudget_le_optimizedBudget n c.size (2 ^ n) le_rfl
  obtain ⟨out, hout, hs⟩ := forest_reachability_circuit c L hL hLN
  refine ⟨out, hout, ?_⟩
  have hs' : (out.size : ℝ) ≤ 4500000 * (powerBudget n c.size (2 ^ n) L : ℝ) := by
    exact_mod_cast hs
  linarith

end Cslib.Circuits.Boolean.Iteration
