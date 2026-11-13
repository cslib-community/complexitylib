/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.DiscrepancyOracle
public import CslibFrontier.Computability.Communication.Lifting.DensityCompiler

/-!
# A concrete discrepancy lifting theorem

For an alphabet of size `B ^ 2048` and uniform gadget discrepancy at most `B ^ (-1024)`,
every deterministic communication protocol yields a correct decision tree with an explicit
query-depth bound. The local density guarantees are proved from discrepancy, not assumed.
-/

public section

namespace Cslib.Communication.Lifting

open Probability

-- Avoid the exponent-warning path during dependency analysis of the alphabet type.
set_option exponentiation.threshold 2048 in
/-- A concrete polynomial-alphabet discrepancy lifting theorem for arbitrary output relations.
The conservative constants give `B ^ (31 * queryDepth) ≤ 8 ^ (2 * communicationDepth)`. -/
theorem exists_decisionTree_of_polynomial_discrepancy {n B : ℕ} [NeZero B] {O : Type*}
    (g : Fin (B ^ 2048) → Fin (B ^ 2048) → Bool)
    (hB : 2 ≤ B) (hn : 2 ≤ n) (hnB : n ≤ B)
    (hdisc : discrepancy (PMF.uniformOfFintype (Fin (B ^ 2048) × Fin (B ^ 2048))) g ≤
      ((B : ℝ) ^ 1024)⁻¹)
    (R : (Fin n → Bool) → O → Prop)
    (p : Protocol (Fin n → Fin (B ^ 2048)) (Fin n → Fin (B ^ 2048)) O)
    (hp : ∀ x y, R (fun i => g (x i) (y i)) (p.run x y)) :
    ∃ t : DecisionTree (Fin n) O, (∀ z, R z (t.eval z)) ∧
      (B : ℝ) ^ (31 * t.depth) ≤ 8 ^ (2 * p.depth) := by
  have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hBpos : (0 : ℝ) < B := by linarith
  obtain ⟨oa, ob⟩ := densityOracles_polynomial g hB hn hnB hdisc
  obtain ⟨hσ, hστ, hτm, hbase⟩ := polynomial_density_ratios hBR
  have hbase' : 1 ≤ (B : ℝ) ^ 31 := one_le_pow₀ (by linarith)
  obtain ⟨t, ht, hdepth⟩ := exists_simulating_decisionTree g
    ((B : ℝ) ^ 2016) ((B : ℝ) ^ 1984) oa ob
    (by positivity) (by positivity) hσ.le
    (by simpa only [Nat.cast_pow] using hτm.le)
    (by simpa only [Nat.cast_pow] using (hστ.trans hτm).le)
    (by simpa only [Nat.cast_pow] using hbase'.trans hbase) R p hp
  refine ⟨t, ht, ?_⟩
  rw [pow_mul]
  exact (pow_le_pow_left₀ (by positivity) hbase t.depth).trans
    (by simpa only [Nat.cast_pow] using hdepth)

end Cslib.Communication.Lifting
