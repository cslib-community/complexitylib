/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.DiscrepancyOracle
public import CslibFrontier.Computability.Communication.Lifting.DensityCompiler
public import CslibFrontier.Computability.Communication.Lifting.GeneralParameters

/-!
# Discrepancy lifting with an adjustable polynomial exponent

The real alphabet base allows the parameter family to apply to arbitrary finite alphabet sizes.
Increasing the integer parameter accommodates every fixed positive discrepancy exponent.
-/

public section

namespace Cslib.Communication.Lifting

open Probability

/-- The adjustable scalar certificate supplies both orientations of the density simulator. -/
theorem densityOracles_parameter {n m a k : ℕ} [NeZero m] {B : ℝ}
    (g : Fin m → Fin m → Bool) (hk : 1 ≤ k)
    (ha : a + 64 * k = 2048 * k ^ 2) (hB : 2 ≤ B) (hn : 2 ≤ n)
    (hnB : (n : ℝ) ≤ B) (hm : (m : ℝ) = B ^ (2048 * k ^ 2))
    (hdisc : discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g ≤
      (B ^ (1024 * k))⁻¹) :
    DensityOracle (n := n) g (B ^ (a + 32 * k)) (B ^ a) ∧
      DensityOracle (n := n) (fun y x => g x y) (B ^ (a + 32 * k)) (B ^ a) := by
  have hBp : 0 < B := by linarith
  obtain ⟨hgap, hratio, hu, hsize, hq, hweight, hd⟩ :=
    general_parameter_certificate (N := (n : ℝ)) hk ha hB
      (by exact_mod_cast hn) hnB hdisc
  apply densityOracles_of_discrepancy g (r := 16 * k) (u := B ^ (128 * k + 1))
    (q := 1 / (4 * B ^ (128 * k + 3))) (by positivity) (by positivity) hn
    (by omega) hgap hratio hu _ hq _ _
  · simpa only [Nat.cast_mul, hm, ha] using hsize
  · simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hweight
  · simpa only [hm, ha] using hd

/-- Lifting for arbitrary alphabet sizes represented by a real polynomial base. -/
theorem exists_decisionTree_of_parameter_discrepancy {n m k : ℕ} [NeZero m] {B : ℝ}
    {O : Type*} (g : Fin m → Fin m → Bool) (hk : 1 ≤ k)
    (hB : 2 ≤ B) (hn : 2 ≤ n) (hnB : (n : ℝ) ≤ B)
    (hm : (m : ℝ) = B ^ (2048 * k ^ 2))
    (hdisc : discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g ≤
      (B ^ (1024 * k))⁻¹)
    (R : (Fin n → Bool) → O → Prop)
    (p : Protocol (Fin n → Fin m) (Fin n → Fin m) O)
    (hp : ∀ x y, R (fun i => g (x i) (y i)) (p.run x y)) :
    ∃ t : DecisionTree (Fin n) O, (∀ z, R z (t.eval z)) ∧
      B ^ ((32 * k - 1) * t.depth) ≤ 8 ^ (2 * p.depth) := by
  let a := 2048 * k ^ 2 - 64 * k
  have ha : a + 64 * k = 2048 * k ^ 2 := general_lowerDensityExponent_add hk
  have hBp : 0 < B := by linarith
  obtain ⟨oa, ob⟩ := densityOracles_parameter g hk ha hB hn hnB hm hdisc
  obtain ⟨hσ, hστ, hτm, hbase⟩ := general_density_ratios (a := a) hk hB
  have hbase' : 1 ≤ B ^ (32 * k - 1) := one_le_pow₀ (by linarith)
  obtain ⟨t, ht, hdepth⟩ := exists_simulating_decisionTree g
    (B ^ (a + 32 * k)) (B ^ a) oa ob
    (Nat.pos_of_ne_zero (NeZero.ne m)) (by positivity) hσ.le
    (by simpa only [hm, ha] using hτm.le)
    (by simpa only [hm, ha] using (hστ.trans hτm).le)
    (by simpa only [hm, ha] using hbase'.trans hbase) R p hp
  refine ⟨t, ht, ?_⟩
  rw [pow_mul]
  exact (pow_le_pow_left₀ (by positivity) hbase t.depth).trans
    (by simpa only [hm, ha] using hdepth)

/-- The simulation bound in terms of the actual alphabet size, with constants depending only
on the integer discrepancy parameter. -/
theorem exists_decisionTree_of_parameter_discrepancy_alphabet {n m k : ℕ} [NeZero m] {B : ℝ}
    {O : Type*} (g : Fin m → Fin m → Bool) (hk : 1 ≤ k)
    (hB : 2 ≤ B) (hn : 2 ≤ n) (hnB : (n : ℝ) ≤ B)
    (hm : (m : ℝ) = B ^ (2048 * k ^ 2))
    (hdisc : discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g ≤
      (B ^ (1024 * k))⁻¹)
    (R : (Fin n → Bool) → O → Prop)
    (p : Protocol (Fin n → Fin m) (Fin n → Fin m) O)
    (hp : ∀ x y, R (fun i => g (x i) (y i)) (p.run x y)) :
    ∃ t : DecisionTree (Fin n) O, (∀ z, R z (t.eval z)) ∧
      (m : ℝ) ^ t.depth ≤ 8 ^ (256 * k * p.depth) := by
  obtain ⟨t, ht, hd⟩ := exists_decisionTree_of_parameter_discrepancy g hk hB hn hnB hm
    hdisc R p hp
  have hsmall : B ^ (16 * k * t.depth) ≤ (8 : ℝ) ^ (2 * p.depth) := by
    apply le_trans (pow_le_pow_right₀ (by linarith : 1 ≤ B) ?_) hd
    exact Nat.mul_le_mul_right t.depth (by omega)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ B ^ (16 * k * t.depth)) hsmall (128 * k)
  refine ⟨t, ht, ?_⟩
  rw [hm, ← pow_mul]
  simpa only [← pow_mul, show 16 * k * t.depth * (128 * k) = 2048 * k ^ 2 * t.depth by ring,
    show 2 * p.depth * (128 * k) = 256 * k * p.depth by ring] using hpow

end Cslib.Communication.Lifting
