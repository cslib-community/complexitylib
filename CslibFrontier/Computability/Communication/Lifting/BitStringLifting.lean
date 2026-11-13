/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.LogarithmicLifting
public import CslibFrontier.Computability.Communication.Discrepancy.Transport
public import CslibFrontier.Foundations.Data.BitString.Basic

/-!
# Discrepancy lifting for bit-string gadgets

Transport through `BitString.equivFin` preserves uniform discrepancy and protocol depth.
Consequently the finite-alphabet lifting theorem applies directly to a gadget on `b`-bit
strings and yields query depth times `b` bounded by communication depth.
-/

public section

namespace Cslib.Communication.Lifting

open Probability

/-- A discrepancy lifting theorem for literal bit-string inputs. -/
theorem exists_decisionTree_bitString {n b k : ℕ} {η : ℝ} {O : Type*}
    (hk : 1 ≤ k) (hη : 1 ≤ 2 * (k : ℝ) * η)
    (hn : 2 ≤ n) (hb : n ^ (2048 * k ^ 2) ≤ 2 ^ b)
    (g : BitString b → BitString b → Bool)
    (hdisc : discrepancy (PMF.uniformOfFintype (BitString b × BitString b)) g ≤
      ((2 : ℝ) ^ b) ^ (-η))
    (R : (Fin n → Bool) → O → Prop)
    (p : Protocol (Fin n → BitString b) (Fin n → BitString b) O)
    (hp : ∀ x y, R (fun i => g (x i) (y i)) (p.run x y)) :
    ∃ t : DecisionTree (Fin n) O, (∀ z, R z (t.eval z)) ∧
      t.depth * b ≤ 768 * k * p.depth := by
  let e := (BitString.equivFin b).symm
  let f : (Fin n → Fin (2 ^ b)) → (Fin n → BitString b) := fun x i => e (x i)
  have hd : discrepancy (PMF.uniformOfFintype (Fin (2 ^ b) × Fin (2 ^ b)))
      (fun x y => g (e x) (e y)) ≤ ((2 ^ b : ℕ) : ℝ) ^ (-η) := by
    rw [discrepancy_uniform_comap_equiv e e g]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hdisc
  obtain ⟨t, ht, hcost⟩ := exists_decisionTree_of_discrepancy_exponent hk hη hn hb
    (fun x y => g (e x) (e y)) hd R (p.comap f f)
    (by intro x y; simpa only [Protocol.run_comap] using hp (f x) (f y))
  refine ⟨t, ht, ?_⟩
  apply queryDepth_mul_bits_le
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Protocol.depth_comap] using hcost

/-- The same bit-string theorem with the alphabet threshold expressed as a bit-length bound. -/
theorem exists_decisionTree_bitString_of_log_bound {n b k : ℕ} {η : ℝ} {O : Type*}
    (hk : 1 ≤ k) (hη : 1 ≤ 2 * (k : ℝ) * η)
    (hn : 2 ≤ n)
    (hb : (2048 * k ^ 2 : ℕ) * Real.log n ≤ (b : ℝ) * Real.log 2)
    (g : BitString b → BitString b → Bool)
    (hdisc : discrepancy (PMF.uniformOfFintype (BitString b × BitString b)) g ≤
      (2 : ℝ) ^ (-(η * b)))
    (R : (Fin n → Bool) → O → Prop)
    (p : Protocol (Fin n → BitString b) (Fin n → BitString b) O)
    (hp : ∀ x y, R (fun i => g (x i) (y i)) (p.run x y)) :
    ∃ t : DecisionTree (Fin n) O, (∀ z, R z (t.eval z)) ∧
      t.depth * b ≤ 768 * k * p.depth := by
  apply exists_decisionTree_bitString hk hη hn
    ((polynomial_le_two_pow_iff (by omega)).2 hb) g _ R p hp
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  convert hdisc using 1; congr 1; ring

end Cslib.Communication.Lifting
