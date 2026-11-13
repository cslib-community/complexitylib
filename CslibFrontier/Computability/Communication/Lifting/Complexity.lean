/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.BitStringLifting

/-!
# Minimum-complexity discrepancy lifting

The protocol simulation implies a lower bound between the repository's existing minimum
measures: deterministic decision-tree complexity and deterministic communication complexity.
The extended-natural communication measure includes the case of no solving protocol.
-/

public section

namespace Cslib.Communication.Lifting

open Probability

/-- A bound valid for every computing protocol is also valid for minimum communication cost,
including infinite cost. -/
private theorem le_mul_ecomplexityFun_of_forall {X Y O : Type*} (F : X → Y → O) {a c : ℕ}
    (hc : 0 < c)
    (h : ∀ p : Protocol X Y O, p.run = F → a ≤ c * p.depth) :
    (a : ℕ∞) ≤ (c : ℕ∞) * Protocol.ecomplexityFun F := by
  generalize he : Protocol.ecomplexityFun F = e
  induction e using ENat.recTopCoe with
  | top => simp [show (c : ℕ∞) ≠ 0 by exact_mod_cast hc.ne']
  | coe d =>
    obtain ⟨p, hp, hd⟩ := Protocol.ecomplexityFun_le_iff.mp he.le
    exact_mod_cast (h p hp).trans (Nat.mul_le_mul_left c hd)

/-- The minimum decision-tree complexity times gadget bit length is bounded by a constant
multiple of the minimum communication complexity of the composed function. -/
theorem complexity_mul_bits_le_ecomplexityFun {n b k : ℕ} {η : ℝ} {O : Type*}
    (hk : 1 ≤ k) (hη : 1 ≤ 2 * (k : ℝ) * η)
    (hn : 2 ≤ n)
    (hb : (2048 * k ^ 2 : ℕ) * Real.log n ≤ (b : ℝ) * Real.log 2)
    (g : BitString b → BitString b → Bool)
    (hdisc : discrepancy (PMF.uniformOfFintype (BitString b × BitString b)) g ≤
      (2 : ℝ) ^ (-(η * b)))
    (f : (Fin n → Bool) → O) :
    ((DecisionTree.complexity f * b : ℕ) : ℕ∞) ≤ (768 * k : ℕ∞) *
      Protocol.ecomplexityFun (fun x y : Fin n → BitString b => f (fun i => g (x i) (y i))) := by
  apply le_mul_ecomplexityFun_of_forall _ (by omega : 0 < 768 * k)
  intro p hp
  obtain ⟨t, ht, hd⟩ := exists_decisionTree_bitString_of_log_bound hk hη hn hb g hdisc
    (fun z o => o = f z) p (by intro x y; exact congrFun (congrFun hp x) y)
  exact (Nat.mul_le_mul_right b (DecisionTree.complexity_le_depth ht)).trans hd

/-- Every positive discrepancy exponent admits one lifting constant uniformly over dimensions,
bit lengths, gadgets, output types, and outer functions. -/
theorem exists_complexity_lifting_parameter {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ 1 / (2 * η) + 1 ∧
      ∀ (n b : ℕ), 2 ≤ n →
      (2048 * k ^ 2 : ℕ) * Real.log n ≤ (b : ℝ) * Real.log 2 →
      ∀ (g : BitString b → BitString b → Bool),
      discrepancy (PMF.uniformOfFintype (BitString b × BitString b)) g ≤
        (2 : ℝ) ^ (-(η * b)) →
      ∀ (O : Type*) (f : (Fin n → Bool) → O),
      ((DecisionTree.complexity f * b : ℕ) : ℕ∞) ≤ (768 * k : ℕ∞) *
        Protocol.ecomplexityFun
          (fun x y : Fin n → BitString b => f (fun i => g (x i) (y i))) := by
  obtain ⟨k, hk, hηk, hupper⟩ := exists_density_exponent_le hη
  refine ⟨k, hk, hupper, ?_⟩
  intro n b hn hb g hd O f
  exact complexity_mul_bits_le_ecomplexityFun hk hηk hn hb g hd f

end Cslib.Communication.Lifting
