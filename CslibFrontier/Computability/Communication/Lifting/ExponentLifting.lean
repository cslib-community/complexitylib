/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.GeneralDiscrepancyLifting
public import CslibFrontier.Computability.Communication.Lifting.ExponentParameters

/-!
# Deterministic lifting for every positive discrepancy exponent

For every fixed `η > 0`, choose an integer `k ≤ 1/(2η)+1` with `2kη ≥ 1`. Every alphabet
size `m ≥ n^(2048k²)` and gadget of uniform discrepancy at most `m^(-η)` then admits a
correct decision-tree simulation satisfying `m^queryDepth ≤ 8^(256k*communicationDepth)`.
The alphabet need not be a perfect power. Taking logarithms gives the deterministic
query-to-communication lower bound with constants depending only on `η`.

This is the deterministic part of CFKMP, arXiv:1904.13056v4, Theorem 1.2, with conservative
constants and an arbitrary finite alphabet represented by `Fin m`. Randomized lifting and
round-sensitive refinements are not claimed. The proof uses the elementary fourth-power XOR
estimate already documented in this development, rather than the paper's sharper cited result.
-/

public section

namespace Cslib.Communication.Lifting

open Probability

/-- General discrepancy-exponent lifting with an explicit integer parameter. -/
theorem exists_decisionTree_of_discrepancy_exponent {n m k : ℕ} [NeZero m] {η : ℝ} {O : Type*}
    (hk : 1 ≤ k) (hη : 1 ≤ 2 * (k : ℝ) * η)
    (hn : 2 ≤ n) (hm : n ^ (2048 * k ^ 2) ≤ m)
    (g : Fin m → Fin m → Bool)
    (hdisc : discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g ≤ (m : ℝ) ^ (-η))
    (R : (Fin n → Bool) → O → Prop)
    (p : Protocol (Fin n → Fin m) (Fin n → Fin m) O)
    (hp : ∀ x y, R (fun i => g (x i) (y i)) (p.run x y)) :
    ∃ t : DecisionTree (Fin n) O, (∀ z, R z (t.eval z)) ∧
      (m : ℝ) ^ t.depth ≤ 8 ^ (256 * k * p.depth) := by
  obtain ⟨hB, hnB, hMB, hd⟩ := density_root_parameters hk hη
    (show (2 : ℝ) ≤ n by exact_mod_cast hn)
    (show (n : ℝ) ^ (2048 * k ^ 2) ≤ m by exact_mod_cast hm) hdisc
  exact exists_decisionTree_of_parameter_discrepancy_alphabet g hk hB hn hnB hMB hd R p hp

/-- For every positive discrepancy exponent, one parameter works uniformly for every outer
relation, every sufficiently large alphabet, and every protocol solving its gadget composition. -/
theorem exists_general_lifting_parameter {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ 1 / (2 * η) + 1 ∧
      ∀ (n m : ℕ) [NeZero m], 2 ≤ n → n ^ (2048 * k ^ 2) ≤ m →
      ∀ (g : Fin m → Fin m → Bool),
      discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g ≤ (m : ℝ) ^ (-η) →
      ∀ (O : Type*) (R : (Fin n → Bool) → O → Prop)
        (p : Protocol (Fin n → Fin m) (Fin n → Fin m) O),
      (∀ x y, R (fun i => g (x i) (y i)) (p.run x y)) →
      ∃ t : DecisionTree (Fin n) O, (∀ z, R z (t.eval z)) ∧
        (m : ℝ) ^ t.depth ≤ 8 ^ (256 * k * p.depth) := by
  obtain ⟨k, hk, hηk, hupper⟩ := exists_density_exponent_le hη
  refine ⟨k, hk, hupper, ?_⟩
  intro n m _ hn hm g hd O R p hp
  exact exists_decisionTree_of_discrepancy_exponent hk hηk hn hm g hd R p hp

end Cslib.Communication.Lifting
