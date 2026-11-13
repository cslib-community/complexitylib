/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module

import CslibFrontier.Computability.Communication.Lifting.Complexity

/-! Regression clients for arbitrary positive discrepancy exponents and alphabet sizes. -/

open Cslib Cslib.Communication Cslib.Communication.Lifting Cslib.Probability

/-- The parameter choice is bounded and independent of the input dimension and alphabet. -/
example {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, 1 ≤ k ∧ 1 ≤ 2 * (k : ℝ) * η ∧ (k : ℝ) ≤ 1 / (2 * η) + 1 :=
  exists_density_exponent_le hη

/-- Discrepancy exponent `1/100` is covered, unlike the previous fixed `1/2` endpoint.
The alphabet size is arbitrary subject to the lower bound, not a prescribed perfect power. -/
example {n m : ℕ} [NeZero m] (hn : 2 ≤ n) (hm : n ^ (2048 * 50 ^ 2) ≤ m)
    (g : Fin m → Fin m → Bool) (f : (Fin n → Bool) → Bool)
    (hd : discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g ≤
      (m : ℝ) ^ (-(1 / 100 : ℝ)))
    (p : Protocol (Fin n → Fin m) (Fin n → Fin m) Bool)
    (hp : ∀ x y, p.run x y = f (fun i => g (x i) (y i))) :
    ∃ t : DecisionTree (Fin n) Bool, (∀ z, t.eval z = f z) ∧
      (m : ℝ) ^ t.depth ≤ 8 ^ (256 * 50 * p.depth) :=
  exists_decisionTree_of_discrepancy_exponent (k := 50) (by norm_num) (by norm_num)
    hn hm g hd (fun z o => o = f z) p hp

/-- The real-root bridge also permits alphabets strictly between successive powers. -/
example {M : ℝ} (hM : (3 : ℝ) ^ 2048 ≤ M) :
    (3 : ℝ) ≤ M ^ ((2048 : ℝ)⁻¹) := by
  have hD : (0 : ℝ) ≤ M ^ (-(1 : ℝ)) :=
    Real.rpow_nonneg ((pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) 2048).trans hM) _
  have h := density_root_parameters (k := 1) (η := 1) (D := 0)
    (by norm_num) (by norm_num) (by norm_num : (2 : ℝ) ≤ 3) (by simpa using hM) hD
  simpa using h.2.1

/-- Alphabet transport also handles an empty bit string and unequal player alphabet sizes. -/
example (g : BitString 0 → BitString 1 → Bool) :
    discrepancy (PMF.uniformOfFintype (Fin (2 ^ 0) × Fin (2 ^ 1)))
      (fun x y => g ((BitString.equivFin 0).symm x) ((BitString.equivFin 1).symm y)) =
      discrepancy (PMF.uniformOfFintype (BitString 0 × BitString 1)) g :=
  discrepancy_uniform_comap_equiv (BitString.equivFin 0).symm (BitString.equivFin 1).symm g

/-- A Boolean-function client uses literal bit-string gadget inputs throughout. -/
example {n b k : ℕ} {η : ℝ}
    (hk : 1 ≤ k) (hη : 1 ≤ 2 * (k : ℝ) * η) (hn : 2 ≤ n)
    (hb : (2048 * k ^ 2 : ℕ) * Real.log n ≤ (b : ℝ) * Real.log 2)
    (g : BitString b → BitString b → Bool) (f : (Fin n → Bool) → Bool)
    (hd : discrepancy (PMF.uniformOfFintype (BitString b × BitString b)) g ≤
      (2 : ℝ) ^ (-(η * b)))
    (p : Protocol (Fin n → BitString b) (Fin n → BitString b) Bool)
    (hp : ∀ x y, p.run x y = f (fun i => g (x i) (y i))) :
    ∃ t : DecisionTree (Fin n) Bool, (∀ z, t.eval z = f z) ∧
      t.depth * b ≤ 768 * k * p.depth :=
  exists_decisionTree_bitString_of_log_bound hk hη hn hb g hd (fun z o => o = f z) p hp

/-- A query lower bound transfers directly to minimum communication complexity,
without supplying any protocol or decision-tree witness. -/
example {n b k q : ℕ} {η : ℝ}
    (hk : 1 ≤ k) (hη : 1 ≤ 2 * (k : ℝ) * η) (hn : 2 ≤ n)
    (hb : (2048 * k ^ 2 : ℕ) * Real.log n ≤ (b : ℝ) * Real.log 2)
    (g : BitString b → BitString b → Bool) (f : (Fin n → Bool) → Bool)
    (hd : discrepancy (PMF.uniformOfFintype (BitString b × BitString b)) g ≤
      (2 : ℝ) ^ (-(η * b))) (hq : q ≤ DecisionTree.complexity f) :
    ((q * b : ℕ) : ℕ∞) ≤ (768 * k : ℕ∞) * Protocol.ecomplexityFun
      (fun x y : Fin n → BitString b => f (fun i => g (x i) (y i))) := by
  have h := complexity_mul_bits_le_ecomplexityFun hk hη hn hb g hd f
  apply le_trans ?_ h
  exact_mod_cast Nat.mul_le_mul_right b hq
