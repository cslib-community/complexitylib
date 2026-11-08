/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import CslibFrontierAbstracts.Check
import CslibFrontier.Computability.Communication.Disjointness
import CslibFrontier.Computability.Communication.Discrepancy

/-! # Transfer of communication lower bounds to individual protocols

The abstract uses the elementary deterministic protocol tree, but defines its own tree-depth
bound and per-input error conditions. No communication-complexity infimum occurs in its statements.
-/

namespace ComplexityAbstracts.CommunicationBridge

open Cslib.Communication

theorem equality {n c : ℕ} (hn : 0 < n) :
    (∃ p : Protocol (Fin n → Bool) (Fin n → Bool) Bool,
      (∀ x y, p.run x y = decide (x = y)) ∧ p.depth ≤ c) ↔ n + 1 ≤ c := by
  have h := Protocol.ecomplexityFun_le_iff
    (f := fun x y : Fin n → Bool => decide (x = y)) (k := c)
  rw [show Protocol.ecomplexityFun (fun x y : Fin n → Bool => decide (x = y)) = n + 1 from
    ecomplexity_equality hn] at h
  norm_cast at h
  simpa only [funext_iff] using h.symm

/-- Convert the public cost and error conditions to the library's infimum bound. -/
theorem complexity_le {n c : ℕ}
    (μ : PMF (Protocol (Fin n → Bool) (Fin n → Bool) Bool))
    (f : (Fin n → Bool) → (Fin n → Bool) → Bool)
    (hc : ∀ p ∈ μ.support, p.depth ≤ c)
    (he : ∀ x y, (μ.toOuterMeasure {p | p.run x y ≠ f x y}).toReal ≤ (1 : ℝ) / 3) :
    PublicCoin.ecomplexityFun (1 / 3) f ≤ c := by
  apply (PublicCoin.ecomplexity_le_depth (μ := μ) ?_).trans
    (PublicCoin.depth_le_iff.mpr fun p hp => by exact_mod_cast hc p hp)
  intro x _ y _
  simpa only [PublicCoin.errorProb, ne_comm] using he x y

theorem disjointness {n c : ℕ}
    (μ : PMF (Protocol (Fin n → Bool) (Fin n → Bool) Bool))
    (hc : ∀ p ∈ μ.support, p.depth ≤ c)
    (he : ∀ x y, (μ.toOuterMeasure
      {p | p.run x y ≠ decide (∀ i, (x i && y i) = false)}).toReal ≤ (1 : ℝ) / 3) :
    n ≤ 2 ^ 16 * c + 2 ^ 12 := by
  have h := PublicCoin.le_mul_ecomplexityFun_disjointness_add n
  have hf : Cslib.Communication.disjointness =
      (fun x y : Fin n → Bool => decide (∀ i, (x i && y i) = false)) := by
    funext x y
    simp only [Cslib.Communication.disjointness, decide_eq_decide]
  rw [hf] at h
  have hcost := complexity_le μ _ hc he
  have hbound : (n : ℕ∞) ≤ 2 ^ 16 * (c : ℕ∞) + 2 ^ 12 :=
    h.trans (by gcongr)
  exact_mod_cast hbound

theorem innerProduct {n c : ℕ}
    (μ : PMF (Protocol (Fin n → Bool) (Fin n → Bool) Bool))
    (hc : ∀ p ∈ μ.support, p.depth ≤ c)
    (he : ∀ x y, (μ.toOuterMeasure {p | p.run x y ≠ x ⬝ᵥ y}).toReal ≤ (1 : ℝ) / 3) :
    n ≤ 2 * c + 3 := by
  have h := PublicCoin.le_two_mul_ecomplexityFun_dotProduct_add_three n
  have hcost := complexity_le μ (fun x y => x ⬝ᵥ y) hc he
  have hbound : (n : ℕ∞) ≤ 2 * (c : ℕ∞) + 3 := h.trans (by gcongr)
  exact_mod_cast hbound

end ComplexityAbstracts.CommunicationBridge
