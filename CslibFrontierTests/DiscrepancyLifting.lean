/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module

import CslibFrontier.Computability.Communication.Discrepancy.Extractor
import CslibFrontier.Computability.Communication.Discrepancy.Xor
import CslibFrontier.Computability.Communication.Lifting.FullRange
import CslibFrontier.Foundations.Combinatorics.Subsets.Geometric

/-! Regression clients for the ingredients of low-discrepancy lifting. -/

open Cslib Cslib.Communication Cslib.BitString Cslib.Probability Finset

namespace DiscrepancyLiftingTests

/-- Uniform parity biases certify exact atom masses, including the empty cube. -/
example (n : ℕ) (z : Fin n → Bool) :
    |2 ^ n * ((PMF.uniformOfFintype (Fin n → Bool)) z).toReal - 1| ≤ 0 := by
  have h := abs_mul_mass_sub_one_le_of_bias_le (ι := Fin n)
    (PMF.uniformOfFintype (Fin n → Bool)) (ε := 0) (by norm_num)
    (fun S hS => by simp [bias_uniformOfFintype, hS.ne_empty]) z
  simpa only [Fintype.card_fin] using h

/-- A point mass has maximal singleton bias. -/
example : bias (PMF.pure (fun _ : Fin 1 => false)) {0} = 1 := by
  simp [chi]

/-- The subset-weight bound applies to a two-coordinate example. -/
example : (∑ S ∈ (univ : Finset (Fin 2)).powerset.filter Finset.Nonempty,
    (1 / 4 : ℝ) ^ S.card) ≤ 1 := by
  apply sum_nonempty_powerset_pow_card_le_one <;> norm_num

/-- Independent deterministic inputs can leave a gadget completely biased. -/
example : |∑ x : Bool, ∑ y : Bool,
    ((PMF.pure false) x).toReal * ((PMF.pure false) y).toReal *
      signVal (x ^^ y)| = 1 := by
  simp

/-- The XOR product computes the parity of coordinatewise AND outputs. -/
example : NOF.xorProduct (κ := Fin 2) (fun v : Fin 2 → Bool => v 0 && v 1)
    ![![true, false], ![true, true]] = true := by
  simp [NOF.xorProduct, Fin.sum_univ_two, show (0 : Bool) = false from rfl]

/-- Empty output coordinates still give a supported preimage. -/
example (z : Fin 0 → Bool) :
    ∃ x ∈ (PMF.pure false).support, ∃ y ∈ (PMF.pure true).support,
      (fun _ : Fin 0 => x && y) = z := by
  apply Lifting.exists_pair_of_parity_bias_le (PMF.pure false) (PMF.pure true)
    (fun x y _ => x && y) (ε := 0) (by norm_num) (by norm_num)
  intro S hS
  obtain ⟨i, _⟩ := hS
  exact Fin.elim0 i

/-- The public XOR estimate specializes directly to Boolean gadgets. -/
example (g : Bool → Bool → Bool) :
    discrepancy (PMF.uniformOfFintype ((Fin 2 → Bool) × (Fin 2 → Bool)))
      (fun x y => ∑ i, g (x i) (y i)) ^ 4 ≤
        (4 * discrepancy (PMF.uniformOfFintype (Bool × Bool)) g) ^ 2 := by
  simpa using discrepancy_xor_fourth_pow_le (κ := Fin 2) g

/-- A caller can retain the strict sampling conclusion in entropy parameters. -/
example (p q : PMF Bool) (g : Bool → Bool → Bool) (η γ lam : ℝ)
    (hd : discrepancy (PMF.uniformOfFintype (Bool × Bool)) g ≤ 2 ^ (-η * 1))
    (he : (2 - η + γ + lam) * 1 + 1 ≤ PMF.minEntropy p + PMF.minEntropy q) :
    (∑ x with 2 ^ (-lam * 1) < |∑ y, (q y).toReal * signVal (g x y)|,
      (p x).toReal) < 2 ^ (-γ * 1) := by
  simpa only [Nat.cast_one] using
    sum_mass_filter_rowBias_lt_rpow_of_minEntropy p q g (b := 1) (η := η) (γ := γ) (lam := lam)
      (by decide) (by simpa only [Nat.cast_one] using hd)
      (by simpa only [Nat.cast_one] using he)

end DiscrepancyLiftingTests
