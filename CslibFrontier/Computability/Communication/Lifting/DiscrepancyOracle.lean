/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.DensityOracle
public import CslibFrontier.Computability.Communication.Lifting.RareDanger
public import CslibFrontier.Computability.Communication.Discrepancy.Symmetry
public import CslibFrontier.Computability.Communication.Lifting.ParameterSpecialization

/-!
# Local simulation guarantees from discrepancy

The finite dangerous-values theorem supplies both fields of `DensityOracle`: a density-preserving
step and a terminal preimage for every residual output. Uniform discrepancy is symmetric, so the
same numerical assumptions provide the guarantees in both speaker orientations.
-/

public section

namespace Cslib.Communication.Lifting

open Probability

variable {n m : ℕ}

/-- Numerical density/counting conditions and a single-gadget discrepancy bound give the local
step and full-range guarantees required by the recursive density simulator. -/
theorem densityOracle_of_discrepancy [NeZero m]
    (g : Fin m → Fin m → Bool) {τ σ u q : ℝ} {r : ℕ}
    (hτ : 0 < τ) (hσ : 0 < σ) (hn : 2 ≤ n) (hr : 0 < r)
    (hgap : 16 * (n : ℝ) ^ 2 ≤ τ / σ)
    (hratio : (n : ℝ) ^ (2 * r) ≤ τ / σ)
    (hu : 1 ≤ u) (hsize : ((n * m : ℕ) : ℝ) ≤ u ^ r) (hq : 0 < q)
    (hweight : n * (((n + 1 : ℕ) : ℝ) * u * q) ≤ 1 / 2)
    (hdisc : 16384 * ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 / (σ * τ)) ^ 4 *
      discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g ≤ (q / (2 * n)) ^ 4) :
    DensityOracle (n := n) g τ σ where
  step _F _X _Y hXne hYne hX hY send :=
    exists_densityStep_of_discrepancy g hX hY hσ hτ hσ hXne hYne hn hr
      hgap hratio hu hsize hq hweight hdisc send
  full _F _X _Y hXne hYne hX hY answer :=
    exists_pair_of_discrepancy g hX hY hσ hτ hσ hXne hYne hn hr
      hgap hratio hu hsize hq hweight hdisc answer

/-- The same numerical assumptions give simulation guarantees with either player speaking.
The swapped gadget has exactly the same uniform discrepancy. -/
theorem densityOracles_of_discrepancy [NeZero m]
    (g : Fin m → Fin m → Bool) {τ σ u q : ℝ} {r : ℕ}
    (hτ : 0 < τ) (hσ : 0 < σ) (hn : 2 ≤ n) (hr : 0 < r)
    (hgap : 16 * (n : ℝ) ^ 2 ≤ τ / σ)
    (hratio : (n : ℝ) ^ (2 * r) ≤ τ / σ)
    (hu : 1 ≤ u) (hsize : ((n * m : ℕ) : ℝ) ≤ u ^ r) (hq : 0 < q)
    (hweight : n * (((n + 1 : ℕ) : ℝ) * u * q) ≤ 1 / 2)
    (hdisc : 16384 * ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 / (σ * τ)) ^ 4 *
      discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g ≤ (q / (2 * n)) ^ 4) :
    DensityOracle (n := n) g τ σ ∧ DensityOracle (n := n) (fun y x => g x y) τ σ := by
  refine ⟨densityOracle_of_discrepancy g hτ hσ hn hr hgap hratio hu hsize hq hweight hdisc, ?_⟩
  apply densityOracle_of_discrepancy (fun y x => g x y) hτ hσ hn hr hgap hratio hu hsize hq hweight
  simpa only [discrepancy_uniform_flip] using hdisc

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

private instance polynomialAlphabet_neZero {B : ℕ} [NeZero B] : NeZero (B ^ 2048) :=
  ⟨pow_ne_zero _ (NeZero.ne B)⟩

-- Avoid the Lean exponent-warning path during dependency analysis of the alphabet type.
set_option exponentiation.threshold 2048 in
/-- A concrete polynomial-size alphabet supplies both speaker orientations. The gadget's
uniform discrepancy is at most the inverse square root of the alphabet size; the exponent
`2048` is a deliberately loose consequence of the elementary XOR estimate. -/
theorem densityOracles_polynomial {B : ℕ} [NeZero B]
    (g : Fin (B ^ 2048) → Fin (B ^ 2048) → Bool)
    (hB : 2 ≤ B) (hn : 2 ≤ n) (hnB : n ≤ B)
    (hdisc : discrepancy (PMF.uniformOfFintype (Fin (B ^ 2048) × Fin (B ^ 2048))) g ≤
      ((B : ℝ) ^ 1024)⁻¹) :
    DensityOracle (n := n) g ((B : ℝ) ^ 2016) ((B : ℝ) ^ 1984) ∧
      DensityOracle (n := n) (fun y x => g x y) ((B : ℝ) ^ 2016) ((B : ℝ) ^ 1984) := by
  exact densityOracles_parameter g (k := 1) (a := 1984) (B := (B : ℝ))
    (by decide) (by decide)
    (by exact_mod_cast hB) hn (by exact_mod_cast hnB)
    (by simp only [one_pow, Nat.mul_one, Nat.cast_pow]) hdisc

end Cslib.Communication.Lifting
