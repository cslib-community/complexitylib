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
  have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hBp : (0 : ℝ) < B := by linarith
  obtain ⟨hgap, hratio, hu, hsize, hq, hweight, hd⟩ :=
    polynomial_parameter_certificate (N := (n : ℝ)) hBR (by exact_mod_cast hn)
      (by exact_mod_cast hnB) hdisc
  apply densityOracles_of_discrepancy g (r := 16) (u := (B : ℝ) ^ 129)
    (q := 1 / (4 * (B : ℝ) ^ 131)) (by positivity) (by positivity) hn (by norm_num)
    hgap hratio hu _ hq _ _
  · simpa only [Nat.cast_mul, Nat.cast_pow] using hsize
  · simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hweight
  · simpa only [Nat.cast_pow] using hd

end Cslib.Communication.Lifting
