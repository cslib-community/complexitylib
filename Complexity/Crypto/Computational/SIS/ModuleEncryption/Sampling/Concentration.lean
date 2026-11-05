/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.LWE
public import Complexity.Crypto.Computational.SIS.Module
public import Complexity.Languages.Probabilistic.CenteredBinomial.Concentration
public import Complexity.Probability.Product.Event

/-!
# Centered-binomial polynomial noise tails

The existing scalar modular law is sampled independently at each coefficient. Under the
strict no-wrap margin, its centered lift is the sampled integer. The scalar sampler tail
and coordinate union bound then bound the actual polynomial noise law. This is original
supporting probability algebra, with no encryption correctness or security conclusion.

## Main results

* `toOuterMeasure_moduleLWECBD_noise_tail_le`: the coefficient union bound.
-/

public section

namespace Cslib.Crypto

open Probability ProbComp
open scoped ENNReal

/-- A polynomial noise draw pays one scalar tail for each coefficient, with the strict
no-wrap margin identifying the centered integer lift of every supported scalar draw. -/
theorem toOuterMeasure_moduleLWECBD_noise_tail_le {n w η B : ℕ}
    (hη : 0 < η) (hwrap : 2 * η < 2 ^ w) :
    (PMF.pi (fun _ : Fin n => Homomorphic.GSW.noiseLaw w η)).toOuterMeasure
      {e | ¬ GeneralSIS.inInfNormBound B e} ≤
        n * ENNReal.ofReal (4 * Real.exp (-(B : ℝ) ^ 2 / (2 * η))) := by
  have hscalar : (Homomorphic.GSW.noiseLaw w η).toOuterMeasure
      {z | (B : ℤ) < |z.valMinAbs|} ≤
        ENNReal.ofReal (4 * Real.exp (-(B : ℝ) ^ 2 / (2 * η))) := by
    rw [Homomorphic.GSW.noiseLaw, PMF.toOuterMeasure_map_apply]
    refine (PMF.toOuterMeasure_mono _ ?_).trans
      (sampleCenteredBinomial_strict_tail_le hη (Nat.cast_nonneg B))
    intro z hz
    have hb := (mem_support_sampleCenteredBinomial_iff η z).mp hz.2
    have hlift : (z : ZMod (2 ^ w)).valMinAbs = z := by
      rw [ZMod.valMinAbs_spec]
      exact ⟨rfl, by omega, by omega⟩
    have hbad : (B : ℤ) < |z| := by simpa only [Set.mem_preimage, Set.mem_ofPred_eq,
      hlift] using hz.1
    exact_mod_cast hbad
  calc
    _ ≤ ∑ _i : Fin n, (Homomorphic.GSW.noiseLaw w η).toOuterMeasure
        {z | (B : ℤ) < |z.valMinAbs|} := by
      simpa only [GeneralSIS.inInfNormBound, not_forall, not_le, Set.mem_ofPred_eq] using
        PMF.toOuterMeasure_pi_exists_le
          (fun _ : Fin n => Homomorphic.GSW.noiseLaw w η)
          (fun _ => {z | (B : ℤ) < |z.valMinAbs|})
    _ ≤ ∑ _i : Fin n, ENNReal.ofReal
        (4 * Real.exp (-(B : ℝ) ^ 2 / (2 * η))) :=
      Finset.sum_le_sum (fun _ _ => hscalar)
    _ = _ := by simp

end Cslib.Crypto
