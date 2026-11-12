/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StatisticalDistance.TotalVariation
public import CslibFrontier.Languages.Probabilistic.UniformNat

/-!
# All-event approximation for bounded modular sampling

The existing finite statistical-distance bound for `ProbComp.sampleModNat` also controls
all events after arbitrary postprocessing. The sampler remains the existing bounded fair-bit
program; no exact uniform sampler for arbitrary moduli is asserted.

## Main results

* `closeTo_uniform_sampleModNat`: uniform residues are close to the actual sampled residues.
-/

public section

namespace Cslib.Probability

open scoped ENNReal NNReal Cslib.Probability.PMF

/-- `sampleModNat width q` read in `ZMod q` is within `q / 2 ^ width` of uniform in `CloseTo`. -/
theorem closeTo_uniform_sampleModNat (width q : ℕ) [NeZero q] :
    CloseTo (PMF.uniformOfFintype (ZMod q))
      ((ProbComp.eval (ProbComp.sampleModNat width q)).map (Nat.cast : ℕ → ZMod q))
      ((q : ℝ≥0∞) / 2 ^ width) := by
  have hd := ProbComp.dist_map_natCast_eval_sampleModNat_le width q
  rw [dist_comm] at hd
  have hc := closeTo_of_dist_le (ε := (q : ℝ≥0) / 2 ^ width) hd
  rwa [ENNReal.coe_div (pow_ne_zero _ two_ne_zero), ENNReal.coe_natCast, ENNReal.coe_pow,
    ENNReal.coe_ofNat] at hc

end Cslib.Probability
