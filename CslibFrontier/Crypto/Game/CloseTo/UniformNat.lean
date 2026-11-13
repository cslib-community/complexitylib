/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Statistical
public import CslibFrontier.Probability.StatisticalDistance.TotalVariation
public import CslibFrontier.Languages.Probabilistic.UniformNat

/-!
# All-event approximation for bounded modular sampling

The existing finite statistical-distance bound for `ProbComp.sampleModNat` also controls
all events after arbitrary postprocessing. The sampler remains the existing bounded fair-bit
program; no exact uniform sampler for arbitrary moduli is asserted.

## Main results

* `closeTo_uniform_sampleModNat`: uniform residues are close to the actual sampled residues.
* `Cslib.Crypto.Game.advantage_bind_sampleModNat_fin_le`: replacing a uniform draw on `Fin M` by
  `ProbComp.sampleModNat width M` changes the advantage of any continuation by at most
  `M / 2 ^ width`.
* `Cslib.Crypto.Game.advantage_bind_sampleModNat_fin_fin_le`: the same for two successive draws,
  with bound `(M + N) / 2 ^ width`.
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

namespace Cslib.Crypto

open ProbComp Probability
open scoped NNReal Cslib.Probability.PMF

/-- Replacing an exact uniform draw on `Fin M` by `ProbComp.sampleModNat width M` changes
`Game.advantage` of any Boolean continuation by at most `(M : ℝ≥0) / 2 ^ width`. -/
theorem Game.advantage_bind_sampleModNat_fin_le (width M : ℕ) [NeZero M] (k : ℕ → Game) :
    Game.advantage
      ((ProbComp.eval (sampleModNat width M)).bind k)
      ((PMF.uniformOfFintype (Fin M)).bind fun i => k i.val) ≤
      (M : ℝ≥0) / 2 ^ width := by
  have hmod :
      (ProbComp.eval (sampleModNat width M)).bind k =
        ((ProbComp.eval (sampleModNat width M)).map (Nat.cast : ℕ → ZMod M)).bind
          (fun r : ZMod M => k r.val) := by
    rw [PMF.bind_map, eval_sampleModNat, PMF.bind_map, PMF.bind_map]
    congr 1 with x : 1
    simp only [Function.comp_def, ZMod.val_natCast,
      Nat.mod_eq_of_lt (Nat.mod_lt x.val (NeZero.pos M))]
  rw [← NNReal.coe_le_coe, hmod, Probability.PMF.uniformOfFintype_fin_bind,
    Game.advantage_eq_nndist, coe_nndist]
  exact (PMF.dist_bind_le
    ((ProbComp.eval (sampleModNat width M)).map (Nat.cast : ℕ → ZMod M))
    (PMF.uniformOfFintype (ZMod M)) (fun r : ZMod M => k r.val)).trans
    (by simpa only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat] using
      ProbComp.dist_map_natCast_eval_sampleModNat_le width M)

/-- Replacing exact uniform draws on `Fin M` and then `Fin N` by two `sampleModNat width` draws
changes `Game.advantage` of any Boolean continuation by at most `(M + N) / 2 ^ width`. -/
theorem Game.advantage_bind_sampleModNat_fin_fin_le (width M N : ℕ) [NeZero M] [NeZero N]
    (k : ℕ → ℕ → Game) :
    Game.advantage
      ((ProbComp.eval (sampleModNat width M)).bind fun i =>
        (ProbComp.eval (sampleModNat width N)).bind fun j => k i j)
      ((PMF.uniformOfFintype (Fin M)).bind fun i =>
        (PMF.uniformOfFintype (Fin N)).bind fun j => k i.val j.val) ≤
      ((M + N : ℕ) : ℝ≥0) / 2 ^ width := by
  refine (Game.advantage_triangle _ ((PMF.uniformOfFintype (Fin M)).bind fun i =>
      (ProbComp.eval (sampleModNat width N)).bind fun j => k i.val j) _).trans ?_
  rw [Nat.cast_add, add_div]
  exact add_le_add
    (advantage_bind_sampleModNat_fin_le width M fun i =>
      (ProbComp.eval (sampleModNat width N)).bind fun j => k i j)
    (Game.advantage_bind_le_nnreal _ _ _ fun i =>
      advantage_bind_sampleModNat_fin_le width N fun j => k i.val j)

end Cslib.Crypto
