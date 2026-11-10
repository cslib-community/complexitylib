/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.Lattice.Periodization
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Lattice periodization of Schwartz functions

## Main results

* `SchwartzMap.summable_norm_restrict_translate`: local normal convergence on any discrete lattice.
* `SchwartzMap.continuous_tsum_translate`: continuity of the actual lattice sum.
* `SchwartzMap.continuous_automorphize`: continuity on the lattice quotient.

## References

The lattice need not have full rank. These results supply the continuous periodized function
needed for Fourier analysis on a lattice quotient; they do not identify its Fourier coefficients.
-/

public section

noncomputable section

open Filter TopologicalSpace
open scoped SchwartzMap Topology

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (f : 𝓢(E, F)) (L : Submodule ℤ E) [DiscreteTopology L]

/-- Schwartz decay gives summable sup norms of lattice translates on each compact set. -/
theorem summable_norm_restrict_translate (K : Compacts E) :
    Summable (fun z : L ↦ ‖(f.toContinuousMap.comp
      (ContinuousMap.addRight (z : E))).restrict K‖) :=
  ZLattice.summable_norm_restrict_translate L f.toContinuousMap
    (b := (Module.finrank ℤ L : ℝ) + 1) (by linarith)
    (f.isBigO_cocompact_rpow _) K

/-- The lattice sum of a Schwartz function is continuous. -/
theorem continuous_tsum_translate [CompleteSpace F] :
    Continuous (fun x : E ↦ ∑' z : L, f (x + z)) :=
  ZLattice.continuous_tsum_translate L f.toContinuousMap
    (b := (Module.finrank ℤ L : ℝ) + 1) (by linarith)
    (f.isBigO_cocompact_rpow _)

/-- The canonical quotient periodization of a Schwartz function is continuous. -/
theorem continuous_automorphize [CompleteSpace F] :
    Continuous (QuotientAddGroup.automorphize f : E ⧸ L.toAddSubgroup → F) :=
  ZLattice.continuous_automorphize L f.toContinuousMap
    (b := (Module.finrank ℤ L : ℝ) + 1) (by linarith)
    (f.isBigO_cocompact_rpow _)

end SchwartzMap
