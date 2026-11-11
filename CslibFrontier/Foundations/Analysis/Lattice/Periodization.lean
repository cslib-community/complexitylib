/-
Copyright (c) 2026 David Loeffler, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.Group.Quotient

import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Normal convergence of lattice periodization

A continuous function with polynomial decay of exponent greater than the lattice rank has
summable sup norms of its lattice translates on each compact set. Its lattice sum therefore
converges locally uniformly to a continuous function. The lattice need not span the ambient space.

## Main results

* `ZLattice.summable_norm_restrict_translate`: local normal convergence from polynomial decay.
* `ZLattice.continuous_tsum_translate`: continuity of the lattice sum.
* `ZLattice.continuous_automorphize`: continuity of the existing quotient periodization.

## References

The compact-translate estimate generalizes the one-dimensional argument in Mathlib's
`isBigO_norm_restrict_cocompact` (David Loeffler). This is a convergence prerequisite
for Poisson summation; it does not identify Fourier coefficients or prove Poisson summation.
-/

public section

noncomputable section

open Asymptotics Filter TopologicalSpace
open scoped Topology

namespace ContinuousMap

variable {E F : Type*} [NormedAddCommGroup E] [ProperSpace E] [NormedAddCommGroup F]

/-- Polynomial decay is uniform under translations by points in a fixed compact set. -/
theorem isBigO_norm_restrict_add_cocompact (f : C(E, F)) {b : ℝ} (hb : 0 < b)
    (hf : f =O[cocompact E] (fun x ↦ ‖x‖ ^ (-b))) (K : Compacts E) :
    (fun z : E ↦ ‖(f.comp (ContinuousMap.addRight z)).restrict K‖) =O[cocompact E]
      (fun z ↦ ‖z‖ ^ (-b)) := by
  obtain ⟨C, hC, hbound⟩ := hf.exists_pos
  obtain ⟨R, hR⟩ := Metric.closedBall_compl_subset_of_mem_cocompact hbound.bound (0 : E)
  obtain ⟨S, hS⟩ := K.isCompact.isBounded.subset_closedBall (0 : E)
  refine IsBigO.of_bound (C * (2 : ℝ) ^ b) ?_
  filter_upwards [tendsto_norm_cocompact_atTop.eventually
    (eventually_gt_atTop (max (2 * S) (max (2 * R) 0)))] with z hz
  have hzS : 2 * S < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  have hzR : 2 * R < ‖z‖ := lt_of_le_of_lt
    ((le_max_left _ _).trans (le_max_right _ _)) hz
  have hz0 : 0 < ‖z‖ := lt_of_le_of_lt
    ((le_max_right _ _).trans (le_max_right _ _)) hz
  rw [norm_norm, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  apply (norm_le _ (by positivity)).2
  intro x
  have hx : ‖(x : E)‖ ≤ S := by simpa using hS x.property
  have hhalf : ‖z‖ / 2 ≤ ‖(x : E) + z‖ := by
    have := norm_add_le ((x : E) + z) (-(x : E))
    rw [add_neg_cancel_comm, norm_neg] at this
    linarith
  have hdecay : ‖f ((x : E) + z)‖ ≤ C * ‖(x : E) + z‖ ^ (-b) := by
    have hxR : (x : E) + z ∈ (Metric.closedBall (0 : E) R)ᶜ := by
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
      linarith
    simpa only [Set.mem_ofPred_eq, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      using hR hxR
  change ‖f ((x : E) + z)‖ ≤ _
  calc
    _ ≤ C * ‖(x : E) + z‖ ^ (-b) := hdecay
    _ ≤ C * (‖z‖ / 2) ^ (-b) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (neg_nonpos.mpr hb.le)) hC.le
    _ = C * 2 ^ b * ‖z‖ ^ (-b) := by
      rw [Real.div_rpow (norm_nonneg _) (by positivity), Real.rpow_neg (by positivity),
        Real.rpow_neg (by positivity), div_inv_eq_mul]
      ring

end ContinuousMap

namespace ZLattice

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [NormedAddCommGroup F]
variable (L : Submodule ℤ E) [DiscreteTopology L]

/-- The sup norms of the lattice translates are summable on every compact set when the
polynomial decay exponent exceeds the integer rank of the lattice. -/
theorem summable_norm_restrict_translate (f : C(E, F)) {b : ℝ}
    (hb : (Module.finrank ℤ L : ℝ) < b)
    (hf : f =O[cocompact E] (fun x ↦ ‖x‖ ^ (-b))) (K : Compacts E) :
    Summable (fun z : L ↦ ‖(f.comp (ContinuousMap.addRight (z : E))).restrict K‖) := by
  have hclosed : IsClosed (L : Set E) := L.toAddSubgroup.isClosed_of_discreteTopology
  have ht : Tendsto ((↑) : L → E) cofinite (cocompact E) :=
    tendsto_cofinite_cocompact_of_discrete hclosed.isClosedEmbedding_subtypeVal.tendsto_cocompact
  exact summable_of_isBigO (summable_norm_rpow L (-b) (by linarith))
    ((f.isBigO_norm_restrict_add_cocompact
      (lt_of_le_of_lt (Nat.cast_nonneg _) hb) hf K).comp_tendsto ht)

variable [CompleteSpace F]

/-- The lattice translates are summable in the compact-open topology, hence their partial
sums converge locally uniformly. -/
theorem summable_translate (f : C(E, F)) {b : ℝ}
    (hb : (Module.finrank ℤ L : ℝ) < b)
    (hf : f =O[cocompact E] (fun x ↦ ‖x‖ ^ (-b))) :
    Summable (fun z : L ↦ f.comp (ContinuousMap.addRight (z : E))) :=
  ContinuousMap.summable_of_locally_summable_norm
    (summable_norm_restrict_translate L f hb hf)

/-- Periodization of a sufficiently rapidly decaying continuous function is continuous. -/
theorem continuous_tsum_translate (f : C(E, F)) {b : ℝ}
    (hb : (Module.finrank ℤ L : ℝ) < b)
    (hf : f =O[cocompact E] (fun x ↦ ‖x‖ ^ (-b))) :
    Continuous (fun x : E ↦ ∑' z : L, f (x + z)) := by
  have hs := summable_translate L f hb hf
  have heq : (fun x : E ↦ ∑' z : L, f (x + z)) =
      ⇑(∑' z : L, f.comp (ContinuousMap.addRight (z : E))) := by
    funext x
    exact ContinuousMap.tsum_apply hs x
  rw [heq]
  exact ContinuousMap.continuous _

/-- The canonical periodization on the lattice quotient is continuous. -/
theorem continuous_automorphize (f : C(E, F)) {b : ℝ}
    (hb : (Module.finrank ℤ L : ℝ) < b)
    (hf : f =O[cocompact E] (fun x ↦ ‖x‖ ^ (-b))) :
    Continuous (QuotientAddGroup.automorphize f : E ⧸ L.toAddSubgroup → F) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  change Continuous (fun x : E ↦ ∑' z : L.toAddSubgroup.op, f (z +ᵥ x))
  have heq : (fun x : E ↦ ∑' z : L.toAddSubgroup.op, f (z +ᵥ x)) =
      (fun x : E ↦ ∑' z : L, f (x + z)) := by
    funext x
    exact (L.toAddSubgroup.equivOp.tsum_eq (fun z ↦ f (z +ᵥ x))).symm
  rw [heq]
  exact continuous_tsum_translate L f hb hf

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L] [CompleteSpace F] in
/-- Lattice periodization is invariant under every lattice translation. This reindexing
identity holds even without convergence; the convergence theorems above ensure a genuine sum. -/
theorem periodic_tsum_translate (f : E → F) (a : L) :
    Function.Periodic (fun x : E ↦ ∑' z : L, f (x + z)) (a : E) := by
  intro x
  simpa only [Equiv.coe_addLeft, Submodule.coe_add, add_assoc] using
    (Equiv.addLeft a).tsum_eq (fun z : L ↦ f (x + z))

end ZLattice
