/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualPolicies
public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchOptimum
import Mathlib.Tactic

/-!
# Native residual token lower optimum on one common oracle

[Wang2027], Theorem 6, PDF pp. 12--13. The competitor class and accrued-bill
infimum are exactly `BatchOptimum.optimum`, used for Theorem 5. Specializing its
original input to the decoded residual construction identifies certified native
acceptance with original-label weight-one optimality. Arbitrary finite-control
native competitors use the same residual sampler and initial seed. Neither a
behavioral representation nor a cost lower bound is an admission premise.

This module proves the one- and two-turn lower optima. Native attainment,
equalities and the ratio are assembled downstream in `NativeResidualMinima`.
The price convention here identifies the
source prices with actual discrete per-opportunity invoices; arbitrary real
invoice encodings remain outside this wire model.

## Main results

* `accept_eq`: the actual native certificate test is source optimal-cover acceptance.
* `one_lower`, `two_lower`: residual lower bounds for the existing native token optima.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualOptimum
open Finset NativeRetention ResidualCover NativeResidualEncoding ConcurrentBatch
open NativeOpenExecution NativeBatch
open scoped ENNReal NNReal
variable {z n : ℕ} (T : Fin z → Block) (points : Fin n ≃ Point T)
variable (data : GuardedStartup.Input)
variable (candidates : Fin data.startup.system.rows.length ≃ Candidate T)

/-- The original runtime input's native certificate test is exactly optimal
cover acceptance under the source candidate labels. Its objective value one
follows from the residual construction, not an assumed optimum. -/
theorem accept_eq (hz : 0 < z) (hx : Valid data.startup.system)
    (hdata : data.startup.system = SourceEncoding.toNative (source T points candidates)) :
    BatchOutput.accept data.startup.system hx =
      NativeResidualPolicies.optimalAccept T candidates hz := by
  classical
  funext C
  have hI : instanceOf data.startup.system hx = nativeInstance T points candidates hz := by
    simp only [nativeInstance, ← hdata]
  have hlabels : (C.map candidates.toEmbedding).map (candidateLabel T candidates) =
      C.image Fin.val := by
    simp [candidateLabel, Finset.map_eq_image, Finset.image_image, Function.comp_def]
  have hground := ground_label T points candidates hz
  have hcost := cost_label T points candidates hz (C.map candidates.toEmbedding)
  have hcovered := covered_label T points candidates hz (C.map candidates.toEmbedding)
  rw [hlabels] at hcost hcovered
  have hcover : (instanceOf data.startup.system hx).covered (C.image Fin.val) =
      (instanceOf data.startup.system hx).ground ↔
      (coverInstance T hz).covered (C.map candidates.toEmbedding) =
        (coverInstance T hz).ground := by
    rw [hI, hcovered, hground]
    exact (Finset.map_injective (pointLabel T points)).eq_iff
  have hge (hc : (coverInstance T hz).covered (C.map candidates.toEmbedding) =
      (coverInstance T hz).ground) : 1 ≤ (coverInstance T hz).cost (C.map candidates.toEmbedding) :=
    (primal_optimum T hz).2.2 _ hc
  have hrho : data.startup.system.rho = 1 := by rw [hdata]; rfl
  simp only [BatchOutput.accept, hrho, Rat.cast_one, one_mul, hI,
    native_dual_objective, hcost, NativeResidualPolicies.optimalAccept, optimalOutput]
  congr 1
  apply propext
  rw [hI] at hcover
  constructor
  · rintro ⟨hc, hw⟩
    have hc' := hcover.mp hc
    have he := le_antisymm hw (hge hc')
    simp [hc', he]
  · intro h
    have hh : (coverInstance T hz).covered (C.map candidates.toEmbedding) =
        (coverInstance T hz).ground ∧
        (coverInstance T hz).cost (C.map candidates.toEmbedding) = 1 := by
      simpa only [ite_eq_left_iff, zero_ne_one, imp_false, not_not] using h
    exact ⟨by simpa only [hI] using hcover.mpr hh.1, hh.2.le⟩

private theorem optimal_event {k : ℕ} {Control : Type} {input : List Bool}
    (hz : 0 < z)
    (result : Option (World k Control Unit (ServerState (z + 1) Unit) input)) :
    Coverage.nativeSuccess (NativeResidualPolicies.optimalAccept T candidates hz) result =
      decide (optimalOutput hz
        (NativeResidualPolicies.terminalOutput T candidates result) = 1) := by
  cases result with
  | none => simp [Coverage.nativeSuccess, NativeResidualPolicies.terminalOutput,
      optimalOutput, PartialCover.Instance.cost]
  | some next =>
    cases hc : NativeOpenSelection.result
        (decodeFamily data.startup.system.rows.length) next with
    | none => simp [Coverage.nativeSuccess, NativeResidualPolicies.terminalOutput, hc,
        optimalOutput, PartialCover.Instance.cost]
    | some C => simp [Coverage.nativeSuccess, NativeResidualPolicies.terminalOutput, hc,
        NativeResidualPolicies.optimalAccept]

/-- Theorem 6's two-turn token lower optimum, over every admitted finite-control
selection-only native machine in the existing Theorem 5 common-oracle class.
The source deadline and actual bill are those of the same sampler and input.
No expected-cost, integrability, representation or optimality conclusion is a premise. -/
theorem two_lower (P : Parameters z) (limits : Limits (z + 1))
    (invoice : Fin (z + 1) → ℕ) (hz : 0 < z) (hx : Valid data.startup.system)
    (hdata : data.startup.system = SourceEncoding.toNative (source T points candidates))
    (ht : limits.turns = 2)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) :
    ENNReal.ofReal (min (∑ j, P.specialistCost j)
      (P.nearCost + P.missing.mean P.specialistCost)) ≤
      BatchOptimum.optimum limits (NativeResidualOracle.sample T points candidates P invoice)
        data () hx 1 := by
  apply le_sInf
  intro v hv
  obtain ⟨k, Control, hfinite, machine, hadmit, hsuccess, rfl⟩ := hv
  let world : World k Control Unit (ServerState (z + 1) Unit) (GuardedStartup.encoding data) :=
    ⟨machine.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial (), []⟩⟩
  have he := accept_eq T points data candidates hz hx hdata
  rw [he] at hadmit
  have hs := hsuccess.trans (BatchOptimum.certified_le_accepted limits data.startup.system hx
    (NativeUnboundedExecution.terminal machine
      (environment limits (NativeResidualOracle.sample T points candidates P invoice)) world))
  rw [he] at hs
  rw [show Coverage.nativeSuccess (NativeResidualPolicies.optimalAccept T candidates hz) =
    (fun result => decide (optimalOutput hz
      (NativeResidualPolicies.terminalOutput T candidates result) = 1)) from
        funext (optimal_event T data candidates hz)] at hs
  exact NativeResidualPolicies.native_two_lower T points candidates P limits invoice machine
    world (NativeBatch.initial_invariant limits ()) rfl ht hz hprice hadmit
      (le_antisymm (PMF.coe_le_one _ _) hs)

/-- Theorem 6's one-turn token lower optimum, over every admitted finite-control
selection-only native machine in the existing Theorem 5 common-oracle class.
The source deadline and actual bill are those of the same sampler and input.
No expected-cost, integrability, representation or optimality conclusion is a premise. -/
theorem one_lower (P : Parameters z) (limits : Limits (z + 1))
    (invoice : Fin (z + 1) → ℕ) (hz : 0 < z) (hx : Valid data.startup.system)
    (hdata : data.startup.system = SourceEncoding.toNative (source T points candidates))
    (ht : limits.turns = 1)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) :
    ENNReal.ofReal (∑ j, P.specialistCost j) ≤
      BatchOptimum.optimum limits (NativeResidualOracle.sample T points candidates P invoice)
        data () hx 1 := by
  apply le_sInf
  intro v hv
  obtain ⟨k, Control, hfinite, machine, hadmit, hsuccess, rfl⟩ := hv
  let world : World k Control Unit (ServerState (z + 1) Unit) (GuardedStartup.encoding data) :=
    ⟨machine.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial (), []⟩⟩
  have he := accept_eq T points data candidates hz hx hdata
  rw [he] at hadmit
  have hs := hsuccess.trans (BatchOptimum.certified_le_accepted limits data.startup.system hx
    (NativeUnboundedExecution.terminal machine
      (environment limits (NativeResidualOracle.sample T points candidates P invoice)) world))
  rw [he] at hs
  rw [show Coverage.nativeSuccess (NativeResidualPolicies.optimalAccept T candidates hz) =
    (fun result => decide (optimalOutput hz
      (NativeResidualPolicies.terminalOutput T candidates result) = 1)) from
        funext (optimal_event T data candidates hz)] at hs
  exact NativeResidualPolicies.native_one_lower T points candidates P limits invoice machine
    world (NativeBatch.initial_invariant limits ()) rfl ht hz hprice hadmit
      (le_antisymm (PMF.coe_le_one _ _) hs)

end Cslib.Probability.StochasticOracle.NativeResidualOptimum
