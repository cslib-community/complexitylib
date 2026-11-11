/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyChildRootMoment
public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyEstimatedInput
public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.SecondSignal

/-!
# Shared finite context for reserve-output bounds

`ReserveOutputContext` records the finite instance, routing and cutoff conditions used by both
reserve-output theorems. `ReserveOutputChildren` records the raw, preparation and maximum
families. Their named constructions define the same finite allocation, full-terminal raw walk,
selected preparation, usage-terminal preparation walk and two-signal increment as the explicit
assembly in `ReserveOutput`.

These objects are quantified after the output constant: the constant depends only on the fixed
hierarchy, ζ, scale and positive floor, before the prime, environment width, finite horizon or
child families. The allocation and walk lengths still depend on the finite instance. This
maintenance extraction adds no recursive accuracy, copy routing, parameter/workspace bound or
RL=L result. The underlying row/normalization assembly is adapted from Samuel Schlesinger.

## Main definitions

* `ReserveOutputContext`: finite geometric and cutoff data with the hypotheses of the existing
  reserve-output bounds.
* `ReserveOutputChildren`: independently supplied raw, preparation and maximum families.
* `ReserveOutputContext.rawSteps`, `ReserveOutputContext.prepSteps`: the explicit spectral walk
  allocations; `amplification` and `tolerance` display their width/rate and horizon losses.
* `ReserveOutputContext.rawWalk`, `ReserveOutputContext.prepWalk`,
  `ReserveOutputContext.increment`: the two actual walks and their compression signal.
* `ReserveOutputContext.cost`: the conditional lower-child cost reserved by `ReserveOutput`.

The constructions are reducible abbreviations so applications of the existing component lemmas
retain exactly the unbundled terms, without compatibility wrappers or additional hypotheses.
-/

public section
noncomputable section

namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments

open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Finite instance and hypotheses shared by the two reserve-output theorems.
This record is supplied only after the uniform output coefficient has been chosen. -/
structure ReserveOutputContext (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (P J : ℕ) [Fact P.Prime] where
  /-- Nonzero direction used by the retained grids. -/
  direction : ZMod P
  /-- The grid direction is nonzero. -/
  direction_ne_zero : direction ≠ 0
  /-- Admissible finite exponent and identifier horizon. -/
  horizon : Horizon P
  /-- Distinct source, midpoint and terminal roles. -/
  roles : RoleProfile J
  /-- Hierarchy request level. -/
  level : ℕ
  /-- Source grid-rate exponent. -/
  sourceExponent : ℕ
  /-- Midpoint grid-rate exponent. -/
  midpointExponent : ℕ
  /-- Full terminal-rank exponent. -/
  terminalExponent : ℕ
  /-- Last bin index; active bins are `range (lastBin + 1)`. -/
  lastBin : ℕ
  /-- The source grid lies in the admitted horizon. -/
  source_in_horizon : sourceExponent ≤ horizon.maxExponent
  /-- The midpoint exponent does not exceed the source exponent. -/
  midpoint_le_source : midpointExponent ≤ sourceExponent
  /-- Source copy-identifier suffix. -/
  sourceSuffix : List (ZMod P)
  /-- Midpoint copy-identifier suffix. -/
  midpointSuffix : List (ZMod P)
  /-- Terminal copy-identifier suffix. -/
  terminalSuffix : List (ZMod P)
  /-- Rate exponent of each bin. -/
  binExponent : ℕ → ℕ
  /-- Every active bin lies in the admitted horizon. -/
  bins_in_horizon : ∀ i ∈ range (lastBin + 1), binExponent i ≤ horizon.maxExponent
  /-- Nonnegative substochastic kernel whose canonical residual is estimated. -/
  kernel : Matrix (ZMod P) (ZMod P) ℝ
  /-- The kernel is entrywise nonnegative. -/
  kernel_nonneg : ∀ x y, 0 ≤ kernel x y
  /-- Every kernel row has mass at most one. -/
  kernel_row_mass : kernel *ᵥ 1 ≤ 1
  /-- Kernel entries are bounded by the midpoint rate. -/
  kernel_rate : ∀ x y, kernel x y ≤ rate midpointExponent
  /-- Monotone bin-routing cutoff. -/
  binCutoff : ℝ → ℝ
  /-- The bin cutoff is one above one. -/
  cutoff_one : ∀ v, 1 ≤ v → binCutoff v = 1
  /-- Preparation cutoff supplied at each bin. -/
  preparationCutoff : ℕ → ℝ → ℝ
  /-- Gate used by the canonical child requests. -/
  requestGate : ℝ → ℝ
  /-- Rank used by the canonical child requests. -/
  requestRank : ℕ
  /-- Preparation agrees with one wherever the routed bin cutoff is nonzero. -/
  preparation_one : ∀ i ∈ range (lastBin + 1), ∀ v,
    routedBinCutoff binCutoff (fun i => rate (binExponent i)) i (fun _ => 1) v ≠ 0 →
      preparationCutoff i v = 1
  /-- The request gate is nonnegative. -/
  requestGate_nonneg : ∀ v, 0 ≤ requestGate v
  /-- The request gate is bounded by one. -/
  requestGate_le_one : ∀ v, requestGate v ≤ 1
  /-- Positive interval on which the request gate is one. -/
  gateThreshold : ℝ
  /-- The request-gate threshold is positive. -/
  gateThreshold_pos : 0 < gateThreshold
  /-- The request gate is one through its threshold. -/
  gate_one : ∀ v, v ≤ gateThreshold → requestGate v = 1
  /-- The request rank meets the existing gate bound. -/
  rank_bound : 2 * (1 + 32 / gateThreshold) ≤ requestRank
  /-- The bin cutoff is monotone. -/
  cutoff_monotone : Monotone binCutoff
  /-- The bin cutoff vanishes below one half. -/
  cutoff_zero : ∀ v, v ≤ 1 / 2 → binCutoff v = 0
  /-- The bin cutoff stays in the unit interval. -/
  cutoff_range : ∀ v, binCutoff v ∈ Set.Icc 0 1
  /-- Bin rates decrease with the bin index. -/
  rates_antitone : Antitone (fun i => rate (binExponent i))
  /-- Successive bin-rate ratios are at most sixteen. -/
  rate_ratio : ∀ i, rate (binExponent i) / rate (binExponent (i + 1)) ≤ 16
  /-- Kernel density cap at the first bin. -/
  densityCap : ℝ
  /-- The density cap is nonnegative. -/
  densityCap_nonneg : 0 ≤ densityCap
  /-- The first-bin density cap bounds the kernel. -/
  kernel_cap : ∀ z w, kernel z w ≤ densityCap * rate (binExponent 0)
  /-- Rank supplied to incoming correction children. -/
  correctionRank : ℕ
  /-- The final active bin covers each nonzero kernel entry. -/
  kernel_cover : ∀ z y, kernel z y = 0 ∨ rate (binExponent lastBin) ≤ kernel z y
  /-- Exponent of the narrower final usage mask. -/
  usageExponent : ℕ
  /-- Usage is contained in the full terminal rank. -/
  terminal_le_usage : terminalExponent ≤ usageExponent
  /-- The full terminal grid lies in the admitted horizon. -/
  terminal_in_horizon : terminalExponent ≤ horizon.maxExponent
  /-- Lipschitz constant for the hierarchy preparation cutoff. -/
  preparationLipschitz : ℝ
  /-- Lipschitz constant for the hierarchy row gate. -/
  gateLipschitz : ℝ
  /-- The preparation Lipschitz constant is nonnegative. -/
  preparationLipschitz_nonneg : 0 ≤ preparationLipschitz
  /-- The gate Lipschitz constant is nonnegative. -/
  gateLipschitz_nonneg : 0 ≤ gateLipschitz
  /-- The hierarchy preparation cutoff has the supplied Lipschitz bound. -/
  preparation_lipschitz : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤
    preparationLipschitz * |a - b|
  /-- The hierarchy row gate has the supplied Lipschitz bound. -/
  gate_lipschitz : ∀ a b, |HP.ρ a - HP.ρ b| ≤ gateLipschitz * |a - b|
  /-- Positive finite prefix horizon of the actual compression iterate. -/
  prefixLength : ℕ
  /-- The prefix horizon is positive. -/
  prefixLength_pos : 0 < prefixLength

/-- Raw, preparation and maximum child families, supplied independently after choosing the
uniform output coefficient and the finite instance. No accuracy assumption is bundled here. -/
structure ReserveOutputChildren (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (P J : ℕ) [Fact P.Prime] where
  /-- Raw child estimates, indexed by precision, bin and request. -/
  raw : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
    Environment P J → Matrix (ZMod P) (ZMod P) ℝ
  /-- Preparation child estimates with the same indices. -/
  prep : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
    Environment P J → Matrix (ZMod P) (ZMod P) ℝ
  /-- Maximum estimates on each requested source row. -/
  maximum : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
    Environment P J → ZMod P → ℝ

/-- Spectral contraction factor used by both finite walk allocations. -/
abbrev reserveOutputContraction (J : ℕ) : ℝ :=
  1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)

namespace ReserveOutputContext

variable {HP : FourthRootHierarchyParams 16 1 16 32 8} {P J : ℕ} [Fact P.Prime]

/-- Full B1 width and inverse-terminal-rate amplification. -/
abbrev amplification (ctx : ReserveOutputContext HP P J) (ζ : ℝ) : ℝ :=
  P * (|ζ| * (ctx.preparationLipschitz + ctx.gateLipschitz) / rate ctx.terminalExponent) ^ 4

/-- Uniform child tolerance, retaining the finite prefix horizon. -/
abbrev tolerance (ctx : ReserveOutputContext HP P J) (ε : ℝ) : ℝ :=
  ε / (2 * (ctx.prefixLength + 1))

/-- Finite input fourth-moment payment, including the vertex width. -/
abbrev payment (ctx : ReserveOutputContext HP P J) : ℝ :=
  16 * P * (estimatedResidualBound HP P ctx.midpointExponent ctx.terminalExponent ctx.lastBin
    ctx.binExponent (estimatedBinCap ctx.densityCap)) ^ 4

/-- Raw walk length satisfying both the first-noise and amplified B1 requirements. -/
abbrev rawSteps (ctx : ReserveOutputContext HP P J) (ζ ε : ℝ) : ℕ → ℕ :=
  fun j => max
    (spectralWalkLength (reserveOutputContraction J) ((rate ctx.terminalExponent)⁻¹ ^ 4 * 32 *
      ctx.payment) ε (dyadicSlack ctx.prefixLength (j - 1)))
    (spectralWalkLength (reserveOutputContraction J) ((1 + (ctx.amplification ζ)) * 32 *
      ctx.payment) (ctx.tolerance ε) 0)

/-- Preparation walk length for the existing sixteen-rank payment. -/
abbrev prepSteps (ctx : ReserveOutputContext HP P J) (ζ ε : ℝ) : ℕ → ℕ :=
  fun j => spectralWalkLength (reserveOutputContraction J) (ζ ^ 4 * 512 * HP.K) ε (dyadicSlack
    ctx.prefixLength (j - 1))

/-- Routed bin cutoff at the supplied rates. -/
abbrev cutoff (ctx : ReserveOutputContext HP P J) : ℕ → ℝ → ℝ :=
  fun i => routedBinCutoff ctx.binCutoff (fun i => rate (ctx.binExponent i)) i (fun _ => 1)

/-- Bounded routed bin cutoff at the supplied density cap. -/
abbrev bounded (ctx : ReserveOutputContext HP P J) : ℕ → ℝ → ℝ :=
  fun i => boundedRoutedBinCutoff ctx.binCutoff (fun i => rate (ctx.binExponent i)) ctx.densityCap
    i (fun _ => 1)

/-- Source request channel, including its suffix. -/
abbrev source (ctx : ReserveOutputContext HP P J) :=
  gridChannel ctx.roles.source ctx.sourceExponent ctx.sourceSuffix

/-- Midpoint request channel, including its suffix. -/
abbrev midpoint (ctx : ReserveOutputContext HP P J) :=
  gridChannel ctx.roles.midpoint ctx.midpointExponent ctx.midpointSuffix

/-- Full terminal request channel, including its suffix. -/
abbrev terminal (ctx : ReserveOutputContext HP P J) :=
  gridChannel ctx.roles.terminal ctx.terminalExponent ctx.terminalSuffix

/-- Incoming normalized child estimates from the supplied families. -/
abbrev estimated (ctx : ReserveOutputContext HP P J) (children : ReserveOutputChildren HP P J) :=
  fun precision i σ r => incomingChildren HP ctx.direction id ctx.correctionRank (ctx.bounded i)
    (children.raw precision i) (children.prep precision i) (children.maximum precision i) r σ

/-- Canonical normalized children for the supplied kernel and request cutoffs. -/
abbrev canonical (ctx : ReserveOutputContext HP P J) :
    ℕ → Environment P J → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Matrix (ZMod P) (ZMod P) ℝ :=
  fun i σ r => canonicalRequestChild HP ctx.direction id ctx.kernel
    (ctx.cutoff i) (ctx.preparationCutoff i) ctx.requestGate ctx.requestRank r σ

/-- Retained channel interpretation on the field vertices. -/
abbrev channelsV (ctx : ReserveOutputContext HP P J) :
    Fin J → ℝ → List (ZMod P) → Environment P J → ZMod P → Prop :=
  fun role b suffix σ v => channels ctx.direction role b suffix σ (id v)

/-- Actual signed residual input from the child families. -/
abbrev input (ctx : ReserveOutputContext HP P J) (children : ReserveOutputChildren HP P J) :=
  estimatedResidualInput HP ctx.direction id ctx.roles ctx.level ctx.sourceExponent
    ctx.midpointExponent ctx.terminalExponent ctx.lastBin ctx.sourceSuffix ctx.midpointSuffix
    ctx.terminalSuffix ctx.binExponent ctx.correctionRank ctx.bounded
    children.raw children.prep children.maximum

/-- Genuine canonical residual of the supplied kernel at the midpoint rate. -/
abbrev residual (ctx : ReserveOutputContext HP P J) :=
  HP.toHierarchyParams.residual (canonicalChannel id (rate ctx.midpointExponent))
    (canonicalChannel id (rate ctx.midpointExponent)) (rate ctx.midpointExponent) ctx.kernel

/-- Completed raw walk on the source and full terminal-rank masks. -/
abbrev rawWalk (ctx : ReserveOutputContext HP P J) (children : ReserveOutputChildren HP P J)
    (ζ ε : ℝ) :=
  fun j => conditionalWalk (retainedMask ctx.roles.source (side P ctx.sourceExponent)
    ctx.direction ctx.sourceSuffix)
    (retainedMask ctx.roles.terminal (side P ctx.terminalExponent) ctx.direction ctx.terminalSuffix)
    (graph ctx.roles.source ctx.roles.terminal ctx.roles.source_terminal (side P
      ctx.sourceExponent) (side P ctx.terminalExponent)
      (side_le P ctx.sourceExponent) (side_le P ctx.terminalExponent) (fun x =>
        CopyPadding.identifier ctx.direction ctx.sourceSuffix x)
      (fun y => CopyPadding.identifier ctx.direction ctx.terminalSuffix y)) (fun _ _ =>
        (ctx.rawSteps ζ ε) j) ((ctx.input children) j)

/-- Conditional lower-child error cost, at precision one past the prefix index. -/
abbrev cost (ctx : ReserveOutputContext HP P J) (children : ReserveOutputChildren HP P J) :=
  fun j x y => HierarchyTask.conditionalChildCost ctx.channelsV (range (ctx.lastBin + 1)) ctx.level
    ctx.source ctx.midpoint ctx.terminal (fun i => rate (ctx.binExponent i))
    (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * max ctx.densityCap 16)
    ((ctx.estimated children) (j + 1)) ctx.canonical x y

/-- Selected preparation of the completed raw walk. -/
abbrev preparation (ctx : ReserveOutputContext HP P J) (children : ReserveOutputChildren HP P J)
    (ζ ε : ℝ) :=
  fun j σ x y => selectedPreparation HP ctx.direction ctx.roles ctx.terminalSuffix
    ctx.terminalExponent ((ctx.rawWalk children ζ ε) j) σ x y

/-- Preparation walk on the source and narrower usage masks. -/
abbrev prepWalk (ctx : ReserveOutputContext HP P J) (children : ReserveOutputChildren HP P J)
    (ζ ε : ℝ) :=
  fun j => conditionalWalk (retainedMask ctx.roles.source (side P ctx.sourceExponent)
    ctx.direction ctx.sourceSuffix)
    (retainedMask ctx.roles.terminal (side P ctx.usageExponent) ctx.direction ctx.terminalSuffix)
    (graph ctx.roles.source ctx.roles.terminal ctx.roles.source_terminal (side P
      ctx.sourceExponent) (side P ctx.usageExponent)
      (side_le P ctx.sourceExponent) (side_le P ctx.usageExponent) (fun x =>
        CopyPadding.identifier ctx.direction ctx.sourceSuffix x)
      (fun y => CopyPadding.identifier ctx.direction ctx.terminalSuffix y)) (fun _ _ =>
        (ctx.prepSteps ζ ε) j) ((ctx.preparation children ζ ε) j)

/-- Two-signal increment passed to the actual compatible-capacity iterate. -/
abbrev increment (ctx : ReserveOutputContext HP P J) (children : ReserveOutputChildren HP P J)
    (ζ ε : ℝ) :=
  firstSignalIncrement (ctx.rawWalk children ζ ε) ctx.terminalExponent (secondSignalIncrement
    (ctx.prepWalk children ζ ε) ζ)

end ReserveOutputContext

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
