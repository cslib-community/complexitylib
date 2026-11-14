/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeBatch.Interaction.Envelopes
public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchOptimum

/-!
# Primitive fixed-source envelopes for the native token lower optimum

[Wang2027], Theorem 5(2), PDF p. 12, Appendix A.5 p. 16. The primitive assumptions
bound the complete fixed enriched source's newly revealed coverage, progress
probability and conditional invoice mean. They concern actual supported selections
of the admitted native competitor class, rather than forged request snapshots or
arbitrary null histories. No native posterior identity or aggregate cost bound is
assumed.

`LowerBounds.toNative` transfers these primitive bounds to the existing native
conditional envelopes; `lower` then reuses the existing native optimum theorem.
The source budget counts issued batches. The additional decision epoch finalizes
native output and may halt or diverge without issuing a batch. Previously accrued
receipts remain in the actual trace. This is a lower-bound transfer in the finite
opportunity, discrete PMF native model; no upper strategy is constructed here.

## Main definitions

* `LowerBounds`: primitive limitations of one fixed source over actual supported native selections.

## Main results

* `LowerBounds.toNative`: derive native conditional envelopes from primitive source bounds.
* `lower`: the existing common-oracle native optimum lower bound under those primitive assumptions.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.SourceEnvelopes
open NativeOpenExecution ConcurrentBatch NativeBatch Trace Quantitative Turing
open AdaptiveSelection PartialCover
open scoped ENNReal
variable {n : ℕ} {Private : Type}

/-- Primitive source bounds over the actual finite-control selection-only class.
The source and seed are fixed for every competitor, with no integrability premise. -/
structure LowerBounds (limits : Limits n) (sample : Sampler n Private)
    (data : GuardedStartup.Input) (seed : Private) (hx : Valid data.startup.system)
    (b : ℕ) (p c : ℝ≥0∞) : Prop where
  /-- Bound complete source draws at reached pre-response selections. Failed
  output masks are restricted only by the existing successful-output admission. -/
  bounds : ∀ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : MultiTapePTM k Bool Control Unit),
    let world := (⟨machine.initialConfig (GuardedStartup.encoding data),
      ⟨ConcurrentBatch.initial seed, []⟩⟩ :
        World k Control Unit (ServerState n Private) (GuardedStartup.encoding data))
    NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
      (candidateParser (n := n) data.startup.system.rows.length)
      (decodeFamily data.startup.system.rows.length) (BatchOutput.accept data.startup.system hx)
      world → ∀ t < limits.turns + 1,
      ∀ view ∈ (NativeBatch.Interaction.selectionViews limits sample (PMF.pure seed) machine
        (machine.initialConfig (GuardedStartup.encoding data)) t).support,
      let draw := (ConcurrentBatch.Interaction.source limits sample (PMF.pure seed)).draw
        view.history view.query
      let history := view.history.map Prod.snd
      (∀ pair ∈ draw.support,
        (revealed (BatchOptimum.finiteInstance data.startup.system hx)
          (Coverage.proposal data.startup.system.rows.length) (pair.1 :: history) \
          revealed (BatchOptimum.finiteInstance data.startup.system hx)
            (Coverage.proposal data.startup.system.rows.length) history).card ≤ b) ∧
      (view.query.isSome = true →
        (∑' pair, draw pair * if reveals (BatchOptimum.finiteInstance data.startup.system hx)
          (Coverage.proposal data.startup.system.rows.length) history pair.1 then 1 else 0) ≤ p) ∧
      (view.query.isSome = true → c ≤ ∑' pair, draw pair * Trace.charge pair.1)

/-- Primitive source limitations imply the original native conditional envelopes,
including support-wise coverage and extended invoice means on divergent prefixes. -/
theorem LowerBounds.toNative (limits : Limits n) (sample : Sampler n Private)
    (data : GuardedStartup.Input) (seed : Private) (hx : Valid data.startup.system)
    (b : ℕ) (p c : ℝ≥0∞) (H : LowerBounds limits sample data seed hx b p c) :
    BatchOptimum.LowerEnvelopes limits sample data seed hx b p c := by
  constructor
  intro k Control hfinite machine world hadmit t ht o ho
  let config := machine.initialConfig (GuardedStartup.encoding data)
  have ho' : o ∈ ((Quantitative.select limits sample machine
      ((PMF.pure seed).bind fun privateState => Trace.law limits sample machine t
        ⟨config, ⟨ConcurrentBatch.initial privateState, []⟩⟩)).map
          (Quantitative.observe limits)).support := by
    simpa only [PMF.pure_bind] using ho
  have hprimitive := H.bounds k Control hfinite machine hadmit t ht
  have issued (view : NativeBatch.Interaction.Selection n k Unit Control
      (GuardedStartup.encoding data))
      (hv : view ∈ (NativeBatch.Interaction.selectionViews limits sample (PMF.pure seed) machine
        config t).support)
      (he : NativeBatch.Interaction.selectedObservation limits view = o)
      (hi : o.issued = true) : view.query.isSome = true := by
    rw [(NativeBatch.Interaction.selectionViews_valid limits sample (PMF.pure seed) machine
      config t view hv).1, ← NativeBatch.Interaction.selectedObservation_issued limits view, he]
    exact hi
  refine ⟨?_, ?_, ?_⟩
  · intro next hn
    let P : List (Trace.Record n) → Trace.Record n → Prop := fun history record =>
      (revealed (BatchOptimum.finiteInstance data.startup.system hx)
        (Coverage.proposal data.startup.system.rows.length) (record :: history) \
        revealed (BatchOptimum.finiteInstance data.startup.system hx)
          (Coverage.proposal data.startup.system.rows.length) history).card ≤ b
    obtain ⟨record, hrecord, hcard⟩ := NativeBatch.Interaction.conditional_records limits sample
      (PMF.pure seed) machine config t o ho' P (by
        intro view hv _ pair hp
        exact (hprimitive view hv).1 pair hp) next
      (by simpa only [PMF.pure_bind] using hn)
    rw [hrecord]
    exact hcard
  · intro hi
    have hm := NativeBatch.Interaction.conditional_reward_le limits sample (PMF.pure seed)
      machine config t o
      (fun history record => if reveals (BatchOptimum.finiteInstance data.startup.system hx)
        (Coverage.proposal data.startup.system.rows.length) history record then 1 else 0)
      p ho' (by
        intro view hv he
        exact (hprimitive view hv).2.1 (issued view hv he hi))
    simpa only [PMF.pure_bind] using hm
  · intro hi
    have hm := NativeBatch.Interaction.conditional_reward_ge limits sample (PMF.pure seed)
      machine config t o (fun _ record => Trace.charge record) c ho' (by
        intro view hv he
        exact (hprimitive view hv).2.2 (issued view hv he hi))
    simp only [PMF.pure_bind] at hm
    exact hm

/-- The original common-oracle native token lower bound follows from the fixed
source's primitive limitations, without reproving the optimum argument. -/
theorem lower (limits : Limits n) (sample : Sampler n Private)
    (data : GuardedStartup.Input) (seed : Private) (hx : Valid data.startup.system)
    (η : ℝ≥0∞) (b r : ℕ) (p c : ℝ≥0∞)
    (hr : ∀ q < r, b * q < (instanceOf data.startup.system hx).ground.card)
    (hp : p ≠ 0) (hpt : p ≠ ∞)
    (H : LowerBounds limits sample data seed hx b p c) :
    (η * r * c) / p ≤ BatchOptimum.optimum limits sample data seed hx η :=
  BatchOptimum.lower limits sample data seed hx η b r p c hr hp hpt
    (H.toNative limits sample data seed hx b p c)

end Cslib.Probability.StochasticOracle.NativeRetention.SourceEnvelopes
