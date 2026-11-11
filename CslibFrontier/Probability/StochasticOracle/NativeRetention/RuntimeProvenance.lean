/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.RuntimeControl
public import CslibFrontier.Probability.StochasticOracle.NativeRetention.Selector
public import CslibFrontier.Computability.Probabilistic.NativeBatch
import Mathlib.Tactic

/-!
# Native retention provenance from authenticated raw reply history

The actual local retention algorithm emits only parsed returned candidates.
The hypotheses identify its runtime history with recorded raw replies and their
canonical source packet parsing; no scheduler, successful output or native
representation conclusion is assumed.

## Main results

* `result_available`: every decoded result has native response provenance.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.RuntimeProvenance
open NativeOpenExecution ConcurrentBatch
variable {n : ℕ} {Private : Type}

/-- Canonical raw packets and authenticated reply history suffice for actual
retention output provenance, independently of the concrete request planner. -/
theorem result_available (state : RuntimeControl.State) (events : List (Event Unit))
    (hx : Valid state.work.system) (hopps : state.work.opportunities = n)
    (hhistory : state.work.history = events.map (fun e => e.reply.word))
    (hpackets : ∀ word ∈ state.work.history,
      Packets.families n state.work.system.rows.length word =
        (parseProposals n state.work.system.rows.length word).map sourceIndices)
    (C : Finset (Fin state.work.system.rows.length))
    (hC : decodeFamily state.work.system.rows.length (RuntimeControl.result state) = some C) :
    C ⊆ NativeBatch.nativeAvailable (n := n) state.work.system.rows.length events := by
  let selected : Selector.State := ⟨state.work.history, false, state.requests, state.privateWord⟩
  have hp : Packets.assemble state.work = Selector.data n state.work.system selected := by
    have hps : state.work.history.reverse.flatMap
        (Packets.families n state.work.system.rows.length) =
        state.work.history.reverse.flatMap
          (fun word => (parseProposals n state.work.system.rows.length word).map
            sourceIndices) := by
      apply List.flatMap_congr
      intro word hw
      exact hpackets word (List.mem_reverse.mp hw)
    simpa only [Packets.assemble, hopps, Selector.data, selected, List.map_flatMap] using
      congrArg (fun ps => { state.work.system with proposals := ps }) hps
  have hav : Selector.available n state.work.system.rows.length state.work.history =
      NativeBatch.nativeAvailable (n := n) state.work.system.rows.length events := by
    rw [hhistory]
    clear hhistory
    induction events with
    | nil => rfl
    | cons e es ih =>
      simp only [List.map_cons, Selector.available, NativeBatch.nativeAvailable, ih]
  have hprov := Selector.provenance n state.work.system hx selected
  rw [hav] at hprov
  unfold RuntimeControl.result Packets.decision at hC
  rw [hp] at hC
  split_ifs at hC with hc
  · dsimp only [Prod.snd] at hC
    change decodeFamily (Selector.data n state.work.system selected).rows.length
      (output (Selector.data n state.work.system selected)) = some C at hC
    rw [decode_output] at hC
    cases hC
    exact hprov
  · simp only [decodeFamily, List.length_nil] at hC
    split_ifs at hC
    cases hC
    intro i hi
    have hbad := (Finset.mem_filter.mp hi).2
    simp at hbad

end Cslib.Probability.StochasticOracle.NativeRetention.RuntimeProvenance
