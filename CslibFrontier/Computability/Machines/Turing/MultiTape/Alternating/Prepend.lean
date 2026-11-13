/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DeterministicPhase
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.StateSimulation

/-!
# A native deterministic prefix before an alternating continuation

The existing sequential tape-machine compiler redirects the prefix's halting transition to the
continuation. There is no extra handoff step. The specification accepts padded prefix clocks:
the first halt is used, and the continuation's all-branch halting bound justifies padding.
-/

public section

namespace Turing.MultiTapeATM

open MultiTapeTM

variable {k : ℕ} {P L : Type}

/-- Run a native deterministic preparation and then the alternating machine on its actual output
configuration. The two phases share tapes; only their finite control states are separated. -/
@[expose] noncomputable def prependTM (prepare : MultiTapeTM k Bool P)
    (leaf : MultiTapeATM k Bool L) : MultiTapeATM k Bool (P ⊕ L) :=
  ofTMs (fun b => prepare.seq (leaf.toPTM.withCoin b).toTM)
    (Sum.elim (fun _ => false) leaf.universal)

private noncomputable def prependContinuation (prepare : MultiTapeTM k Bool P)
    (leaf : MultiTapeATM k Bool L) : StateSimulation leaf (prependTM prepare leaf) where
  stateMap := Sum.inr
  universal_eq _ := rfl
  next_eq c b := by
    rw [prependTM, next_ofTMs, MultiTapeTM.seq, step_combine_right]
    rfl

private theorem prepend_prefix_step (prepare : MultiTapeTM k Bool P)
    (leaf : MultiTapeATM k Bool L) {input : List Bool} (b : Bool)
    (cfg : Cfg k Bool P input) (hc : cfg.state ≠ none) :
    (prependTM prepare leaf).next b
      (cfg.mapState (handOver leaf.toPTM.toNTM.q₀)) =
      (prepare.step cfg).mapState (handOver leaf.toPTM.toNTM.q₀) := by
  rw [prependTM, next_ofTMs]
  exact step_combine_left (tm₀ := prepare) (tm₁ := (leaf.toPTM.withCoin b).toTM)
    (handOver_some _) hc

/-- Actual prefix and continuation clocks add, with exact acceptance of the continuation.
The prefix may halt before its supplied clock; both machines retain their original semantics. -/
theorem prependTM_spec (prepare : MultiTapeTM k Bool P) (leaf : MultiTapeATM k Bool L)
    {input : List Bool} (start finish : Cfg k Bool Unit input) (t n : ℕ)
    (hr : prepare.runFrom (start.withState (some prepare.q₀)) t = finish.withState none)
    (hh : leaf.HaltsWithin n (finish.withState (some leaf.toPTM.toNTM.q₀))) :
    (prependTM prepare leaf).HaltsWithin (t + n)
        (start.withState (some (prependTM prepare leaf).toPTM.toNTM.q₀)) ∧
      ((prependTM prepare leaf).AcceptsWithin (t + n)
        (start.withState (some (prependTM prepare leaf).toPTM.toNTM.q₀)) ↔
        leaf.AcceptsWithin n (finish.withState (some leaf.toPTM.toNTM.q₀))) := by
  let atm := prependTM prepare leaf
  let lift := fun c : Cfg k Bool P input => c.mapState (handOver leaf.toPTM.toNTM.q₀)
  have hs : ∀ b c, c.state ≠ none → atm.next b (lift c) = lift (prepare.step c) :=
    fun b c hc => prepend_prefix_step prepare leaf b c hc
  have hl : ∀ c, (lift c).state ≠ none := by
    intro c
    cases hc : c.state <;> simp [lift, Cfg.mapState, handOver, hc]
  obtain ⟨τ, hτ, hstep, _, hend⟩ := exists_deterministic_phase atm lift hs hl
    (show (prepare.runFrom (start.withState (some prepare.q₀)) t).state = none by rw [hr]; rfl)
  rw [hr] at hend
  have htail := (prependContinuation prepare leaf).haltsWithin_iff n
    (finish.withState (some leaf.toPTM.toNTM.q₀))
  have hhalt : atm.HaltsWithin (τ + n) (lift (start.withState (some prepare.q₀))) := by
    rw [haltsWithin_add_iff_of_next_eq hstep, hend]
    exact htail.mpr hh
  have haccept : atm.AcceptsWithin (τ + n) (lift (start.withState (some prepare.q₀))) ↔
      leaf.AcceptsWithin n (finish.withState (some leaf.toPTM.toNTM.q₀)) := by
    rw [acceptsWithin_add_iff_of_next_eq hstep, hend]
    exact (prependContinuation prepare leaf).acceptsWithin_iff n
      (finish.withState (some leaf.toPTM.toNTM.q₀))
  refine ⟨hhalt.mono (by omega), ?_⟩
  exact ⟨fun h => haccept.mp (h.of_halted_stepCoins hhalt),
    fun h => (haccept.mpr h).mono (by omega)⟩

end Turing.MultiTapeATM
