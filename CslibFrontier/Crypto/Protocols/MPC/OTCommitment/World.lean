/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.Commitment.World
public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.Extraction
public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.Equivocation
import CslibFrontier.Languages.Probabilistic.Norm

/-!
# OT commitment simulations through a phased world

These original semantic drivers connect the OT commitment laws to actual transitions of
`Commitment.Phased.world`. The corrupted-sender driver commits the extracted bit before invoking
the opening continuation. The corrupted-receiver prefix has no bit input; it obtains a bit only
from the world's later opening observation. Prefix-dependent randomized withholding and
arbitrary post-opening continuation retain the receiver's private states jointly.

All laws start the functionality in `Store.idle` and hide its final private state. The drivers
use `StateT Store PMF` because the strategies allow arbitrary PMFs. They are not claimed to be
realized `ProbOracleComp` programs or efficient simulators. This remains one fixed-length,
single-session corruption case at a time, with no mid-commit abort, arbitrary scheduling,
malformed-byte parser, composition, or UC realization.

## Main definitions

* `senderIdeal`: commit-before-finish corrupted-sender driver.
* `receiverPrefix`: bit-free receiver prefix with an actual receipt poll.
* `receiverIdeal`, `receiverReal`: ideal-world and honest-OT delayed-opening laws.

## Main results

* `senderIdeal_coupled`: joint output/state simulation error at most `2⁻⌈k/2⌉`.
* `receiverPrefix_committed`: the actual prefix observation has no committed-bit dependence.
* `receiverIdeal_eq_real`: exact joint receiver law, including withholding and continuation.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment

open Crypto.Protocols.Commitment Probability
open scoped ENNReal

/-- A corrupted-sender driver using actual world commands. Only this simulator sees the sender's
OT tables; `finish` receives only the sender's commit-final state. The extraction is committed
before `finish` runs. Both public observations and the sender's auxiliary output are retained. -/
noncomputable def senderIdeal {State Output : Type} (A : Sender State) (k : ℕ)
    (initial : PMF State)
    (finish : State → PMF (Option (Bool × Opening k) × Output)) :
    StateT Phased.Store PMF (Phased.Observation × Phased.Observation × State × Output) := do
  let st ← StateT.lift initial
  let (ts, final) ← StateT.lift (senderTables A k st)
  Phased.world.impl (.inl (.commit (extract ts)))
  let received ← Phased.world.impl (.inr ())
  let choices ← StateT.lift (PMF.uniformOfFintype (Fin k → Bool))
  let (submission, out) ← StateT.lift (finish final)
  let result := openResult choices
    (fun i => ts i (boolPairToFin4 (false, choices i))) submission
  if result = some (extract ts) then Phased.world.impl (.inl .open)
  else Phased.world.impl (.inl .abort)
  let observed ← Phased.world.impl (.inr ())
  return (received, observed, final, out)

/-- The actual phased-world driver refines the previously proved sender simulation law.
Only the program's output is observed; final functionality state stays private. -/
theorem senderIdeal_run {State Output : Type} (A : Sender State) (k : ℕ)
    (initial : PMF State)
    (finish : State → PMF (Option (Bool × Opening k) × Output)) :
    (senderIdeal A k initial finish .idle).map Prod.fst =
      (simulatedOpening A k initial finish).map (fun (result, final, out) =>
        (Phased.Observation.receipt, result.elim .aborted .opened, final, out)) := by
  classical
  change ((senderIdeal A k initial finish).run .idle).map Prod.fst = _
  simp only [senderIdeal, StateT.run_bind]
  simp only [pmf_norm, simulatedOpening, StateT.lift, StateT.run, Phased.handler,
    OracleComp.sumHandler, Phased.advance, Phased.observe]
  apply congrArg (initial.bind)
  funext st
  apply congrArg ((senderTables A k st).bind)
  apply funext
  rintro ⟨ts, final⟩
  apply congrArg ((PMF.uniformOfFintype (Fin k → Bool)).bind)
  funext choices
  apply congrArg ((finish final).bind)
  apply funext
  rintro ⟨submission, out⟩
  split <;>
    change PMF.map Prod.fst (StateT.run (m := PMF) _ _) = _
  all_goals simp only [StateT.run_bind, StateT.run_pure]
  all_goals simp [StateT.run]

/-- Actual world transitions inherit the sender output/state coupling. The error is the
extraction bound, not the smaller double-opening bound. -/
theorem senderIdeal_coupled {State Output : Type} (A : Sender State) (k : ℕ)
    (initial : PMF State)
    (finish : State → PMF (Option (Bool × Opening k) × Output)) :
    Probability.PMF.CoupledWithin
      ((realOpening A k initial finish).map (fun (result, final, out) =>
        (Phased.Observation.receipt, result.elim .aborted .opened, final, out)))
      ((senderIdeal A k initial finish .idle).map Prod.fst)
      ((2 : ℝ≥0∞)⁻¹ ^ (k - k / 2)) := by
  rw [senderIdeal_run]
  exact (simulatedOpening_coupled A k initial finish).map _

/-- Callable receiver prefix without a committed-bit input. It polls the actual world and then
runs the bit-independent OT receiver view, retaining the receiver's entire commit-final state. -/
noncomputable def receiverPrefix {State : Type} (A : Receiver State) (k : ℕ) (st : State) :
    StateT Phased.Store PMF (Phased.Observation × (Fin k → Fin 4 × Bool) × State) := do
  let received ← Phased.world.impl (.inr ())
  let (transcript, final) ← StateT.lift (receiverRun A false k st)
  return (received, transcript, final)

/-- In a committed world, the prefix exposes only the receipt and a bit-independent receiver
view. The functionality's stored bit stays hidden even though its private state is available
inside the semantic monad. -/
theorem receiverPrefix_committed {State : Type} (A : Receiver State) (k : ℕ)
    (st : State) (b : Bool) :
    (receiverPrefix A k st (.committed b)).map Prod.fst =
      (receiverRun A false k st).map (fun (transcript, final) =>
        (Phased.Observation.receipt, transcript, final)) := by
  change ((receiverPrefix A k st).run (.committed b)).map Prod.fst = _
  simp only [receiverPrefix, StateT.run_bind, StateT.run_pure]
  simp [StateT.run, StateT.lift, Phased.handler, OracleComp.sumHandler, Phased.observe,
    PMF.bind_bind, PMF.map, Function.comp_def]

/-- Delayed-opening corrupted-receiver driver. `plan` sees only the prefix transcript and
receiver state and may randomly withhold opening, returning an updated private `Later` state.
The simulator learns the bit from a poll only after opening; abort supplies no opening to the
continuation. Both observations, both receiver states and the continuation output are retained. -/
noncomputable def receiverIdeal {State Later Output : Type} (A : Receiver State) (b : Bool)
    (k : ℕ) (st : State)
    (plan : (Fin k → Fin 4 × Bool) → State → PMF (Bool × Later))
    (finish : (Fin k → Fin 4 × Bool) → State → Later → Phased.Observation →
      Option (Opening k) → PMF Output) :
    StateT Phased.Store PMF
      (Phased.Observation × Phased.Observation × (Fin k → Fin 4 × Bool) ×
        State × Later × Output) := do
  Phased.world.impl (.inl (.commit b))
  let (received, transcript, final) ← receiverPrefix A k st
  let (release, later) ← StateT.lift (plan transcript final)
  if release then Phased.world.impl (.inl .open)
  else Phased.world.impl (.inl .abort)
  let observed ← Phased.world.impl (.inr ())
  let pairs := match observed with
    | .opened bit => some (equivocate bit transcript)
    | _ => none
  let out ← StateT.lift (finish transcript final later observed pairs)
  return (received, observed, transcript, final, later, out)

/-- Honest OT execution followed by the same prefix-dependent release decision and randomized
continuation. Released pairs use the sender masks actually sampled during the OT interaction. -/
noncomputable def receiverReal {State Later Output : Type} (A : Receiver State) (b : Bool)
    (k : ℕ) (st : State)
    (plan : (Fin k → Fin 4 × Bool) → State → PMF (Bool × Later))
    (finish : (Fin k → Fin 4 × Bool) → State → Later → Phased.Observation →
      Option (Opening k) → PMF Output) :
    PMF (Phased.Observation × Phased.Observation × (Fin k → Fin 4 × Bool) ×
      State × Later × Output) := do
  let (masks, transcript, final) ← receiverCommit A b k st
  let (release, later) ← plan transcript final
  let out ← finish transcript final later
      (if release then .opened b else .aborted) (if release then some (opening b masks) else none)
  return (.receipt, if release then .opened b else .aborted, transcript, final, later, out)

/-- Exact joint corrupted-receiver simulation through the actual functionality, with an initial
idle store. Withholding depends only on the commit view; the continuation runs after release or
abort and may retain all private data in its output. -/
theorem receiverIdeal_eq_real {State Later Output : Type} (A : Receiver State) (b : Bool)
    (k : ℕ) (st : State)
    (plan : (Fin k → Fin 4 × Bool) → State → PMF (Bool × Later))
    (finish : (Fin k → Fin 4 × Bool) → State → Later → Phased.Observation →
      Option (Opening k) → PMF Output) :
    (receiverIdeal A b k st plan finish .idle).map Prod.fst =
      receiverReal A b k st plan finish := by
  have h := equivocation_bind A b k st (fun transcript final pairs => do
    let (release, later) ← plan transcript final
    let out ← finish transcript final later
      (if release then .opened b else .aborted) (if release then some pairs else none)
    return (Phased.Observation.receipt, if release then Phased.Observation.opened b else .aborted,
      transcript, final, later, out))
  rw [show receiverReal A b k st plan finish = _ from h]
  change ((receiverIdeal A b k st plan finish).run .idle).map Prod.fst = _
  simp only [receiverIdeal, receiverPrefix, StateT.run_bind, StateT.run_pure]
  simp only [pmf_norm, StateT.lift, StateT.run, Phased.handler, OracleComp.sumHandler,
    Phased.advance, Phased.observe]
  apply congrArg ((receiverRun A false k st).bind)
  apply funext
  rintro ⟨transcript, final⟩
  apply congrArg ((plan transcript final).bind)
  apply funext
  rintro ⟨release, later⟩
  cases release <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    change PMF.map Prod.fst (StateT.run (m := PMF) _ _) = _
  all_goals simp only [StateT.run_bind, StateT.run_pure]
  all_goals simp [StateT.run, StateT.lift, PMF.bind_bind, PMF.map_bind]

end Cslib.Crypto.Protocols.MPC.OTCommitment
