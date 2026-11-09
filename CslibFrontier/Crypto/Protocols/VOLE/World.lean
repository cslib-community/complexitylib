/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.VOLE.Basic
public import CslibFrontier.Computability.Interactive.Basic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

/-!
# A cached ideal VOLE world

The existing ideal correlation distribution is exposed through separate sender and receiver
oracles. The first request samples one correlation; all later requests read the same cached
correlation. Neither role can query the other role's interface. Each evaluation of the world
starts a fresh session. Repeated reads do not supply fresh correlations.

## Main definitions

* `voleSenderSpec`, `voleReceiverSpec`: the two role-local setup interfaces.
* `voleWorld`: the shared, lazily sampled ideal correlation in `Interactive.World`.

## Main results

* `voleWorld_cached_sender`, `voleWorld_cached_receiver`: cached requests return the same share.
* `voleWorld_cached_run`: arbitrary randomized clients preserve that cache and read fixed shares.
* `voleWorld_eval`: lazy setup has the same output law as sampling one correlation up front.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.VOLE

open Probability Interactive

/-- The sender can read only its two vectors, never the receiver key or tags. -/
abbrev voleSenderSpec (F : Type) (n : ℕ) : OracleSpec Unit :=
  fun _ => (Fin n → F) × (Fin n → F)

/-- The receiver can read only its key and tag vector. -/
abbrev voleReceiverSpec (F : Type) (n : ℕ) : OracleSpec Unit :=
  fun _ => F × (Fin n → F)

/-- One ideal correlation shared between the role-local interfaces and cached for the session.
The initial state is empty, so no key or correlation is supplied as a public parameter. -/
noncomputable def voleWorld (F : Type) [CommRing F] [Fintype F] (n : ℕ) :
    World (voleSenderSpec F n) (voleReceiverSpec F n) where
  State := Option (VOLECorrelation F n)
  init := none
  impl
    | .inl () => fun cache => do
      let c ← match cache with
        | none => voleIdealDist F n
        | some c => pure c
      return (c.senderView, some c)
    | .inr () => fun cache => do
      let c ← match cache with
        | none => voleIdealDist F n
        | some c => pure c
      return (c.receiverView, some c)

variable {F : Type} [CommRing F] [Fintype F] {n : ℕ}

/-- Reading a cached sender share does not resample the correlation. -/
theorem voleWorld_cached_sender (c : VOLECorrelation F n) :
    (voleWorld F n).impl (.inl ()) (some c) = PMF.pure (c.senderView, some c) := by
  simp [voleWorld]

/-- Reading a cached receiver share does not resample the correlation. -/
theorem voleWorld_cached_receiver (c : VOLECorrelation F n) :
    (voleWorld F n).impl (.inr ()) (some c) = PMF.pure (c.receiverView, some c) := by
  simp [voleWorld]

/-- Once cached, an arbitrary randomized client reads the same role-specific shares throughout
its execution. The equality retains the final cache and all client outputs. -/
theorem voleWorld_cached_run {α : Type} (c : VOLECorrelation F n)
    (program : ProbOracleComp (voleSenderSpec F n ⊕ₒ voleReceiverSpec F n) α) :
    ProbOracleComp.runWith (voleWorld F n).impl program (some c) =
      (OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
        (OracleComp.sumHandler (fun _ => PMF.pure c.senderView)
          (fun _ => PMF.pure c.receiverView))) program).map (·, some c) := by
  let oracle := OracleComp.sumHandler (fun _ : Unit => PMF.pure c.senderView)
    (fun _ : Unit => PMF.pure c.receiverView)
  have h := ProbOracleComp.run_interpret_map_state
    (fun q => StateT.lift (σ := Unit) (oracle q)) (voleWorld F n).impl
    (fun _ => some c) (fun q state => ?_) program ()
  · change (ProbOracleComp.runWith (fun q => StateT.lift (σ := Unit) (oracle q))
      program ()).map (fun (a, _) => (a, some c)) =
        ProbOracleComp.runWith (voleWorld F n).impl program (some c) at h
    rw [ProbOracleComp.runWith_lift] at h
    simp only [PMF.map_comp, Function.comp_def, OracleComp.evalWith, oracle] at h
    exact h.symm
  · cases q with
    | inl q =>
      cases q
      simp only [pmf_norm, oracle, OracleComp.sumHandler, StateT.lift, voleWorld_cached_sender]
      rfl
    | inr q =>
      cases q
      simp only [pmf_norm, oracle, OracleComp.sumHandler, StateT.lift, voleWorld_cached_receiver]
      rfl

/-- Sampling the cached correlation before execution preserves every output law, including
for programs that never query setup. Each role still reads only its own fixed share. -/
theorem voleWorld_eval {α : Type}
    (program : ProbOracleComp (voleSenderSpec F n ⊕ₒ voleReceiverSpec F n) α) :
    (voleWorld F n).eval program = (do
      let c ← voleIdealDist F n
      OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
        (OracleComp.sumHandler (fun _ => PMF.pure c.senderView)
          (fun _ => PMF.pure c.receiverView))) program) := by
  let relate : Option (VOLECorrelation F n) → PMF (VOLECorrelation F n)
    | none => voleIdealDist F n
    | some c => PMF.pure c
  let replies : (q : Unit ⊕ Unit) → VOLECorrelation F n →
      PMF ((voleSenderSpec F n ⊕ₒ voleReceiverSpec F n) q) := fun q c =>
    OracleComp.sumHandler (fun _ => PMF.pure c.senderView)
      (fun _ => PMF.pure c.receiverView) q
  let oracle := fun q c => (replies q c).map (·, c)
  have h := ProbOracleComp.run_interpret_simulation (voleWorld F n).impl oracle relate
    (fun q state => ?_) program none
  · have houtput := congrArg (fun law => law.map Prod.fst) h
    simp only [pmf_norm, PMF.map, PMF.bind_const] at houtput
    refine houtput.trans ?_
    change (voleIdealDist F n).bind _ = _
    congr 1
    funext c
    change ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      program).run c).map Prod.fst = _
    rw [ProbOracleComp.run_interpret_readOnly replies]
    simp only [PMF.map_comp, Function.comp_def]
    change PMF.map id _ = _
    rw [PMF.map_id]
  · rcases q with q | q <;> cases q <;> cases state <;>
      simp [voleWorld, relate, oracle, replies, OracleComp.sumHandler, PMF.map]

end Cslib.Crypto.Protocols.VOLE
