/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Interactive.Basic

/-!
# A single-session phased commitment world

An original commitment-with-abort interface implemented by `Interactive.World`. The sender can
commit, open, or abort; the receiver can only poll. A first commitment fixes a private bit, and
polling reveals only a receipt until opening. Early opening and repeated commitments do nothing.
Abort before opening is terminal; an opened value cannot be retracted.

This is a concrete phased functionality, not UC Fcom or a security definition. In particular,
it does not model concurrent sessions, a network scheduler, corruption, or simulator efficiency.
The noninteractive `Commitment.Scheme` instead produces a commitment and opening together;
it does not describe these stateful commands.

## Main definitions

* `Command`, `Store`, `Observation`: sender calls, private state, and public polling replies.
* `handler`: deterministic transitions in either semantic or program effects.
* `world`: the functionality with separated sender and receiver interfaces.

## Main results

* `polling_secrecy`: arbitrary adaptive receiver polling, with private samples, cannot reveal
  the committed bit before opening.
* `committed_invariant`: after commitment, any supported execution retains the bit or aborts.
* `opened_terminal`, `aborted_terminal`: opened and aborted states are terminal under every call.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.Commitment.Phased

/-- Commands available only to the sender. -/
inductive Command where
  | commit (bit : Bool)
  | open
  | abort
  deriving DecidableEq

/-- Private functionality state. The committed bit is not a polling reply. -/
inductive Store where
  | idle
  | committed (bit : Bool)
  | opened (bit : Bool)
  | aborted
  deriving DecidableEq

/-- Public receiver observations, including the distinction between no commitment and a receipt. -/
inductive Observation where
  | idle
  | receipt
  | opened (bit : Bool)
  | aborted
  deriving DecidableEq, Fintype

/-- The public observation of a private state. -/
def observe : Store → Observation
  | .idle => .idle
  | .committed _ => .receipt
  | .opened b => .opened b
  | .aborted => .aborted

/-- Total command processing. Invalid-order commands are ignored. Opened and aborted states
are terminal, so abort cannot retract an opening. -/
def advance : Command → Store → Store
  | .commit b, .idle => .committed b
  | .open, .committed b => .opened b
  | .abort, .idle | .abort, .committed _ => .aborted
  | _, s => s

/-- Sender calls return no information. -/
abbrev senderSpec : OracleSpec Command := fun _ => Unit

/-- The receiver's only call is a poll. -/
abbrev receiverSpec : OracleSpec Unit := fun _ => Observation

/-- The deterministic functionality handler, shared by semantic and program interpretations.
Only the surrounding pure-effect monad varies; the command and observation rules are identical. -/
def handler {m : Type → Type} [Pure m] :
    (q : Command ⊕ Unit) → StateT Store m ((senderSpec ⊕ₒ receiverSpec) q) :=
  OracleComp.sumHandler
    (fun cmd s => pure ((), advance cmd s))
    (fun _ s => pure (observe s, s))

/-- Closing a private probabilistic sample through the actual handler only lifts its state. -/
theorem interpret_sample {α : Type} (program : ProbComp α) :
    OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) handler)
      (ProbOracleComp.sample program) = StateT.lift (σ := Store) program := by
  funext st
  rw [ProbOracleComp.interpret_sample]
  change (OracleComp.interpret (m := StateT Store ProbComp) _ program).run st = _
  rw [OracleComp.run_interpret_lift, ProbComp.interpret_unifFin]
  simp [StateT.lift, bind_pure_comp]

/-- One phased session, with sender commands on the left and receiver polls on the right.
Only `World.eval`'s program output is public; its state remains private.
Privacy here is the observation boundary, not Lean declaration accessibility. -/
noncomputable abbrev world : Interactive.World senderSpec receiverSpec where
  State := Store
  init := .idle
  impl := handler

/-- Polling leaves the private state unchanged. Its complete reply law depends only on the
public observation of that state, including for adaptive programs with private randomness. -/
theorem polling_run {α : Type} (program : ProbOracleComp receiverSpec α) (s : Store) :
    ProbOracleComp.runWith (fun q => world.impl (.inr q)) program s =
      (OracleComp.evalWith
        (OracleComp.sumHandler ProbComp.unifOracle (fun _ => pure (observe s))) program).map
          (·, s) := by
  let oracle : (q : ℕ ⊕ Unit) → Store → PMF ((unifSpec ⊕ₒ receiverSpec) q) :=
    fun q s => OracleComp.sumHandler ProbComp.unifOracle (fun _ => pure (observe s)) q
  have handlers : OracleComp.sumHandler
      (fun n => StateT.lift (σ := Store) (ProbComp.unifOracle n))
      (fun q => world.impl (.inr q)) =
      fun q s => (fun a => (a, s)) <$> oracle q s := by
    funext q s
    cases q <;>
      simp [oracle, handler, OracleComp.sumHandler, StateT.lift, PMF.map, Function.comp_def]
  unfold ProbOracleComp.runWith OracleComp.runWith
  rw [handlers, OracleComp.run_interpret_readOnly]
  rfl

/-- Before opening, receiver-only interaction reveals no committed bit. The program may retain
its complete transcript and private randomness in its result. World state is not an observation. -/
theorem polling_secrecy {α : Type} (program : ProbOracleComp receiverSpec α) (b b' : Bool) :
    (ProbOracleComp.runWith (fun q => world.impl (.inr q)) program (.committed b)).map
        Prod.fst =
      (ProbOracleComp.runWith (fun q => world.impl (.inr q)) program (.committed b')).map
        Prod.fst := by
  rw [polling_run, polling_run, PMF.map_comp, PMF.map_comp]
  rfl

/-- After commitment, commands cannot substitute another stored or released bit. -/
theorem advance_committed (cmd : Command) (b : Bool) {s : Store}
    (h : s = .committed b ∨ s = .opened b ∨ s = .aborted) :
    advance cmd s = .committed b ∨ advance cmd s = .opened b ∨
      advance cmd s = .aborted := by
  rcases h with rfl | rfl | rfl <;> cases cmd <;> simp [advance]

/-- Every supported adaptive joint execution after commitment retains its bit or aborts.
Both parties' calls and fresh private samples are included. -/
theorem committed_invariant {α : Type}
    (program : ProbOracleComp (senderSpec ⊕ₒ receiverSpec) α) (b : Bool)
    {result : α} {s : Store}
    (h : (result, s) ∈ (ProbOracleComp.runWith world.impl program (.committed b)).support) :
    s = .committed b ∨ s = .opened b ∨ s = .aborted := by
  apply OracleComp.run_interpret_invariant
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) world.impl)
    (fun s => s = .committed b ∨ s = .opened b ∨ s = .aborted) _
    program (.committed b) (Or.inl rfl) result s h
  intro q st hst a next hnext
  cases q with
  | inl n =>
    change (a, next) ∈ ((ProbComp.unifOracle n).map (·, st)).support at hnext
    obtain ⟨_, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
    cases heq
    exact hst
  | inr q =>
    cases q with
    | inl cmd =>
      change (a, next) ∈ (PMF.pure ((), advance cmd st)).support at hnext
      have heq : next = advance cmd st :=
        congrArg Prod.snd ((PMF.mem_support_pure_iff _ _).mp hnext)
      rw [heq]
      exact advance_committed cmd b hst
    | inr poll =>
      change (a, next) ∈ (PMF.pure (observe st, st)).support at hnext
      have heq : next = st := congrArg Prod.snd ((PMF.mem_support_pure_iff _ _).mp hnext)
      rwa [heq]

/-- An opened value cannot be overwritten or retracted, even by abort. -/
theorem opened_terminal (cmd : Command) (b : Bool) : advance cmd (.opened b) = .opened b := by
  cases cmd <;> rfl

/-- Abort is terminal, including when it occurred before any commitment. -/
theorem aborted_terminal (cmd : Command) : advance cmd .aborted = .aborted := by
  cases cmd <;> rfl

end Cslib.Crypto.Protocols.Commitment.Phased
