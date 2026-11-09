/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card

/-!
# Synchronous Byzantine agreement

Deterministic synchronous message passing on the complete graph of processes `P`, in the presence
of Byzantine faults, following the model of [Fischer, Lynch and Merritt][FischerLynchMerritt1985]
(§2) for the problem of [Pease, Shostak and Lamport][PeaseShostakLamport1980].

A `Protocol P State Msg` gives every process an initial state from its input bit, and in every
round a message to every process, a new state computed from the messages received, and a Boolean
decision. Every process may run different code, since all fields take the process as an argument.
The processes in a set `F` are *faulty*: in round `r + 1` a faulty process `j` sends `adv r j i` to
`i`, arbitrarily and possibly differently to different recipients. `Protocol.state` and
`Protocol.decision` give the resulting run. Since runs are deterministic, quantifying over a fixed
table `adv` loses nothing against adaptive (even rushing) adversaries: the messages an adaptive
adversary sends in the run on a given input form such a table. `Protocol.adaptiveState_eq_state`
checks this for a rushing adversary that sees the global state before choosing its messages.

`Protocol.SolvesByzantineAgreement t R` asks that, whenever at most `t` processes are faulty, the
correct processes' decisions after `R` rounds satisfy

* *agreement*: all correct processes decide the same value, and
* *validity*: if all correct processes have input `v`, they decide `v`.

Termination is built in: decisions are read off after round `R`. A protocol that decides earlier
can keep its state unchanged in later rounds. Protocols whose decision round depends on the run
are not covered. For finite `P` and `Msg` this loses nothing, since by König's lemma such a
protocol decides within a bound uniform over all runs, but for infinite `Msg` a fixed `R` is
strictly narrower than eventual decision.

`Protocol.coverState` runs the protocol on a *covering network*, in which every node runs the code
of some process and receives the message of process `j` from a designated neighbour. The covering
lemma `Protocol.state_eq_coverState` says that a Byzantine run coincides on the correct processes
with a covering network whenever the faulty processes replay what the network shows them. It
packages the Locality and Fault axioms of Fischer, Lynch and Merritt, proved here for this model,
and is the engine of the impossibility proofs in
`CslibFrontier.Computability.Distributed.Byzantine.NodeBound`.

## Main definitions

* `Cslib.Distributed.Byzantine.Protocol`: synchronous deterministic protocols.
* `Cslib.Distributed.Byzantine.Protocol.state`, `Protocol.decision`: runs with Byzantine faults.
* `Cslib.Distributed.Byzantine.Protocol.adaptiveState`: runs against a rushing adversary.
* `Cslib.Distributed.Byzantine.Protocol.SolvesByzantineAgreement`: agreement and validity
  against at most `t` Byzantine faults after `R` rounds.
* `Cslib.Distributed.Byzantine.Protocol.ownInput`: decide the own input, without communication.
* `Cslib.Distributed.Byzantine.Protocol.coverState`: runs on covering networks.

## Main results

* `Cslib.Distributed.Byzantine.Protocol.adaptiveState_eq_state`: a rushing adversary is no
  stronger than a fixed message table.
* `Cslib.Distributed.Byzantine.Protocol.SolvesByzantineAgreement.adaptive`: agreement and
  validity hold against rushing adversaries.
* `Cslib.Distributed.Byzantine.Protocol.SolvesByzantineAgreement.mono`: tolerating `t` faults
  implies tolerating fewer.
* `Cslib.Distributed.Byzantine.Protocol.solvesByzantineAgreement_ownInput`: a single process
  solves Byzantine agreement against any number of faults.
* `Cslib.Distributed.Byzantine.Protocol.state_eq_coverState`: the covering lemma.

## References

* [M. Pease, R. Shostak, L. Lamport, *Reaching agreement in the presence of
  faults*][PeaseShostakLamport1980]
* [M. J. Fischer, N. A. Lynch, M. Merritt, *Easy impossibility proofs for distributed consensus
  problems*][FischerLynchMerritt1985]
-/

public section

namespace Cslib.Distributed.Byzantine

/-- A deterministic synchronous message-passing protocol on the complete graph of processes `P`.

Process `i` with input bit `b` starts in state `init i b`. In round `r + 1` it sends
`send r i s j` to every process `j` (itself included) and then moves to `update r i s m`, where
`s` is its state and `m j` the message it received from `j`. Its decision in state `s` is
`output i s`. -/
structure Protocol (P State Msg : Type*) where
  /-- The initial state of a process with a given input bit. -/
  init : P → Bool → State
  /-- `send r i s j`: the message process `i` in state `s` sends to `j` in round `r + 1`. -/
  send : ℕ → P → State → P → Msg
  /-- `update r i s m`: the state of `i` after round `r + 1`, where `m j` came from `j`. -/
  update : ℕ → P → State → (P → Msg) → State
  /-- The decision of a process in a given state. -/
  output : P → State → Bool

namespace Protocol

variable {P S M : Type*} [DecidableEq P] (π : Protocol P S M)

/-- The state of process `i` after `r` rounds on inputs `x` when the processes in `F` are
faulty and a faulty `j` sends `adv r j i` to `i` in round `r + 1`. A faulty process's own state
evolves by the protocol, but nobody sees it: only its messages matter. -/
@[expose] def state (F : Finset P) (adv : ℕ → P → P → M) (x : P → Bool) : ℕ → P → S
  | 0, i => π.init i (x i)
  | r + 1, i => π.update r i (state F adv x r i)
      (fun j => if j ∈ F then adv r j i else π.send r j (state F adv x r j) i)

/-- The decision of process `i` after `R` rounds. -/
@[expose] def decision (F : Finset P) (adv : ℕ → P → P → M) (x : P → Bool) (R : ℕ) (i : P) :
    Bool :=
  π.output i (π.state F adv x R i)

/-- `π` solves Byzantine agreement against at most `t` faults in `R` rounds: whenever at most
`t` processes are faulty, whatever they send, the correct processes agree after `R` rounds, and
they decide `v` when all of them have input `v`
[Fischer, Lynch and Merritt, §3][FischerLynchMerritt1985]. -/
structure SolvesByzantineAgreement (t R : ℕ) : Prop where
  /-- Agreement: all correct processes decide the same value. -/
  agreement : ∀ F : Finset P, F.card ≤ t → ∀ (adv : ℕ → P → P → M) (x : P → Bool),
    ∀ i ∉ F, ∀ j ∉ F, π.decision F adv x R i = π.decision F adv x R j
  /-- Validity: if all correct processes have input `v`, they decide `v`. -/
  validity : ∀ F : Finset P, F.card ≤ t → ∀ (adv : ℕ → P → P → M) (x : P → Bool) (v : Bool),
    (∀ i ∉ F, x i = v) → ∀ i ∉ F, π.decision F adv x R i = v

/-- Tolerating `t` faults implies tolerating at most `t' ≤ t` faults. -/
theorem SolvesByzantineAgreement.mono {π : Protocol P S M} {t t' R : ℕ}
    (h : π.SolvesByzantineAgreement t R) (ht : t' ≤ t) : π.SolvesByzantineAgreement t' R where
  agreement F hF := h.agreement F (hF.trans ht)
  validity F hF := h.validity F (hF.trans ht)

/-- The state of process `i` after `r` rounds against a *rushing* adversary: in round `r + 1` a
faulty `j` sends `strat r σ j i` to `i`, where `σ` is the global state after `r` rounds, which
determines the messages of the correct processes in round `r + 1`. -/
@[expose] def adaptiveState (F : Finset P) (strat : ℕ → (P → S) → P → P → M) (x : P → Bool) :
    ℕ → P → S
  | 0, i => π.init i (x i)
  | r + 1, i => π.update r i (adaptiveState F strat x r i)
      (fun j => if j ∈ F then strat r (adaptiveState F strat x r) j i
        else π.send r j (adaptiveState F strat x r j) i)

/-- A rushing adversary is no stronger than a fixed table: the run against `strat` is the run
against the table of the messages that `strat` sends in it. -/
theorem adaptiveState_eq_state (F : Finset P) (strat : ℕ → (P → S) → P → P → M) (x : P → Bool) :
    ∀ r, π.adaptiveState F strat x r =
      π.state F (fun r j i => strat r (π.adaptiveState F strat x r) j i) x r
  | 0 => rfl
  | r + 1 => by
    funext i
    simp only [adaptiveState, state]
    rw [← adaptiveState_eq_state F strat x r]

/-- Agreement and validity hold against rushing adversaries as well. -/
theorem SolvesByzantineAgreement.adaptive {π : Protocol P S M} {t R : ℕ}
    (h : π.SolvesByzantineAgreement t R) {F : Finset P} (hF : F.card ≤ t)
    (strat : ℕ → (P → S) → P → P → M) (x : P → Bool) :
    (∀ i ∉ F, ∀ j ∉ F, π.output i (π.adaptiveState F strat x R i) =
      π.output j (π.adaptiveState F strat x R j)) ∧
    ∀ v, (∀ i ∉ F, x i = v) → ∀ i ∉ F, π.output i (π.adaptiveState F strat x R i) = v := by
  rw [π.adaptiveState_eq_state F strat x R]
  exact ⟨h.agreement F hF _ x, h.validity F hF _ x⟩

/-- The protocol in which every process decides its own input without communicating. -/
@[expose] def ownInput (P : Type*) : Protocol P Bool Unit where
  init _ b := b
  send _ _ _ _ := ()
  update _ _ s _ := s
  output _ s := s

/-- On at most one process, deciding the own input solves Byzantine agreement against any number
of faults, with any decision round `R`. -/
theorem solvesByzantineAgreement_ownInput {P : Type*} [DecidableEq P] [Subsingleton P]
    (t R : ℕ) : (ownInput P).SolvesByzantineAgreement t R := by
  have hstate : ∀ F adv x r i, (ownInput P).state F adv x r i = x i := by
    intro F adv x r i
    induction r with
    | zero => rfl
    | succ r ih => exact ih
  refine ⟨fun F _ adv x i _ j _ => by rw [Subsingleton.elim i j], fun F _ adv x v hv i hi => ?_⟩
  rw [decision, hstate]
  exact hv i hi

/-- The state of node `a` of a covering network after `r` rounds. Node `a` runs the code of
process `label a` on input `input a`, and receives the message of process `j` from node
`nbr a j`, which sends it as `j` would. In the covering networks of interest
`label (nbr a j) = j`, but the definition does not need this. -/
@[expose] def coverState {N : Type*} (label : N → P) (input : N → Bool) (nbr : N → P → N) :
    ℕ → N → S
  | 0, a => π.init (label a) (input a)
  | r + 1, a => π.update r (label a) (coverState label input nbr r a)
      (fun j => π.send r j (coverState label input nbr r (nbr a j)) (label a))

/-- **The covering lemma.** Suppose that the correct processes embed into a covering network by
`e`, preserving their code, their inputs and their mutual wiring, and that every faulty process
`j` sends to a correct `i` what the neighbour of `e i` standing for `j` sends. Then every correct
process `i` is in the same state as node `e i` after every round. This is the content of the
Locality and Fault axioms of [Fischer, Lynch and Merritt, §2][FischerLynchMerritt1985] in this
model. -/
theorem state_eq_coverState {N : Type*} (label : N → P) (input : N → Bool) (nbr : N → P → N)
    (F : Finset P) (adv : ℕ → P → P → M) (x : P → Bool) (e : P → N)
    (hlabel : ∀ i ∉ F, label (e i) = i) (hinput : ∀ i ∉ F, input (e i) = x i)
    (hnbr : ∀ i ∉ F, ∀ j ∉ F, nbr (e i) j = e j)
    (hadv : ∀ r, ∀ i ∉ F, ∀ j ∈ F,
      adv r j i = π.send r j (π.coverState label input nbr r (nbr (e i) j)) i) :
    ∀ r, ∀ i ∉ F, π.state F adv x r i = π.coverState label input nbr r (e i)
  | 0, i, hi => by simp only [state, coverState, hlabel i hi, hinput i hi]
  | r + 1, i, hi => by
    simp only [state, coverState, hlabel i hi]
    congr 1
    · exact state_eq_coverState label input nbr F adv x e hlabel hinput hnbr hadv r i hi
    · funext j
      split_ifs with hj
      · exact hadv r i hi j hj
      · rw [state_eq_coverState label input nbr F adv x e hlabel hinput hnbr hadv r j hj,
          hnbr i hi j hj]

end Protocol

end Cslib.Distributed.Byzantine
