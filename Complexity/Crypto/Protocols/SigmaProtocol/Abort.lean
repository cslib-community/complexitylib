/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.SigmaProtocol.Basic
import Complexity.Probability.PMF

/-!
# Sigma protocols with aborts

In lattice-based Sigma protocols the prover may refuse to answer a challenge: in Lyubashevsky's
*Fiat–Shamir with aborts* ([Lyubashevsky2009], [Lyubashevsky2012]) it withholds every response
that would leak information about its witness. Such a protocol is an ordinary `SigmaProtocol`
whose responses are `Option Z`. The prover answers `none` to abort, and the verifier is expected
to reject `none`.

This module studies an *erased-abort projection*, not the full interactive verifier view.
An identification verifier has already seen the commitment before an abort; retrying does not
erase that observation. A signer can instead keep aborted attempts unpublished and retry with
fresh randomness. Full interactive-view simulation requires a separate theorem.
`acceptedTranscript x y c` is the honest commitment and response at the challenge `c`, erased to
`none` when the prover aborts. A simulator must reproduce the abort probability as well as the
law of the transcripts that are not aborted. Plain `SpecialHVZK` usually fails for these
protocols, because the commitment of an aborted run depends on the witness.

* `NonAbortComplete R`: every honest transcript in which the prover does not abort is accepting.
* `NonAbortSpecialHVZK R simulate`: the simulator outputs accepting transcripts or `none`, and for
  each witness-statement pair and each fixed challenge it has exactly the law of the accepted
  view.

These are the exact, per-challenge analogues of `Complete` and `SpecialHVZK`. Special soundness
needs no change: it only concerns accepting conversations, and `SpecialSoundness` applies as it
stands.

## Main definitions

* `SigmaProtocol.acceptedTranscript`, `SigmaProtocol.acceptedConversation`: honest executions
  with aborted runs erased.
* `SigmaProtocol.NonAbortComplete`: completeness up to aborts.
* `SigmaProtocol.NonAbortSpecialHVZK`: special honest-verifier zero knowledge up to aborts.

## Main results

* `SigmaProtocol.NonAbortComplete.accepts_of_mem_support_acceptedConversation`: published
  honest conversations are accepting.
* `SigmaProtocol.NonAbortSpecialHVZK.acceptedConversation_eq`: with a uniform challenge, the
  simulator reproduces the accepted view of an honest conversation, aborts included.

## References

* [V. Lyubashevsky, *Fiat-Shamir with Aborts: Applications to Lattice and Factoring-Based
  Signatures*][Lyubashevsky2009]
* [V. Lyubashevsky, *Lattice Signatures without Trapdoors*][Lyubashevsky2012]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 19.4.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability

universe u

variable {X Y T C Z : Type u} (P : SigmaProtocol X Y T C (Option Z))

/-- The honest commitment and response at the challenge `c`, or `none` if the prover aborts. -/
noncomputable def acceptedTranscript (x : X) (y : Y) (c : C) : PMF (Option (T × Z)) :=
  (P.transcript x y c).map fun tz => tz.2.map fun z => (tz.1, z)

/-- An honest conversation with a uniform challenge, or `none` if the prover aborts. -/
noncomputable def acceptedConversation [Fintype C] [Nonempty C] (x : X) (y : Y) :
    PMF (Option (T × C × Z)) :=
  (P.conversation x y).map fun tcz => (Prod.snd tcz.2).map fun z => (tcz.1, Prod.fst tcz.2, z)

/-- Completeness up to aborts: for every witness-statement pair in `R` and every challenge,
every honest transcript in which the prover does not abort is accepting. -/
def NonAbortComplete (R : X → Y → Prop) : Prop :=
  ∀ x y, R x y → ∀ c t z, some (t, z) ∈ (P.acceptedTranscript x y c).support →
    P.Accepts y t c (some z)

/-- Special honest-verifier zero knowledge up to aborts, with the explicit simulator `simulate`.
Given a statement and a challenge, the simulator returns a commitment and a response, or `none`
for an abort. -/
structure NonAbortSpecialHVZK (R : X → Y → Prop) (simulate : Y → C → PMF (Option (T × Z))) :
    Prop where
  /-- Simulated transcripts that are not aborted are accepting, for every statement and
  challenge. -/
  accepts : ∀ y c t z, some (t, z) ∈ (simulate y c).support → P.Accepts y t c (some z)
  /-- For a witness-statement pair, simulation at any fixed challenge has the law of the
  accepted view, aborts included. -/
  acceptedTranscript_eq : ∀ x y, R x y → ∀ c, simulate y c = P.acceptedTranscript x y c

variable {P} {R R' : X → Y → Prop}

/-- Completeness up to aborts for a relation implies it for every smaller relation. -/
theorem NonAbortComplete.mono (h : P.NonAbortComplete R) (hR : ∀ x y, R' x y → R x y) :
    P.NonAbortComplete R' :=
  fun x y hxy => h x y (hR x y hxy)

/-- A simulator up to aborts for a relation is one for every smaller relation. -/
theorem NonAbortSpecialHVZK.mono {simulate : Y → C → PMF (Option (T × Z))}
    (h : P.NonAbortSpecialHVZK R simulate) (hR : ∀ x y, R' x y → R x y) :
    P.NonAbortSpecialHVZK R' simulate :=
  ⟨h.accepts, fun x y hxy => h.acceptedTranscript_eq x y (hR x y hxy)⟩

variable (P)

/-- An honest execution with aborted runs erased samples the challenge first. -/
theorem acceptedConversation_eq_bind [Fintype C] [Nonempty C] (x : X) (y : Y) :
    P.acceptedConversation x y = do
      let c ← PMF.uniformOfFintype C
      let tz ← P.acceptedTranscript x y c
      return tz.map fun tz => (tz.1, c, tz.2) := by
  rw [acceptedConversation, conversation_eq_bind_transcript]
  simp only [acceptedTranscript, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind,
    PMF.pure_map, PMF.bind_map]
  congr 1
  funext c
  congr 1
  funext tz
  obtain ⟨t, _ | z⟩ := tz <;> rfl

variable {P}

/-- Every published honest conversation is accepting. -/
theorem NonAbortComplete.accepts_of_mem_support_acceptedConversation [Fintype C] [Nonempty C]
    (h : P.NonAbortComplete R) {x : X} {y : Y} (hxy : R x y) {t : T} {c : C} {z : Z}
    (htcz : some (t, c, z) ∈ (P.acceptedConversation x y).support) :
    P.Accepts y t c (some z) := by
  rw [acceptedConversation_eq_bind] at htcz
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at htcz
  obtain ⟨c', -, tz, htz, hsome⟩ := htcz
  cases tz with
  | none => cases hsome
  | some tz =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsome
    obtain ⟨rfl, rfl, rfl⟩ := hsome
    exact h x y hxy _ _ _ htz

/-- **Zero knowledge up to aborts.** With a uniform challenge, the simulator reproduces the
accepted view of an honest conversation: the abort probability, and the law of the published
conversations. -/
theorem NonAbortSpecialHVZK.acceptedConversation_eq [Fintype C] [Nonempty C]
    {simulate : Y → C → PMF (Option (T × Z))} (h : P.NonAbortSpecialHVZK R simulate) {x : X}
    {y : Y} (hxy : R x y) :
    P.acceptedConversation x y = do
      let c ← PMF.uniformOfFintype C
      let tz ← simulate y c
      return tz.map fun tz => (tz.1, c, tz.2) := by
  rw [acceptedConversation_eq_bind]
  simp only [h.acceptedTranscript_eq x y hxy]

end SigmaProtocol

end Cslib.Crypto.Protocols
