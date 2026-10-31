/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Probability.PMF
import Complexity.Probability.PMF

/-!
# Sigma protocols

A Sigma protocol ([BonehShoup2023], Section 19.4) is a three-move protocol for a relation
`R : X → Y → Prop`: given a witness `x` for the statement `y`, the prover sends a commitment
`t`, the verifier replies with a uniformly random challenge `c` from a finite set, the prover
answers with a response `z`, and the verifier decides deterministically from `y` and the
conversation `(t, c, z)`.

The prover's private state between its two messages is explicit. Its commitment and state are
sampled together, and its response is a function of the state and the challenge; randomness the
response needs can be sampled with the commitment and kept in the state. Protocols are plain
functions and distributions, with no efficiency or finiteness assumption; the properties are
exact statements about a single protocol. The same holds for extractors and simulators: Boneh and
Shoup require them to be efficient algorithms (Definitions 19.4 and 19.5), but `SpecialSoundness`
and `SpecialHVZK` accept arbitrary functions and distributions, so neither makes an efficiency
claim. The efficient variants, `EfficientSpecialSoundness` and `EfficientSpecialHVZK` in
`Complexity.Crypto.Protocols.SigmaProtocol.Efficient`, add a polynomial-time extractor and a strict
PPT simulator over an indexed family of protocols.

Each property carries its algorithm explicitly. `SpecialSoundness R extract` says that the
deterministic `extract` computes a witness from any two accepting conversations that share a
commitment and have distinct challenges, for every statement, with or without a witness. The
extracted witness may have its own type and relation, as in lattice-based protocols, where
extraction yields a short solution of a relaxed relation rather than a prover's witness.
`SpecialHVZK R simulate` says that the simulator, given a statement and a challenge, always
outputs accepting conversations, and that for each witness-statement pair and *each* fixed
challenge its output has exactly the law of the honest commitment and response. With a uniform
challenge this gives the book's Definition 19.5 (`SpecialHVZK.conversation_eq`).

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol`: commitment, response and verification.
* `SigmaProtocol.transcript`, `SigmaProtocol.conversation`: honest executions.
* `SigmaProtocol.Complete`: honest conversations always accept.
* `SigmaProtocol.SpecialSoundness`: an explicit witness extractor (Definition 19.4).
* `SigmaProtocol.SpecialHVZK`: an explicit perfect simulator (Definition 19.5).

## Main results

* `SigmaProtocol.Complete.accepts_of_mem_support_conversation`: the verifier always accepts the
  honest prover.
* `SigmaProtocol.SpecialHVZK.conversation_eq`: a simulated conversation with a uniform
  challenge has the law of an honest one.
* `SigmaProtocol.SpecialSoundness.exists_witness`: two accepting conversations with a common
  commitment and distinct challenges certify that the statement has a witness.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 19.4.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols

open Probability

universe u

/-- A Sigma protocol with witnesses in `Witness`, statements in `Statement`, and conversations
`(t, c, z)` in `Commitment × Challenge × Response` ([BonehShoup2023], Definition 19.3).
Completeness and the security properties are separate predicates. -/
structure SigmaProtocol (Witness Statement Commitment Challenge Response : Type u) where
  /-- The prover's private state between its commitment and its response. -/
  State : Type u
  /-- Sample the commitment together with the prover's private state. -/
  commit : Witness → Statement → PMF (Commitment × State)
  /-- Answer a challenge from the private state. -/
  respond : Witness → Statement → State → Challenge → Response
  /-- The verifier's deterministic decision on a statement and a conversation. -/
  verify : Statement → Commitment → Challenge → Response → Bool

namespace SigmaProtocol

variable {X Y T C Z : Type u} (P : SigmaProtocol X Y T C Z)

/-- The conversation `(t, c, z)` is accepting for the statement `y`. -/
def Accepts (y : Y) (t : T) (c : C) (z : Z) : Prop := P.verify y t c z = true

instance (y : Y) (t : T) (c : C) (z : Z) : Decidable (P.Accepts y t c z) :=
  inferInstanceAs (Decidable (P.verify y t c z = true))

/-- The honest prover's commitment and response when the verifier sends the challenge `c`. -/
noncomputable def transcript (x : X) (y : Y) (c : C) : PMF (T × Z) :=
  (P.commit x y).map fun ts => (ts.1, P.respond x y ts.2 c)

/-- An honest execution: the prover commits, the verifier sends a uniform challenge, and the
prover responds. -/
noncomputable def conversation [Fintype C] [Nonempty C] (x : X) (y : Y) : PMF (T × C × Z) := do
  let ts ← P.commit x y
  let c ← PMF.uniformOfFintype C
  return (ts.1, c, P.respond x y ts.2 c)

/-- Completeness ([BonehShoup2023], Definition 19.3): for every witness-statement pair in `R`
and every challenge, every honest transcript is accepting. -/
def Complete (R : X → Y → Prop) : Prop :=
  ∀ x y, R x y → ∀ c, ∀ tz ∈ (P.transcript x y c).support, P.Accepts y tz.1 c tz.2

/-- Special soundness ([BonehShoup2023], Definition 19.4): `extract` returns a witness for any
statement from two accepting conversations with a common commitment and distinct challenges.
The extracted witness has a type `W` and a relation `R` of its own. Usually these are the
prover's witness type and relation; lattice-based protocols extract a witness of a relaxed
relation instead. The book requires an efficient deterministic extractor; `extract` here is an
arbitrary function, and `EfficientSpecialSoundness` adds the efficiency requirement. -/
def SpecialSoundness {W : Type*} (R : W → Y → Prop) (extract : Y → T → C → Z → C → Z → W) :
    Prop :=
  ∀ y t c z c' z', c ≠ c' → P.Accepts y t c z → P.Accepts y t c' z' →
    R (extract y t c z c' z') y

/-- Special honest-verifier zero knowledge ([BonehShoup2023], Definition 19.5) with the explicit
simulator `simulate`. The simulator gets a statement and a challenge and returns a commitment
and a response. The book requires an efficient probabilistic simulator; `simulate` here is an
arbitrary distribution-valued function, and `EfficientSpecialHVZK` adds the efficiency
requirement. -/
structure SpecialHVZK (R : X → Y → Prop) (simulate : Y → C → PMF (T × Z)) : Prop where
  /-- Simulated conversations are accepting, for every statement and challenge. -/
  accepts : ∀ y c, ∀ tz ∈ (simulate y c).support, P.Accepts y tz.1 c tz.2
  /-- For a witness-statement pair, simulation at any fixed challenge has the honest law. -/
  transcript_eq : ∀ x y, R x y → ∀ c, simulate y c = P.transcript x y c

variable {P} {R R' : X → Y → Prop}

/-- Completeness for a relation implies completeness for every smaller relation. -/
theorem Complete.mono (h : P.Complete R) (hR : ∀ x y, R' x y → R x y) : P.Complete R' :=
  fun x y hxy => h x y (hR x y hxy)

/-- A witness extractor for a relation is one for every larger relation. -/
theorem SpecialSoundness.mono {W : Type*} {R R' : W → Y → Prop}
    {extract : Y → T → C → Z → C → Z → W}
    (h : P.SpecialSoundness R extract) (hR : ∀ x y, R x y → R' x y) :
    P.SpecialSoundness R' extract :=
  fun y t c z c' z' hc hz hz' => hR _ _ (h y t c z c' z' hc hz hz')

/-- A simulator for a relation is one for every smaller relation. -/
theorem SpecialHVZK.mono {simulate : Y → C → PMF (T × Z)}
    (h : P.SpecialHVZK R simulate) (hR : ∀ x y, R' x y → R x y) :
    P.SpecialHVZK R' simulate :=
  ⟨h.accepts, fun x y hxy => h.transcript_eq x y (hR x y hxy)⟩

/-- Every possible honest commitment leads to an accepting response, whatever the
challenge. -/
theorem Complete.accepts_of_mem_support_commit (h : P.Complete R) {x : X} {y : Y}
    (hxy : R x y) {ts : T × P.State} (hts : ts ∈ (P.commit x y).support) (c : C) :
    P.Accepts y ts.1 c (P.respond x y ts.2 c) :=
  h x y hxy c _ ((PMF.mem_support_map_iff _ _ _).mpr ⟨ts, hts, rfl⟩)

/-- Special soundness certifies that the statement has a witness. -/
theorem SpecialSoundness.exists_witness {W : Type*} {R : W → Y → Prop}
    {extract : Y → T → C → Z → C → Z → W}
    (h : P.SpecialSoundness R extract) {y : Y} {t : T} {c c' : C} {z z' : Z} (hc : c ≠ c')
    (hz : P.Accepts y t c z) (hz' : P.Accepts y t c' z') : ∃ x, R x y :=
  ⟨_, h y t c z c' z' hc hz hz'⟩

variable (P)

/-- Continuing after an honest transcript is continuing after the commitment with the honest
response. -/
theorem transcript_bind {β : Type*} (x : X) (y : Y) (c : C) (next : T × Z → PMF β) :
    (P.transcript x y c).bind next =
      (P.commit x y).bind fun ts => next (ts.1, P.respond x y ts.2 c) :=
  PMF.bind_map _ _ _

/-- An honest execution samples the challenge first and then the prover's messages. -/
theorem conversation_eq_bind_transcript [Fintype C] [Nonempty C] (x : X) (y : Y) :
    P.conversation x y = do
      let c ← PMF.uniformOfFintype C
      let tz ← P.transcript x y c
      return (tz.1, c, tz.2) := by
  simp only [conversation, transcript, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_map]
  rw [PMF.bind_comm]
  rfl

variable {P}

/-- Every honest conversation is accepting: the verifier always accepts the honest prover. -/
theorem Complete.accepts_of_mem_support_conversation [Fintype C] [Nonempty C]
    (h : P.Complete R) {x : X} {y : Y} (hxy : R x y) {tcz : T × C × Z}
    (htcz : tcz ∈ (P.conversation x y).support) : P.Accepts y tcz.1 tcz.2.1 tcz.2.2 := by
  rw [conversation_eq_bind_transcript] at htcz
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at htcz
  obtain ⟨c, -, tz, htz, rfl⟩ := htcz
  exact h x y hxy c tz htz

/-- With a uniform challenge, the simulator reproduces the honest conversation law
([BonehShoup2023], Definition 19.5 (ii)). -/
theorem SpecialHVZK.conversation_eq [Fintype C] [Nonempty C] {simulate : Y → C → PMF (T × Z)}
    (h : P.SpecialHVZK R simulate) {x : X} {y : Y} (hxy : R x y) :
    P.conversation x y = do
      let c ← PMF.uniformOfFintype C
      let tz ← simulate y c
      return (tz.1, c, tz.2) := by
  rw [conversation_eq_bind_transcript]
  simp only [h.transcript_eq x y hxy]

end SigmaProtocol

end Cslib.Crypto.Protocols
