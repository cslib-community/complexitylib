/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman.Finite
public import CslibFrontier.Crypto.Protocols.MPC.Advantage
public import CslibFrontier.Crypto.Protocols.MPC.BatchOT
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Probability.Uniform.Translate

/-!
# Three-Message DDH 1-out-of-2 Oblivious Transfer

This module formalizes a three-message 1-out-of-2 oblivious transfer protocol from the Decision
Diffie-Hellman (DDH) assumption over a finite additive group `G` that is a `ZMod q`-module, with a
public element `g`, expressed as a two-party protocol `ddhOTProtocol` in
`Cslib.Crypto.Protocols.MPC` computing `otFunctionality G` (compatible with `batchOTSpec 1 G` from
`CslibFrontier/Crypto/Protocols/MPC/BatchOT.lean`). Groups are written additively, so the textbook
`g^a` is `a • g`. The protocol is a variant of the DDH-based protocol of [BonehShoup2023],
Section 23.5.7, Figure 23.17; DDH-based oblivious transfer of this kind goes back to
[NaorPinkas2001]. Its rounds are:

1. **Round 1 (`.message 0 1 G`):** The sender (party `0`) samples `a : ZMod q` and sends
   `u = a • g` to the receiver (party `1`).
2. **Round 2 (`.message 1 0 (G × G)`):** The receiver samples `b : ZMod q`, sets `v = b • g`,
   and sends `(w₀, w₁) = if σ then (u - v, v) else (v, u - v)` so that the chosen branch key
   `w_σ = v` has known discrete logarithm `b`, the unchosen branch key `w_{1-σ} = u - v` has
   unknown discrete logarithm, and `w₀ + w₁ = u`.
3. **Round 3 (`.message 0 1 ((G × G) × (G × G))`):** The sender checks `w₀ + w₁ = u`. If the check
   holds, it encrypts each branch `i ∈ {0, 1}` with fresh randomization coins
   `(rᵢ, sᵢ) : ZMod q × ZMod q` via `ddhOTEncryptBranch g u wᵢ mᵢ rᵢ sᵢ a` (since the sender holds
   `a` with `u = a • g`, this equals ElGamal encryption under `wᵢ` with exponent `rᵢ + a * sᵢ`;
   if the check fails, the sender sends zeros). The receiver decrypts its chosen ciphertext
   `(e_σ, c_σ)` as `c_σ - b • e_σ`.

## Differences from Figure 23.17

* In Figure 23.17 the sender samples its first message `d` uniformly from the group, without
  knowing its discrete logarithm. Here the sender samples `a` and sends `u = a • g`, so it
  knows the discrete logarithm of `u`.
* Figure 23.17 encrypts both branches with one exponent `β` and one first component `g^β`. Here
  each branch `i` has its own coins `(rᵢ, sᵢ)` and its own first component `rᵢ • g + sᵢ • u`.
* Figure 23.17 has no check. Here the sender checks `w₀ + w₁ = u`, the additive form of the check
  in [BonehShoup2023], Section 23.5.7.3, Remark 23.6, and sends zeros instead of aborting when the
  check fails. `ddhOTUncheckedProtocol` omits the check.
* Theorem 23.7 of [BonehShoup2023] is stated for Figure 23.17. The results below are proved
  directly for this variant.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.ddhOTSchedule`: the three-message point-to-point schedule.
* `Cslib.Crypto.Protocols.MPC.ddhOTProtocol`: the checked three-message DDH OT protocol.
* `Cslib.Crypto.Protocols.MPC.ddhOTUncheckedProtocol`: the variant omitting the `w₀ + w₁ = u`
  check.
* `Cslib.Crypto.Protocols.MPC.ddhOTSenderReplyOf`: the honest sender's Round 3 reply in a protocol
  along `ddhOTSchedule G`, for an arbitrary Round 2 message.
* `Cslib.Crypto.Protocols.MPC.ddhOTSenderSim`, `Cslib.Crypto.Protocols.MPC.ddhOTReceiverSim`: the
  semi-honest simulators for a corrupted sender (`{0}`) and a corrupted receiver (`{1}`).
* `Cslib.Crypto.Protocols.MPC.ddhOTReduction`: the DDH reduction induced by a receiver
  distinguisher.
* `Cslib.Crypto.Protocols.MPC.ddhOTUncheckedRealGame`,
  `Cslib.Crypto.Protocols.MPC.ddhOTUncheckedIdealGame`: the real and ideal games for a malicious
  receiver against `ddhOTUncheckedProtocol`.

## Main results

* `Cslib.Crypto.Protocols.MPC.ddhOT_output_of_mem_support`: **correctness** — in every execution of
  `ddhOTProtocol`, the receiver outputs `m_σ` and the sender outputs `()`.
* `Cslib.Crypto.Protocols.MPC.idealJoint_ddhOT_sender`,
  `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_ddhOT_sender`: **perfect sender privacy** — the
  ideal joint distribution with `ddhOTSenderSim` equals the real one, so every distinguisher has
  advantage zero.
* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_ddhOT_receiver_eq`: **receiver privacy as a
  per-instance equality** — when `g` generates `G` and `G` has `q` elements, a corrupted
  receiver's distinguishing advantage equals
  `Cslib.Crypto.ddhAdvantage q g (ddhOTReduction g q x D)`, the fixed-group DDH advantage of
  `CslibFrontier/Crypto/Computational/DiffieHellman/Finite.lean`. There is no security parameter
  and no efficiency certificate for `ddhOTReduction`, so this is not a computational privacy
  theorem.
* `Cslib.Crypto.Protocols.MPC.ddhOTSenderReply_eq_unchecked_of_add`,
  `Cslib.Crypto.Protocols.MPC.ddhOTSenderReply_eq_zero_of_add_ne`,
  `Cslib.Crypto.Protocols.MPC.ddhOTAttackBothMessages_eq`,
  `Cslib.Crypto.Protocols.MPC.succProbability_ddhOTUncheckedIdealGame_le`,
  `Cslib.Crypto.Protocols.MPC.ddhOTUnchecked_malicious_receiver_advantage`: **malicious-receiver
  attack on the unchecked variant** — a malicious receiver that sends `(b₀ • g, b₁ • g)` in
  Round 2 of `ddhOTUncheckedProtocol` recovers both `(m₀, m₁)` from one run. A simulator that
  chooses one query bit `τ` and receives only `m_τ` outputs both messages with probability at most
  `(Fintype.card G : ℝ)⁻¹`, so the advantage against every such simulator is at least
  `1 - (Fintype.card G : ℝ)⁻¹`.

## References

* [M. Naor and B. Pinkas, *Efficient Oblivious Transfer Protocols*][NaorPinkas2001]
* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 23.5.7 (Figure 23.17, Theorem 23.7, and Remark 23.6).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto
open scoped ENNReal NNReal

variable {G : Type} [AddCommGroup G]

/-! ### 1-out-of-2 Oblivious Transfer functionality and protocol syntax -/

/-- Per-party input types for 1-out-of-2 Oblivious Transfer over message type `M`:
party `0` (sender) holds `(m₀, m₁) : M × M` and party `1` (receiver) holds `σ : Bool`. -/
abbrev OTIn (M : Type) : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) (M × M) (fun _ => Bool) i

/-- Per-party output types for 1-out-of-2 Oblivious Transfer over message type `M`:
party `0` (sender) receives `Unit` and party `1` (receiver) receives `m_σ : M`. -/
abbrev OTOut (M : Type) : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) Unit (fun _ => M) i

/-- Deterministic output tuple of `otFunctionality M`: `()` for the sender and `m_σ` for the
receiver. -/
@[expose] def otOutputs {M : Type} (x : (i : Fin 2) → OTIn M i) : (i : Fin 2) → OTOut M i :=
  fun i => Fin.cases (motive := fun i => OTOut M i) ()
    (fun _ =>
      let σ : Bool := x 1
      if σ then (x 0).2 else (x 0).1) i

/-- Ideal functionality for 1-out-of-2 Oblivious Transfer over `M`. -/
@[expose] def otFunctionality (M : Type) : Functionality 2 (OTIn M) (OTOut M) :=
  Functionality.ofDeterministic otOutputs

/-- Convert a single-transfer input tuple `x : (i : Fin 2) → OTIn M i` into a query to
`batchOTSpec 1 M` from `CslibFrontier/Crypto/Protocols/MPC/BatchOT.lean`. -/
@[expose] def otInputToBatchOTQuery {M : Type} (x : (i : Fin 2) → OTIn M i)
    (s : Fin 2) : (batchOTSpec 1 M).Query () s :=
  Fin.cases (motive := fun s => (batchOTSpec 1 M).Query () s)
    (fun _ b => if b then (x 0).2 else (x 0).1)
    (fun _ _ => x 1)
    s

/-- `otOutputs` agrees with the single-transfer specialization `k = 1` of `batchOTAnswer`. -/
theorem otOutputs_eq_batchOTAnswer {M : Type} (x : (i : Fin 2) → OTIn M i) :
    otOutputs x 1 = batchOTAnswer (otInputToBatchOTQuery x) 1 0 :=
  rfl

/-- The sender's random coins in the DDH OT protocol: `(a, r₀, s₀, r₁, s₁) ∈ (ZMod q)⁵`. -/
abbrev DDHOTSenderCoins (q : ℕ) : Type :=
  ZMod q × ZMod q × ZMod q × ZMod q × ZMod q

/-- Per-party random coin types for the DDH OT protocol. -/
abbrev DDHOTCoins (q : ℕ) : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) (DDHOTSenderCoins q) (fun _ => ZMod q) i

/-- Sample the sender's five exponents uniformly from `ZMod q`. -/
@[expose] noncomputable def sampleDDHOTSenderCoins (q : ℕ) [NeZero q] :
    ProbComp (DDHOTSenderCoins q) := do
  let a ← ProbComp.uniform (ZMod q)
  let r₀ ← ProbComp.uniform (ZMod q)
  let s₀ ← ProbComp.uniform (ZMod q)
  let r₁ ← ProbComp.uniform (ZMod q)
  let s₁ ← ProbComp.uniform (ZMod q)
  return (a, r₀, s₀, r₁, s₁)

/-- Pair of sender and receiver coins as a dependent tuple over `Fin 2`. -/
@[expose] def ddhOTCoins {q : ℕ} (c₀ : DDHOTSenderCoins q) (b : ZMod q) :
    (i : Fin 2) → DDHOTCoins q i :=
  fun i => Fin.cases (motive := fun i => DDHOTCoins q i) c₀ (fun _ => b) i

/-- Three-message point-to-point schedule for the DDH OT protocol: sender to receiver (`G`),
receiver to sender (`G × G`), and sender to receiver (`(G × G) × (G × G)`). -/
abbrev ddhOTSchedule (G : Type) : Schedule 2 noOracleSpec :=
  [.message 0 1 G, .message 1 0 (G × G), .message 0 1 ((G × G) × (G × G))]

/-- Round 2 receiver message: given `u : G`, choice bit `σ : Bool`, and coin `b : ZMod q`,
outputs `(w₀, w₁)` with `w_σ = b • g` and `w_{1-σ} = u - b • g`. -/
@[expose] def ddhOTReceiverMsg {q : ℕ} [Module (ZMod q) G] (g : G) (σ : Bool) (b : ZMod q)
    (u : G) : G × G :=
  let v := b • g
  if σ then (u - v, v) else (v, u - v)

/-- Honest Round 2 receiver messages always satisfy the sender's check `w.1 + w.2 = u`. -/
theorem ddhOTReceiverMsg_add {q : ℕ} [Module (ZMod q) G] (g : G) (σ : Bool) (b : ZMod q)
    (u : G) : (ddhOTReceiverMsg g σ b u).1 + (ddhOTReceiverMsg g σ b u).2 = u := by
  cases σ <;> simp [ddhOTReceiverMsg]

/-- Encrypt a single branch message `m : G` under `(g, u, w)` using coins `(r, s)` and sender
exponent `a`. When `u = a • g`, this equals ElGamal encryption
`((r + a * s) • g, (r + a * s) • w + m)` under key `w`. -/
@[expose] def ddhOTEncryptBranch {q : ℕ} [Module (ZMod q) G] (g u w m : G) (r s a : ZMod q) :
    G × G :=
  (r • g + s • u, r • w + s • (a • w) + m)

/-- Decrypting an honestly encrypted branch with `w = b • g` and `u = a • g` recovers `m`. -/
theorem ddhOTReceiverOutput_encryptBranch {q : ℕ} [Module (ZMod q) G] (g m : G)
    (a b r s : ZMod q) :
    let u := a • g
    let w := b • g
    let ct := ddhOTEncryptBranch g u w m r s a
    ct.2 - b • ct.1 = m := by
  dsimp only [ddhOTEncryptBranch]
  module

/-- Algebraic identity for the chosen branch ciphertext in `ddhOTProtocol`. -/
private theorem chosen_branch_eq {q : ℕ} [Module (ZMod q) G] (g m : G) (a b r s : ZMod q) :
    ddhOTEncryptBranch g (a • g) (b • g) m r s a =
      let e := r • g + s • (a • g)
      (e, b • e + m) := by
  dsimp only [ddhOTEncryptBranch]
  refine Prod.ext rfl ?_
  dsimp only
  module

/-- Algebraic identity for the unchosen branch ciphertext in `ddhOTProtocol`. -/
private theorem unchosen_branch_eq {q : ℕ} [Module (ZMod q) G] (g m : G) (a b r s : ZMod q) :
    ddhOTEncryptBranch g (a • g) (a • g - b • g) m r s a =
      let u' := (r + a * s) • g
      let w_ddh := (a * (r + a * s)) • g
      (u', w_ddh - b • u' + m) := by
  dsimp only [ddhOTEncryptBranch]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> module

/-- Round 3 sender reply in the unchecked variant: omits the `w.1 + w.2 = u` verification. -/
@[expose] def ddhOTSenderReplyUnchecked {q : ℕ} [Module (ZMod q) G] (g : G) (m : G × G)
    (c : DDHOTSenderCoins q) (w : G × G) : (G × G) × (G × G) :=
  let (a, r₀, s₀, r₁, s₁) := c
  let u := a • g
  (ddhOTEncryptBranch g u w.1 m.1 r₀ s₀ a, ddhOTEncryptBranch g u w.2 m.2 r₁ s₁ a)

/-- Receiver output decryption: selects ciphertext `σ` and unmasks by subtracting `b • e_σ`. -/
@[expose] def ddhOTReceiverOutput {q : ℕ} [Module (ZMod q) G] (σ : Bool) (b : ZMod q)
    (reply : (G × G) × (G × G)) : G :=
  let ct := if σ then reply.2 else reply.1
  ct.2 - b • ct.1

/-- Final local state type at the end of `ddhOTSchedule G`. -/
abbrev DDHOTFinal (G : Type) (q : ℕ) (i : Fin 2) : Type :=
  (((OTIn G i × DDHOTCoins q i) ×
    (Round.message (spec := noOracleSpec) 0 1 G).Received i) ×
    (Round.message (spec := noOracleSpec) 1 0 (G × G)).Received i) ×
    (Round.message (spec := noOracleSpec) 0 1 ((G × G) × (G × G))).Received i

/-- Output extraction at the end of `ddhOTSchedule G`. -/
@[expose] def ddhOTOutput {q : ℕ} [Module (ZMod q) G] (i : Fin 2) (st : DDHOTFinal G q i) :
    OTOut G i :=
  Fin.cases (motive := fun i => DDHOTFinal G q i → OTOut G i)
    (fun _ => ())
    (fun j ((((σ, b), _), _), reply) => ddhOTReceiverOutput (G := G) σ b
      (reply (Fin.fin_one_eq_zero j ▸ rfl)))
    i st

/-- **Unchecked three-message DDH OT protocol**: `ddhOTProtocol` without the sender's
`w₀ + w₁ = u` check. [BonehShoup2023], Section 23.5.7.3, Remark 23.6 describes the
malicious-receiver attack that the check is meant to stop; `ddhOTUncheckedRealGame` runs that
attack against this protocol. -/
@[expose] noncomputable def ddhOTUncheckedProtocol (g : G) (q : ℕ) [NeZero q]
    [Module (ZMod q) G] :
    Protocol 2 noOracleSpec (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G) where
  sampleCoins i := Fin.cases (motive := fun i => ProbComp (DDHOTCoins q i))
    (sampleDDHOTSenderCoins q) (fun _ => ProbComp.uniform (ZMod q)) i
  steps :=
    .message (fun (_, (a, _)) => a • g)
      (.message (fun ((σ, b), u) => ddhOTReceiverMsg g σ b (u rfl))
        (.message (fun (((m, c), _), w) => ddhOTSenderReplyUnchecked g m c (w rfl))
          (.done ddhOTOutput)))

omit [AddCommGroup G] in
/-- The honest sender's Round 3 reply in a protocol `proto` along `ddhOTSchedule G`, on input `m`
and coins `c`, when the receiver's Round 2 message is `w`. The sender's local state is built as in
`Steps.run`; a malicious receiver may choose `w` freely. -/
@[expose] def ddhOTSenderReplyOf {q : ℕ}
    (proto : Protocol 2 noOracleSpec (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G))
    (m : G × G) (c : DDHOTSenderCoins q) (w : G × G) : (G × G) × (G × G) :=
  match proto.steps with
  | .message send₁ (.message _ (.message send₃ _)) =>
    send₃ (((m, c), fun _ => send₁ (m, c)), fun _ => w)

/-- The Round 3 reply of `ddhOTUncheckedProtocol` is `ddhOTSenderReplyUnchecked`. -/
theorem ddhOTSenderReplyOf_ddhOTUncheckedProtocol (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (m : G × G) (c : DDHOTSenderCoins q) (w : G × G) :
    ddhOTSenderReplyOf (ddhOTUncheckedProtocol g q) m c w = ddhOTSenderReplyUnchecked g m c w :=
  rfl

/-- Malicious Round 2 message `(b₀ • g, b₁ • g)` with known discrete logs `(b₀, b₁)`. -/
@[expose] def ddhOTAttackMsg {q : ℕ} [Module (ZMod q) G] (g : G) (b₀ b₁ : ZMod q) : G × G :=
  (b₀ • g, b₁ • g)

/-- Simultaneous decryption of both branches from the unchecked sender reply using `(b₀, b₁)`. -/
@[expose] def ddhOTAttackBothMessages {q : ℕ} [Module (ZMod q) G] (b₀ b₁ : ZMod q)
    (reply : (G × G) × (G × G)) : G × G :=
  let ((e₀, c₀), (e₁, c₁)) := reply
  (c₀ - b₀ • e₀, c₁ - b₁ • e₁)

/-- **Simultaneous recovery on the unchecked variant**: when the sender omits `w₀ + w₁ = u`,
a malicious receiver sending `ddhOTAttackMsg g b₀ b₁` recovers both `(m.1, m.2)` from
`ddhOTSenderReplyUnchecked`. -/
theorem ddhOTAttackBothMessages_eq {q : ℕ} [Module (ZMod q) G] (g : G) (m : G × G)
    (c₀ : DDHOTSenderCoins q) (b₀ b₁ : ZMod q) :
    ddhOTAttackBothMessages b₀ b₁
      (ddhOTSenderReplyUnchecked g m c₀ (ddhOTAttackMsg g b₀ b₁)) = m := by
  rcases c₀ with ⟨a, r₀, s₀, r₁, s₁⟩
  rcases m with ⟨m₀, m₁⟩
  dsimp only [ddhOTAttackBothMessages, ddhOTSenderReplyUnchecked, ddhOTAttackMsg]
  exact Prod.ext (ddhOTReceiverOutput_encryptBranch g m₀ a b₀ r₀ s₀)
    (ddhOTReceiverOutput_encryptBranch g m₁ a b₁ r₁ s₁)

variable [DecidableEq G]

/-- Round 3 sender reply in the checked protocol: verifies `w.1 + w.2 = a • g` before
encrypting `(m.1, m.2)`. -/
@[expose] def ddhOTSenderReply {q : ℕ} [Module (ZMod q) G] (g : G) (m : G × G)
    (c : DDHOTSenderCoins q) (w : G × G) : (G × G) × (G × G) :=
  let (a, r₀, s₀, r₁, s₁) := c
  let u := a • g
  if w.1 + w.2 = u then
    (ddhOTEncryptBranch g u w.1 m.1 r₀ s₀ a, ddhOTEncryptBranch g u w.2 m.2 r₁ s₁ a)
  else
    ((0, 0), (0, 0))

/-- When the receiver's Round 2 message satisfies `w.1 + w.2 = c.1 • g`, the checked sender
reply `ddhOTSenderReply` coincides with `ddhOTSenderReplyUnchecked`. -/
theorem ddhOTSenderReply_eq_unchecked_of_add {q : ℕ} [Module (ZMod q) G] (g : G) (m : G × G)
    (c : DDHOTSenderCoins q) (w : G × G) (hw : w.1 + w.2 = c.1 • g) :
    ddhOTSenderReply g m c w = ddhOTSenderReplyUnchecked g m c w := by
  rcases c with ⟨a, r₀, s₀, r₁, s₁⟩
  simp only [ddhOTSenderReply, ddhOTSenderReplyUnchecked, hw, ↓reduceIte]

/-- When the receiver's Round 2 message violates `w.1 + w.2 = c.1 • g`, the checked sender
reply `ddhOTSenderReply` aborts to `((0, 0), (0, 0))`. -/
theorem ddhOTSenderReply_eq_zero_of_add_ne {q : ℕ} [Module (ZMod q) G] (g : G) (m : G × G)
    (c : DDHOTSenderCoins q) (w : G × G) (hw : w.1 + w.2 ≠ c.1 • g) :
    ddhOTSenderReply g m c w = ((0, 0), (0, 0)) := by
  rcases c with ⟨a, r₀, s₀, r₁, s₁⟩
  simp only [ddhOTSenderReply, hw, ↓reduceIte]

/-- **Three-message DDH 1-out-of-2 Oblivious Transfer protocol**: a variant of [BonehShoup2023],
Section 23.5.7, Figure 23.17, with the check `w₀ + w₁ = u` from Remark 23.6. Unlike in
Figure 23.17, the sender knows the discrete logarithm `a` of its first message `u = a • g`
and encrypts each branch with its own coins `(rᵢ, sᵢ)`; the module docstring lists the
differences. -/
@[expose] noncomputable def ddhOTProtocol (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G] :
    Protocol 2 noOracleSpec (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G) where
  sampleCoins i := Fin.cases (motive := fun i => ProbComp (DDHOTCoins q i))
    (sampleDDHOTSenderCoins q) (fun _ => ProbComp.uniform (ZMod q)) i
  steps :=
    .message (fun (_, (a, _)) => a • g)
      (.message (fun ((σ, b), u) => ddhOTReceiverMsg g σ b (u rfl))
        (.message (fun (((m, c), _), w) => ddhOTSenderReply g m c (w rfl))
          (.done ddhOTOutput)))

/-! ### Party views and execution characterization -/

/-- The sender's `PartyView` from its input `x₀`, coins `c₀`, and received Round 2 message `w`. -/
@[expose] def ddhOTSenderView {q : ℕ} (x₀ : G × G) (c₀ : DDHOTSenderCoins q) (w : G × G) :
    PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) 0 where
  input := x₀
  coins := c₀
  received := (fun h => absurd h (by decide), (fun _ => w, (fun h => absurd h (by decide), ())))

/-- The receiver's `PartyView` from its input `σ`, coin `b`, Round 1 message `u`, and Round 3
reply `reply`. -/
@[expose] def ddhOTReceiverView {q : ℕ} (σ : Bool) (b : ZMod q) (u : G)
    (reply : (G × G) × (G × G)) :
    PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) 1 where
  input := σ
  coins := b
  received := (fun _ => u, (fun h => absurd h (by decide), (fun _ => reply, ())))

/-- Received transcript tuple in a run of `ddhOTProtocol` from initial local states `st`. -/
private def ddhOTReceived {q : ℕ} [Module (ZMod q) G] (g : G)
    (st : (i : Fin 2) → OTIn G i × DDHOTCoins q i) (i : Fin 2) :
    (ddhOTSchedule G).Received i :=
  let u := (st 0).2.1 • g
  let w := ddhOTReceiverMsg g (st 1).1 (st 1).2 u
  let reply := ddhOTSenderReply g (st 0).1 (st 0).2 w
  (Round.deliverMessage u i, (Round.deliverMessage w i, (Round.deliverMessage reply i, ())))

/-- The steps of `ddhOTProtocol` are deterministic once the coins are fixed. -/
private theorem evalWith_ddhOTSteps (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (st : (i : Fin 2) → OTIn G i × DDHOTCoins q i) :
    (ddhOTProtocol g q).steps.evalWith noOracleWorld st =
      PMF.pure (ddhOTReceived g st) := by
  dsimp only [ddhOTProtocol]
  refine (Steps.evalWith_message _ _ _ _).trans ?_
  refine (congrArg (PMF.map _) (Steps.evalWith_message _ _ _ _)).trans ?_
  refine (congrArg (PMF.map _ ∘ PMF.map _) (Steps.evalWith_message _ _ _ _)).trans ?_
  simp only [Function.comp_apply, Steps.evalWith_done, PMF.pure_map]
  rfl

/-- Independent coin sampling draws the sender's and receiver's coins. -/
private theorem eval_pi_ddhOTSampleCoins (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G] :
    ProbComp.eval (OracleComp.pi (ddhOTProtocol g q).sampleCoins) =
      (ProbComp.eval (sampleDDHOTSenderCoins q)).bind fun c₀ =>
        (PMF.uniformOfFintype (ZMod q)).map fun b => ddhOTCoins c₀ b := by
  have h1 : ProbComp.eval ((ddhOTProtocol g q).sampleCoins (Fin.succ 0)) =
      (PMF.uniformOfFintype (ZMod q) : PMF (DDHOTCoins q (Fin.succ 0))) :=
    ProbComp.eval_uniform (α := ZMod q)
  simp only [OracleComp.pi_succ, OracleComp.pi_zero, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, h1]
  refine congrArg (PMF.bind _) (funext fun c₀ => ?_)
  erw [PMF.map_bind]
  simp only [PMF.pure_map]
  rw [← PMF.bind_pure_comp]
  refine congrArg (PMF.bind _) (funext fun b => congrArg PMF.pure
    (funext (β := DDHOTCoins q) fun i => ?_))
  fin_cases i <;> rfl

/-- Receiver's view in a run with coins `(c₀, b)`. -/
private theorem ddhOTReceived_one {q : ℕ} [Module (ZMod q) G] (g : G)
    (x : (i : Fin 2) → OTIn G i)
    (c₀ : DDHOTSenderCoins q) (b : ZMod q) :
    (⟨x 1, ddhOTCoins c₀ b 1, ddhOTReceived g (fun i => (x i, ddhOTCoins c₀ b i)) 1⟩ :
        PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) 1) =
      let u := c₀.1 • g
      let w := ddhOTReceiverMsg g (x 1) b u
      ddhOTReceiverView (x 1) b u (ddhOTSenderReply g (x 0) c₀ w) := by
  refine PartyView.ext rfl rfl (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl)))
  · exact Round.received_message_ext fun _ => rfl
  · exact Round.received_message_eq_of_ne (by decide) _ _
  · exact Round.received_message_ext fun _ => rfl

/-- Sender's view in a run with coins `(c₀, b)`. -/
private theorem ddhOTReceived_zero {q : ℕ} [Module (ZMod q) G] (g : G)
    (x : (i : Fin 2) → OTIn G i)
    (c₀ : DDHOTSenderCoins q) (b : ZMod q) :
    (⟨x 0, ddhOTCoins c₀ b 0, ddhOTReceived g (fun i => (x i, ddhOTCoins c₀ b i)) 0⟩ :
        PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) 0) =
      ddhOTSenderView (x 0) c₀ (ddhOTReceiverMsg g (x 1) b (c₀.1 • g)) := by
  refine PartyView.ext rfl rfl (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl)))
  · exact Round.received_message_eq_of_ne (by decide) _ _
  · exact Round.received_message_ext fun _ => rfl
  · exact Round.received_message_eq_of_ne (by decide) _ _

/-! ### Correctness -/

/-- In a run with coins `(c₀, b)`, the receiver outputs `otOutputs x 1`. -/
private theorem outputOfView_ddhOT_one (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (x : (i : Fin 2) → OTIn G i) (c₀ : DDHOTSenderCoins q) (b : ZMod q) :
    (ddhOTProtocol g q).outputOfView 1
        ⟨x 1, ddhOTCoins c₀ b 1, ddhOTReceived g (fun i => (x i, ddhOTCoins c₀ b i)) 1⟩ =
      otOutputs x 1 := by
  rcases c₀ with ⟨a, r₀, s₀, r₁, s₁⟩
  let σ : Bool := x 1
  change ddhOTReceiverOutput σ b
    (ddhOTSenderReply g (x 0) (a, r₀, s₀, r₁, s₁)
      (ddhOTReceiverMsg g σ b (a • g))) =
    if σ then (x 0).2 else (x 0).1
  simp only [ddhOTSenderReply, ddhOTReceiverMsg_add, ↓reduceIte, ddhOTReceiverOutput]
  cases σ
  · simp only [Bool.false_eq_true, ↓reduceIte, ddhOTReceiverMsg]
    exact ddhOTReceiverOutput_encryptBranch g (x 0).1 a b r₀ s₀
  · simp only [↓reduceIte, ddhOTReceiverMsg]
    exact ddhOTReceiverOutput_encryptBranch g (x 0).2 a b r₁ s₁

/-- Full execution distribution of `ddhOTProtocol` in terms of the sampled coins. -/
private theorem evalWith_ddhOT (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (x : (i : Fin 2) → OTIn G i) :
    (ddhOTProtocol g q).evalWith noOracleWorld x =
      (ProbComp.eval (sampleDDHOTSenderCoins q)).bind fun c₀ =>
        (PMF.uniformOfFintype (ZMod q)).map fun b =>
          (fun i => ⟨x i, ddhOTCoins c₀ b i, ddhOTReceived g (fun i => (x i, ddhOTCoins c₀ b i)) i⟩,
            otOutputs x) := by
  rw [Protocol.evalWith_eq, eval_pi_ddhOTSampleCoins]
  simp only [evalWith_ddhOTSteps, PMF.bind_bind, PMF.bind_map, PMF.pure_map]
  refine congrArg (ProbComp.eval (sampleDDHOTSenderCoins q)).bind (funext fun c₀ => ?_)
  rw [← PMF.bind_pure_comp]
  refine congrArg (PMF.uniformOfFintype (ZMod q)).bind
    (funext fun b => congrArg PMF.pure (Prod.ext rfl ?_))
  funext i
  fin_cases i
  · rfl
  · exact outputOfView_ddhOT_one g q x c₀ b

/-- **Correctness**: in every execution of `ddhOTProtocol`, the sender outputs `()` and the
receiver outputs `if x 1 then (x 0).2 else (x 0).1`. -/
theorem ddhOT_output_of_mem_support (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (x : (i : Fin 2) → OTIn G i)
    {r : ((i : Fin 2) → PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i)}
    (hr : r ∈ ((ddhOTProtocol g q).evalWith noOracleWorld x).support) :
    r.2 = otOutputs x := by
  rw [evalWith_ddhOT, PMF.mem_support_bind_iff] at hr
  obtain ⟨c₀, _, hr⟩ := hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨b, _, rfl⟩ := hr
  rfl

/-! ### Perfect privacy against a corrupted sender -/

/-- Simulator for a corrupted sender (`{0}`): samples fresh sender coins `c₀` and a uniform
`b : ZMod q`, and sets the Round 2 message to `(b • g, c₀.1 • g - b • g)`. -/
@[expose] noncomputable def ddhOTSenderSim (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G] :
    CoalitionSimulator (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G) {0} :=
  fun xI _ => do
    let c₀ ← sampleDDHOTSenderCoins q
    let b ← ProbComp.uniform (ZMod q)
    let u := c₀.1 • g
    let v := b • g
    return singletonView (ddhOTSenderView (xI ⟨0, Finset.mem_singleton_self 0⟩) c₀ (v, u - v))

/-- Real joint distribution for a corrupted sender (`{0}`). -/
theorem realJoint_ddhOT_sender (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (x : (i : Fin 2) → OTIn G i) :
    (ddhOTProtocol g q).realJoint noOracleWorld {0} x =
      (ProbComp.eval (sampleDDHOTSenderCoins q)).bind fun c₀ =>
        (PMF.uniformOfFintype (ZMod q)).map fun b =>
          (singletonView (ddhOTSenderView (x 0) c₀ (ddhOTReceiverMsg g (x 1) b (c₀.1 • g))),
            otOutputs x) := by
  rw [Protocol.realJoint, evalWith_ddhOT, PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun c₀ => ?_)
  rw [PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun b => ?_)
  simp only [Function.comp_apply, Prod.map, id, restrict_singleton]
  rw [ddhOTReceived_zero]

/-- **Perfect privacy against a corrupted sender**: the ideal joint distribution with
`ddhOTSenderSim` equals the real joint distribution. -/
theorem idealJoint_ddhOT_sender (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (x : (i : Fin 2) → OTIn G i) :
    ProbComp.eval (idealJoint (otFunctionality G) {0} (ddhOTSenderSim g q) x) =
      (ddhOTProtocol g q).realJoint noOracleWorld {0} x := by
  rw [realJoint_ddhOT_sender]
  simp only [idealJoint, otFunctionality, Functionality.ofDeterministic, ddhOTSenderSim,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.pure_bind, PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun c₀ => ?_)
  rw [← PMF.bind_pure_comp]
  let σ : Bool := x 1
  change (PMF.uniformOfFintype (ZMod q)).bind (fun b =>
      PMF.pure (singletonView (ddhOTSenderView (x 0) c₀
        (b • g, c₀.1 • g - b • g)), otOutputs x)) =
    (PMF.uniformOfFintype (ZMod q)).bind (fun b =>
      PMF.pure (singletonView (ddhOTSenderView (x 0) c₀
        (ddhOTReceiverMsg g σ b (c₀.1 • g))), otOutputs x))
  cases σ
  · rfl
  · conv_lhs => rw [← PMF.uniformOfFintype_map_sub_left c₀.1, PMF.bind_map]
    refine congrArg (PMF.bind _) (funext fun b => ?_)
    simp only [Function.comp_apply, ddhOTReceiverMsg, ↓reduceIte,
      sub_smul, sub_sub_cancel]

/-- A corrupted sender has advantage zero against every distinguisher. -/
theorem semiHonestAdvantage_ddhOT_sender (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (x : (i : Fin 2) → OTIn G i)
    (D : ((i : ({0} : Finset (Fin 2))) →
        PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i) → ProbComp Bool) :
    semiHonestAdvantage (ddhOTProtocol g q) noOracleWorld (otFunctionality G) {0}
      (ddhOTSenderSim g q) x D = 0 :=
  (semiHonestAdvantage_eq_zero_iff _ _ _ _ _ x).mpr (idealJoint_ddhOT_sender g q x) D

/-! ### Computational privacy against a corrupted receiver under DDH -/

/-- DDH reduction for receiver privacy: given a DDH challenge `(u, u', w_ddh)`, embeds it into
the unchosen branch ciphertext and runs `D` on the resulting receiver view and outputs. It is a
distinguisher for `Cslib.Crypto.ddhRealExperiment` and `Cslib.Crypto.ddhRandomExperiment`. -/
@[expose] noncomputable def ddhOTReduction (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (x : (i : Fin 2) → OTIn G i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i) → ProbComp Bool)
    (u u' w_ddh : G) : ProbComp Bool := do
  let b ← ProbComp.uniform (ZMod q)
  let r ← ProbComp.uniform (ZMod q)
  let s ← ProbComp.uniform (ZMod q)
  let σ : Bool := x 1
  let e_σ := r • g + s • u
  let m_σ := if σ then (x 0).2 else (x 0).1
  let m_other := if σ then (x 0).1 else (x 0).2
  let c_σ := b • e_σ + m_σ
  let c_other := w_ddh - b • u' + m_other
  let reply := if σ then ((u', c_other), (e_σ, c_σ)) else ((e_σ, c_σ), (u', c_other))
  D (singletonView (ddhOTReceiverView σ b u reply), otOutputs x)

/-- Collapsing `(r₁, s₁)` into a single uniform exponent `k = r₁ + a * s₁` when `(r₀, s₀)` is on
the chosen branch. -/
private theorem bind_unchosen_right {q : ℕ} [NeZero q] (a : ZMod q)
    (f : ZMod q → ZMod q → ZMod q → PMF Bool) :
    (PMF.uniformOfFintype (ZMod q)).bind (fun r₀ =>
      (PMF.uniformOfFintype (ZMod q)).bind (fun s₀ =>
        (PMF.uniformOfFintype (ZMod q)).bind (fun r₁ =>
          (PMF.uniformOfFintype (ZMod q)).bind (fun s₁ =>
            f r₀ s₀ (r₁ + a * s₁))))) =
    (PMF.uniformOfFintype (ZMod q)).bind (fun k =>
      (PMF.uniformOfFintype (ZMod q)).bind (fun r₀ =>
        (PMF.uniformOfFintype (ZMod q)).bind (fun s₀ =>
          f r₀ s₀ k))) := by
  have hinner : ∀ r₀ s₀ : ZMod q,
      (PMF.uniformOfFintype (ZMod q)).bind (fun r₁ =>
        (PMF.uniformOfFintype (ZMod q)).bind (fun s₁ => f r₀ s₀ (r₁ + a * s₁))) =
      (PMF.uniformOfFintype (ZMod q)).bind (fun k => f r₀ s₀ k) := fun r₀ s₀ => by
    rw [PMF.bind_comm]
    have hconst : ∀ s₁ : ZMod q,
        (PMF.uniformOfFintype (ZMod q)).bind (fun r₁ => f r₀ s₀ (r₁ + a * s₁)) =
        (PMF.uniformOfFintype (ZMod q)).bind (fun k => f r₀ s₀ k) := fun s₁ => by
      exact PMF.uniformOfFintype_bind_add_right (a * s₁) (f r₀ s₀)
    simp_rw [hconst]
    ext c
    simp only [PMF.bind_apply, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  simp_rw [hinner]
  trans (PMF.uniformOfFintype (ZMod q)).bind (fun r₀ =>
    (PMF.uniformOfFintype (ZMod q)).bind (fun k =>
      (PMF.uniformOfFintype (ZMod q)).bind (fun s₀ => f r₀ s₀ k)))
  · refine congrArg (PMF.bind _) (funext fun r₀ => ?_)
    rw [PMF.bind_comm]
  · rw [PMF.bind_comm]

/-- Collapsing `(r₀, s₀)` into a single uniform exponent `k = r₀ + a * s₀` when `(r₁, s₁)` is on
the chosen branch. -/
private theorem bind_unchosen_left {q : ℕ} [NeZero q] (a : ZMod q)
    (f : ZMod q → ZMod q → ZMod q → PMF Bool) :
    (PMF.uniformOfFintype (ZMod q)).bind (fun r₀ =>
      (PMF.uniformOfFintype (ZMod q)).bind (fun s₀ =>
        (PMF.uniformOfFintype (ZMod q)).bind (fun r₁ =>
          (PMF.uniformOfFintype (ZMod q)).bind (fun s₁ =>
            f r₁ s₁ (r₀ + a * s₀))))) =
    (PMF.uniformOfFintype (ZMod q)).bind (fun k =>
      (PMF.uniformOfFintype (ZMod q)).bind (fun r₁ =>
        (PMF.uniformOfFintype (ZMod q)).bind (fun s₁ =>
          f r₁ s₁ k))) := by
  rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod q))]
  have hconst : ∀ s₀ : ZMod q,
      (PMF.uniformOfFintype (ZMod q)).bind (fun r₀ =>
        (PMF.uniformOfFintype (ZMod q)).bind (fun r₁ =>
          (PMF.uniformOfFintype (ZMod q)).bind (fun s₁ => f r₁ s₁ (r₀ + a * s₀)))) =
      (PMF.uniformOfFintype (ZMod q)).bind (fun k =>
        (PMF.uniformOfFintype (ZMod q)).bind (fun r₁ =>
          (PMF.uniformOfFintype (ZMod q)).bind (fun s₁ => f r₁ s₁ k))) := fun s₀ => by
    exact PMF.uniformOfFintype_bind_add_right (a * s₀) fun k =>
      (PMF.uniformOfFintype (ZMod q)).bind fun r₁ =>
        (PMF.uniformOfFintype (ZMod q)).bind fun s₁ => f r₁ s₁ k
  simp_rw [hconst]
  ext c
  simp only [PMF.bind_apply, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Moving the fifth independent bind over `p` to the front of four binds over `p`. -/
private theorem bind_four_comm {α β : Type} (p : PMF α) (f : α → α → α → α → α → PMF β) :
    p.bind (fun r₀ => p.bind (fun s₀ => p.bind (fun r₁ => p.bind (fun s₁ => p.bind (fun b =>
      f r₀ s₀ r₁ s₁ b))))) =
    p.bind (fun b => p.bind (fun r₀ => p.bind (fun s₀ => p.bind (fun r₁ => p.bind (fun s₁ =>
      f r₀ s₀ r₁ s₁ b))))) := by
  simp_rw [PMF.bind_comm p p (fun s₁ b => f _ _ _ s₁ b),
    PMF.bind_comm p p (fun r₁ b => p.bind fun s₁ => f _ _ r₁ s₁ b),
    PMF.bind_comm p p (fun s₀ b => p.bind fun r₁ => p.bind fun s₁ => f _ s₀ r₁ s₁ b),
    PMF.bind_comm p p (fun r₀ b =>
      p.bind fun s₀ => p.bind fun r₁ => p.bind fun s₁ => f r₀ s₀ r₁ s₁ b)]

/-- The real execution for a corrupted receiver is the real DDH world
`Cslib.Crypto.ddhRealExperiment q g` run on `ddhOTReduction`. -/
theorem real_receiver_eq_ddhRealExperiment (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (x : (i : Fin 2) → OTIn G i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i) → ProbComp Bool) :
    ((ddhOTProtocol g q).realJoint noOracleWorld {1} x).bind (fun r => ProbComp.eval (D r)) =
      ProbComp.eval (ddhRealExperiment q g (ddhOTReduction g q x D)) := by
  rw [Protocol.realJoint, evalWith_ddhOT, PMF.bind_map]
  simp only [sampleDDHOTSenderCoins, ddhRealExperiment, ddhOTReduction,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.bind_bind, PMF.pure_bind, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun a => ?_)
  let σ : Bool := x 1
  trans (PMF.uniformOfFintype (ZMod q)).bind (fun b =>
    (PMF.uniformOfFintype (ZMod q)).bind (fun r₀ =>
      (PMF.uniformOfFintype (ZMod q)).bind (fun s₀ =>
        (PMF.uniformOfFintype (ZMod q)).bind (fun r₁ =>
          (PMF.uniformOfFintype (ZMod q)).bind (fun s₁ =>
            ProbComp.eval (D (singletonView (ddhOTReceiverView σ b (a • g)
              (ddhOTSenderReply g (x 0) (a, r₀, s₀, r₁, s₁)
                (ddhOTReceiverMsg g σ b (a • g)))), otOutputs x)))))))
  · rw [bind_four_comm]
    refine congrArg (PMF.bind _) (funext fun b =>
      congrArg (PMF.bind _) (funext fun r₀ =>
        congrArg (PMF.bind _) (funext fun s₀ =>
          congrArg (PMF.bind _) (funext fun r₁ =>
            congrArg (PMF.bind _) (funext fun s₁ => ?_)))))
    simp only [Function.comp_apply, Prod.map, id, restrict_singleton, ddhOTReceived_one]
    rfl
  · conv_rhs => rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod q))]
    refine congrArg (PMF.bind _) (funext fun b => ?_)
    change (PMF.uniformOfFintype (ZMod q)).bind (fun r₀ =>
        (PMF.uniformOfFintype (ZMod q)).bind (fun s₀ =>
          (PMF.uniformOfFintype (ZMod q)).bind (fun r₁ =>
            (PMF.uniformOfFintype (ZMod q)).bind (fun s₁ =>
              ProbComp.eval (D (singletonView (ddhOTReceiverView σ b (a • g)
                (ddhOTSenderReply g (x 0) (a, r₀, s₀, r₁, s₁)
                  (ddhOTReceiverMsg g σ b (a • g)))), otOutputs x)))))) =
      (PMF.uniformOfFintype (ZMod q)).bind (fun k =>
        (PMF.uniformOfFintype (ZMod q)).bind (fun r =>
          (PMF.uniformOfFintype (ZMod q)).bind (fun s =>
            let u := a • g
            let u' := k • g
            let w_ddh := (a * k) • g
            let e_σ := r • g + s • u
            let m_σ := if σ then (x 0).2 else (x 0).1
            let m_other := if σ then (x 0).1 else (x 0).2
            let c_σ := b • e_σ + m_σ
            let c_other := w_ddh - b • u' + m_other
            let reply := if σ then ((u', c_other), (e_σ, c_σ)) else ((e_σ, c_σ), (u', c_other))
            ProbComp.eval (D (singletonView (ddhOTReceiverView σ b u reply), otOutputs x)))))
    simp only [ddhOTSenderReply, ddhOTReceiverMsg_add, ↓reduceIte]
    cases σ
    · simp only [ddhOTReceiverMsg, ↓reduceIte,
        Bool.false_eq_true, chosen_branch_eq, unchosen_branch_eq]
      exact bind_unchosen_right a (fun r₀ s₀ k =>
        let u := a • g
        let u' := k • g
        let w_ddh := (a * k) • g
        let e_σ := r₀ • g + s₀ • u
        let c_σ := b • e_σ + (x 0).1
        let c_other := w_ddh - b • u' + (x 0).2
        ProbComp.eval (D (singletonView (ddhOTReceiverView false b u
          ((e_σ, c_σ), (u', c_other))), otOutputs x)))
    · simp only [ddhOTReceiverMsg, ↓reduceIte,
        chosen_branch_eq, unchosen_branch_eq]
      exact bind_unchosen_left a (fun r₁ s₁ k =>
        let u := a • g
        let u' := k • g
        let w_ddh := (a * k) • g
        let e_σ := r₁ • g + s₁ • u
        let c_σ := b • e_σ + (x 0).2
        let c_other := w_ddh - b • u' + (x 0).1
        ProbComp.eval (D (singletonView (ddhOTReceiverView true b u
          ((u', c_other), (e_σ, c_σ))), otOutputs x)))

variable [Fintype G]

/-- Simulator for a corrupted receiver (`{1}`): given the receiver's choice bit `σ` and ideal
output `m_σ`, samples `a, b, r, s : ZMod q` and uniform `u', w' : G` for the unchosen branch,
and constructs `(e_σ, b • e_σ + m_σ)` on the chosen branch and `(u', w')` on the unchosen
branch. -/
@[expose] noncomputable def ddhOTReceiverSim (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G] :
    CoalitionSimulator (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G) {1} :=
  fun xI yI => do
    let σ : Bool := xI ⟨1, Finset.mem_singleton_self 1⟩
    let m_σ : G := yI ⟨1, Finset.mem_singleton_self 1⟩
    let a ← ProbComp.uniform (ZMod q)
    let b ← ProbComp.uniform (ZMod q)
    let r ← ProbComp.uniform (ZMod q)
    let s ← ProbComp.uniform (ZMod q)
    let u' ← ProbComp.uniform G
    let w' ← ProbComp.uniform G
    let u := a • g
    let e_σ := r • g + s • u
    let c_σ := b • e_σ + m_σ
    let reply := if σ then ((u', w'), (e_σ, c_σ)) else ((e_σ, c_σ), (u', w'))
    return singletonView (ddhOTReceiverView σ b u reply)

/-- Moving two outer binds over `p` inside three inner binds over `p`. -/
private theorem bind_two_three_comm {α β : Type} (p : PMF α) (f : α → α → α → α → α → PMF β) :
    p.bind (fun x₁ => p.bind (fun x₂ => p.bind (fun y₁ => p.bind (fun y₂ => p.bind (fun y₃ =>
      f x₁ x₂ y₁ y₂ y₃))))) =
    p.bind (fun y₁ => p.bind (fun y₂ => p.bind (fun y₃ => p.bind (fun x₁ => p.bind (fun x₂ =>
      f x₁ x₂ y₁ y₂ y₃))))) := by
  simp_rw [PMF.bind_comm p p (fun x₂ y₁ => p.bind fun y₂ => p.bind fun y₃ => f _ x₂ y₁ y₂ y₃),
    PMF.bind_comm p p (fun x₂ y₂ => p.bind fun y₃ => f _ x₂ _ y₂ y₃),
    PMF.bind_comm p p (fun x₂ y₃ => f _ x₂ _ _ y₃),
    PMF.bind_comm p p (fun x₁ y₁ =>
      p.bind fun y₂ => p.bind fun y₃ => p.bind fun x₂ => f x₁ x₂ y₁ y₂ y₃),
    PMF.bind_comm p p (fun x₁ y₂ => p.bind fun y₃ => p.bind fun x₂ => f x₁ x₂ _ y₂ y₃),
    PMF.bind_comm p p (fun x₁ y₃ => p.bind fun x₂ => f x₁ x₂ _ _ y₃)]

omit [DecidableEq G] in
/-- When `g` generates `G` and `G` has `q` elements, the ideal execution for a corrupted receiver
is the random DDH world `Cslib.Crypto.ddhRandomExperiment q g` run on `ddhOTReduction`. -/
theorem ideal_receiver_eq_ddhRandomExperiment (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (hcard : Fintype.card G = q) (hgen : ∀ y : G, ∃ k : ZMod q, k • g = y)
    (x : (i : Fin 2) → OTIn G i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i) → ProbComp Bool) :
    ProbComp.eval (idealJoint (otFunctionality G) {1} (ddhOTReceiverSim g q) x >>= D) =
      ProbComp.eval (ddhRandomExperiment q g (ddhOTReduction g q x D)) := by
  have hg : Function.Bijective fun c : ZMod q => c • g :=
    (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hgen, by rw [ZMod.card, hcard]⟩
  simp only [idealJoint, otFunctionality, Functionality.ofDeterministic, ddhOTReceiverSim,
    ddhRandomExperiment, ddhOTReduction, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.pure_bind, PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun a => ?_)
  rw [bind_two_three_comm]
  refine congrArg (PMF.bind _) (funext fun b =>
    congrArg (PMF.bind _) (funext fun r =>
      congrArg (PMF.bind _) (funext fun s => ?_)))
  rw [← uniformOfFintype_bind_smul hg]
  refine congrArg (PMF.bind _) (funext fun b_ddh => ?_)
  let σ : Bool := x 1
  let m_other : G := if σ then (x 0).1 else (x 0).2
  let u' := b_ddh • g
  let e_shift : G ≃ G :=
    { toFun := fun w => w - b • u' + m_other
      invFun := fun w => w - m_other + b • u'
      left_inv := fun w => by dsimp; rw [add_sub_cancel_right, sub_add_cancel]
      right_inv := fun w => by dsimp; rw [add_sub_cancel_right, sub_add_cancel] }
  rw [← PMF.uniformOfFintype_map_equiv e_shift, PMF.bind_map, ← uniformOfFintype_bind_smul hg]
  rfl

/-- **Privacy against a corrupted receiver, as a per-instance equality**: for a fixed group, input
and distinguisher, the distinguisher's advantage between the ideal joint distribution with
`ddhOTReceiverSim` and the real one equals the fixed-group DDH advantage of `ddhOTReduction`, when
`g` generates `G` and `G` has `q` elements. This is not a computational privacy theorem: there is
no security parameter, and `ddhOTReduction` has no efficiency certificate. -/
theorem semiHonestAdvantage_ddhOT_receiver_eq (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (hcard : Fintype.card G = q) (hgen : ∀ y : G, ∃ k : ZMod q, k • g = y)
    (x : (i : Fin 2) → OTIn G i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i) → ProbComp Bool) :
    semiHonestAdvantage (ddhOTProtocol g q) noOracleWorld (otFunctionality G) {1}
        (ddhOTReceiverSim g q) x D =
      ddhAdvantage q g (ddhOTReduction g q x D) := by
  rw [semiHonestAdvantage, ideal_receiver_eq_ddhRandomExperiment g q hcard hgen,
    real_receiver_eq_ddhRealExperiment g q, Game.advantage_comm, ddhAdvantage]

/-! ### Malicious-receiver attack on the unchecked variant -/

/-- Real game for a malicious receiver against `ddhOTUncheckedProtocol`. The sender holds uniform
messages `(m₀, m₁) ← G × G` and coins drawn by the protocol's own sampler. The receiver sends
`ddhOTAttackMsg g b₀ b₁` in Round 2, gets the sender's Round 3 reply
`ddhOTSenderReplyOf (ddhOTUncheckedProtocol g q)`, and wins if it recovers both messages. -/
@[expose] noncomputable def ddhOTUncheckedRealGame (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (b₀ b₁ : ZMod q) : ProbComp Bool := do
  let m₀ ← ProbComp.uniform G
  let m₁ ← ProbComp.uniform G
  let c : DDHOTSenderCoins q ← (ddhOTUncheckedProtocol g q).sampleCoins 0
  let reply :=
    ddhOTSenderReplyOf (ddhOTUncheckedProtocol g q) (m₀, m₁) c (ddhOTAttackMsg g b₀ b₁)
  return decide (ddhOTAttackBothMessages b₀ b₁ reply = (m₀, m₁))

/-- Ideal game for a malicious receiver against oblivious transfer. The simulator `S` first outputs
a query bit `τ` together with a guessing function, which may share the simulator's randomness. For
uniform messages `(m₀, m₁) ← G × G` the ideal functionality gives it `if τ then m₁ else m₀`, and
the simulator wins if its guess equals `(m₀, m₁)`. -/
@[expose] noncomputable def ddhOTUncheckedIdealGame
    (S : ProbComp (Bool × (G → ProbComp (G × G)))) : ProbComp Bool := do
  let s ← S
  let m₀ ← ProbComp.uniform G
  let m₁ ← ProbComp.uniform G
  let pair ← s.2 (if s.1 then m₁ else m₀)
  return decide (pair = (m₀, m₁))

/-- In `ddhOTUncheckedRealGame`, the malicious receiver recovers both messages with
probability `1`. -/
theorem succProbability_ddhOTUncheckedRealGame (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (b₀ b₁ : ZMod q) :
    (Game.succProbability (ProbComp.eval (ddhOTUncheckedRealGame g q b₀ b₁)) : ℝ) = 1 := by
  have hcoins : (ddhOTUncheckedProtocol g q).sampleCoins 0 = sampleDDHOTSenderCoins q := rfl
  rw [Game.coe_succProbability]
  simp only [ddhOTUncheckedRealGame, hcoins,
    ddhOTSenderReplyOf_ddhOTUncheckedProtocol, ddhOTAttackBothMessages_eq, decide_true,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_const, PMF.pure_apply, ↓reduceIte,
    ENNReal.toReal_one]

/-- In `ddhOTUncheckedIdealGame`, every simulator `S` outputs both messages with probability at
most `(Fintype.card G : ℝ)⁻¹`: the message it does not query is uniform and independent of its
view. -/
theorem succProbability_ddhOTUncheckedIdealGame_le
    (S : ProbComp (Bool × (G → ProbComp (G × G)))) :
    (Game.succProbability (ProbComp.eval (ddhOTUncheckedIdealGame S)) : ℝ) ≤
      (Fintype.card G : ℝ)⁻¹ := by
  have h_ennreal :
      ProbComp.eval (ddhOTUncheckedIdealGame S) true ≤ (Fintype.card G : ENNReal)⁻¹ := by
    simp only [ddhOTUncheckedIdealGame, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbComp.eval_uniform]
    refine PMF.bind_apply_le_on_support _ fun s _ => ?_
    obtain ⟨τ, guess⟩ := s
    cases τ
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine PMF.bind_apply_le_on_support _ fun m₀ _ => ?_
      rw [PMF.bind_comm]
      refine PMF.bind_apply_le_on_support _ fun pair _ => ?_
      exact PMF.uniformOfFintype_bind_pure_apply_true_le fun y hy y' hy' =>
        (congrArg Prod.snd (of_decide_eq_true hy)).symm.trans
          (congrArg Prod.snd (of_decide_eq_true hy'))
    · simp only [↓reduceIte]
      rw [PMF.bind_comm]
      refine PMF.bind_apply_le_on_support _ fun m₁ _ => ?_
      rw [PMF.bind_comm]
      refine PMF.bind_apply_le_on_support _ fun pair _ => ?_
      exact PMF.uniformOfFintype_bind_pure_apply_true_le fun y hy y' hy' =>
        (congrArg Prod.fst (of_decide_eq_true hy)).symm.trans
          (congrArg Prod.fst (of_decide_eq_true hy'))
  rw [Game.coe_succProbability, ← ENNReal.toReal_natCast, ← ENNReal.toReal_inv]
  exact ENNReal.toReal_mono (by simp) h_ennreal

/-- **Malicious-receiver separation for `ddhOTUncheckedProtocol`**: for every simulator `S`, the
distinguishing advantage between `ddhOTUncheckedRealGame` and `ddhOTUncheckedIdealGame S` is at
least `1 - (Fintype.card G : ℝ)⁻¹`. -/
theorem ddhOTUnchecked_malicious_receiver_advantage (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (b₀ b₁ : ZMod q)
    (S : ProbComp (Bool × (G → ProbComp (G × G)))) :
    1 - (Fintype.card G : ℝ)⁻¹ ≤
      (Game.advantage (ProbComp.eval (ddhOTUncheckedRealGame g q b₀ b₁))
        (ProbComp.eval (ddhOTUncheckedIdealGame S)) : ℝ) := by
  rw [Game.coe_advantage, succProbability_ddhOTUncheckedRealGame]
  exact (sub_le_sub_left (succProbability_ddhOTUncheckedIdealGame_le S) 1).trans
    (le_abs_self _)

end Cslib.Crypto.Protocols.MPC
