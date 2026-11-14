/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Family
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Tactic.Negligible

/-!
# PPT simulators for DDH oblivious transfer over a group family

`CslibFrontier/Crypto/Protocols/MPC/DDHOT/Family.lean` proves, assuming `F.DDH setup`, that the
real runs of `Cslib.Crypto.Protocols.MPC.ddhOTProtocol` over a `PrimeOrderGroupFamily` `F` are
indistinguishable from the ideal runs with the exact-sampling simulators `ddhOTSenderSim` and
`ddhOTReceiverSim`. Those simulators draw exact uniform exponents in `ZMod (F.order d)`, which no
bounded-time fair-coin machine can do for an odd prime order. This module gives simulator families
that run the same algorithms (`ddhOTSenderSimWithCoins`, `ddhOTReceiverSimWithCoins`) on six
exponents drawn with `sampleExp n d`, the technique of [BonehShoup2023], Remark 23.5 (p. 1059),
proves them uniform strict PPT, and proves that they are statistically within `6 / 2 ^ n` of the
exact-sampling simulators. Under `F.DDH setup`, the real runs are therefore indistinguishable
from the ideal runs with these PPT simulators in the sense of `ddhOTRealIdealIndistinguishable`:
for every distinguisher against a corrupted sender, and for every PPT distinguisher against a
corrupted receiver (`DDH.ddhOTStandaloneSemiHonestSecure`). The two comparisons below say how
this stand-alone semi-honest notion differs from [BonehShoup2023], Theorem 23.7, and from
[Lindell2017], Definition 4.1.

A simulator family is PPT (`DDHOTSimulator.IsPPTSender`, `DDHOTSimulator.IsPPTReceiver`) when one
uniform strict PPT machine reads the unary security parameter, the group parameters and the
corrupted party's input and output, with group elements as `F.encode d` words, and writes the
simulated view as words (`encDDHOTSenderViewWords`, `encDDHOTReceiverViewWords`). The words
determine the view (`ddhOTSenderViewWords_injective`, `ddhOTReceiverViewWords_injective`), so the
certificate covers the whole simulated view.

## Comparison with [BonehShoup2023], Theorem 23.7

`DDH.ddhOTStandaloneSemiHonestSecure` is a step towards [BonehShoup2023], Theorem 23.7 (p. 1058),
not the cited result. Its simulators are efficient, as Definition 23.5 (p. 1044) and
Section 23.5.2.2 (p. 1043) require, but it still differs from the theorem in the ways listed in
`CslibFrontier/Crypto/Protocols/MPC/DDHOT/Family.lean`:

* the notion is stand-alone: the distinguisher chooses the inputs and sees the corrupted party's
  view and both outputs after the run, whereas the theorem is stated in the restricted execution
  framework of Section 23.5.6 (p. 1054);
* only the corruption of exactly one party is covered, whereas the theorem covers every set of
  corrupted parties;
* the honest parties sample exact uniform exponents and their views hold these exponents, whereas
  the source requires the parties' only random objects to be random bit strings (p. 1059);
* the protocol is the variant of Figure 23.17 documented in `DDHOT.lean`, and the setup law is
  arbitrary.

The library's PPT notion `IsPPTOn` is strict: every run halts within a polynomial bound. The
source's compatibility condition (Section 23.5.2.2) bounds the running time only with overwhelming
probability.

## Comparison with [Lindell2017], Definition 4.1

[Lindell2017], Section 4.2, Definition 4.1 (p. 7) defines security of a two-party protocol against
static semi-honest adversaries in the stand-alone setting. Like `ddhOTStandaloneSemiHonestSecure`,
it asks for one PPT simulator per corrupted party, given `1ⁿ`, that party's input and its output,
and compares the simulator's output paired with both parties' outputs against that party's view
paired with both parties' outputs. The simulators are fixed before the distinguisher. The notions
differ as follows, so `DDH.ddhOTStandaloneSemiHonestSecure` is not that definition for DDH
oblivious transfer:

* In the source the parties run in polynomial time (p. 3), and a party's view holds the contents
  of its random tape (p. 7). The honest parties of `ddhOTProtocol` draw exact uniform exponents in
  `ZMod (F.order d)`, which no bounded-time fair-coin machine can do for an odd prime order, and
  their views hold these exponents. This idealizes the protocol's own algorithms, as the
  comparison with Theorem 23.7 above also notes.
* Computational indistinguishability in the source (p. 3) quantifies over non-uniform
  polynomial-time distinguishers, with one negligible function for all inputs. Here the
  distinguishers against a corrupted receiver are uniform strict PPT machines
  (`DDHOTDistinguisher.IsPPT`) that choose the inputs adaptively, after seeing the group
  parameters, and the negligible function may depend on the distinguisher. The distinguishers
  against a corrupted sender are unrestricted.
* The group parameters are drawn from a public setup law, which both the simulator and the
  distinguisher see. The source has no setup; a deterministic setup law corresponds to it.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.DDHOTSenderViewWords`,
  `Cslib.Crypto.Protocols.MPC.DDHOTReceiverViewWords`, and their encodings: a corrupted party's
  view as words.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDHOTSenderSimInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDHOTReceiverSimInput`, and their encodings: a simulator's
  input as a record.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDHOTSimulator.IsPPTSender`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDHOTSimulator.IsPPTReceiver`: PPT simulator families.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTSenderSimSampleExp`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTReceiverSimSampleExp`: the simulator families that draw
  their exponents with `sampleExp`.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTStandaloneSemiHonestSecure`: there are PPT simulator
  families for which `ddhOTRealIdealIndistinguishable` holds.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTSender_ddhOTSenderSimSampleExp`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTReceiver_ddhOTReceiverSimSampleExp`: the simulator
  families are PPT.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_ddhOTSenderSimSampleExp_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_ddhOTReceiverSimSampleExp_le`: on every input,
  they are within statistical distance `6 / 2 ^ n` of the exact-sampling simulators, so the ideal
  games differ by at most `6 / 2 ^ n`
  (`Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhOTIdealGame_ddhOTSenderSimSampleExp_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhOTIdealGame_ddhOTReceiverSimSampleExp_le`).
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.ddhOTRealIdealIndistinguishable_sampleExpSim`: under DDH,
  the real runs are indistinguishable from the ideal runs with these simulator families.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.ddhOTStandaloneSemiHonestSecure`: a step towards
  [BonehShoup2023], Theorem 23.7, not the cited result: `F.DDH setup` implies
  `F.ddhOTStandaloneSemiHonestSecure setup`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 23.5 (Section 23.5.2.2, p. 1043; Definition 23.5, p. 1044;
  Section 23.5.6, p. 1054; Theorem 23.7, p. 1058; Remark 23.5, p. 1059).
* [Y. Lindell, *How To Simulate It – A Tutorial on the Simulation Proof Technique*, ECCC
  TR17-112][Lindell2017], Section 2 (p. 3) and Section 4.2 (Definition 4.1, p. 7).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Turing.MultiTapeTM

/-- The words of a corrupted sender's view in `ddhOTProtocol`: its two messages, its five
exponents `a, r₀, s₀, r₁, s₁` as natural numbers, and the two branch keys of the receiver's
message. -/
structure DDHOTSenderViewWords where
  /-- The word of the message `m₀`. -/
  message₀ : List Bool
  /-- The word of the message `m₁`. -/
  message₁ : List Bool
  /-- The exponent `a` of the first message `u = a • g`. -/
  exponent : ℕ
  /-- The coin `r₀` of branch `0`. -/
  coinR₀ : ℕ
  /-- The coin `s₀` of branch `0`. -/
  coinS₀ : ℕ
  /-- The coin `r₁` of branch `1`. -/
  coinR₁ : ℕ
  /-- The coin `s₁` of branch `1`. -/
  coinS₁ : ℕ
  /-- The word of the branch key `w₀`. -/
  branchKey₀ : List Bool
  /-- The word of the branch key `w₁`. -/
  branchKey₁ : List Bool

/-- The encoding of a sender's view words: each field in turn, all but the last framed. -/
enc_structure encDDHOTSenderViewWords : DDHOTSenderViewWords where
  message₀ : encBits, message₁ : encBits, exponent : encNat, coinR₀ : encNat, coinS₀ : encNat,
  coinR₁ : encNat, coinS₁ : encNat, branchKey₀ : encBits, branchKey₁ : encBits

/-- The words of a corrupted receiver's view in `ddhOTProtocol`: its choice bit, its coin `b` as a
natural number, the sender's first message, and the two components of each branch ciphertext of
the sender's reply. -/
structure DDHOTReceiverViewWords where
  /-- The receiver's choice bit `σ`. -/
  choiceBit : Bool
  /-- The receiver's coin `b`. -/
  coin : ℕ
  /-- The word of the sender's first message `u`. -/
  firstMessage : List Bool
  /-- The word of the first component of the ciphertext of branch `0`. -/
  ephemeral₀ : List Bool
  /-- The word of the second component of the ciphertext of branch `0`. -/
  body₀ : List Bool
  /-- The word of the first component of the ciphertext of branch `1`. -/
  ephemeral₁ : List Bool
  /-- The word of the second component of the ciphertext of branch `1`. -/
  body₁ : List Bool

/-- The encoding of a receiver's view words: each field in turn, all but the last framed. -/
enc_structure encDDHOTReceiverViewWords : DDHOTReceiverViewWords where
  choiceBit : encBool, coin : encNat, firstMessage : encBits, ephemeral₀ : encBits,
  body₀ : encBits, ephemeral₁ : encBits, body₁ : encBits

end Cslib.Crypto.Protocols.MPC

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Cslib.Crypto.Protocols.MPC
open scoped NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### Simulator inputs and simulated views as words -/

/-- The input of a simulator for a corrupted sender: the security parameter, the group parameters
and the sender's two messages. The sender's output `()` carries no information. -/
structure DDHOTSenderSimInput where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- The group parameters. -/
  groupParameters : F.Desc
  /-- The sender's message `m₀`. -/
  message₀ : F.Carrier groupParameters
  /-- The sender's message `m₁`. -/
  message₁ : F.Carrier groupParameters

/-- The encoding of a sender simulator's input: the unary security parameter, the group
parameters and the words `F.encode d m₀`, `F.encode d m₁`, each framed except the last. -/
enc_structure encDDHOTSenderSimInput (F : PrimeOrderGroupFamily) : DDHOTSenderSimInput F where
  secParam : encUnary, groupParameters : F.encDesc,
  message₀ : (F.encode groupParameters) using (F.encode_injective groupParameters),
  message₁ : (F.encode groupParameters) using (F.encode_injective groupParameters)

/-- The input of a simulator for a corrupted receiver: the security parameter, the group
parameters, the receiver's choice bit and its output `m_σ`. -/
structure DDHOTReceiverSimInput where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- The group parameters. -/
  groupParameters : F.Desc
  /-- The receiver's choice bit `σ`. -/
  choiceBit : Bool
  /-- The receiver's output `m_σ`. -/
  output : F.Carrier groupParameters

/-- The encoding of a receiver simulator's input: the unary security parameter, the group
parameters, the choice bit and the word `F.encode d m_σ`, each framed except the last. -/
enc_structure encDDHOTReceiverSimInput (F : PrimeOrderGroupFamily) : DDHOTReceiverSimInput F where
  secParam : encUnary, groupParameters : F.encDesc, choiceBit : encBool,
  output : (F.encode groupParameters) using (F.encode_injective groupParameters)

/-- The words of a sender's view in `ddhOTProtocol` over `F.Carrier d`: the messages and branch
keys as `F.encode d` words, and the exponents as their values below `F.order d`. -/
@[expose] def ddhOTSenderViewWords (d : F.Desc)
    (view : PartyView (OTIn (F.Carrier d)) (DDHOTCoins (F.order d)) (ddhOTSchedule (F.Carrier d))
      0) : DDHOTSenderViewWords :=
  let (m₀, m₁) := view.input
  let (a, r₀, s₀, r₁, s₁) := view.coins
  let (_, w, _) := view.received
  let (w₀, w₁) := w rfl
  ⟨F.encode d m₀, F.encode d m₁, a.val, r₀.val, s₀.val, r₁.val, s₁.val, F.encode d w₀,
    F.encode d w₁⟩

/-- The words of a receiver's view in `ddhOTProtocol` over `F.Carrier d`: the choice bit, the
coin as its value below `F.order d`, and the received group elements as `F.encode d` words. -/
@[expose] def ddhOTReceiverViewWords (d : F.Desc)
    (view : PartyView (OTIn (F.Carrier d)) (DDHOTCoins (F.order d)) (ddhOTSchedule (F.Carrier d))
      1) : DDHOTReceiverViewWords :=
  let (u, _, reply, _) := view.received
  let ((e₀, c₀), (e₁, c₁)) := reply rfl
  ⟨view.input, view.coins.val, F.encode d (u rfl), F.encode d e₀, F.encode d c₀, F.encode d e₁,
    F.encode d c₁⟩

/-- The words determine a sender's view. -/
theorem ddhOTSenderViewWords_injective (d : F.Desc) :
    Function.Injective (F.ddhOTSenderViewWords d) := by
  rintro ⟨⟨m₀, m₁⟩, ⟨a, r₀, s₀, r₁, s₁⟩, ⟨u, w, reply, ⟨⟩⟩⟩
    ⟨⟨m₀', m₁'⟩, ⟨a', r₀', s₀', r₁', s₁'⟩, ⟨u', w', reply', ⟨⟩⟩⟩ h
  simp only [ddhOTSenderViewWords, DDHOTSenderViewWords.mk.injEq] at h
  obtain ⟨hm₀, hm₁, ha, hr₀, hs₀, hr₁, hs₁, hw₀, hw₁⟩ := h
  refine PartyView.ext ?_ ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl)))
  · exact Prod.ext (F.encode_injective d hm₀) (F.encode_injective d hm₁)
  · simp only [ZMod.val_injective _ |>.eq_iff] at ha hr₀ hs₀ hr₁ hs₁
    rw [ha, hr₀, hs₀, hr₁, hs₁]
  · exact Round.received_message_eq_of_ne (by decide) _ _
  · exact Round.received_message_ext fun _ =>
      Prod.ext (F.encode_injective d hw₀) (F.encode_injective d hw₁)
  · exact Round.received_message_eq_of_ne (by decide) _ _

/-- The words determine a receiver's view. -/
theorem ddhOTReceiverViewWords_injective (d : F.Desc) :
    Function.Injective (F.ddhOTReceiverViewWords d) := by
  rintro ⟨σ, b, ⟨u, w, reply, ⟨⟩⟩⟩ ⟨σ', b', ⟨u', w', reply', ⟨⟩⟩⟩ h
  injection h with hσ hb hu he₀ hc₀ he₁ hc₁
  refine PartyView.ext hσ (ZMod.val_injective _ hb) (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl)))
  · exact Round.received_message_ext fun _ => F.encode_injective d hu
  · exact Round.received_message_eq_of_ne (by decide) _ _
  · exact Round.received_message_ext fun _ =>
      Prod.ext (Prod.ext (F.encode_injective d he₀) (F.encode_injective d hc₀))
        (Prod.ext (F.encode_injective d he₁) (F.encode_injective d hc₁))

variable {F}

/-! ### PPT simulator families -/

/-- A simulator family for a corrupted sender is PPT when one uniform strict PPT machine reads
`encDDHOTSenderSimInput` (the unary security parameter, the group parameters and the sender's
messages as words) and writes the words of the simulated view, `encDDHOTSenderViewWords`. Every
input tuple of the coalition `{0}` is `uniqueElim (m₀, m₁)`, every output tuple is
`uniqueElim ()`, and the words determine the view (`ddhOTSenderViewWords_injective`), so this
constrains the simulator on all of its inputs and outputs. -/
@[expose] def DDHOTSimulator.IsPPTSender (S : F.DDHOTSimulator {0}) : Prop :=
  IsPPTOn F.encDDHOTSenderSimInput encDDHOTSenderViewWords fun x =>
    (fun v => F.ddhOTSenderViewWords x.groupParameters (v ⟨0, Finset.mem_singleton_self 0⟩)) <$>
      S x.secParam x.groupParameters (uniqueElim (x.message₀, x.message₁)) (uniqueElim ())

/-- A simulator family for a corrupted receiver is PPT when one uniform strict PPT machine reads
`encDDHOTReceiverSimInput` (the unary security parameter, the group parameters, the receiver's
choice bit and its output as a word) and writes the words of the simulated view,
`encDDHOTReceiverViewWords`. Every input and output tuple of the coalition `{1}` is of the form
`uniqueElim σ`, `uniqueElim m_σ`, and the words determine the view
(`ddhOTReceiverViewWords_injective`), so this constrains the simulator on all of its inputs and
outputs. -/
@[expose] def DDHOTSimulator.IsPPTReceiver (S : F.DDHOTSimulator {1}) : Prop :=
  IsPPTOn F.encDDHOTReceiverSimInput encDDHOTReceiverViewWords fun x =>
    (fun v => F.ddhOTReceiverViewWords x.groupParameters (v ⟨1, Finset.mem_singleton_self 1⟩)) <$>
      S x.secParam x.groupParameters (uniqueElim x.choiceBit) (uniqueElim x.output)

variable (F)

/-- The simulator family for a corrupted sender that runs the algorithm of `ddhOTSenderSim`,
`ddhOTSenderSimWithCoins`, on six exponents drawn with `sampleExp n d` instead of exact uniform
ones. -/
@[expose] noncomputable def ddhOTSenderSimSampleExp : F.DDHOTSimulator {0} := fun n d xI _ => do
  let a ← F.sampleExp n d
  let r₀ ← F.sampleExp n d
  let s₀ ← F.sampleExp n d
  let r₁ ← F.sampleExp n d
  let s₁ ← F.sampleExp n d
  let b ← F.sampleExp n d
  return ddhOTSenderSimWithCoins (F.generator d) ((a : ZMod (F.order d)), (r₀ : ZMod (F.order d)),
    (s₀ : ZMod (F.order d)), (r₁ : ZMod (F.order d)), (s₁ : ZMod (F.order d))) b xI

/-- The simulator family for a corrupted receiver that runs the algorithm of `ddhOTReceiverSim`,
`ddhOTReceiverSimWithCoins`, on six exponents drawn with `sampleExp n d` instead of exact uniform
ones. -/
@[expose] noncomputable def ddhOTReceiverSimSampleExp : F.DDHOTSimulator {1} :=
  fun n d xI yI => do
    let a ← F.sampleExp n d
    let b ← F.sampleExp n d
    let r ← F.sampleExp n d
    let s ← F.sampleExp n d
    let k ← F.sampleExp n d
    let c ← F.sampleExp n d
    return ddhOTReceiverSimWithCoins (F.generator d) a b r s k c xI yI

/-! ### Statistical closeness to the exact-sampling simulators -/

/-- On every input, no test `k` tells `ddhOTSenderSimSampleExp` from `ddhOTSenderSim` with
advantage more than `6 / 2 ^ n`. -/
theorem advantage_bind_ddhOTSenderSimSampleExp_le (n : ℕ) (d : F.Desc)
    (xI : (i : ({0} : Finset (Fin 2))) → OTIn (F.Carrier d) i)
    (yI : (i : ({0} : Finset (Fin 2))) → OTOut (F.Carrier d) i)
    (k : ((i : ({0} : Finset (Fin 2))) →
      PartyView (OTIn (F.Carrier d)) (DDHOTCoins (F.order d)) (ddhOTSchedule (F.Carrier d)) i) →
        Game) :
    Game.advantage ((ProbComp.eval (ddhOTSenderSim (F.generator d) (F.order d) xI yI)).bind k)
      ((ProbComp.eval (F.ddhOTSenderSimSampleExp n d xI yI)).bind k) ≤ 6 / 2 ^ n := by
  simp only [ddhOTSenderSim, ddhOTSenderSimSampleExp, sampleDDHOTSenderCoins, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  rw [Game.advantage_comm]
  exact F.advantage_bind_sampleExp_six_le n d fun a r₀ s₀ r₁ s₁ b =>
    k (ddhOTSenderSimWithCoins (F.generator d) (a, r₀, s₀, r₁, s₁) b xI)

/-- On every input, no test `k` tells `ddhOTReceiverSimSampleExp` from `ddhOTReceiverSim` with
advantage more than `6 / 2 ^ n`. -/
theorem advantage_bind_ddhOTReceiverSimSampleExp_le (n : ℕ) (d : F.Desc)
    (xI : (i : ({1} : Finset (Fin 2))) → OTIn (F.Carrier d) i)
    (yI : (i : ({1} : Finset (Fin 2))) → OTOut (F.Carrier d) i)
    (k : ((i : ({1} : Finset (Fin 2))) →
      PartyView (OTIn (F.Carrier d)) (DDHOTCoins (F.order d)) (ddhOTSchedule (F.Carrier d)) i) →
        Game) :
    Game.advantage ((ProbComp.eval (ddhOTReceiverSim (F.generator d) (F.order d) xI yI)).bind k)
      ((ProbComp.eval (F.ddhOTReceiverSimSampleExp n d xI yI)).bind k) ≤ 6 / 2 ^ n := by
  simp only [ddhOTReceiverSim, ddhOTReceiverSimSampleExp, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  rw [Game.advantage_comm]
  exact F.advantage_bind_sampleExp_six_le n d fun a b r s k' c =>
    k (ddhOTReceiverSimWithCoins (F.generator d) a b r s k' c xI yI)

/-- Two simulator families that are within `ε` of each other on every input and against every
test give ideal games within `ε` of each other. -/
private theorem advantage_ddhOTIdealGame_le (setup : ℕ → PMF F.Desc) {I : Finset (Fin 2)}
    (S S' : F.DDHOTSimulator I) (A : F.DDHOTDistinguisher I) (n : ℕ) {ε : ℝ≥0}
    (h : ∀ (d : F.Desc) xI yI (k : _ → Game),
      Game.advantage ((ProbComp.eval (S n d xI yI)).bind k)
        ((ProbComp.eval (S' n d xI yI)).bind k) ≤ ε) :
    Game.advantage (F.ddhOTIdealGame setup I S A n) (F.ddhOTIdealGame setup I S' A n) ≤ ε := by
  simp only [ddhOTIdealGame, idealJoint, otFunctionality, Functionality.ofDeterministic,
    PMF.monad_bind_eq_bind, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, PMF.bind_bind]
  exact Game.advantage_bind_le_nnreal _ _ _ fun d =>
    Game.advantage_bind_le_nnreal _ _ _ fun _ => h d _ _ _

/-- For every distinguisher against a corrupted sender, the ideal games with `ddhOTSenderSim`
and with `ddhOTSenderSimSampleExp` differ by at most `6 / 2 ^ n`. -/
theorem advantage_ddhOTIdealGame_ddhOTSenderSimSampleExp_le (setup : ℕ → PMF F.Desc)
    (A : F.DDHOTDistinguisher {0}) (n : ℕ) :
    Game.advantage
        (F.ddhOTIdealGame setup {0} (fun _ d => ddhOTSenderSim (F.generator d) (F.order d)) A n)
        (F.ddhOTIdealGame setup {0} F.ddhOTSenderSimSampleExp A n) ≤ 6 / 2 ^ n :=
  F.advantage_ddhOTIdealGame_le setup _ _ A n (F.advantage_bind_ddhOTSenderSimSampleExp_le n)

/-- For every distinguisher against a corrupted receiver, the ideal games with `ddhOTReceiverSim`
and with `ddhOTReceiverSimSampleExp` differ by at most `6 / 2 ^ n`. -/
theorem advantage_ddhOTIdealGame_ddhOTReceiverSimSampleExp_le (setup : ℕ → PMF F.Desc)
    (A : F.DDHOTDistinguisher {1}) (n : ℕ) :
    Game.advantage
        (F.ddhOTIdealGame setup {1} (fun _ d => ddhOTReceiverSim (F.generator d) (F.order d)) A n)
        (F.ddhOTIdealGame setup {1} F.ddhOTReceiverSimSampleExp A n) ≤ 6 / 2 ^ n :=
  F.advantage_ddhOTIdealGame_le setup _ _ A n (F.advantage_bind_ddhOTReceiverSimSampleExp_le n)

/-! ### Efficiency of the simulator families -/

/-- Six `sampleExp` draws followed by an efficiently computable function of the input and the
draws are uniform strict PPT. -/
private theorem isPPTOn_sampleExp_six {α β : Type} {enc : α ↪ List Bool}
    {encOut : β ↪ List Bool} {n : α → ℕ} {d : α → F.Desc}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc F.encDesc)
    {W : α → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → β}
    (hW : ∀ {γ : Type} {encγ : γ ↪ List Bool} {x : γ → α} {a₁ a₂ a₃ a₄ a₅ a₆ : γ → ℕ},
      ComputableInPolyTime x encγ enc → ComputableInPolyTime a₁ encγ encNat →
      ComputableInPolyTime a₂ encγ encNat → ComputableInPolyTime a₃ encγ encNat →
      ComputableInPolyTime a₄ encγ encNat → ComputableInPolyTime a₅ encγ encNat →
      ComputableInPolyTime a₆ encγ encNat →
      ComputableInPolyTime (fun c => W (x c) (a₁ c) (a₂ c) (a₃ c) (a₄ c) (a₅ c) (a₆ c)) encγ
        encOut) :
    IsPPTOn enc encOut (fun x => do
      let a₁ ← F.sampleExp (n x) (d x)
      let a₂ ← F.sampleExp (n x) (d x)
      let a₃ ← F.sampleExp (n x) (d x)
      let a₄ ← F.sampleExp (n x) (d x)
      let a₅ ← F.sampleExp (n x) (d x)
      let a₆ ← F.sampleExp (n x) (d x)
      pure (W x a₁ a₂ a₃ a₄ a₅ a₆)) := by
  have hsample {γ : Type} {encγ : γ ↪ List Bool} {x : γ → α}
      (hx : ComputableInPolyTime x encγ enc) :
      IsPPTOn encγ encNat fun c => F.sampleExp (n (x c)) (d (x c)) :=
    F.isPPTOn_sampleExp (hn.comp hx) (hd.comp hx)
  refine IsPPTOn.bind_with (hsample .id') ?_
  refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
  exact (hW (γ := ((((((α × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)) (x := fun p => p.1.1.1.1.1.1)
    (a₁ := fun p => p.1.1.1.1.1.2) (a₂ := fun p => p.1.1.1.1.2) (a₃ := fun p => p.1.1.1.2)
    (a₄ := fun p => p.1.1.2) (a₅ := fun p => p.1.2) (a₆ := fun p => p.2) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)).isPPTOn

/-- The view words that `ddhOTSenderSimSampleExp` writes on input `x` and exponents
`a, r₀, s₀, r₁, s₁, b`: the exponents reduced modulo `q = F.order d`, and the branch keys
`b • g` and `a • g + (q - b % q) • g`. -/
private def ddhOTSenderSimWords (x : F.DDHOTSenderSimInput) (a r₀ s₀ r₁ s₁ b : ℕ) :
    DDHOTSenderViewWords :=
  let d := x.groupParameters
  let q := F.order d
  let g := F.generator d
  ⟨F.encode d x.message₀, F.encode d x.message₁, a % q, r₀ % q, s₀ % q, r₁ % q, s₁ % q,
    F.encode d ((b : ZMod q) • g), F.encode d ((a : ZMod q) • g + ((q - b % q : ℕ) : ZMod q) • g)⟩

/-- `-(b : ZMod q)` is the cast of `q - b % q`. -/
private theorem natCast_sub_mod_eq_neg (d : F.Desc) (b : ℕ) :
    ((F.order d - b % F.order d : ℕ) : ZMod (F.order d)) = -(b : ZMod (F.order d)) := by
  rw [Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ (F.prime_order _).pos)), ZMod.natCast_self,
    ZMod.natCast_mod, zero_sub]

/-- `ddhOTSenderSimSampleExp` is PPT. -/
theorem isPPTSender_ddhOTSenderSimSampleExp : (F.ddhOTSenderSimSampleExp).IsPPTSender := by
  refine (F.isPPTOn_sampleExp_six (F.encDDHOTSenderSimInput_secParam_polyTime .id')
    (F.encDDHOTSenderSimInput_groupParameters_polyTime .id') (W := F.ddhOTSenderSimWords)
    fun hx ha hr₀ hs₀ hr₁ hs₁ hb => ?_).congr fun x => ?_
  · have hd := F.encDDHOTSenderSimInput_groupParameters_polyTime hx
    have hq := F.computableInPolyTime_order.comp hd
    have hg := computableInPolyTime_encode_generator hd
    exact encDDHOTSenderViewWords_mk_polyTime (F.encDDHOTSenderSimInput_message₀_polyTime hx)
      (F.encDDHOTSenderSimInput_message₁_polyTime hx) (ha.binary_mod' hq) (hr₀.binary_mod' hq)
      (hs₀.binary_mod' hq) (hr₁.binary_mod' hq) (hs₁.binary_mod' hq)
      (computableInPolyTime_encode_natCast_smul hd hb hg)
      (computableInPolyTime_encode_add hd (computableInPolyTime_encode_natCast_smul hd ha hg)
        (computableInPolyTime_encode_natCast_smul hd (hq.binary_sub' (hb.binary_mod' hq)) hg))
  · simp only [ddhOTSenderSimSampleExp, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map]
    refine congrArg (PMF.bind _) (funext fun a => congrArg (PMF.bind _) (funext fun r₀ =>
      congrArg (PMF.bind _) (funext fun s₀ => congrArg (PMF.bind _) (funext fun r₁ =>
        congrArg (PMF.bind _) (funext fun s₁ => congrArg (PMF.bind _) (funext fun b =>
          congrArg PMF.pure ?_))))))
    let q := F.order x.groupParameters
    let g := F.generator x.groupParameters
    change _ = F.ddhOTSenderViewWords x.groupParameters (ddhOTSenderView (x.message₀, x.message₁)
      ((a : ZMod q), (r₀ : ZMod q), (s₀ : ZMod q), (r₁ : ZMod q), (s₁ : ZMod q))
      ((b : ZMod q) • g, (a : ZMod q) • g - (b : ZMod q) • g))
    simp only [ddhOTSenderSimWords, ddhOTSenderViewWords, ddhOTSenderView, natCast_sub_mod_eq_neg,
      neg_smul, ← sub_eq_add_neg, ZMod.val_natCast]
    rfl

/-- The view words that `ddhOTReceiverSimSampleExp` writes on input `x` and exponents
`a, b, r, s, k, c`: the coin reduced modulo `F.order d`, the first message `a • g`, and the
branches `(e, b • e + m_σ)` with `e = r • g + s • (a • g)` and `(k • g, c • g)`, in the order
given by the choice bit. -/
private def ddhOTReceiverSimWords (x : F.DDHOTReceiverSimInput) (a b r s k c : ℕ) :
    DDHOTReceiverViewWords :=
  let d := x.groupParameters
  let q := F.order d
  let g := F.generator d
  let e := (r : ZMod q) • g + (s : ZMod q) • (a : ZMod q) • g
  let chosen₁ := F.encode d e
  let chosen₂ := F.encode d ((b : ZMod q) • e + x.output)
  let other₁ := F.encode d ((k : ZMod q) • g)
  let other₂ := F.encode d ((c : ZMod q) • g)
  let σ := x.choiceBit
  ⟨σ, b % q, F.encode d ((a : ZMod q) • g), if σ then other₁ else chosen₁,
    if σ then other₂ else chosen₂, if σ then chosen₁ else other₁, if σ then chosen₂ else other₂⟩

/-- `ddhOTReceiverSimSampleExp` is PPT. -/
theorem isPPTReceiver_ddhOTReceiverSimSampleExp :
    (F.ddhOTReceiverSimSampleExp).IsPPTReceiver := by
  refine (F.isPPTOn_sampleExp_six (F.encDDHOTReceiverSimInput_secParam_polyTime .id')
    (F.encDDHOTReceiverSimInput_groupParameters_polyTime .id') (W := F.ddhOTReceiverSimWords)
    fun hx ha hb hr hs hk hc => ?_).congr fun x => ?_
  · have hd := F.encDDHOTReceiverSimInput_groupParameters_polyTime hx
    have hg := computableInPolyTime_encode_generator hd
    have hσ := F.encDDHOTReceiverSimInput_choiceBit_polyTime hx
    have hu := computableInPolyTime_encode_natCast_smul hd ha hg
    have he := computableInPolyTime_encode_add hd
      (computableInPolyTime_encode_natCast_smul hd hr hg)
      (computableInPolyTime_encode_natCast_smul hd hs hu)
    have hbody := computableInPolyTime_encode_add hd
      (computableInPolyTime_encode_natCast_smul hd hb he)
      (F.encDDHOTReceiverSimInput_output_polyTime hx)
    have hk' := computableInPolyTime_encode_natCast_smul hd hk hg
    have hc' := computableInPolyTime_encode_natCast_smul hd hc hg
    exact encDDHOTReceiverViewWords_mk_polyTime hσ
      (hb.binary_mod' (F.computableInPolyTime_order.comp hd)) hu (hσ.ite' hk' he)
      (hσ.ite' hc' hbody) (hσ.ite' he hk') (hσ.ite' hbody hc')
  · simp only [ddhOTReceiverSimSampleExp, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map]
    refine congrArg (PMF.bind _) (funext fun a => congrArg (PMF.bind _) (funext fun b =>
      congrArg (PMF.bind _) (funext fun r => congrArg (PMF.bind _) (funext fun s =>
        congrArg (PMF.bind _) (funext fun k => congrArg (PMF.bind _) (funext fun c =>
          congrArg PMF.pure ?_))))))
    obtain ⟨n, d, σ, m⟩ := x
    let q := F.order d
    let g := F.generator d
    let e := (r : ZMod q) • g + (s : ZMod q) • (a : ZMod q) • g
    change _ = F.ddhOTReceiverViewWords d (ddhOTReceiverView σ (b : ZMod q) ((a : ZMod q) • g)
      (if σ then (((k : ZMod q) • g, (c : ZMod q) • g), (e, (b : ZMod q) • e + m))
        else ((e, (b : ZMod q) • e + m), ((k : ZMod q) • g, (c : ZMod q) • g))))
    cases σ <;> simp only [ddhOTReceiverSimWords, ddhOTReceiverViewWords, ddhOTReceiverView,
      Bool.false_eq_true, ↓reduceIte, ZMod.val_natCast] <;> rfl

/-! ### Security with PPT simulators -/

/-- A step towards [BonehShoup2023], Theorem 23.7, not the security notion of that theorem:
stand-alone semi-honest security of `ddhOTProtocol` over the family `F` against the corruption of
one party, with PPT simulators. There are simulator families for a corrupted sender and a
corrupted receiver, each PPT (`DDHOTSimulator.IsPPTSender`, `DDHOTSimulator.IsPPTReceiver`), for
which `ddhOTRealIdealIndistinguishable setup` holds. The source's notion, Definition 23.5
(p. 1044) carried over to the restricted execution framework of Section 23.5.6 (p. 1054), is not
stand-alone, covers every set of corrupted parties, and has the parties draw only random bit
strings; the module documentation lists the differences. -/
@[expose] def ddhOTStandaloneSemiHonestSecure (setup : ℕ → PMF F.Desc) : Prop :=
  ∃ (S₀ : F.DDHOTSimulator {0}) (S₁ : F.DDHOTSimulator {1}),
    S₀.IsPPTSender ∧ S₁.IsPPTReceiver ∧ F.ddhOTRealIdealIndistinguishable setup S₀ S₁

/-- Under DDH, the real runs of DDH oblivious transfer are indistinguishable from the ideal runs
with the PPT simulator families `ddhOTSenderSimSampleExp` and `ddhOTReceiverSimSampleExp`.
Against a corrupted sender, the advantage of every distinguisher is at most `6 / 2 ^ n`; against
a corrupted receiver, it is at most that against the exact-sampling simulators plus `6 / 2 ^ n`.
The only premise is `F.DDH setup`. -/
theorem DDH.ddhOTRealIdealIndistinguishable_sampleExpSim {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} (hDDH : F.DDH setup) :
    F.ddhOTRealIdealIndistinguishable setup F.ddhOTSenderSimSampleExp
      F.ddhOTReceiverSimSampleExp := by
  have hexact := hDDH.ddhOTRealIdealIndistinguishable_exactSim
  exact ⟨hexact.1.trans fun A _ => by
      negligible using F.advantage_ddhOTIdealGame_ddhOTSenderSimSampleExp_le setup A,
    hexact.2.trans fun A _ => by
      negligible using F.advantage_ddhOTIdealGame_ddhOTReceiverSimSampleExp_le setup A⟩

/-- A step towards [BonehShoup2023], Theorem 23.7, not the cited result: `F.DDH setup` implies
stand-alone semi-honest security of DDH oblivious transfer against the corruption of one party,
with PPT simulators. The simulators are `ddhOTSenderSimSampleExp` and
`ddhOTReceiverSimSampleExp`. The theorem is stated in the restricted execution framework of
Section 23.5.6, covers every set of corrupted parties, and has the parties derive their exponents
from random bit strings; the module documentation lists these and the other differences. The only
premise is `F.DDH setup`; the reduction is certified by `isPPT_ddhOTReceiverToDDHDistinguisher`. -/
theorem DDH.ddhOTStandaloneSemiHonestSecure {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) : F.ddhOTStandaloneSemiHonestSecure setup :=
  ⟨_, _, F.isPPTSender_ddhOTSenderSimSampleExp, F.isPPTReceiver_ddhOTReceiverSimSampleExp,
    hDDH.ddhOTRealIdealIndistinguishable_sampleExpSim⟩

end Cslib.Crypto.PrimeOrderGroupFamily
