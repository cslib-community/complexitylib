/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Protocols.MPC.DDHOT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PMFSwap

/-!
# Real and simulated views of DDH oblivious transfer are indistinguishable under DDH

`Cslib.Crypto.Protocols.MPC.ddhOTProtocol` is a three-message 1-out-of-2 oblivious transfer over
a group of prime order, a variant of the protocol of [BonehShoup2023], Section 23.5.7, Figure 23.17
(p. 1057). `CslibFrontier/Crypto/Protocols/MPC/DDHOT.lean` defines it, lists its differences from
Figure 23.17, and relates it to the DDH experiment in one fixed group. This module runs it in the
groups of a `PrimeOrderGroupFamily` `F` whose group parameters are drawn from a setup law, and
proves, assuming `F.DDH setup`, that a run with one semi-honest corrupted party is
computationally indistinguishable from the output of the exact-sampling simulators
`ddhOTSenderSim` and `ddhOTReceiverSim` of `DDHOT.lean`.

This is a step towards [BonehShoup2023], Theorem 23.7 (p. 1058), not the cited result: the
theorem asks for efficient simulators, and these simulators are not shown to be PPT (see the
comparison below). Its reduction to DDH is the certified part.

The security games run against a two-stage distinguisher `DDHOTDistinguisher`, which plays the
role of the environment `Z` in the source: given the security parameter `n` and group parameters
`d`, it chooses both parties' inputs, the sender's two messages in `F.Carrier d` and the
receiver's choice bit (`OTChoice`). It then sees the corrupted party's view and both parties'
outputs and returns a bit. In `ddhOTRealGame` the view comes from a run of the protocol. In
`ddhOTIdealGame` a simulator computes it from the corrupted party's input and output in the ideal
oblivious-transfer functionality. `ddhOTRealIdealIndistinguishable setup S₀ S₁` asks the two
games to be indistinguishable with given simulator families: for every distinguisher when the
sender is corrupted, with `S₀`, and for every PPT distinguisher (`DDHOTDistinguisher.IsPPT`) when
the receiver is corrupted, with `S₁`. It asks nothing about the efficiency of `S₀` and `S₁`.
Distinguishers receive group elements and their efficiency is stated on encodings, as for
`DDHDistinguisher`.

The library has no general asymptotic computational notion of semi-honest security for protocols
(`Cslib.Crypto.Protocols.MPC.semiHonestAdvantage` is the advantage on one fixed input tuple), so
the games and the distinguisher class are defined here for this protocol.

**Proof.** A run against a corrupted sender is simulated perfectly
(`Cslib.Crypto.Protocols.MPC.idealJoint_ddhOT_sender`), so the two games are equal. Against a
corrupted receiver, `ddhOTReceiverToDDHDistinguisher` turns a distinguisher `A` into a DDH
distinguisher. It runs `A`'s input choice, draws the receiver's coin and the chosen branch's coins
with `sampleExp`, and embeds the DDH triple into the unchosen branch as
`Cslib.Crypto.Protocols.MPC.ddhOTReductionWithCoins` does. With exact uniform coins, the real DDH
game would be the real game (`Cslib.Crypto.Protocols.MPC.real_receiver_eq_ddhRealExperiment`), and
the random DDH game would be the ideal game
(`Cslib.Crypto.Protocols.MPC.ideal_receiver_eq_ddhRandomExperiment`). The three approximate draws
cost at most `3 / 2 ^ n` on each side (`advantage_bind_sampleExp_triple_le`), which gives
`advantage_ddhOTReceiverGame_le`. `isPPT_ddhOTReceiverToDDHDistinguisher` proves that the reduction
is PPT whenever `A` is, and `DDH.ddhOTRealIdealIndistinguishable_exactSim` applies `F.DDH setup`
to it through that certificate.

## Comparison with [BonehShoup2023], Theorem 23.7

* Theorem 23.7 is stated in the restricted framework of Section 23.5.6 (p. 1054), in which the
  environment exchanges messages with the parties and the adversary or simulator during the
  execution. Here the distinguisher chooses the inputs, and after the run it sees the corrupted
  party's view and both outputs: the stand-alone notion that
  `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage` measures on one input tuple, made asymptotic.
  The environment of the source likewise knows all parties' inputs and outputs (p. 1059).
* The source requires the simulator to be efficient (compatible with the functionality,
  Section 23.5.2.2, p. 1043). The simulators here sample exact uniform exponents in
  `ZMod (F.order d)`, as the protocol's own coin sampler does, which no bounded-time fair-coin
  machine can do for an odd prime order, and `ddhOTRealIdealIndistinguishable` does not ask them
  to be PPT. This is why the result is a step and not Theorem 23.7. The reduction, which must be
  PPT, draws its coins with `sampleExp` instead, the technique of Remark 23.5 (p. 1059).
* Only the corruption of exactly one party is covered (`I = {0}` and `I = {1}`). Theorem 23.7
  covers every set of corrupted parties; the source treats no corruption and full corruption as
  the cases in which there is not much for the simulator to do (p. 1059).
* The honest parties sample exact uniform exponents in `ZMod (F.order d)`, and their views hold
  these exponents. The source requires the only random objects to be random bit strings, from
  which the parties derive statistically near-uniform values ("Further assumptions about
  randomness", p. 1059).
* The protocol is a variant of Figure 23.17. `CslibFrontier/Crypto/Protocols/MPC/DDHOT.lean`
  lists the differences.
* The setup law is an arbitrary distribution on group parameters, as in `F.DDH setup`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.OTChoice`, `Cslib.Crypto.Protocols.MPC.encOTChoice`: the inputs and
  saved state chosen by a distinguisher, and the encoding of a choice with word messages.
* `Cslib.Crypto.Protocols.MPC.DDHOTJoint`: the corrupted parties' views and both outputs.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDHOTDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDHOTSimulator`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTIdealGame`: two-stage distinguishers, simulator
  families, and the real and ideal games over the family.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDHOTReceiverGuessInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encDDHOTReceiverGuessInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDHOTDistinguisher.IsPPT`: the input of a receiver-corrupting
  distinguisher's guess as a record, its encoding, and the distinguisher's efficiency.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTRealIdealIndistinguishable`: indistinguishability of
  the real and simulated runs of `ddhOTProtocol` over the family, with given simulator families
  and no efficiency requirement on them.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTReceiverToDDHDistinguisher`: the reduction to DDH.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.DDHOTReceiverGuessInput.exists_joint_eq`: every joint value
  of a corrupted receiver is described by a guessing-stage input record.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTRealGame_sender_eq`: perfect simulation of a corrupted
  sender.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhOTReceiverGame_le`: the advantage against a
  corrupted receiver is at most the DDH advantage of the reduction plus `6 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhOTReceiverToDDHDistinguisher`: the reduction is
  PPT.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.ddhOTRealIdealIndistinguishable_exactSim`: a step
  towards [BonehShoup2023], Theorem 23.7, not the cited result: `F.DDH setup` implies
  `F.ddhOTRealIdealIndistinguishable setup` with the exact-sampling simulators `ddhOTSenderSim`
  and `ddhOTReceiverSim`, which are not shown to be PPT.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 23.5.7 (Figure 23.17, p. 1057; Theorem 23.7, p. 1058;
  Remark 23.5 and the simulators, pp. 1059–1060).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Turing.MultiTapeTM

/-! ### Input choices and joint values -/

/-- The inputs a distinguisher chooses for one run of 1-out-of-2 oblivious transfer over `M`, and
the state it keeps for its guess. -/
structure OTChoice (M : Type) where
  /-- The sender's message `m₀`. -/
  message₀ : M
  /-- The sender's message `m₁`. -/
  message₁ : M
  /-- The receiver's choice bit `σ`. -/
  choiceBit : Bool
  /-- The state passed to the guessing stage. -/
  state : List Bool

/-- The input tuple of `otFunctionality M` given by a choice: `(m₀, m₁)` for the sender (party
`0`) and `σ` for the receiver (party `1`). -/
@[expose] def OTChoice.inputs {M : Type} (c : OTChoice M) : (i : Fin 2) → OTIn M i :=
  fun i => Fin.cases (motive := fun i => OTIn M i) (c.message₀, c.message₁)
    (fun _ => c.choiceBit) i

/-- Apply `f` to both messages of a choice. -/
@[expose] def OTChoice.map {M N : Type} (f : M → N) (c : OTChoice M) : OTChoice N where
  message₀ := f c.message₀
  message₁ := f c.message₁
  choiceBit := c.choiceBit
  state := c.state

/-- The encoding of a choice whose messages are words: the words `m₀` and `m₁`, the bit `σ` and
the state, each framed except the last. -/
enc_structure encOTChoice : OTChoice (List Bool) where
  message₀ : encBits, message₁ : encBits, choiceBit : encBool, state : encBits

/-- The joint value that a corrupted set `I` of parties of `ddhOTProtocol` over `G` sees in the
security games: the views of the parties in `I` and the outputs of both parties. -/
abbrev DDHOTJoint (G : Type) (q : ℕ) (I : Finset (Fin 2)) : Type :=
  ((i : I) → PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i) × ((i : Fin 2) → OTOut G i)

end Cslib.Crypto.Protocols.MPC

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Cslib.Crypto.Protocols.MPC
open scoped NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### Distinguishers and games -/

/-- A two-stage distinguisher against `ddhOTProtocol` over the family `F` when the parties in `I`
are corrupted. Given the security parameter `n` and group parameters `d`, `choose` picks both
parties' inputs and a state; `guess` sees the state, the views of the parties in `I` and both
parties' outputs, and returns a bit. -/
structure DDHOTDistinguisher (I : Finset (Fin 2)) where
  /-- Choose the inputs of both parties and a state. -/
  choose : ℕ → (d : F.Desc) → ProbComp (OTChoice (F.Carrier d))
  /-- Guess from the state and the joint value of the corrupted parties. -/
  guess : ℕ → (d : F.Desc) → List Bool → DDHOTJoint (F.Carrier d) (F.order d) I → ProbComp Bool

/-- The real game: draw group parameters `d` from the setup law, let `A` choose the inputs, run
`ddhOTProtocol` in `F.Carrier d` with generator `F.generator d`, and give `A` the views of the
corrupted parties `I` and both outputs. -/
@[expose] noncomputable def ddhOTRealGame (setup : ℕ → PMF F.Desc) (I : Finset (Fin 2))
    (A : F.DDHOTDistinguisher I) (n : ℕ) : Game := do
  let d ← setup n
  let c ← ProbComp.eval (A.choose n d)
  let r ← (ddhOTProtocol (F.generator d) (F.order d)).realJoint noOracleWorld I c.inputs
  ProbComp.eval (A.guess n d c.state r)

/-- A simulator family for the corrupted parties `I` of `ddhOTProtocol` over the family `F`: for
the security parameter `n` and group parameters `d`, a simulator `S n d` that produces the views of
the parties in `I` from their inputs and outputs. The simulator may depend on the security
parameter, for instance to sample approximately uniform exponents with `sampleExp`. Nothing here
asks it to be efficient. -/
abbrev DDHOTSimulator (I : Finset (Fin 2)) : Type :=
  ℕ → (d : F.Desc) → CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
    (DDHOTCoins (F.order d)) (OTOut (F.Carrier d)) I

/-- The ideal game: draw group parameters `d` from the setup law, let `A` choose the inputs,
compute the outputs of `otFunctionality`, let the simulator `S n d` produce the views of the
corrupted parties `I` from their inputs and outputs, and give `A` these views and both outputs. -/
@[expose] noncomputable def ddhOTIdealGame (setup : ℕ → PMF F.Desc) (I : Finset (Fin 2))
    (S : F.DDHOTSimulator I) (A : F.DDHOTDistinguisher I) (n : ℕ) : Game := do
  let d ← setup n
  let c ← ProbComp.eval (A.choose n d)
  let r ← ProbComp.eval (idealJoint (otFunctionality (F.Carrier d)) I (S n d) c.inputs)
  ProbComp.eval (A.guess n d c.state r)

/-! ### Efficiency of receiver-corrupting distinguishers -/

/-- The input of the guessing stage of a distinguisher that corrupts the receiver, as a record:
the security parameter, the group parameters, the saved state, and the corrupted receiver's
choice bit, coin, first received message, the two branch ciphertexts of the sender's reply, and
the receiver's output. `DDHOTReceiverGuessInput.joint` rebuilds the joint value, and every joint
value arises this way (`DDHOTReceiverGuessInput.exists_joint_eq`). -/
structure DDHOTReceiverGuessInput where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- The group parameters. -/
  groupParameters : F.Desc
  /-- The state saved by the choosing stage. -/
  state : List Bool
  /-- The receiver's choice bit `σ`. -/
  choiceBit : Bool
  /-- The receiver's coin `b`. -/
  coin : ZMod (F.order groupParameters)
  /-- The sender's first message `u`. -/
  firstMessage : F.Carrier groupParameters
  /-- The first component of the ciphertext of branch `0`. -/
  ephemeral₀ : F.Carrier groupParameters
  /-- The second component of the ciphertext of branch `0`. -/
  body₀ : F.Carrier groupParameters
  /-- The first component of the ciphertext of branch `1`. -/
  ephemeral₁ : F.Carrier groupParameters
  /-- The second component of the ciphertext of branch `1`. -/
  body₁ : F.Carrier groupParameters
  /-- The receiver's output. -/
  output : F.Carrier groupParameters

/-- The encoding of a guessing-stage input: the unary security parameter, the group parameters,
the state, the choice bit, the coin as the binary number `b.val`, and the words `F.encode d x` of
the seven group elements, each framed except the last. -/
enc_structure encDDHOTReceiverGuessInput (F : PrimeOrderGroupFamily) :
    DDHOTReceiverGuessInput F where
  secParam : encUnary, groupParameters : F.encDesc, state : encBits, choiceBit : encBool,
  coin : (fun b : ZMod (F.order groupParameters) => encNat b.val)
    using (encNat.injective.comp (ZMod.val_injective _)),
  firstMessage : (F.encode groupParameters) using (F.encode_injective groupParameters),
  ephemeral₀ : (F.encode groupParameters) using (F.encode_injective groupParameters),
  body₀ : (F.encode groupParameters) using (F.encode_injective groupParameters),
  ephemeral₁ : (F.encode groupParameters) using (F.encode_injective groupParameters),
  body₁ : (F.encode groupParameters) using (F.encode_injective groupParameters),
  output : (F.encode groupParameters) using (F.encode_injective groupParameters)

variable {F}

/-- The joint value described by a guessing-stage input: the corrupted receiver's view in
`ddhOTProtocol`, and the outputs `()` of the sender and `output` of the receiver. -/
@[expose] def DDHOTReceiverGuessInput.joint (y : F.DDHOTReceiverGuessInput) :
    DDHOTJoint (F.Carrier y.groupParameters) (F.order y.groupParameters) {1} :=
  (singletonView (ddhOTReceiverView y.choiceBit y.coin y.firstMessage
      ((y.ephemeral₀, y.body₀), (y.ephemeral₁, y.body₁))),
    fun i => Fin.cases (motive := fun i => OTOut (F.Carrier y.groupParameters) i) ()
      (fun _ => y.output) i)

/-- Every joint value of a corrupted receiver is described by a guessing-stage input, so
`DDHOTDistinguisher.IsPPT` constrains the guessing stage on all of its inputs. -/
theorem DDHOTReceiverGuessInput.exists_joint_eq (n : ℕ) (d : F.Desc) (state : List Bool)
    (j : DDHOTJoint (F.Carrier d) (F.order d) {1}) :
    ∃ (σ : Bool) (b : ZMod (F.order d)) (u e₀ c₀ e₁ c₁ m : F.Carrier d),
      (⟨n, d, state, σ, b, u, e₀, c₀, e₁, c₁, m⟩ : F.DDHOTReceiverGuessInput).joint = j := by
  obtain ⟨v, out⟩ := j
  let view := v ⟨1, Finset.mem_singleton_self 1⟩
  let reply := view.received.2.2.1 rfl
  refine ⟨view.input, view.coins, view.received.1 rfl, reply.1.1, reply.1.2, reply.2.1, reply.2.2,
    out 1, Prod.ext (funext fun ⟨i, hi⟩ => ?_) (funext fun i => ?_)⟩
  · obtain rfl := Finset.mem_singleton.mp hi
    refine PartyView.ext rfl rfl (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl)))
    · exact Round.received_message_ext fun _ => rfl
    · exact Round.received_message_eq_of_ne (by simp) _ _
    · exact Round.received_message_ext fun _ => rfl
  · fin_cases i <;> rfl

/-- A distinguisher that corrupts the receiver is PPT when its choosing stage is computed by a
uniform strict PPT machine that reads the unary security parameter and the group parameters and
writes the chosen inputs with encoded messages (`encOTChoice`), and its guessing stage by one that
reads `encDDHOTReceiverGuessInput` and writes the output bit. -/
structure DDHOTDistinguisher.IsPPT (A : F.DDHOTDistinguisher {1}) : Prop where
  /-- The choosing stage is uniform strict PPT. -/
  choose : IsPPTOn (encPair encUnary F.encDesc) encOTChoice
    fun ⟨n, d⟩ => OTChoice.map (F.encode d) <$> A.choose n d
  /-- The guessing stage is uniform strict PPT. -/
  guess : IsPPTOn F.encDDHOTReceiverGuessInput encBool
    fun y => A.guess y.secParam y.groupParameters y.state y.joint

variable (F)

/-- A step towards [BonehShoup2023], Theorem 23.7, not the security notion of that theorem:
indistinguishability of the real and simulated runs of `ddhOTProtocol` over the family `F` for a
setup law, with given simulator families `S₀` and `S₁` and no efficiency requirement on them. The
source's notion asks for an efficient simulator (Definition 23.5, p. 1044, and Section 23.5.2.2,
p. 1043). Against a corrupted sender, the real game and the ideal game with `S₀` are
indistinguishable for every distinguisher; against a corrupted receiver, the real game and the
ideal game with `S₁` are indistinguishable for every PPT distinguisher. -/
@[expose] def ddhOTRealIdealIndistinguishable (setup : ℕ → PMF F.Desc) (S₀ : F.DDHOTSimulator {0})
    (S₁ : F.DDHOTSimulator {1}) : Prop :=
  Game.Indistinguishable (F.ddhOTRealGame setup {0}) (F.ddhOTIdealGame setup {0} S₀)
      (fun _ => True) ∧
    Game.Indistinguishable (F.ddhOTRealGame setup {1}) (F.ddhOTIdealGame setup {1} S₁)
      DDHOTDistinguisher.IsPPT

/-! ### Corrupted sender -/

/-- **Perfect simulation of a corrupted sender**: for every distinguisher, the real game and the
ideal game with `ddhOTSenderSim` are equal. -/
theorem ddhOTRealGame_sender_eq (setup : ℕ → PMF F.Desc) (A : F.DDHOTDistinguisher {0})
    (n : ℕ) :
    F.ddhOTRealGame setup {0} A n =
      F.ddhOTIdealGame setup {0} (fun _ d => ddhOTSenderSim (F.generator d) (F.order d)) A n := by
  simp only [ddhOTRealGame, ddhOTIdealGame, idealJoint_ddhOT_sender]

/-! ### Corrupted receiver: the reduction to DDH -/

/-- The DDH distinguisher built from a distinguisher `A` that corrupts the receiver: given the
security parameter `n`, group parameters `d` and a DDH triple `(u, v, w)`, run `A.choose`, draw
the receiver's coin `b` and the chosen branch's coins `r, s` with `sampleExp`, and run
`ddhOTReductionWithCoins` with `A.guess`, which embeds the triple into the unchosen branch. -/
@[expose] noncomputable def ddhOTReceiverToDDHDistinguisher (A : F.DDHOTDistinguisher {1}) :
    F.DDHDistinguisher := fun n d u v w => do
  let c ← A.choose n d
  let b ← F.sampleExp n d
  let r ← F.sampleExp n d
  let s ← F.sampleExp n d
  ddhOTReductionWithCoins (F.generator d) c.inputs (A.guess n d c.state)
    (b : ZMod (F.order d)) (r : ZMod (F.order d)) (s : ZMod (F.order d)) u v w

/-- The reduction with exact uniform coins: run `A.choose`, then `ddhOTReduction`. It is not PPT;
it compares the games with the DDH games of `ddhOTReceiverToDDHDistinguisher`. -/
private noncomputable def ddhOTReceiverToDDHExact (A : F.DDHOTDistinguisher {1}) :
    F.DDHDistinguisher := fun n d u v w => do
  let c ← A.choose n d
  ddhOTReduction (F.generator d) (F.order d) c.inputs (A.guess n d c.state) u v w

/-- The real game against a corrupted receiver is the real DDH game of the exact reduction. -/
private theorem ddhOTRealGame_receiver_eq (setup : ℕ → PMF F.Desc)
    (A : F.DDHOTDistinguisher {1}) (n : ℕ) :
    F.ddhOTRealGame setup {1} A n = F.ddhRealGame setup (F.ddhOTReceiverToDDHExact A) n := by
  simp only [ddhOTRealGame, ddhRealGame, Game.withSetup, PMF.monad_bind_eq_bind]
  refine congrArg (PMF.bind _) (funext fun d => ?_)
  simp only [real_receiver_eq_ddhRealExperiment, eval_ddhRealExperiment,
    ddhOTReceiverToDDHExact, ProbComp.eval_bind]
  pmf_swap

/-- The ideal game against a corrupted receiver is the random DDH game of the exact
reduction. -/
private theorem ddhOTIdealGame_receiver_eq (setup : ℕ → PMF F.Desc)
    (A : F.DDHOTDistinguisher {1}) (n : ℕ) :
    F.ddhOTIdealGame setup {1} (fun _ d => ddhOTReceiverSim (F.generator d) (F.order d)) A n =
      F.ddhRandomGame setup (F.ddhOTReceiverToDDHExact A) n := by
  simp only [ddhOTIdealGame, ddhRandomGame, Game.withSetup, PMF.monad_bind_eq_bind]
  refine congrArg (PMF.bind _) (funext fun d => ?_)
  simp only [← ProbComp.eval_bind,
    ideal_receiver_eq_ddhRandomExperiment _ _ (F.smul_generator_surjective d)]
  simp only [eval_ddhRandomExperiment, ddhOTReceiverToDDHExact, ProbComp.eval_bind]
  pmf_swap

/-- On every triple, the exact and the `sampleExp` reductions accept with probabilities within
`3 / 2 ^ n`. -/
private theorem advantage_ddhOTReceiverToDDHExact_le (A : F.DDHOTDistinguisher {1}) (n : ℕ)
    (d : F.Desc) (u v w : F.Carrier d) :
    Game.advantage (ProbComp.eval (F.ddhOTReceiverToDDHExact A n d u v w))
      (ProbComp.eval (F.ddhOTReceiverToDDHDistinguisher A n d u v w)) ≤ 3 / 2 ^ n := by
  simp only [ddhOTReceiverToDDHExact, ddhOTReceiverToDDHDistinguisher, ddhOTReduction,
    ProbComp.eval_bind, ProbComp.eval_uniform]
  refine Game.advantage_bind_le_nnreal _ _ _ fun c => ?_
  rw [Game.advantage_comm]
  exact F.advantage_bind_sampleExp_triple_le n d fun b r s =>
    ProbComp.eval (ddhOTReductionWithCoins (F.generator d) c.inputs (A.guess n d c.state)
      b r s u v w)

/-- **Concrete bound for a corrupted receiver**: the advantage of `A` between the real game and
the ideal game with `ddhOTReceiverSim` is at most the DDH advantage of
`ddhOTReceiverToDDHDistinguisher A` plus `6 / 2 ^ n`. -/
theorem advantage_ddhOTReceiverGame_le (setup : ℕ → PMF F.Desc) (A : F.DDHOTDistinguisher {1})
    (n : ℕ) :
    Game.advantage (F.ddhOTRealGame setup {1} A n)
        (F.ddhOTIdealGame setup {1} (fun _ d => ddhOTReceiverSim (F.generator d) (F.order d)) A n) ≤
      Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher A) n)
        (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher A) n) + 6 / 2 ^ n := by
  rw [ddhOTRealGame_receiver_eq, ddhOTIdealGame_receiver_eq]
  have hreal : Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHExact A) n)
      (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher A) n) ≤ 3 / 2 ^ n := by
    simp only [ddhRealGame, Game.withSetup, eval_ddhRealExperiment]
    exact Game.advantage_bind_le_nnreal _ _ _ fun d =>
      Game.advantage_bind_le_nnreal _ _ _ fun a => Game.advantage_bind_le_nnreal _ _ _ fun b =>
        F.advantage_ddhOTReceiverToDDHExact_le A n d _ _ _
  have hrandom : Game.advantage (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher A) n)
      (F.ddhRandomGame setup (F.ddhOTReceiverToDDHExact A) n) ≤ 3 / 2 ^ n := by
    rw [Game.advantage_comm]
    simp only [ddhRandomGame, Game.withSetup, eval_ddhRandomExperiment]
    exact Game.advantage_bind_le_nnreal _ _ _ fun d =>
      Game.advantage_bind_le_nnreal _ _ _ fun a => Game.advantage_bind_le_nnreal _ _ _ fun b =>
        Game.advantage_bind_le_nnreal _ _ _ fun c =>
          F.advantage_ddhOTReceiverToDDHExact_le A n d _ _ _
  calc _ ≤ 3 / 2 ^ n + (Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher A) n)
          (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher A) n) + 3 / 2 ^ n) :=
        (Game.advantage_triangle _ _ _).trans (add_le_add hreal
          ((Game.advantage_triangle _ _ _).trans (add_le_add le_rfl hrandom)))
    _ = _ := by ring

/-! ### Corrupted receiver: efficiency of the reduction -/

/-- The words of the guessing-stage input that `ddhOTReceiverToDDHDistinguisher` gives the
distinguisher, laid out as `encDDHOTReceiverGuessInputFields`, from the DDH input `x`, the choice
`cw` with encoded messages and the coins `b, r, s`. The second components of the branch
ciphertexts add the encoded messages with `F.add`, and `-b` is `F.order d - b % F.order d`. -/
private def ddhOTReceiverGuessWords (x : F.DDHInput) (cw : OTChoice (List Bool)) (b r s : ℕ) :
    ℕ × F.Desc × List Bool × Bool × List Bool × List Bool × List Bool × List Bool × List Bool ×
      List Bool × List Bool :=
  let d := x.groupParameters
  let q := F.order d
  let e := (r : ZMod q) • F.generator d + (s : ZMod q) • x.leftPublic
  let chosen := F.encode d ((b : ZMod q) • e)
  let other := F.encode d (x.candidateShared + ((q - b % q : ℕ) : ZMod q) • x.rightPublic)
  let σ := cw.choiceBit
  (x.secParam, d, cw.state, σ, encNat (b % q), F.encode d x.leftPublic,
    if σ then F.encode d x.rightPublic else F.encode d e,
    F.add (d, if σ then other else chosen, cw.message₀),
    if σ then F.encode d e else F.encode d x.rightPublic,
    F.add (d, if σ then chosen else other, cw.message₁),
    if σ then cw.message₁ else cw.message₀)

/-- `ddhOTReceiverToDDHDistinguisher A` is uniform strict PPT whenever `A` is. -/
theorem isPPT_ddhOTReceiverToDDHDistinguisher {A : F.DDHOTDistinguisher {1}} (hA : A.IsPPT) :
    (F.ddhOTReceiverToDDHDistinguisher A).IsPPT := by
  obtain ⟨W, hW, hWeq⟩ := hA.guess.exists_bool_factor F.encDDHOTReceiverGuessInput_apply
  let E := encPair (encPair (encPair (encPair F.encDDHInput encOTChoice) encNat) encNat) encNat
  have hx : ComputableInPolyTime (fun p : (((F.DDHInput × OTChoice (List Bool)) × ℕ) × ℕ) × ℕ =>
      p.1.1.1.1) E F.encDDHInput := by fun_prop
  have hcw : ComputableInPolyTime (fun p : (((F.DDHInput × OTChoice (List Bool)) × ℕ) × ℕ) × ℕ =>
      p.1.1.1.2) E encOTChoice := by fun_prop
  have hb : ComputableInPolyTime (fun p : (((F.DDHInput × OTChoice (List Bool)) × ℕ) × ℕ) × ℕ =>
      p.1.1.2) E encNat := by fun_prop
  have hr : ComputableInPolyTime (fun p : (((F.DDHInput × OTChoice (List Bool)) × ℕ) × ℕ) × ℕ =>
      p.1.2) E encNat := by fun_prop
  have hs : ComputableInPolyTime (fun p : (((F.DDHInput × OTChoice (List Bool)) × ℕ) × ℕ) × ℕ =>
      p.2) E encNat := by fun_prop
  have hd := F.encDDHInput_groupParameters_polyTime hx
  have hu := F.encDDHInput_leftPublic_polyTime hx
  have hv := F.encDDHInput_rightPublic_polyTime hx
  have hw := F.encDDHInput_candidateShared_polyTime hx
  have hq := F.computableInPolyTime_order.comp hd
  have hmod := ComputableInPolyTime.binary_mod' hb hq
  have he := computableInPolyTime_encode_add hd
    (computableInPolyTime_encode_natCast_smul hd hr (computableInPolyTime_encode_generator hd))
    (computableInPolyTime_encode_natCast_smul hd hs hu)
  have hchosen := computableInPolyTime_encode_natCast_smul hd hb he
  have hother := computableInPolyTime_encode_add hd hw
    (computableInPolyTime_encode_natCast_smul hd (ComputableInPolyTime.binary_sub' hq hmod) hv)
  have hσ := encOTChoice_choiceBit_polyTime hcw
  have hm₀ := encOTChoice_message₀_polyTime hcw
  have hm₁ := encOTChoice_message₁_polyTime hcw
  have hwords : ComputableInPolyTime
      (fun p : (((F.DDHInput × OTChoice (List Bool)) × ℕ) × ℕ) × ℕ =>
        F.ddhOTReceiverGuessWords p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
      E F.encDDHOTReceiverGuessInputFields :=
    (F.encDDHInput_secParam_polyTime hx).prod (hd.prod ((encOTChoice_state_polyTime hcw).prod
      (hσ.prod (hmod.encoding_comp.prod (hu.prod ((hσ.ite' hv he).prod
        ((F.computableInPolyTime_add.comp (hd.prod ((hσ.ite' hother hchosen).prod hm₀))).prod
          ((hσ.ite' he hv).prod
            ((F.computableInPolyTime_add.comp (hd.prod ((hσ.ite' hchosen hother).prod hm₁))).prod
              (hσ.ite' hm₁ hm₀))))))))))
  have hsample {α : Type} {enc : α ↪ List Bool} {x : α → F.DDHInput}
      (hx : ComputableInPolyTime x enc F.encDDHInput) :
      IsPPTOn enc encNat fun a => F.sampleExp (x a).secParam (x a).groupParameters :=
    F.isPPTOn_sampleExp (by fun_prop) (by fun_prop)
  have hprogram : IsPPTOn F.encDDHInput encBool (fun x => do
      let cw ← OTChoice.map (F.encode x.groupParameters) <$>
        A.choose x.secParam x.groupParameters
      let b ← F.sampleExp x.secParam x.groupParameters
      let r ← F.sampleExp x.secParam x.groupParameters
      let s ← F.sampleExp x.secParam x.groupParameters
      W (F.ddhOTReceiverGuessWords x cw b r s)) := by
    refine IsPPTOn.bind_with (hA.choose.preprocess
      (prepare := fun x : F.DDHInput => (x.secParam, x.groupParameters)) (by fun_prop)) ?_
    refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
    refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
    refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
    exact hW.preprocess hwords
  refine hprogram.congr fun x => ?_
  simp only [ddhOTReceiverToDDHDistinguisher, ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun c => congrArg (PMF.bind _) (funext fun b =>
    congrArg (PMF.bind _) (funext fun r => congrArg (PMF.bind _) (funext fun s => ?_))))
  obtain ⟨m₀, m₁, σ, state⟩ := c
  have hneg : ((F.order x.groupParameters - b % F.order x.groupParameters : ℕ) :
      ZMod (F.order x.groupParameters)) = -(b : ZMod (F.order x.groupParameters)) := by
    rw [Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ (F.prime_order _).pos)), ZMod.natCast_self,
      ZMod.natCast_mod, zero_sub]
  let d := x.groupParameters
  let e := (r : ZMod (F.order d)) • F.generator d + (s : ZMod (F.order d)) • x.leftPublic
  cases σ
  · refine congrArg ProbComp.eval (Eq.trans ?_ (hWeq ⟨x.secParam, d, state, false, b,
      x.leftPublic, e, (b : ZMod (F.order d)) • e + m₀, x.rightPublic,
      x.candidateShared - (b : ZMod (F.order d)) • x.rightPublic + m₁, m₀⟩).symm)
    simp only [ddhOTReceiverGuessWords, OTChoice.map, Bool.false_eq_true, ↓reduceIte,
      F.add_encode, hneg, neg_smul, ← sub_eq_add_neg, ZMod.val_natCast]
    rfl
  · refine congrArg ProbComp.eval (Eq.trans ?_ (hWeq ⟨x.secParam, d, state, true, b,
      x.leftPublic, x.rightPublic, x.candidateShared - (b : ZMod (F.order d)) • x.rightPublic + m₀,
      e, (b : ZMod (F.order d)) • e + m₁, m₁⟩).symm)
    simp only [ddhOTReceiverGuessWords, OTChoice.map, ↓reduceIte,
      F.add_encode, hneg, neg_smul, ← sub_eq_add_neg, ZMod.val_natCast]
    rfl

/-- A step towards [BonehShoup2023], Theorem 23.7, not the cited result: `F.DDH setup` implies
that the real runs of DDH oblivious transfer are indistinguishable from the ideal runs with the
exact-sampling simulators `ddhOTSenderSim` and `ddhOTReceiverSim`. The theorem also asks the
simulators to be efficient, and these sample exact uniform exponents and are not shown to be PPT.
The only premise is `F.DDH setup`; the reduction is certified by
`isPPT_ddhOTReceiverToDDHDistinguisher`. -/
theorem DDH.ddhOTRealIdealIndistinguishable_exactSim {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} (hDDH : F.DDH setup) :
    F.ddhOTRealIdealIndistinguishable setup (fun _ d => ddhOTSenderSim (F.generator d) (F.order d))
      (fun _ d => ddhOTReceiverSim (F.generator d) (F.order d)) := by
  refine ⟨fun A _ => ?_, fun A hA => ?_⟩
  · simp only [ddhOTRealGame_sender_eq, Game.advantage_self]
    negligible
  · have hB := hDDH _ (F.isPPT_ddhOTReceiverToDDHDistinguisher hA)
    negligible using F.advantage_ddhOTReceiverGame_le setup A

end Cslib.Crypto.PrimeOrderGroupFamily
