/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Simulators

/-! # PPT simulators for DDH oblivious transfer: module clients

Clients of `CslibFrontier.Crypto.Protocols.MPC.DDHOT.Simulators` under module encapsulation:
* the encoded words of a simulator's input and of the simulated views;
* the PPT certificates of the `sampleExp` simulator families and their statistical distance from
  the exact-sampling simulators;
* the PPT predicates `DDHOTSimulator.IsPPTSender` and `DDHOTSimulator.IsPPTReceiver`, introduced
  from a machine certificate and consumed as one;
* `DDH.ddhOTStandaloneSemiHonestSecure`, unfolded to its witnesses. -/

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols.MPC
  Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal

public section

namespace CslibFrontierTests.Crypto.DDHOTSimulators

-- The encoded words of a receiver simulator's input.
example (F : PrimeOrderGroupFamily) (x : F.DDHOTReceiverSimInput) :
    F.encDDHOTReceiverSimInput x =
      encPair encUnary (encPair F.encDesc (encPair encBool encBits))
        (x.secParam, x.groupParameters, x.choiceBit, F.encode _ x.output) :=
  F.encDDHOTReceiverSimInput_apply x

-- The encoded words of a receiver's view.
example (w : DDHOTReceiverViewWords) :
    encDDHOTReceiverViewWords w =
      encPair encBool (encPair encNat (encPair encBits (encPair encBits (encPair encBits
        (encPair encBits encBits)))))
        (w.choiceBit, w.coin, w.firstMessage, w.ephemeral₀, w.body₀, w.ephemeral₁, w.body₁) :=
  encDDHOTReceiverViewWords_apply w

-- The words of a receiver's view determine it.
example (F : PrimeOrderGroupFamily) (d : F.Desc) :
    Function.Injective (F.ddhOTReceiverViewWords d) :=
  F.ddhOTReceiverViewWords_injective d

-- Both `sampleExp` simulator families are PPT.
example (F : PrimeOrderGroupFamily) :
    F.ddhOTSenderSimSampleExp.IsPPTSender ∧ F.ddhOTReceiverSimSampleExp.IsPPTReceiver :=
  ⟨F.isPPTSender_ddhOTSenderSimSampleExp, F.isPPTReceiver_ddhOTReceiverSimSampleExp⟩

-- Introducing the predicate: a sender simulator family with the same output laws as
-- `ddhOTSenderSimSampleExp` is PPT, through the latter's machine certificate.
example (F : PrimeOrderGroupFamily) (S : F.DDHOTSimulator {0})
    (hS : ∀ n d xI yI,
      ProbComp.eval (S n d xI yI) = ProbComp.eval (F.ddhOTSenderSimSampleExp n d xI yI)) :
    S.IsPPTSender :=
  IsPPTOn.congr F.isPPTSender_ddhOTSenderSimSampleExp fun x => by
    simp only [ProbComp.eval_map, hS]

-- Consuming the predicate: the receiver simulator family that
-- `DDH.ddhOTStandaloneSemiHonestSecure` provides writes view words of polynomially bounded length.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (hDDH : F.DDH setup) :
    ∃ (S₁ : F.DDHOTSimulator {1}) (c d : ℕ), ∀ (x : F.DDHOTReceiverSimInput) v,
      v ∈ (ProbComp.eval (S₁ x.secParam x.groupParameters (uniqueElim x.choiceBit)
        (uniqueElim x.output))).support →
      (encDDHOTReceiverViewWords (F.ddhOTReceiverViewWords x.groupParameters
        (v ⟨1, Finset.mem_singleton_self 1⟩))).length ≤
        c * ((F.encDDHOTReceiverSimInput x).length + 1) ^ d := by
  obtain ⟨-, S₁, -, h₁, -⟩ := hDDH.ddhOTStandaloneSemiHonestSecure
  obtain ⟨c, d, h⟩ := IsPPTOn.length_le h₁
  exact ⟨S₁, c, d, fun x v hv => h x _ (by
    simpa only [ProbComp.eval_map, PMF.support_map] using Set.mem_image_of_mem _ hv)⟩

-- Against a corrupted receiver, the ideal games with the exact-sampling and the `sampleExp`
-- simulators differ by at most `6 / 2 ^ n`, for every distinguisher.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (A : F.DDHOTDistinguisher {1})
    (n : ℕ) :
    Game.advantage
        (F.ddhOTIdealGame setup {1} (fun _ d => ddhOTReceiverSim (F.generator d) (F.order d)) A n)
        (F.ddhOTIdealGame setup {1} F.ddhOTReceiverSimSampleExp A n) ≤ 6 / 2 ^ n :=
  F.advantage_ddhOTIdealGame_ddhOTReceiverSimSampleExp_le setup A n

-- Under DDH, there are PPT simulator families for which the real and ideal games are
-- indistinguishable.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (hDDH : F.DDH setup) :
    ∃ (S₀ : F.DDHOTSimulator {0}) (S₁ : F.DDHOTSimulator {1}),
      S₀.IsPPTSender ∧ S₁.IsPPTReceiver ∧ F.ddhOTRealIdealIndistinguishable setup S₀ S₁ :=
  hDDH.ddhOTStandaloneSemiHonestSecure

-- Against a corrupted sender, every distinguisher has negligible advantage with the `sampleExp`
-- simulator family.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (hDDH : F.DDH setup)
    (A : F.DDHOTDistinguisher {0}) :
    Negligible fun n => Game.advantage (F.ddhOTRealGame setup {0} A n)
      (F.ddhOTIdealGame setup {0} F.ddhOTSenderSimSampleExp A n) :=
  hDDH.ddhOTRealIdealIndistinguishable_sampleExpSim.1 A trivial

end CslibFrontierTests.Crypto.DDHOTSimulators
