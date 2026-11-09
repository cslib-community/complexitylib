/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Crypto.Protocols.MPC.DDHOT

/-! # Three-Message DDH Oblivious Transfer: checked instances

Concrete checks for `Cslib.Crypto.Protocols.MPC.ddhOTProtocol` instantiated over the additive
cyclic group `ZMod 5` of order `5` with generator `1 : ZMod 5`:
* Computational check (`decide`) that for every sender message pair `(m₀, m₁) : ZMod 5 × ZMod 5`,
  receiver choice bit `σ : Bool`, and receiver mask `b : ZMod 5`, `ddhOTReceiverOutput` recovers
  `if σ then m₁ else m₀`.
* Computational check (`decide`) that on the unchecked variant `ddhOTSenderReplyUnchecked`,
  `ddhOTAttackBothMessages` simultaneously recovers `(m₀, m₁)`.
* `ddhOT_output_of_mem_support`: in every execution of `ddhOTProtocol` over `ZMod 5`, the outputs
  equal `otOutputs x`.
* `idealJoint_ddhOT_sender` and `semiHonestAdvantage_ddhOT_sender`: unconditional perfect privacy
  (zero distinguishing advantage) against a corrupted sender.
* `semiHonestAdvantage_ddhOT_receiver_eq`: computational privacy against a corrupted receiver
  reduced tightly to `DDH.advantage`.
* `ddhOTUnchecked_malicious_receiver_advantage`: any single-query ideal simulator falls short of
  the malicious receiver's simultaneous-recovery success probability on `ZMod 5` by `1 - 5⁻¹`. -/

namespace ComplexityTests.Crypto.DDHOT

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto Cslib.Crypto.Protocols.MPC

private theorem zmod5_nsmul_eq_zero : ∀ y : ZMod 5, (5 : ℕ) • y = 0 := by decide

private theorem zmod5_card : Fintype.card (ZMod 5) = 5 := ZMod.card 5

private theorem zmod5_gen : ∀ y : ZMod 5, ∃ k : ZMod 5, k.val • (1 : ZMod 5) = y := by decide

-- Pointwise decryption check across all choices of σ, sender messages, and receiver mask in ZMod 5.
example : ∀ (σ : Bool) (m₀ m₁ b : ZMod 5),
    let c₀ : DDHOTSenderCoins 5 := (2, 1, 3, 4, 2)
    let u := c₀.1.val • (1 : ZMod 5)
    let v := ddhOTReceiverMsg (1 : ZMod 5) σ b u
    let reply := ddhOTSenderReply (1 : ZMod 5) (m₀, m₁) c₀ v
    ddhOTReceiverOutput σ b reply = (if σ then m₁ else m₀) := by
  decide

-- Simultaneous recovery of both sender messages on the unchecked variant in ZMod 5.
example : ∀ (m₀ m₁ b₀ b₁ : ZMod 5),
    let c₀ : DDHOTSenderCoins 5 := (2, 1, 3, 4, 2)
    let v := ddhOTAttackMsg (1 : ZMod 5) b₀ b₁
    let reply := ddhOTSenderReplyUnchecked (1 : ZMod 5) (m₀, m₁) c₀ v
    ddhOTAttackBothMessages b₀ b₁ reply = (m₀, m₁) := by
  decide

-- Correctness: in every run of the three-message DDH OT protocol over ZMod 5, the outputs equal
-- `otOutputs x`.
example (x : (i : Fin 2) → OTIn (ZMod 5) i)
    {r : ((i : Fin 2) → PartyView (OTIn (ZMod 5)) (DDHOTCoins 5) (ddhOTSchedule (ZMod 5)) i) ×
      ((i : Fin 2) → OTOut (ZMod 5) i)}
    (hr : r ∈ ((ddhOTProtocol (1 : ZMod 5) 5).evalWith noOracleWorld x).support) :
    r.2 = otOutputs x :=
  ddhOT_output_of_mem_support (1 : ZMod 5) 5 x hr

-- Perfect privacy against a corrupted sender over ZMod 5.
example (x : (i : Fin 2) → OTIn (ZMod 5) i) :
    ProbComp.eval (idealJoint (otFunctionality (ZMod 5)) {0}
        (ddhOTSenderSim (1 : ZMod 5) 5) x) =
      (ddhOTProtocol (1 : ZMod 5) 5).realJoint noOracleWorld {0} x :=
  idealJoint_ddhOT_sender (1 : ZMod 5) 5 zmod5_nsmul_eq_zero x

-- Zero semi-honest advantage against a corrupted sender over ZMod 5.
example (x : (i : Fin 2) → OTIn (ZMod 5) i)
    (D : ((i : ({0} : Finset (Fin 2))) →
        PartyView (OTIn (ZMod 5)) (DDHOTCoins 5) (ddhOTSchedule (ZMod 5)) i) ×
      ((i : Fin 2) → OTOut (ZMod 5) i) → ProbComp Bool) :
    semiHonestAdvantage (ddhOTProtocol (1 : ZMod 5) 5) noOracleWorld
        (otFunctionality (ZMod 5)) {0} (ddhOTSenderSim (1 : ZMod 5) 5) x D = 0 :=
  semiHonestAdvantage_ddhOT_sender (1 : ZMod 5) 5 zmod5_nsmul_eq_zero x D

-- Tight DDH reduction for a corrupted receiver over ZMod 5.
example (x : (i : Fin 2) → OTIn (ZMod 5) i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn (ZMod 5)) (DDHOTCoins 5) (ddhOTSchedule (ZMod 5)) i) ×
      ((i : Fin 2) → OTOut (ZMod 5) i) → ProbComp Bool) :
    semiHonestAdvantage (ddhOTProtocol (1 : ZMod 5) 5) noOracleWorld
        (otFunctionality (ZMod 5)) {1} (ddhOTReceiverSim (1 : ZMod 5) 5) x D =
      DDH.advantage (1 : ZMod 5) 5 (ddhOTReduction (1 : ZMod 5) 5 x D) :=
  semiHonestAdvantage_ddhOT_receiver_eq (1 : ZMod 5) 5 zmod5_card zmod5_gen x D

-- Unchecked malicious-receiver separation against any single-query simulator over ZMod 5.
example (b₀ b₁ : ZMod 5) (S : Bool → ZMod 5 → ProbComp (ZMod 5 × ZMod 5)) (σ : Bool) :
    (Game.advantage (ProbComp.eval (ddhOTUncheckedRealGame (1 : ZMod 5) 5 b₀ b₁ σ))
      (ProbComp.eval (ddhOTUncheckedIdealGame S σ)) : ℝ) = 1 - (5 : ℝ)⁻¹ := by
  simpa [zmod5_card] using
    ddhOTUnchecked_malicious_receiver_advantage (1 : ZMod 5) 5 b₀ b₁ S σ

end ComplexityTests.Crypto.DDHOT
