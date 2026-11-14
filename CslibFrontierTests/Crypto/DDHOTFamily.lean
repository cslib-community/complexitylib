/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Family

/-! # DDH oblivious transfer over a group family: module clients

Clients of `CslibFrontier.Crypto.Protocols.MPC.DDHOT.Family` under module encapsulation:
* the encoded words of `encOTChoice` and `encDDHOTReceiverGuessInput`;
* a receiver-corrupting distinguisher that satisfies `DDHOTDistinguisher.IsPPT`, so the class of
  admitted distinguishers is not empty;
* the two halves of `DDH.ddhOTRealIdealIndistinguishable_exactSim` and the concrete bound behind
  the receiver half. -/

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols.MPC
  Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal

public section

namespace CslibFrontierTests.Crypto.DDHOTFamily

-- The encoded words of a word choice: `m₀`, `m₁`, `σ` and the state, all but the last framed.
example (c : OTChoice (List Bool)) :
    encOTChoice c =
      encPair encBits (encPair encBits (encPair encBool encBits))
        (c.message₀, c.message₁, c.choiceBit, c.state) :=
  encOTChoice_apply c

-- The encoded words of a guessing-stage input.
example (F : PrimeOrderGroupFamily) (y : F.DDHOTReceiverGuessInput) :
    F.encDDHOTReceiverGuessInput y =
      encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBool (encPair encBits
        (encPair encBits (encPair encBits (encPair encBits (encPair encBits (encPair encBits
          encBits)))))))))
        (y.secParam, y.groupParameters, y.state, y.choiceBit, encNat y.coin.val,
          F.encode _ y.firstMessage, F.encode _ y.ephemeral₀, F.encode _ y.body₀,
          F.encode _ y.ephemeral₁, F.encode _ y.body₁, F.encode _ y.output) :=
  F.encDDHOTReceiverGuessInput_apply y

/-- A receiver-corrupting distinguisher that sends the messages `0` and `g` with choice bit
`false`, and always guesses `true`. -/
noncomputable def constantDistinguisher (F : PrimeOrderGroupFamily) :
    F.DDHOTDistinguisher {1} where
  choose _ d := pure ⟨0, F.generator d, false, []⟩
  guess _ _ _ _ := pure true

-- The class of PPT distinguishers is not empty.
example (F : PrimeOrderGroupFamily) : (constantDistinguisher F).IsPPT where
  choose := by
    refine (ComputableInPolyTime.isPPTOn (f := fun p : ℕ × F.Desc =>
      (⟨F.encode p.2 0, F.encode p.2 (F.generator p.2), false, []⟩ : OTChoice (List Bool)))
      (by fun_prop)).congr fun _ => rfl
  guess := (ComputableInPolyTime.const true).isPPTOn

-- Against a corrupted sender, the games are equal for every distinguisher.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (A : F.DDHOTDistinguisher {0})
    (n : ℕ) :
    Game.advantage (F.ddhOTRealGame setup {0} A n)
      (F.ddhOTIdealGame setup {0} (fun _ d => ddhOTSenderSim (F.generator d) (F.order d)) A n) =
      0 := by
  rw [F.ddhOTRealGame_sender_eq, Game.advantage_self]

-- Against a corrupted receiver, the advantage is the DDH advantage of an explicit reduction plus
-- `6 / 2 ^ n`.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (A : F.DDHOTDistinguisher {1})
    (n : ℕ) :
    Game.advantage (F.ddhOTRealGame setup {1} A n)
        (F.ddhOTIdealGame setup {1} (fun _ d => ddhOTReceiverSim (F.generator d) (F.order d)) A n) ≤
      Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher A) n)
        (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher A) n) + 6 / 2 ^ n :=
  F.advantage_ddhOTReceiverGame_le setup A n

-- Under DDH, every PPT receiver-corrupting distinguisher has negligible advantage.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (hDDH : F.DDH setup)
    (A : F.DDHOTDistinguisher {1}) (hA : A.IsPPT) :
    Negligible fun n => Game.advantage (F.ddhOTRealGame setup {1} A n)
      (F.ddhOTIdealGame setup {1} (fun _ d => ddhOTReceiverSim (F.generator d) (F.order d)) A n) :=
  hDDH.ddhOTRealIdealIndistinguishable_exactSim.2 A hA

-- The same for the constant distinguisher.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (hDDH : F.DDH setup)
    (hA : (constantDistinguisher F).IsPPT) :
    Negligible fun n => Game.advantage (F.ddhOTRealGame setup {1} (constantDistinguisher F) n)
      (F.ddhOTIdealGame setup {1} (fun _ d => ddhOTReceiverSim (F.generator d) (F.order d))
        (constantDistinguisher F) n) :=
  hDDH.ddhOTRealIdealIndistinguishable_exactSim.2 _ hA

-- Every joint value of a corrupted receiver is described by a guessing-stage input.
example (F : PrimeOrderGroupFamily) (n : ℕ) (d : F.Desc)
    (j : DDHOTJoint (F.Carrier d) (F.order d) {1}) :
    ∃ (σ : Bool) (b : ZMod (F.order d)) (u e₀ c₀ e₁ c₁ m : F.Carrier d),
      (⟨n, d, [], σ, b, u, e₀, c₀, e₁, c₁, m⟩ : F.DDHOTReceiverGuessInput).joint = j :=
  DDHOTReceiverGuessInput.exists_joint_eq n d [] j

end CslibFrontierTests.Crypto.DDHOTFamily
