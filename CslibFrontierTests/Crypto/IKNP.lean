/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Protocols.MPC.IKNP

/-! # IKNP oblivious-transfer extension: checked instances

* Correlation robustness is not vacuous: a constant family has positive advantage against a
  one-query test.
* The key identity `qⱼ + rⱼ s = tⱼ` and the receiver's unmasking, by computation on every input
  and coin for one transfer from one base transfer.
* The correctness theorem and both privacy theorems at concrete parameters, with a toy hash that is
  not correlation robust; the receiver theorem turns a bound on the correlation-robustness
  advantage into a bound on the semi-honest advantage. -/

namespace CslibFrontierTests.Crypto.IKNP

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.MPC Probability

/-! ### Correlation robustness -/

/-- The constant family on one query. -/
def constHash : Fin 1 → BitString 1 → Bool := fun _ _ => false

/-- The test that accepts when the output is `true`. -/
def outputTest : CorrelationRobust.Adversary 1 (BitString 1) Bool := fun p => pure (p.2 0)

-- The constant family is distinguishable from uniform: the advantage is `1 / 2`.
example : CorrelationRobust.advantage constHash outputTest ≠ 0 := by
  have hreal : CorrelationRobust.realGame constHash outputTest = PMF.pure false := by
    simp only [CorrelationRobust.realGame, constHash, outputTest, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.bind_const]
  have hideal : CorrelationRobust.idealGame outputTest = PMF.uniformOfFintype Bool := by
    simp only [CorrelationRobust.idealGame, outputTest, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbComp.eval_uniform, PMF.bind_const]
    exact (PMF.bind_pure_comp _ _).trans
      (Cslib.Probability.PMF.uniformOfFintype_map_equiv (Equiv.funUnique (Fin 1) Bool))
  rw [CorrelationRobust.advantage, hreal, hideal, ne_eq, Game.advantage_pure_false_left]
  simp [Game.succProbability, ENNReal.toNNReal_eq_zero_iff]

/-! ### The protocol's algebra -/

-- The sender's row on the receiver's choice is the receiver's row.
example : ∀ (r : Fin 1 → Bool) (T : Fin 1 → BitString 1) (s : BitString 1) (b : Bool),
    (if b then iknpRows (fun i => iknpColumns r T i (s i)) 0 + s
      else iknpRows (fun i => iknpColumns r T i (s i)) 0) =
      if b = r 0 then T 0 else T 0 + s := by
  decide

-- The receiver unmasks its chosen value, by computation on every input and coin.
example : ∀ (X : Fin 1 → Bool → BitString 1) (r : Fin 1 → Bool) (T : Fin 1 → BitString 1)
    (s : BitString 1),
    iknpMasked (fun _ t => t) X s (fun i => iknpColumns r T i (s i)) 0 (r 0) - T 0 =
      X 0 (r 0) := by
  decide

/-! ### The theorems at concrete parameters -/

/-- A toy hash from `2`-bit rows to `3`-bit values; it is not correlation robust. -/
def toyHash : Fin 4 → BitString 2 → BitString 3 := fun j t i => t 0 && (decide (i = 0) || j = 1)

-- Correctness: four transfers of `3`-bit values from two base transfers of `4`-bit strings.
example (x : (i : Fin 2) → (batchOTSpec 4 (BitString 3)).Query () i)
    {res : ((i : Fin 2) → PartyView ((batchOTSpec 4 (BitString 3)).Query ()) (IKNPCoins 2 4)
        (iknpSchedule 2 4 (BitString 3)) i) ×
      ((i : Fin 2) → (batchOTSpec 4 (BitString 3)).Answer () i)}
    (hres : res ∈ ((iknpProtocol toyHash).evalWith (batchOTWorld 2 (BitString 4)) x).support) :
    res.2 = batchOTAnswer x :=
  iknp_output_of_mem_support toyHash x hres

-- A corrupted sender has advantage zero, whatever the hash.
example (x : (i : Fin 2) → (batchOTSpec 4 (BitString 3)).Query () i)
    (D : ((i : ({0} : Finset (Fin 2))) → PartyView ((batchOTSpec 4 (BitString 3)).Query ())
        (IKNPCoins 2 4) (iknpSchedule 2 4 (BitString 3)) i) ×
      ((i : Fin 2) → (batchOTSpec 4 (BitString 3)).Answer () i) → ProbComp Bool) :
    semiHonestAdvantage (iknpProtocol toyHash) (batchOTWorld 2 (BitString 4))
      (batchOTFunctionality 4 (BitString 3)) {0} (iknpSenderSim 2 4 (BitString 3)) x D = 0 :=
  semiHonestAdvantage_iknp_sender toyHash x D

-- A bound `ε` on the correlation-robustness advantage of every test bounds a corrupted receiver's
-- advantage by `ε`.
example (x : (i : Fin 2) → (batchOTSpec 4 (BitString 3)).Query () i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView ((batchOTSpec 4 (BitString 3)).Query ())
        (IKNPCoins 2 4) (iknpSchedule 2 4 (BitString 3)) i) ×
      ((i : Fin 2) → (batchOTSpec 4 (BitString 3)).Answer () i) → ProbComp Bool)
    (ε : NNReal) (hε : ∀ A, CorrelationRobust.advantage toyHash A ≤ ε) :
    semiHonestAdvantage (iknpProtocol toyHash) (batchOTWorld 2 (BitString 4))
      (batchOTFunctionality 4 (BitString 3)) {1} (iknpReceiverSim toyHash) x D ≤ ε :=
  (semiHonestAdvantage_iknp_receiver toyHash x D).trans_le (hε _)

end CslibFrontierTests.Crypto.IKNP
