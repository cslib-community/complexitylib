/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Family
import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import CslibFrontier.Tactic.PPT
import Mathlib.Tactic.NormNum.Prime

/-! # Word-level DDH-OT over Schnorr groups: checked instance

* Concrete `schnorrGroups` instantiation at `d23` (`p = 23, q = 11, g = 2`).
* Strict PPT certificates for `ddhOTRealWordRun`, `ddhOTSenderSimWord`, `ddhOTReceiverSimWord`,
  and `ddhOTWordReduction` with an explicit strict PPT distinguisher.
* Sender and receiver advantage bounds (`ddhOTWord_sender_advantage_le`,
  `ddhOTWord_receiver_advantage_le`) at concrete inputs. -/

namespace CslibFrontierTests.Crypto.DDHOTFamily

open Cslib
open Cslib.Crypto
open Cslib.Crypto.Protocols.MPC
open Cslib.Probability
open Turing.MultiTapeTM

private def d23 : schnorrGroups.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

private def sched23 (_ : ℕ) : schnorrGroups.Desc := d23

private theorem sched23_poly :
    ComputableInPolyTime sched23 encUnary schnorrGroups.encDesc := by
  unfold sched23
  fun_prop

private noncomputable def sampleX23 :
    (i : Fin 2) → OTIn (schnorrGroups.Carrier d23) i :=
  Fin.cases (motive := OTIn (schnorrGroups.Carrier d23))
    (0, schnorrGroups.generator d23) (fun _ => true)

private noncomputable def constWordX23 (_ : ℕ) : (List Bool × List Bool) × Bool :=
  encodeDDHOTInputWord schnorrGroups d23 sampleX23

private theorem constWordX23_poly :
    ComputableInPolyTime constWordX23 encUnary encDDHOTWordPair := by
  unfold constWordX23
  fun_prop

private def toyDistinguisher : ℕ → List Bool × List Bool → ProbComp Bool :=
  fun _ pair => pure (pair.1.headD false)

private theorem toyDistinguisher_ppt :
    IsPPTOn encDDHOTWordPairInput encBool
      (fun p => toyDistinguisher p.1 p.2) := by
  ppt [toyDistinguisher]

/-- All word-level DDH-OT runners and simulators are strict PPT at schedule `sched23`. -/
theorem runners_and_simulators_ppt :
    IsPPTOn encDDHOTWordInput encDDHOTRunOut (ddhOTRealWordRun schnorrGroups sched23) ∧
    IsPPTOn encDDHOTWordPairInput encBits (ddhOTSenderSimWord schnorrGroups sched23) ∧
    IsPPTOn (encPair encUnary (encPair encBool encBits)) encBits
      (ddhOTReceiverSimWord schnorrGroups sched23) :=
  ⟨isPPTOn_ddhOTRealWordRun schnorrGroups sched23_poly,
   isPPTOn_ddhOTSenderSimWord schnorrGroups sched23_poly,
   isPPTOn_ddhOTReceiverSimWord schnorrGroups sched23_poly⟩

/-- The induced DDH adversary `ddhOTWordReduction` is strict PPT for `constWordX23` and
`toyDistinguisher`. -/
theorem reduction_ppt :
    IsPPTOn schnorrGroups.encDDHInput encBool
      (fun p => ddhOTWordReduction schnorrGroups constWordX23 toyDistinguisher p.1 p.2) :=
  isPPTOn_ddhOTWordReduction schnorrGroups constWordX23_poly toyDistinguisher_ppt

/-- Concrete sender privacy bound at `n = 4` (`≤ 12 / 16`). -/
theorem sender_advantage_concrete :
    Game.advantage
      (ProbComp.eval ((do
        let v_w ← ddhOTSenderSimWord schnorrGroups sched23
          (4, (encodeDDHOTInputWord schnorrGroups d23 sampleX23).1)
        return (v_w, schnorrGroups.encode d23 (otOutputs sampleX23 1))) >>=
        fun r => toyDistinguisher 4 r))
      (ProbComp.eval (ddhOTRealWordRun schnorrGroups sched23
          (4, encodeDDHOTInputWord schnorrGroups d23 sampleX23) >>=
        fun r => toyDistinguisher 4 (r.1, ddhOTRunOut r))) ≤ 12 / 2 ^ 4 := by
  simpa only [sched23] using
    ddhOTWord_sender_advantage_le schnorrGroups sched23 4 sampleX23 toyDistinguisher

/-- Concrete receiver privacy bound at `n = 4` reducing to `ddhRealGame` vs `ddhIdealGame` plus
`18 / 16`. -/
theorem receiver_advantage_concrete :
    Game.advantage
      (ProbComp.eval ((do
        let v_w ← ddhOTReceiverSimWord schnorrGroups sched23
          (4, sampleX23 1, schnorrGroups.encode d23 (otOutputs sampleX23 1))
        return (v_w, schnorrGroups.encode d23 (otOutputs sampleX23 1))) >>=
        fun r => toyDistinguisher 4 r))
      (ProbComp.eval (ddhOTRealWordRun schnorrGroups sched23
          (4, encodeDDHOTInputWord schnorrGroups d23 sampleX23) >>=
        fun r => toyDistinguisher 4 (ddhOTRunReceiverView r, ddhOTRunOut r))) ≤
      Game.advantage
        (schnorrGroups.ddhRealGame (fun k => PMF.pure (sched23 k))
          (ddhOTWordReduction schnorrGroups constWordX23 toyDistinguisher) 4)
        (schnorrGroups.ddhIdealGame (fun k => PMF.pure (sched23 k))
          (ddhOTWordReduction schnorrGroups constWordX23 toyDistinguisher) 4) + 18 / 2 ^ 4 := by
  simpa only [sched23] using
    ddhOTWord_receiver_advantage_le schnorrGroups sched23 4 constWordX23 sampleX23 rfl
      toyDistinguisher

end CslibFrontierTests.Crypto.DDHOTFamily
