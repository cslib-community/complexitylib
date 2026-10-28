/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Protocols.MPC.Basic
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.ZMod.Basic

/-!
# Tests for additive secret sharing and multi-party protocol foundations

Concrete tests for `Complexity.Languages.Probabilistic.Sharing` and
`Complexity.Crypto.Protocols.MPC.Basic`:

1. **Additive secret sharing (`completeShares`, `sampleAdditiveShares`):** concrete evaluations over
   `ZMod 5` and `Bool` (`BooleanRing Bool`), plus 2-out-of-3 coalition marginal uniformity via
   `eval_restrict_sampleAdditiveShares`.
2. **2-party XOR protocol in `noOracleWorld`:** a concrete 2-round point-to-point protocol built
   with `Steps.append` in which party 0 sends `x 0` to party 1, party 1 sends `x 1` to party 0, and
   both output `x 0 + x 1`. Because each party `i` can reconstruct the other party's input from its
   own input `x i` and output `y i = x 0 + x 1` as `y i - x i`, the protocol satisfies
   `PerfectSemiHonestPrivate` against every static coalition `I : Finset (Fin 2)` by
   `perfectSemiHonestPrivate_of_deterministic`.
-/

namespace ComplexityTests.Crypto.MPC

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto.MPC

/-! ### Additive secret sharing tests -/

example : completeShares 3 (2 : ZMod 5) ![1, 3] = ![1, 3, 3] := by
  decide

example (target : Bool) (init : Fin 2 → Bool) :
    ∑ i : Fin 3, completeShares 3 target init i = target :=
  sum_completeShares 3 target init

example (target : Bool) :
    (ProbComp.eval (sampleAdditiveShares 3 target)).map ({0, 1} : Finset (Fin 3)).restrict =
      PMF.uniformOfFintype ((i : ({0, 1} : Finset (Fin 3))) → Bool) :=
  eval_restrict_sampleAdditiveShares ({0, 1} : Finset (Fin 3)) (by decide) target

/-! ### Concrete 2-party XOR protocol and perfect semi-honest privacy -/

/-- Two-round schedule in `noOracleSpec`: party 0 sends a bit to party 1, then party 1 sends a bit
to party 0. -/
abbrev xorSchedule : Schedule 2 noOracleSpec :=
  [.message 0 1 Bool, .message 1 0 Bool]

/-- First round: party 0 sends its input bit to party 1. -/
def xorStep1 :
    Steps (spec := noOracleSpec) (fun _ : Fin 2 => Bool × Unit)
      (fun i => (Bool × Unit) × (Round.message (spec := noOracleSpec) 0 1 Bool).Received i)
      [.message 0 1 Bool] :=
  .message (sender := 0) (receiver := 1) (fun st => st.1) (.done fun _ st => st)

/-- Second round: party 1 sends its input bit to party 0, and each party outputs the sum of its own
input and the bit received from the other party. -/
def xorStep2 :
    Steps (spec := noOracleSpec)
      (fun i : Fin 2 =>
        (Bool × Unit) × (Round.message (spec := noOracleSpec) 0 1 Bool).Received i)
      (fun _ => Bool)
      [.message 1 0 Bool] :=
  .message (sender := 1) (receiver := 0) (fun st => st.1.1)
    (.done fun i st =>
      if h : i = 0 then
        st.1.1.1 + st.2 h
      else
        st.1.2 (by omega) + st.1.1.1)

/-- Two-party XOR protocol built by sequentially composing `xorStep1` and `xorStep2` via
`Steps.append`. -/
def xorProtocol : Protocol 2 noOracleSpec xorSchedule
    (fun _ => Bool) (fun _ => Unit) (fun _ => Bool) where
  sampleCoins _ := pure ()
  steps := xorStep1.append xorStep2

/-- Deterministic 2-party XOR functionality `f x i = x 0 + x 1`. -/
def xorFunc (x : Fin 2 → Bool) (_ : Fin 2) : Bool :=
  x 0 + x 1

/-- Coalition simulator for `xorProtocol`: reconstructs the other party's bit from `y i - x i`. -/
def xorSim (I : Finset (Fin 2)) :
    CoalitionSimulator xorSchedule (fun _ => Bool) (fun _ => Unit) (fun _ => Bool) I :=
  fun xI yI =>
    pure fun i =>
      { input := xI i
        coins := ()
        received :=
          (fun _ => yI i - xI i,
           (fun _ => yI i - xI i, ())) }

/-- `xorProtocol` is perfectly semi-honest private against every static coalition
`I : Finset (Fin 2)`. -/
theorem perfectSemiHonestPrivate_xorProtocol :
    PerfectSemiHonestPrivate xorProtocol noOracleWorld
      (Functionality.ofDeterministic xorFunc) xorSim := by
  apply perfectSemiHonestPrivate_of_deterministic
  · intro I x
    simp only [xorSim, xorProtocol, xorStep1, xorStep2, Protocol.evalWith_eq,
      ProbComp.pi_succ, ProbComp.pi_zero, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, Steps.append, Steps.mapState, Steps.evalWith_message,
      Steps.evalWith_done, PMF.pure_bind, PMF.pure_map]
    refine congrArg PMF.pure (funext fun (i : I) => ?_)
    rcases i with ⟨i, hi⟩
    fin_cases i
    · refine PartyView.ext rfl rfl ?_
      refine Prod.ext (Round.received_message_eq_of_ne (by decide +revert) _ _) (Prod.ext ?_ rfl)
      refine Round.received_message_ext fun _ => ?_
      simp [xorFunc, Round.deliverMessage, add_sub_cancel_left]
    · refine PartyView.ext rfl rfl ?_
      refine Prod.ext ?_ (Prod.ext (Round.received_message_eq_of_ne (by decide +revert) _ _) rfl)
      refine Round.received_message_ext fun _ => ?_
      simp [xorFunc, Round.deliverMessage, sub_eq_add_neg]
  · intro x r hr
    simp only [xorProtocol, xorStep1, xorStep2, Protocol.evalWith_eq,
      ProbComp.pi_succ, ProbComp.pi_zero, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, Steps.append, Steps.mapState, Steps.evalWith_message,
      Steps.evalWith_done, PMF.pure_bind, PMF.pure_map, PMF.mem_support_pure_iff] at hr
    subst hr
    ext i
    fin_cases i <;> rfl

/-- Proper-coalition privacy follows from full-coalition privacy. -/
example :
    PerfectSemiHonestPrivateProper xorProtocol noOracleWorld
      (Functionality.ofDeterministic xorFunc) xorSim :=
  perfectSemiHonestPrivate_xorProtocol.proper

end ComplexityTests.Crypto.MPC
