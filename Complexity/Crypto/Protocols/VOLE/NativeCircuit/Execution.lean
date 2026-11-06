/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.VOLE.NativeCircuit.Kernels
import Complexity.Foundations.Data.List.OfFn

/-!
# Cached execution of the native circuit session

The runtime list kernels implement the existing role-local circuit interaction. Receiver callbacks
read the same cached share at each of their four phases and retain their sampled state. The real
execution identity does not assume a true public output; the simulation identity uses the existing
circuit relation. This is one fresh setup and one fixed session, without raw-bit adversary
transport.

## Main definitions

* `NativeCircuit.receiverStrategy`: existing callback adapter with circuit message encodings.
* `NativeCircuit.viewToLists`: complete typed view in its transmitted list representation.

## Main results

* `NativeCircuit.eval_execute`: native execution agrees with the actual cached World.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.VOLE.NativeCircuit

open Circuits Interactive Interactive.Spec Probability

variable {F State Result : Type} [CommRing F] {p k m : ℕ}

/-- Reuse the existing role-local adapter, with multiplication weights in code order. -/
def receiverStrategy (C : Circuit (arithSignature F) (p + k) m)
    (receiver : Native.Receiver F (Input F) (First F) State Result) :=
  receiver.strategy (p + k + C.size) (firstToLists C)
    (fun i : CircuitMulGate C => ((mulIndexEquiv C).symm i).val)

/-- Complete receiver share, entire transcript and retained private result in list form. -/
def viewToLists (C : Circuit (arithSignature F) (p + k) m) :
    ((F × (Fin (p + k + C.size + 1) → F)) × Transcript (circuitCheckSpec C) × Result) →
      View F Result :=
  fun (share, (first, r, reply, ()), result) =>
    ((share.1, List.ofFn share.2), firstToLists C first,
      List.ofFn (r ∘ mulIndexEquiv C), reply, result)

private theorem weights_inputOfCircuit (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) (r : List F) :
    Native.weights (layout (inputOfCircuit C x y z)).2.1.length r =
      List.ofFn ((fun i => r.getD ((mulIndexEquiv C).symm i).val 0) ∘ mulIndexEquiv C) := by
  simp [layout_inputOfCircuit, Native.inputOfMaps, Native.weights_eq_ofFn, Function.comp_def]

variable [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
private theorem eval_replicate_sample (sample : ProbComp F)
    (hsample : ProbComp.eval sample = PMF.uniformOfFintype F) (count : ℕ) :
    ProbComp.eval (OracleComp.replicate count sample) =
      (PMF.uniformOfFintype (Fin count → F)).map List.ofFn := by
  apply ProbComp.eval_replicate_of_uniform count sample id
  simpa only [PMF.map_id] using hsample

/-- The actual native runner realizes the cached interaction, retaining callback coins and every
selected continuation. This law holds even when the claimed public output is false. -/
theorem eval_execute (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) (w : Fin k → F)
    (sample : ProbComp F) (hsample : ProbComp.eval sample = PMF.uniformOfFintype F)
    (receiver : Native.Receiver F (Input F) (First F) State Result) :
    ProbComp.eval (execute sample receiver (inputOfCircuit C x y z) (List.ofFn w)) =
      (circuitReceiverView C (x, y) (receiverStrategy C receiver) w
        (inputOfCircuit C x y z)).map (some ∘ viewToLists C) := by
  unfold circuitReceiverView
  rw [voleWorld_eval]
  simp only [execute, validInput_inputOfCircuit, wireCount_inputOfCircuit, List.length_ofFn,
    show (inputOfCircuit C x y z).1 = k from rfl,
    decide_true, Bool.and_self, ite_true, ProbComp.eval_bind,
    eval_replicate_sample sample hsample, hsample, voleIdealDist,
    PMF.bind_map, PMF.map_bind, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  dsimp only [Function.comp_def]
  congr 1
  funext u
  congr 1
  funext v
  congr 1
  funext delta
  simp only [List.zipWith_ofFn, senderInit_inputOfCircuit]
  simp only [receiverStrategy, Native.Receiver.strategy, circuitCheck, liftProver, liftVerifier,
    OracleComp.interpret_bind, OracleComp.interpret_pure, ProbOracleComp.query,
    OracleComp.interpret_query, OracleComp.sumHandler, ProbOracleComp.interpret_sample,
    runAgainst, ProverStrategy.hoist,
    VerifierStrategy.hoist, circuitCheckSpec, SigmaProtocol.sigmaSpec, voleSample,
    VOLECorrelation.senderView, VOLECorrelation.receiverView,
    pure_bind, bind_assoc, ProbComp.eval_bind, ProbComp.eval_pure]
  simp only [OracleComp.interpret_map, map_pure, OracleComp.interpret_interpret,
    OracleComp.interpret_bind, OracleComp.interpret_pure, OracleComp.interpret_query,
    OracleComp.sumHandler, ProbOracleComp.sample,
    ProbComp.eval, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.pure_bind, PMF.bind_bind, PMF.map_bind, PMF.pure_map, PMF.monad_map_eq_map]
  simp only [weights_inputOfCircuit, senderReply_inputOfCircuit, viewToLists]

omit [DecidableEq F] in
/-- The native simulator realizes the existing witness-free circuit simulator. Its output contains
all linear openings as well as the receiver share, normalized weights, reply and private result. -/
theorem eval_simulate (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool)
    (sample : ProbComp F) (hsample : ProbComp.eval sample = PMF.uniformOfFintype F)
    (receiver : Native.Receiver F (Input F) (First F) State Result) :
    ProbComp.eval (simulate sample receiver (inputOfCircuit C x y z)) =
      (ProbComp.eval (circuitReceiverSimulate C (x, y) (receiverStrategy C receiver)
        (inputOfCircuit C x y z))).map (some ∘ viewToLists C) := by
  simp only [simulate, validInput_inputOfCircuit, ite_true, Native.simulate,
    show (layout (inputOfCircuit C x y z)).1 = p + k + C.size from
      wireCount_inputOfCircuit C x y z,
    circuitReceiverSimulate, maskedMulCheckReceiverSimulate,
    circuitReceiverAdapter, receiverStrategy, Native.Receiver.strategy,
    OracleComp.interpret_bind, OracleComp.interpret_pure, ProbOracleComp.query,
    OracleComp.interpret_query, OracleComp.sumHandler, ProbOracleComp.interpret_sample,
    OracleComp.interpret_query_eq_self, pure_bind, bind_assoc, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_map, ProbComp.eval_uniform, hsample,
    eval_replicate_sample sample hsample, PMF.bind_map, PMF.map_bind, PMF.pure_map,
    Function.comp_def]
  simp only [weights_inputOfCircuit, publicFirst_inputOfCircuit, checkValue_inputOfCircuit,
    expandView, viewToLists, circuitExpandView]

omit [DecidableEq F] in
/-- Exact full-view privacy of the native session for a satisfying circuit witness. The receiver
callbacks may retain private coins and depend on their cached share and the complete first message.
The supplied scalar sampler is exact; runtime assumptions are separate from this semantic law. -/
theorem eval_execute_eq_simulate (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) (z : List Bool) (w : Fin k → F)
    (hy : C.eval (arithInterpretation F) (Fin.append x w) = y)
    (sample : ProbComp F) (hsample : ProbComp.eval sample = PMF.uniformOfFintype F)
    (receiver : Native.Receiver F (Input F) (First F) State Result) :
    ProbComp.eval (execute sample receiver (inputOfCircuit C x y z) (List.ofFn w)) =
      ProbComp.eval (simulate sample receiver (inputOfCircuit C x y z)) := by
  classical
  rw [eval_execute C x y z w sample hsample receiver,
    circuitReceiverView_eq_simulate C (x, y) (receiverStrategy C receiver) w
      (inputOfCircuit C x y z) hy, eval_simulate C x y z sample hsample receiver]

end Cslib.Crypto.Protocols.VOLE.NativeCircuit
