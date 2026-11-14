/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Request
public import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Native word programs for elementary device operations

Device commands are ordinary `WordOracleComp` programs with the existing native certificates.
A command discards its reply without reading any bits; a bit request reads at most one bit,
defaulting to false for an empty reply. The certificates hold against every stateful word oracle,
including one returning arbitrarily long replies. Gate payloads use `encPhaseGateCode`.

These are original interface helpers. They do not assert that a supplied request is valid or
charge the external oracle's implementation cost; the device handler checks canonical encodings
and placements, and the controller counts attempted calls separately.

## Main definitions

* `Cslib.Quantum.DeviceProgram.command`: issue a word request and discard the reply.
* `Cslib.Quantum.DeviceProgram.gate`: issue an existing elementary gate code.
* `Cslib.Quantum.DeviceProgram.requestBit`: issue a request and read at most one reply bit.

## Main results

* `Cslib.Quantum.DeviceProgram.isOraclePPTOn_command`,
  `Cslib.Quantum.DeviceProgram.isOraclePPTOn_gate`,
  `Cslib.Quantum.DeviceProgram.isOraclePPTOn_requestBit`: native certificates.
* `Cslib.Quantum.DeviceProgram.isCostBounded_command`,
  `Cslib.Quantum.DeviceProgram.isCostBounded_gate`,
  `Cslib.Quantum.DeviceProgram.isCostBounded_requestBit`: weighted operation costs.
-/

public section

namespace Cslib.Quantum.DeviceProgram

open Cslib.Probability Turing.MultiTapeTM

variable {Operation : Type}

/-- Issue a device or service command without reading its reply. The explicit zero-length prefix
admits a native certificate even when an arbitrary oracle returns an unbounded word. -/
@[expose] def command (operation : DeviceOperation ⊕ Operation) (word : List Bool) :
    WordOracleComp (DeviceOperation ⊕ Operation) Unit :=
  (fun _ => ()) <$> (List.take 0 <$> ProbOracleComp.query (operation, word))

/-- Send an existing elementary gate code to the device. -/
@[expose] def gate (code : PhaseGateCode) : WordOracleComp (DeviceOperation ⊕ Operation) Unit :=
  command (.inl .gate) (encPhaseGateCode code)

/-- Read at most one bit from a word reply, using false when the reply is empty. -/
@[expose] def requestBit (operation : DeviceOperation ⊕ Operation) (word : List Bool) :
    WordOracleComp (DeviceOperation ⊕ Operation) Bool :=
  (fun reply => reply.headD false) <$> (List.take 1 <$> ProbOracleComp.query (operation, word))

section Native

variable [DecidableEq Operation] [Finite Operation]

/-- A fixed command is native polynomial time on every encoded input. -/
theorem isOraclePPTOn_command {α : Type} (input : α ↪ List Bool)
    (operation : DeviceOperation ⊕ Operation) (word : List Bool) :
    IsOraclePPTOn input encUnit (fun _ => command operation word) :=
  (IsOraclePPTOn.query_take' operation (.const word) (.const 0)).map' (.const ())

/-- A fixed elementary gate request has a native polynomial-time certificate. -/
theorem isOraclePPTOn_gate {α : Type} (input : α ↪ List Bool) (code : PhaseGateCode) :
    IsOraclePPTOn (Operation := DeviceOperation ⊕ Operation) input encUnit (fun _ => gate code) :=
  isOraclePPTOn_command input _ _

/-- An efficiently constructed request followed by reading one reply bit is native polynomial
time, independently of the length of the unread suffix. -/
theorem isOraclePPTOn_requestBit {α : Type} (input : α ↪ List Bool)
    (operation : DeviceOperation ⊕ Operation) {word : α → List Bool}
    (hword : ComputableInPolyTime word input encBits) :
    IsOraclePPTOn input encBool (fun x => requestBit operation (word x)) :=
  (IsOraclePPTOn.query_take' operation hword (.const 1)).map'
    (ComputableInPolyTime.headD false)

end Native

/-- Discarding the reply does not add external operation costs. -/
theorem isCostBounded_command (cost : (DeviceOperation ⊕ Operation) → ℕ)
    (operation : DeviceOperation ⊕ Operation) (word : List Bool) :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (fun request => cost request.1))
      (command operation word) (cost operation) := by
  apply (OracleComp.isCostBounded_map_iff _ _ _).mpr
  apply (OracleComp.isCostBounded_map_iff _ _ _).mpr
  exact ProbOracleComp.isCostBounded_query _ _

/-- An elementary gate request costs its operation's assigned weight. -/
theorem isCostBounded_gate (cost : (DeviceOperation ⊕ Operation) → ℕ) (code : PhaseGateCode) :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (fun request => cost request.1))
      (gate code) (cost (.inl .gate)) :=
  isCostBounded_command cost _ _

/-- Reading one bit does not add external operation costs. -/
theorem isCostBounded_requestBit (cost : (DeviceOperation ⊕ Operation) → ℕ)
    (operation : DeviceOperation ⊕ Operation) (word : List Bool) :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (fun request => cost request.1))
      (requestBit operation word) (cost operation) := by
  apply (OracleComp.isCostBounded_map_iff _ _ _).mpr
  apply (OracleComp.isCostBounded_map_iff _ _ _).mpr
  exact ProbOracleComp.isCostBounded_query _ _

end Cslib.Quantum.DeviceProgram
