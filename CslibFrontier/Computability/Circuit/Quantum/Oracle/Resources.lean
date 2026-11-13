/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Code

/-!
# Separate resources of coded quantum oracle circuits

The active register width, elementary-gate count and oracle-query count have independent budgets.
These are syntactic resources of a finite description. Validity separately ensures that the
interpreter executes every instruction, and uniform generation separately bounds these resources
as functions of the input sizes. An oracle query is one operation here; implementing its function
is not charged as an elementary circuit.

## Main definitions

* `Cslib.Quantum.OracleCircuit.Resources`: independent qubit, gate and query budgets.
* `Cslib.Quantum.OracleCircuit.Within`: a description satisfies all three budgets.
-/

public section

namespace Cslib.Quantum.OracleCircuit

/-- Independent budgets for the active register, elementary gates and coherent oracle queries. -/
structure Resources where
  /-- Maximum number of active qubits, including inputs and ancillas. -/
  qubits : ℕ
  /-- Maximum number of elementary gates. -/
  gates : ℕ
  /-- Maximum number of oracle queries. -/
  queries : ℕ

/-- The finite description fits each budget. This predicate does not assert well-formedness. -/
@[expose] def Within (codes : OracleCircuit) (width : ℕ) (budget : Resources) : Prop :=
  width ≤ budget.qubits ∧ codes.gateCount ≤ budget.gates ∧ codes.queryCount ≤ budget.queries

instance (codes : OracleCircuit) (width : ℕ) (budget : Resources) :
    Decidable (codes.Within width budget) :=
  inferInstanceAs (Decidable (width ≤ budget.qubits ∧
    codes.gateCount ≤ budget.gates ∧ codes.queryCount ≤ budget.queries))

end Cslib.Quantum.OracleCircuit
