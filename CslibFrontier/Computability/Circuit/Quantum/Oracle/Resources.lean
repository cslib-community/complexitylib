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

The active register width, elementary-gate count, oracle-query count and encoded description
length have independent budgets. The caller supplies the exact description length because the
same instruction list may occur inside encodings with different register metadata. Validity
separately ensures that the interpreter executes every instruction, and uniform generation
separately bounds these resources as functions of the input sizes. An oracle query is one
operation here; implementing its function is not charged as an elementary circuit.

These coordinates describe the generated circuit artifact and its online execution. They do not
charge the static generator program or the time and workspace used to run it. Those costs have a
separate certificate; adding any of them to adversary runtime requires an explicit theorem for an
executed generator, interpreter or copy operation.

## Main definitions

* `Cslib.Quantum.OracleCircuit.Resources`: independent qubit, gate, query and description-bit
  budgets.
* `Cslib.Quantum.OracleCircuit.Within`: a description satisfies all four budgets.
-/

public section

namespace Cslib.Quantum.OracleCircuit

/-- Independent budgets for a finite circuit artifact and its online execution. -/
structure Resources where
  /-- Maximum number of active qubits, including inputs and ancillas. -/
  qubits : ℕ
  /-- Maximum number of elementary gates. -/
  gates : ℕ
  /-- Maximum number of oracle queries. -/
  queries : ℕ
  /-- Maximum number of bits in the selected finite-description encoding. -/
  descriptionBits : ℕ

/-- The finite description fits each budget. The exact encoded length is supplied explicitly
because `codes` alone does not contain all register metadata. This predicate does not assert
well-formedness and does not execute or charge a uniform generator. -/
@[expose] def Within (codes : OracleCircuit) (width descriptionBits : ℕ)
    (budget : Resources) : Prop :=
  width ≤ budget.qubits ∧ codes.gateCount ≤ budget.gates ∧
    codes.queryCount ≤ budget.queries ∧ descriptionBits ≤ budget.descriptionBits

instance (codes : OracleCircuit) (width descriptionBits : ℕ) (budget : Resources) :
    Decidable (codes.Within width descriptionBits budget) :=
  inferInstanceAs (Decidable (width ≤ budget.qubits ∧
    codes.gateCount ≤ budget.gates ∧ codes.queryCount ≤ budget.queries ∧
      descriptionBits ≤ budget.descriptionBits))

end Cslib.Quantum.OracleCircuit
