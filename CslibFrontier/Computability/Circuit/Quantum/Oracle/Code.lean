/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Basic
public import CslibFrontier.Computability.Circuit.Quantum.PhaseCode

/-!
# Finite descriptions of quantum oracle circuits

An `OracleGateCode` is an existing elementary `PhaseGateCode` or a coherent XOR query to a fixed
function on the first `a + b` wires. `OracleCircuit.toCircuit` interprets a list of these
instructions through the existing `Circuit` semantics. It skips malformed instructions, just
as `Circuit.ofPhaseCodes` does; `OracleGateCode.WellFormed` characterizes exactly the instructions
that are retained. A well-formed description therefore has exactly its stated number of gates.

Elementary gates and queries are counted separately. These counts describe the finite circuit;
they do not certify polynomial-time uniform generation or bound the implementation cost of the
oracle. The elementary basis includes Hadamard, NOT, CNOT, Toffoli, phase and controlled phase
gates, with the phase inverses. The constructions and elementary identities below are original
formalization infrastructure.

## Main definitions

* `Cslib.Quantum.OracleGateCode`: elementary gates and coherent oracle-query instructions.
* `Cslib.Quantum.OracleCircuit`: finite instruction lists in execution order.
* `Cslib.Quantum.OracleGateCode.WellFormed`: validity at fixed register and query widths.
* `Cslib.Quantum.OracleCircuit.toCircuit`: interpretation as an existing quantum circuit.
* `Cslib.Quantum.OracleCircuit.queryCount`, `Cslib.Quantum.OracleCircuit.gateCount`:
  independent oracle and elementary-gate counts.

## Main results

* `Cslib.Quantum.OracleCircuit.toCircuit_append`: interpretation respects sequencing.
* `Cslib.Quantum.OracleCircuit.toCircuit_map_gate`: oracle-free programs recover
  `Circuit.ofPhaseCodes`.
* `Cslib.Quantum.OracleCircuit.length_toCircuit`: well-formed instructions are all executed.
* `Cslib.Quantum.OracleCircuit.gateCount_add_queryCount`: the two costs partition the instructions.
-/

public section

namespace Cslib.Quantum

/-- A finite instruction: an elementary gate code, or a coherent query to the supplied oracle. -/
inductive OracleGateCode where
  /-- An existing elementary code, including phase gates and their inverses. -/
  | gate (code : PhaseGateCode)
  /-- XOR the oracle answer into the fixed response register. -/
  | query
  deriving DecidableEq

namespace OracleGateCode

/-- A query is well formed when its argument and response registers fit in the full register.
An elementary gate uses the existing gate-code validity condition. -/
@[expose] def WellFormed (a b m : ℕ) : OracleGateCode → Prop
  | .gate g => g.WellFormed m
  | .query => a + b ≤ m

instance (a b m : ℕ) : DecidablePred (WellFormed a b m)
  | .gate _ => inferInstanceAs (Decidable (PhaseGateCode.WellFormed _ _))
  | .query => inferInstanceAs (Decidable (_ ≤ _))

/-- Interpret an instruction, returning `none` for malformed elementary gates or a query whose
two registers do not fit. The oracle is a single fixed function shared by all query instructions. -/
@[expose] noncomputable def toPlacedGate? {a b : ℕ} (m : ℕ)
    (H : (Fin a → Bool) → Fin b → Bool) : OracleGateCode → Option (PlacedGate m)
  | .gate g => g.toPlacedGate? m
  | .query => if h : a + b ≤ m then some (xorQuery H (Fin.castLEEmb h)) else none

/-- Exactly the well-formed instructions denote placed gates. -/
theorem isSome_toPlacedGate?_iff {a b m : ℕ} (H : (Fin a → Bool) → Fin b → Bool)
    (g : OracleGateCode) : (g.toPlacedGate? m H).isSome ↔ g.WellFormed a b m := by
  cases g with
  | gate g => exact PhaseGateCode.isSome_toPlacedGate?_iff
  | query => simp [toPlacedGate?, WellFormed]

/-- Whether this instruction is an oracle call, independent of its interpretation. -/
@[expose] def isQuery : OracleGateCode → Bool
  | .gate _ => false
  | .query => true

end OracleGateCode

/-- A finite quantum oracle-circuit description, in execution order. -/
abbrev OracleCircuit := List OracleGateCode

namespace OracleCircuit

/-- Interpret finite codes as a circuit. Malformed instructions are skipped; impose
`∀ g ∈ codes, g.WellFormed a b m` to rule them out. -/
@[expose] noncomputable def toCircuit {a b : ℕ} (m : ℕ)
    (H : (Fin a → Bool) → Fin b → Bool) (codes : OracleCircuit) : Circuit m :=
  codes.filterMap (OracleGateCode.toPlacedGate? m H)

/-- Number of oracle calls in the description. -/
@[expose] def queryCount (codes : OracleCircuit) : ℕ := codes.countP OracleGateCode.isQuery

/-- Number of elementary gates in the description; oracle calls have a separate cost. -/
@[expose] def gateCount (codes : OracleCircuit) : ℕ :=
  codes.countP fun g => !g.isQuery

variable {a b m : ℕ} (H : (Fin a → Bool) → Fin b → Bool)

/-- Concatenation executes the first circuit followed by the second. -/
theorem toCircuit_append (codes₁ codes₂ : OracleCircuit) :
    toCircuit m H (codes₁ ++ codes₂) = toCircuit m H codes₁ ++ toCircuit m H codes₂ :=
  List.filterMap_append

/-- An oracle-free description has exactly the original coded-circuit interpretation. -/
theorem toCircuit_map_gate (codes : List PhaseGateCode) :
    toCircuit m H (codes.map OracleGateCode.gate) = Circuit.ofPhaseCodes m codes := by
  rw [toCircuit, List.filterMap_map, Circuit.ofPhaseCodes]
  rfl

/-- Any even number of coherent XOR queries cancels, on arbitrary states. The total interpreter
also has this property when a malformed query is skipped. -/
theorem eval_toCircuit_replicate_query_pairs (k : ℕ) (ψ : Qubits m) :
    (toCircuit m H (List.replicate (2 * k) .query)).eval ψ = ψ := by
  induction k with
  | zero => simp [toCircuit, Circuit.eval_nil]
  | succ k ih =>
    rw [Nat.mul_succ, List.replicate_add, toCircuit_append, Circuit.eval_append, ih]
    by_cases h : a + b ≤ m
    · simp [toCircuit, OracleGateCode.toPlacedGate?, h, Circuit.eval_cons, Circuit.eval_nil,
        xorQuery_eval_twice]
    · simp [toCircuit, OracleGateCode.toPlacedGate?, h, Circuit.eval_nil]

/-- Every well-formed instruction is executed, so semantic gate count equals description length. -/
theorem length_toCircuit (codes : OracleCircuit)
    (h : ∀ g ∈ codes, g.WellFormed a b m) : (toCircuit m H codes).length = codes.length := by
  rw [toCircuit, List.length_filterMap_eq_countP, List.countP_eq_length]
  exact fun g hg => (g.isSome_toPlacedGate?_iff H).mpr (h g hg)

/-- Oracle and elementary-gate costs exhaust the instruction list. -/
theorem gateCount_add_queryCount (codes : OracleCircuit) :
    gateCount codes + queryCount codes = codes.length := by
  simpa only [gateCount, queryCount, decide_not, Bool.decide_coe, Nat.add_comm] using
    (List.length_eq_countP_add_countP (l := codes) OracleGateCode.isQuery).symm

/-- Oracle costs add under sequential composition. -/
theorem queryCount_append (codes₁ codes₂ : OracleCircuit) :
    queryCount (codes₁ ++ codes₂) = queryCount codes₁ + queryCount codes₂ :=
  List.countP_append

/-- Elementary-gate costs add under sequential composition. -/
theorem gateCount_append (codes₁ codes₂ : OracleCircuit) :
    gateCount (codes₁ ++ codes₂) = gateCount codes₁ + gateCount codes₂ :=
  List.countP_append

end OracleCircuit

end Cslib.Quantum
