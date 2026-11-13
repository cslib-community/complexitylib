/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Basic
public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueQuery

/-!
# Placed XOR queries and the quantum value-query model

A placed coherent XOR query agrees with the existing `valueOracle addStep` after reindexing its
query, response and unused registers. This bridge includes arbitrary superpositions and workspace
states. The circuit code layer does not depend on the abstract value-query simulation machinery.

## Main results

* `Cslib.Quantum.xorQuery_eq_valueOracle`: agreement of the placed and value-query semantics.
-/

public section

namespace Cslib.Quantum

variable {a b m : ℕ}

/-- Reindexing the placed gate into its three registers gives the existing value oracle.
This equality covers arbitrary superpositions and arbitrary states of the unused wires. -/
theorem xorQuery_eq_valueOracle (H : (Fin a → Bool) → Fin b → Bool)
    (A : Fin (a + b) ↪ Fin m) (ψ : Qubits m) :
    let reindex := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (queryRegisters A)
    reindex ((xorQuery H A).eval ψ) = valueOracle addStep H (reindex ψ) := by
  intro reindex
  ext ⟨x, y, w⟩
  change ((xorQuery H A).eval ψ).ofLp ((queryRegisters A).symm (x, y, w)) = _
  rw [xorQuery_eval_apply, valueOracle_apply, addStep_apply]
  have hsub : y - H x = y + H x := by
    funext i
    exact BooleanRing.sub_eq_add _ _
  simp [reindex, hsub]

end Cslib.Quantum
