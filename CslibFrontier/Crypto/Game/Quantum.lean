/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Concrete
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Uniform

/-!
# Concrete game bounds for native uniform quantum oracle circuits

The existing resource-indexed game API applies to uniform quantum oracle-circuit families with
separate qubit, elementary-gate and query budgets. Native generation supplies polynomial schedules
for all classical input lengths up to a polynomial bound. A concrete error negligible along every
componentwise polynomial schedule therefore gives asymptotic indistinguishability for every such
family. This is an instance of the existing concrete-to-asymptotic theorem, not a new game or
advantage notion.

The games remain parameters. A caller must show that its experiment executes the supplied family
on input lengths within the declared bound and establishes the concrete security premise. These
bridges do not add quantum-advice quantifiers, sample a random oracle or certify interactive QROM
security. They are original infrastructure; no protocol security result is asserted here.

## Main definitions

* `Cslib.Crypto.Game.WithinOracleCircuits`: all permitted input lengths fit each resource budget.

## Main results

* `Cslib.Crypto.Game.Indistinguishable.of_uniformOracleCircuits`: concrete-to-asymptotic transfer.
* `Cslib.Crypto.Game.Indistinguishable.of_succ_uniformOracleCircuits`: the one-sided version.
-/

public section

namespace Cslib.Crypto.Game

open Quantum
open scoped NNReal

/-- Every generated circuit for a classical input of length at most `inputLength n` respects the
three budgets. The experiment using the family must separately respect this input-length bound. -/
@[expose] def WithinOracleCircuits (inputLength : ℕ → ℕ) (n : ℕ)
    (budget : OracleCircuit.Resources) (family : UniformOracleCircuitFamily) : Prop :=
  ∀ ℓ ≤ inputLength n, (family.description n ℓ).instructions.Within
    (family.description n ℓ).width budget

/-- Concrete bounds negligible for every polynomial qubit, gate and query schedule yield
asymptotic indistinguishability for all native uniform families. Auxiliary lengths may be bounded
by any polynomially bounded function; that bound need not itself be computable. -/
theorem Indistinguishable.of_uniformOracleCircuits {inputLength : ℕ → ℕ}
    (hinput : PolynomiallyBounded inputLength)
    {game₁ game₂ : UniformOracleCircuitFamily → ℕ → Game}
    {ε : ℕ → OracleCircuit.Resources → ℝ≥0}
    (h : IndistinguishableWithin game₁ game₂ (WithinOracleCircuits inputLength) ε)
    (hneg : ∀ qubits gates queries : ℕ → ℕ,
      PolynomiallyBounded qubits → PolynomiallyBounded gates → PolynomiallyBounded queries →
      Negligible (fun n => ε n ⟨qubits n, gates n, queries n⟩)) :
    Indistinguishable game₁ game₂ (fun _ => True) := by
  refine h.indistinguishable (fun r => PolynomiallyBounded (fun n => (r n).qubits) ∧
    PolynomiallyBounded (fun n => (r n).gates) ∧
    PolynomiallyBounded (fun n => (r n).queries)) ?_ ?_
  · intro family _
    obtain ⟨B, _, hB, hbound⟩ := family.exists_computable_resource_bound hinput
    refine ⟨fun n => ⟨B n, B n, B n⟩, ⟨hB, hB, hB⟩, fun n ℓ hℓ => ?_⟩
    have htotal := hbound n ℓ hℓ
    have hcounts := (family.description n ℓ).instructions.gateCount_add_queryCount
    change _ ≤ B n ∧ _ ≤ B n ∧ _ ≤ B n
    omega
  · intro r hr
    exact hneg (fun n => (r n).qubits) (fun n => (r n).gates)
      (fun n => (r n).queries) hr.1 hr.2.1 hr.2.2

/-- A concrete success bound along independent polynomial resource schedules yields asymptotic
indistinguishability from failure, using the existing success/advantage equivalence. -/
theorem Indistinguishable.of_succ_uniformOracleCircuits {inputLength : ℕ → ℕ}
    (hinput : PolynomiallyBounded inputLength)
    {game : UniformOracleCircuitFamily → ℕ → Game}
    {ε : ℕ → OracleCircuit.Resources → ℝ≥0}
    (h : SuccWithin game (WithinOracleCircuits inputLength) ε)
    (hneg : ∀ qubits gates queries : ℕ → ℕ,
      PolynomiallyBounded qubits → PolynomiallyBounded gates → PolynomiallyBounded queries →
      Negligible (fun n => ε n ⟨qubits n, gates n, queries n⟩)) :
    Indistinguishable game (fun _ _ => PMF.pure false) (fun _ => True) :=
  of_uniformOracleCircuits hinput ((indistinguishableWithin_pure_false_iff _ _ _).mpr h) hneg

end Cslib.Crypto.Game
