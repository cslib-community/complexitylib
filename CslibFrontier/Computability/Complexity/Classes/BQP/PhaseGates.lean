/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BQP
public import CslibFrontier.Computability.Circuit.Quantum.PhaseCode

/-!
# `BQP` with controlled phase gates

Adding the controlled phase gates `S = P(i)`, `Λ(P(i))` and their inverses to the gate set of
`Cslib.Complexity.BQP` does not change the class (`Cslib.Complexity.mem_BQP_iff_phase`): every
polynomial-time uniform family over the extended set is simulated, with the same acceptance
probability on every input, by a family over the Hadamard, NOT, CNOT and Toffoli gates on one more
qubit (`Cslib.Quantum.UniformPhaseCircuitFamily.realify`). The simulation is the real encoding of
Bernstein and Vazirani, with the gate decomposition from the proof of Theorem 2 of
[Aharonov][Aharonov2003]; see `CslibFrontier/Computability/Circuit/Quantum/PhaseCode.lean`.

The extended set contains Kitaev's universal set `{Λ(P(i)), H}` [Kitaev1997]. Its universality,
and the Solovay–Kitaev theorem that turns universality into efficient approximation, are not
formalized, so the equivalence of `Cslib.Complexity.BQP` with the class defined over arbitrary
elementary gates remains a cited result.

## Main results

* `Cslib.Complexity.mem_BQP_iff_phase`: `BQP` over the gate set with controlled phase gates.

## References

* [D. Aharonov, *A simple proof that Toffoli and Hadamard are quantum universal*][Aharonov2003]
* [A. Yu. Kitaev, *Quantum computations: algorithms and error correction*][Kitaev1997]
-/

public section

namespace Cslib.Complexity

open Quantum

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- **`BQP` is unchanged by the controlled phase gates**: a problem is in `BQP` exactly when a
polynomial-time uniform family over the Hadamard, NOT, CNOT and Toffoli gates and the controlled
phase gates `S`, `Λ(S)` and their inverses accepts the encoding of every member with probability
at least `2 / 3` and the encoding of every other instance with probability at most `1 / 3`. -/
theorem mem_BQP_iff_phase : A ∈ BQP enc ↔ ∃ F : UniformPhaseCircuitFamily, ∀ a,
    (a ∈ A → 2 / 3 ≤ F.acceptProb (enc a)) ∧ (a ∉ A → F.acceptProb (enc a) ≤ 1 / 3) := by
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨F.toPhaseFamily, fun a => by simpa using hF a⟩
  · rintro ⟨F, hF⟩
    exact ⟨F.realify, fun a => by simpa using hF a⟩

end Cslib.Complexity
