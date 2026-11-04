/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.Uniform

/-!
# The class BQP

`BQP` is the class of problems decided with bounded error by polynomial-time uniform families of
quantum circuits [Bernstein, Vazirani][BernsteinVazirani1997], in the circuit formulation of
[Arora, Barak][AroraBarak09], Chapter 10: `A ∈ BQP enc` when a family
`F : Cslib.Quantum.UniformCircuitFamily` accepts the encoding of every member of `A` with
probability at least `2 / 3`, and the encoding of every other instance with probability at most
`1 / 3`.

## Gate set

The circuits use the Hadamard gate and the classical reversible gates NOT, CNOT and Toffoli
(`Cslib.Quantum.GateCode`), a fixed finite gate set whose matrix entries lie in
`{0, ±1, ±1/√2}`. Arora and Barak instead allow any elementary operation, a unitary acting on at
most three qubits, whose description a polynomial-time machine outputs. The two definitions give
the same class. Toffoli and Hadamard gates are universal for quantum computation
[Shi][Shi2003], [Aharonov][Aharonov2003]; with the Solovay–Kitaev approximation theorem, circuits
over them simulate circuits over arbitrary elementary operations with polynomial overhead and small
error. This equivalence is cited, not formalized here. A fixed finite gate set matters:
Adleman, DeMarrais and Huang show that arbitrary complex amplitudes would put uncountably many
languages into `BQP` [Adleman, DeMarrais, Huang][AdlemanDeMarraisHuang1997].

Acceptance is the measurement of qubit `0`, after a single measurement of the whole register in the
computational basis at the end; Arora and Barak note that intermediate measurements and mixed
states add no power.

## Main definitions

* `Cslib.Complexity.BQP`.

## Main results

* `Cslib.Complexity.compl_mem_BQP`: `BQP` is closed under complement.

## References

* [E. Bernstein, U. Vazirani, *Quantum complexity theory*][BernsteinVazirani1997]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [Y. Shi, *Both Toffoli and Controlled-NOT need little help to do universal quantum
  computation*][Shi2003]
* [D. Aharonov, *A simple proof that Toffoli and Hadamard are quantum universal*][Aharonov2003]
* [L. Adleman, J. DeMarrais, M.-D. Huang, *Quantum computability*][AdlemanDeMarraisHuang1997]
-/

@[expose] public section

namespace Cslib.Complexity

open Quantum

variable {α : Type}

/-- The problems decided with bounded error by polynomial-time uniform families of quantum
circuits over the Hadamard, NOT, CNOT and Toffoli gates, with respect to the encoding `enc` of
instances: members are accepted with probability at least `2 / 3`, and other instances with
probability at most `1 / 3`. -/
def BQP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ F : UniformCircuitFamily, ∀ a,
    (a ∈ A → 2 / 3 ≤ F.acceptProb (enc a)) ∧ (a ∉ A → F.acceptProb (enc a) ≤ 1 / 3)}

variable {enc : α ↪ List Bool} {A : Set α}

theorem mem_BQP : A ∈ BQP enc ↔ ∃ F : UniformCircuitFamily, ∀ a,
    (a ∈ A → 2 / 3 ≤ F.acceptProb (enc a)) ∧ (a ∉ A → F.acceptProb (enc a) ≤ 1 / 3) :=
  Iff.rfl

/-- **`BQP` is closed under complement**: a final NOT gate on qubit `0` exchanges acceptance and
rejection. -/
theorem compl_mem_BQP (hA : A ∈ BQP enc) : Aᶜ ∈ BQP enc := by
  obtain ⟨F, hF⟩ := hA
  refine ⟨F.appendNot, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · have := (hF a).2 ha
    rw [UniformCircuitFamily.acceptProb_appendNot]
    linarith
  · have := (hF a).1 (Set.notMem_compl_iff.mp ha)
    rw [UniformCircuitFamily.acceptProb_appendNot]
    linarith

end Cslib.Complexity
