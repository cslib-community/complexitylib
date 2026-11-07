/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BQP
public import Complexity.Computability.Complexity.Classes.Promise.Basic
public import Complexity.Computability.Circuit.Quantum.Verifier

/-!
# The class QMA

`QMA` (quantum Merlin–Arthur, Kitaev's `BQNP`) is the quantum analogue of `NP` and `MA`: a
polynomial-time quantum verifier receives, besides the input, a quantum witness state
[Kitaev, Shen, Vyalyi][KitaevShenVyalyi2002], Section 14.1; [Watrous][Watrous2008], Section V.1;
[Marriott, Watrous][MarriottWatrous2005], Definition 3.1. A promise problem `Q` is in
`PromiseQMA c s enc` when some polynomial-time uniform family of verifiers
(`Cslib.Quantum.UniformVerifierFamily`) satisfies, with `n` the length of the encoded instance:

* **completeness**: for every yes-instance some unit witness state is accepted with probability at
  least `c n`;
* **soundness**: for every no-instance every unit witness state is accepted with probability at
  most `s n`.

`QMA enc` is the class of decision problems with completeness `2 / 3` and soundness `1 / 3`.

Witnesses are pure states, as in [Marriott, Watrous][MarriottWatrous2005], Definition 3.1. A mixed
witness accepts with a convex combination of the acceptance probabilities of pure witnesses, since
acceptance is a quadratic form in the witness, so mixed witnesses give the same class; this is not
formalized here. The verifiers are uniform circuit families over the gate set of `BQP`
(`Cslib.Complexity.BQP`), with one measurement of the whole register at the end.

## Main definitions

* `Cslib.Complexity.PromiseProblem.IsQMAVerifier`: a verifier family decides a promise problem with
  given completeness and soundness.
* `Cslib.Complexity.PromiseQMA`: `QMA(c, s)` for promise problems.
* `Cslib.Complexity.QMA`: the class `QMA` of decision problems.

## Main results

* `Cslib.Complexity.PromiseQMA_mono`: weakening completeness and soundness.
* `Cslib.Complexity.BQP_subset_QMA`: `BQP ⊆ QMA`.

`NP ⊆ QMA` is `Cslib.Complexity.NP_subset_QMA` and error reduction is
`Cslib.Complexity.mem_QMA_iff_forall_errorExponent`.

## References

* [A. Kitaev, A. Shen, M. Vyalyi, *Classical and Quantum Computation*][KitaevShenVyalyi2002]
* [J. Watrous, *Quantum computational complexity*][Watrous2008]
* [C. Marriott, J. Watrous, *Quantum Arthur–Merlin games*][MarriottWatrous2005]
-/

@[expose] public section

namespace Cslib.Complexity

open Quantum Turing.MultiTapeTM

variable {α : Type}

/-- The verifier family `V` decides the promise problem `Q` with completeness `c` and soundness
`s`: on the encoding of every yes-instance some unit witness state is accepted with probability at
least `c n`, and on the encoding of every no-instance every unit witness state is accepted with
probability at most `s n`, where `n` is the length of the encoding. -/
def PromiseProblem.IsQMAVerifier (enc : α ↪ List Bool) (c s : ℕ → ℝ) (V : UniformVerifierFamily)
    (Q : PromiseProblem α) : Prop :=
  ∀ a, (a ∈ Q.yes → ∃ ψ : Qubits (V.witnessLength (enc a).length), ‖ψ‖ = 1 ∧
      c (enc a).length ≤ V.acceptProb (enc a) ψ) ∧
    (a ∈ Q.no → ∀ ψ : Qubits (V.witnessLength (enc a).length), ‖ψ‖ = 1 →
      V.acceptProb (enc a) ψ ≤ s (enc a).length)

/-- **`QMA(c, s)`** for promise problems: the promise problems decided by a polynomial-time
uniform family of quantum verifiers with completeness `c` and soundness `s`, with respect to the
encoding `enc` of instances. -/
def PromiseQMA (c s : ℕ → ℝ) (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | ∃ V : UniformVerifierFamily, Q.IsQMAVerifier enc c s V}

/-- **`QMA`**: the decision problems decided by a polynomial-time uniform family of quantum
verifiers with completeness `2 / 3` and soundness `1 / 3`, with respect to the encoding `enc` of
instances. -/
def QMA (enc : α ↪ List Bool) : Set (Set α) :=
  {A | PromiseProblem.ofSet A ∈ PromiseQMA (fun _ => 2 / 3) (fun _ => 1 / 3) enc}

variable {enc : α ↪ List Bool} {A : Set α}

/-- Membership in `QMA` unfolded. -/
theorem mem_QMA : A ∈ QMA enc ↔ ∃ V : UniformVerifierFamily, ∀ a,
    (a ∈ A → ∃ ψ : Qubits (V.witnessLength (enc a).length), ‖ψ‖ = 1 ∧
      2 / 3 ≤ V.acceptProb (enc a) ψ) ∧
    (a ∉ A → ∀ ψ : Qubits (V.witnessLength (enc a).length), ‖ψ‖ = 1 →
      V.acceptProb (enc a) ψ ≤ 1 / 3) :=
  Iff.rfl

/-- Weakening the completeness and soundness bounds enlarges `QMA(c, s)`. -/
theorem PromiseQMA_mono {c c' s s' : ℕ → ℝ} (hc : ∀ n, c' n ≤ c n) (hs : ∀ n, s n ≤ s' n) :
    PromiseQMA c s enc ⊆ PromiseQMA c' s' enc := by
  rintro Q ⟨V, hV⟩
  refine ⟨V, fun a => ⟨fun ha => ?_, fun ha ψ hψ => ((hV a).2 ha ψ hψ).trans (hs _)⟩⟩
  obtain ⟨ψ, hψ, h⟩ := (hV a).1 ha
  exact ⟨ψ, hψ, (hc _).trans h⟩

/-- **`BQP ⊆ QMA`**: a `BQP` family is a verifier that reads no witness. -/
theorem BQP_subset_QMA : BQP enc ⊆ QMA enc := by
  rintro A ⟨F, hF⟩
  refine ⟨UniformVerifierFamily.ofCircuitFamily F, fun a => ⟨fun ha => ?_, fun ha ψ hψ => ?_⟩⟩
  · refine ⟨ket default, norm_ket _, ?_⟩
    rw [UniformVerifierFamily.acceptProb_ofCircuitFamily, norm_ket, one_pow, one_mul]
    exact (hF a).1 ha
  · rw [UniformVerifierFamily.acceptProb_ofCircuitFamily, hψ, one_pow, one_mul]
    exact (hF a).2 ha

end Cslib.Complexity
