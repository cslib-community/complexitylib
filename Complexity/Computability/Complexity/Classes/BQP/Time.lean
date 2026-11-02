/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BQP
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives

/-!
# Quantum time classes

`BQTIME enc t` (`Cslib.Complexity.BQTIME`) is the class of problems decided with bounded error by
the polynomial-time uniform families of quantum circuits of `Cslib.Complexity.BQP` whose circuits
for inputs of length `n` have at most `c₁ t n + c₂` gates, for constants `c₁` and `c₂`. The gate
count plays the role of running time.

The families are polynomial-time uniform, so every circuit has polynomially many gates anyway, and
`BQTIME enc t` is only meaningful for polynomially bounded `t`: it always lies in `BQP`
(`Cslib.Complexity.BQTIME_subset_BQP`), and the gate bound no longer constrains the family once `t`
dominates every polynomial. `BQP` is the union of the classes `BQTIME[n ^ k]`
(`Cslib.Complexity.BQP_eq_iUnion_BQTIME`).

The same families with the same gate bounds define three more classes, by other acceptance
conditions:

* **Nondeterministic quantum time** `NQTIME enc t` (`Cslib.Complexity.NQTIME`): members are the
  instances accepted with nonzero probability. It is the time-`t` circuit analogue of the class
  `NQP` of Adleman, DeMarrais and Huang, defined for quantum Turing machines in [Fenner, Green,
  Homer, Pruim][FennerGreenHomerPruim1999], Definition 2.1, who show `NQP = coC₌P` (Theorem 1.1),
  and in Section 4 that `coC₌P` is already in `NQP` with amplitudes in `{0, ±1/√2, ±1}`.
* **Exact quantum time** `EQTIME enc t` (`Cslib.Complexity.EQTIME`): members are accepted with
  probability `1` and other instances with probability `0`, as `EQTime(T(n))` in
  [Bernstein, Vazirani][BernsteinVazirani1997], Definition 8.1, for quantum Turing machines.
  Exactness depends on the gate set: approximating one gate set by another preserves bounded error
  but not zero error, so this is exact quantum time over the Hadamard, NOT, CNOT and Toffoli gates,
  and it is not claimed to equal exact quantum time over other gate sets or quantum Turing
  machines. It lies in `NQTIME` and in `BQTIME` (`Cslib.Complexity.EQTIME_subset_NQTIME`,
  `Cslib.Complexity.EQTIME_subset_BQTIME`).
* **Postselected bounded-error quantum time** `PostBQTIME enc t` (`Cslib.Complexity.PostBQTIME`):
  qubit `1` reads `1` with nonzero probability, and conditioned on that, qubit `0` reads `1` with
  probability at least `2 / 3` on members and at most `1 / 3` otherwise. It is the time-`t`
  analogue of `PostBQP`, [Aaronson][Aaronson2005Postselection], Definition 1, with his first
  (postselected) and second (output) qubits exchanged; he shows `PostBQP = PP` (Theorem 4).

## Main definitions

* `Cslib.Complexity.BQTIME`, `Cslib.Complexity.NQTIME`, `Cslib.Complexity.EQTIME`,
  `Cslib.Complexity.PostBQTIME`.

## Main results

* `Cslib.Complexity.BQTIME_subset_BQP`: every `BQTIME` class lies in `BQP`.
* `Cslib.Complexity.BQP_eq_iUnion_BQTIME`: `BQP = ⋃ k, BQTIME[n ^ k]`.
* `Cslib.Complexity.EQTIME_subset_NQTIME`, `Cslib.Complexity.EQTIME_subset_BQTIME`: exact quantum
  time is nondeterministic and bounded-error quantum time.

## References

* [E. Bernstein, U. Vazirani, *Quantum complexity theory*][BernsteinVazirani1997]
* [S. Fenner, F. Green, S. Homer, R. Pruim, *Determining acceptance possibility for a quantum
  computation is hard for the polynomial hierarchy*][FennerGreenHomerPruim1999]
* [S. Aaronson, *Quantum computing, postselection, and probabilistic
  polynomial-time*][Aaronson2005Postselection]
-/
@[expose] public section

namespace Cslib.Complexity

open Quantum Turing.MultiTapeTM

variable {α : Type}

/-- **Bounded-error quantum time** `t`: the problems decided with bounded error, with respect to
the encoding `enc` of instances, by a polynomial-time uniform family of quantum circuits over the
Hadamard, NOT, CNOT and Toffoli gates (`Cslib.Quantum.UniformCircuitFamily`) whose circuit for
inputs of length `n` has at most `c₁ t n + c₂` gates. Members are accepted with probability at
least `2 / 3` and other instances with probability at most `1 / 3`.

Since the families are polynomial-time uniform, their circuits have polynomially many gates in any
case, so the class is only meaningful for polynomially bounded `t`. -/
def BQTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (F : UniformCircuitFamily) (c₁ c₂ : ℕ), (∀ n, (F.gates n).length ≤ c₁ * t n + c₂) ∧
    ∀ a, (a ∈ A → 2 / 3 ≤ F.acceptProb (enc a)) ∧ (a ∉ A → F.acceptProb (enc a) ≤ 1 / 3)}

/-- **Nondeterministic quantum time** `t`: the problems whose members, with respect to the encoding
`enc` of instances, are exactly the instances accepted with nonzero probability by a
polynomial-time uniform family of quantum circuits over the Hadamard, NOT, CNOT and Toffoli gates
(`Cslib.Quantum.UniformCircuitFamily`) whose circuit for inputs of length `n` has at most
`c₁ t n + c₂` gates. -/
def NQTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (F : UniformCircuitFamily) (c₁ c₂ : ℕ), (∀ n, (F.gates n).length ≤ c₁ * t n + c₂) ∧
    ∀ a, a ∈ A ↔ 0 < F.acceptProb (enc a)}

/-- **Exact quantum time** `t` over the Hadamard, NOT, CNOT and Toffoli gates: the problems decided
without error, with respect to the encoding `enc` of instances, by a polynomial-time uniform family
of quantum circuits whose circuit for inputs of length `n` has at most `c₁ t n + c₂` gates.
Members are accepted with probability `1` and other instances with probability `0`. -/
def EQTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (F : UniformCircuitFamily) (c₁ c₂ : ℕ), (∀ n, (F.gates n).length ≤ c₁ * t n + c₂) ∧
    ∀ a, (a ∈ A → F.acceptProb (enc a) = 1) ∧ (a ∉ A → F.acceptProb (enc a) = 0)}

/-- **Postselected bounded-error quantum time** `t`: the problems decided with bounded error after
postselection, with respect to the encoding `enc` of instances, by a polynomial-time uniform family
of quantum circuits over the Hadamard, NOT, CNOT and Toffoli gates whose circuit for inputs of
length `n` has at most `c₁ t n + c₂` gates. On every instance qubit `1` reads `1` with nonzero
probability, and conditioned on that (`Cslib.Quantum.UniformCircuitFamily.postselectedAcceptProb`)
members are accepted with probability at least `2 / 3` and other instances with probability at
most `1 / 3`. -/
def PostBQTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (F : UniformCircuitFamily) (c₁ c₂ : ℕ), (∀ n, (F.gates n).length ≤ c₁ * t n + c₂) ∧
    ∀ a, 0 < F.onesProb [1] (enc a) ∧ (a ∈ A → 2 / 3 ≤ F.postselectedAcceptProb (enc a)) ∧
      (a ∉ A → F.postselectedAcceptProb (enc a) ≤ 1 / 3)}

variable {enc : α ↪ List Bool}

/-- **Exact quantum time is nondeterministic quantum time**: a probability that is `0` or `1` is
positive exactly when it is `1`. -/
theorem EQTIME_subset_NQTIME (t : ℕ → ℕ) : EQTIME enc t ⊆ NQTIME enc t := by
  rintro A ⟨F, c₁, c₂, hgates, hF⟩
  refine ⟨F, c₁, c₂, hgates, fun a => ⟨fun ha => ?_, fun hp => ?_⟩⟩
  · rw [(hF a).1 ha]
    exact one_pos
  · by_contra ha
    rw [(hF a).2 ha] at hp
    exact lt_irrefl 0 hp

/-- **Exact quantum time is bounded-error quantum time.** -/
theorem EQTIME_subset_BQTIME (t : ℕ → ℕ) : EQTIME enc t ⊆ BQTIME enc t := by
  rintro A ⟨F, c₁, c₂, hgates, hF⟩
  refine ⟨F, c₁, c₂, hgates, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · rw [(hF a).1 ha]
    norm_num
  · rw [(hF a).2 ha]
    norm_num

/-- Every `BQTIME` class lies in `BQP`. -/
theorem BQTIME_subset_BQP (t : ℕ → ℕ) : BQTIME enc t ⊆ BQP enc :=
  fun _ ⟨F, _, _, _, hF⟩ => ⟨F, hF⟩

/-- **`BQP` is the union of the polynomial quantum time classes** `BQTIME[n ^ k]`: the circuits of
a polynomial-time uniform family have polynomially many gates. -/
theorem BQP_eq_iUnion_BQTIME : BQP enc = ⋃ k : ℕ, BQTIME enc fun n => n ^ k := by
  refine Set.Subset.antisymm (fun A ⟨F, hF⟩ => ?_)
    (Set.iUnion_subset fun k => BQTIME_subset_BQP _)
  obtain ⟨c, d, hc⟩ := F.computableInPolyTime_gates.polyBounded_length.exists_le
  refine Set.mem_iUnion.mpr ⟨d, F, c * 2 ^ d, c, fun n => ?_, hF⟩
  have h1 := (Turing.MultiTapeTM.length_le_length_encList encGateCode (F.gates n)).trans (hc n)
  rw [encUnary_apply, List.length_replicate] at h1
  have h2 : (n + 1) ^ d ≤ 2 ^ d * n ^ d + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp
      · simp [Nat.zero_pow hd]
    · calc (n + 1) ^ d ≤ (2 * n) ^ d := Nat.pow_le_pow_left (by omega) d
        _ = 2 ^ d * n ^ d := mul_pow 2 n d
        _ ≤ _ := Nat.le_succ _
  calc (F.gates n).length ≤ c * (n + 1) ^ d := h1
    _ ≤ c * (2 ^ d * n ^ d + 1) := Nat.mul_le_mul_left _ h2
    _ = c * 2 ^ d * n ^ d + c := by ring

end Cslib.Complexity
