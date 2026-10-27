/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ParityTests
public import Mathlib.Data.Nat.Log
import Complexity.Foundations.Data.BitString.InitialTests

/-!
# Exact parity tests for sparse CNF formulas

Combining the initial parity tests of [OpenAI2026ETH, Lemma 6.1]
(`Cslib.BitString.exists_initialTests`) with the greedy selection of [OpenAI2026ETH, Lemma 6.2]
(`Cslib.Logic.PL.CNF.numPassing_greedy`): for a formula on `n ≥ 1` variables with `m ≤ B n`
clauses, there are at most `3 n` initial parity tests on the clause-violation bits, each reading
at most `D₀ = 320000 B² μ³` of them, such that every passing nonsatisfying assignment violates at
least `m / P` clauses, `P = 20000 B² μ²`, `μ = ⌊log₂ m⌋ + 1`
(`Cslib.Logic.PL.CNF.exists_initialTests`). After them, `3 n` greedily chosen tests of list length
`P` are passed exactly by the satisfying assignments
(`Cslib.Logic.PL.CNF.numPassing_greedy_initial`).
Both statements are about existence and counts; computing the tests is not treated here.

## Main results

* `Cslib.Logic.PL.CNF.exists_initialTests`: initial tests for a formula.
* `Cslib.Logic.PL.CNF.numPassing_greedy_initial`: the greedy tests after them are exact.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §§6.1–6.2
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset Cslib.BitString

variable {V : Type*}

/-- **Initial parity tests for a formula** [OpenAI2026ETH, Lemma 6.1]: for a formula on `n ≥ 1`
variables with `m ≤ B n` clauses, `B ≥ 1`, there are at most `3 n` rows on the `m` violation bits,
each with at most `320000 B² μ³` ones, such that every passing nonsatisfying assignment violates at
least `m / (20000 B² μ²)` clauses, where `μ = ⌊log₂ m⌋ + 1`. -/
theorem CNF.exists_initialTests [Fintype V] (φ : CNF V) {B : ℕ} (hn : 1 ≤ Fintype.card V)
    (hB : 1 ≤ B) (hm : φ.length ≤ B * Fintype.card V) :
    ∃ A₀ : List (Fin φ.length → Bool), A₀.length ≤ 3 * Fintype.card V ∧
      (∀ r ∈ A₀, weight r ≤ 320000 * B ^ 2 * (Nat.log 2 φ.length + 1) ^ 3) ∧
      ∀ σ, PassesTests φ.violations A₀ σ → φ.eval σ = false →
        φ.length ≤ 20000 * B ^ 2 * (Nat.log 2 φ.length + 1) ^ 2 * weight (φ.violations σ) := by
  obtain ⟨A₀, hlen, hw, hdist⟩ := Cslib.BitString.exists_initialTests hn hB hm
  refine ⟨A₀, hlen, hw, fun σ hσ hf => hdist _ (fun h0 => ?_) hσ⟩
  simp [CNF.violations_eq_zero_iff, hf] at h0

/-- **Exact parity tests for a formula** [OpenAI2026ETH, Lemmas 6.1–6.2]: for a formula on
`n ≥ 1` variables with `m ≤ B n` clauses, `B ≥ 1`, there are initial rows as in
`CNF.exists_initialTests` such that, after appending `3 n` rows `testRow (γ i)` of list length
`P = 20000 B² μ²`, each minimizing the number of passing assignments, the passing assignments are
exactly the satisfying ones. -/
theorem CNF.numPassing_greedy_initial [Fintype V] [DecidableEq V] (φ : CNF V) {B : ℕ}
    (hn : 1 ≤ Fintype.card V) (hB : 1 ≤ B) (hm : φ.length ≤ B * Fintype.card V) :
    ∃ A₀ : List (Fin φ.length → Bool), A₀.length ≤ 3 * Fintype.card V ∧
      (∀ r ∈ A₀, weight r ≤ 320000 * B ^ 2 * (Nat.log 2 φ.length + 1) ^ 3) ∧
      ∀ (A : ℕ → List (Fin φ.length → Bool))
        (γ : ℕ → Fin (20000 * B ^ 2 * (Nat.log 2 φ.length + 1) ^ 2) → Fin φ.length × Bool),
        A 0 = A₀ → (∀ i, A (i + 1) = A i ++ [testRow (γ i)]) →
        (∀ i (γ' : Fin (20000 * B ^ 2 * (Nat.log 2 φ.length + 1) ^ 2) → Fin φ.length × Bool),
          numPassing φ.violations (A i ++ [testRow (γ i)]) ≤
          numPassing φ.violations (A i ++ [testRow γ'])) →
        numPassing φ.violations (A (3 * Fintype.card V)) = #{σ : V → Bool | φ.eval σ = true} := by
  obtain ⟨A₀, hlen, hw, hinit⟩ := φ.exists_initialTests hn hB hm
  refine ⟨A₀, hlen, hw, fun A γ h0 hA hγ => ?_⟩
  have hP : 1 ≤ 20000 * B ^ 2 * (Nat.log 2 φ.length + 1) ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact CNF.numPassing_greedy φ hn hP A (fun σ hσ hf => hinit σ (h0 ▸ hσ) hf) γ hA hγ

end Cslib.Logic.PL
