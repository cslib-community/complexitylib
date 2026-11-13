/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# The truth-table CNF of a Boolean function

Every Boolean function `f : (Fin ℓ → Bool) → Bool` of `ℓ` variables is computed by a CNF formula
over the variables `Fin ℓ` with at most `ℓ * 2 ^ ℓ` AND and OR symbols
[Arora and Barak, draft, Claim 2.14][AroraBarak07]. The formula `CNF.ofTruthTable f` has one
clause for each assignment `v` with `f v = false`, namely the clause `Clause.excluding v` of the
`ℓ` literals that `v` falsifies, which is false exactly at `v`.

**Size measure.** `CNF.connectiveCount φ` counts the binary AND and OR symbols of `φ` written as
`(l ∨ ⋯ ∨ l) ∧ ⋯ ∧ (l ∨ ⋯ ∨ l)`: a clause of `k` literals has `k - 1` ORs, and `m` clauses are
joined by `m - 1` ANDs (truncated subtraction, so the empty clause and the empty formula
contribute no symbols). The truth-table formula has at most `2 ^ ℓ` clauses of exactly `ℓ`
literals, hence at most `ℓ * 2 ^ ℓ - 1` symbols when `f` has a zero, and none otherwise. The
source states the size as `ℓ 2 ^ ℓ`; its proof bounds it by that, which is the statement here.
The number of literal occurrences is also at most `ℓ * 2 ^ ℓ`
(`CNF.length_vars_ofTruthTable_le`).

## Main definitions

* `Cslib.Logic.PL.CNF.connectiveCount`: the number of AND and OR symbols.
* `Cslib.Logic.PL.Clause.excluding`: the clause false exactly at one assignment.
* `Cslib.Logic.PL.CNF.ofTruthTable`: the truth-table CNF of a Boolean function.

## Main results

* `Cslib.Logic.PL.CNF.eval_ofTruthTable`: the truth-table CNF computes the function.
* `Cslib.Logic.PL.CNF.connectiveCount_ofTruthTable_le`: it has at most `ℓ * 2 ^ ℓ` AND and OR
  symbols.
* `Cslib.Logic.PL.CNF.exists_eval_eq_connectiveCount_le`: Claim 2.14.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft 2007][AroraBarak07]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V : Type*} {ℓ : ℕ}

/-- The number of binary AND and OR symbols of a CNF formula written out as
`(l ∨ ⋯ ∨ l) ∧ ⋯ ∧ (l ∨ ⋯ ∨ l)`: `k - 1` ORs in a clause of `k` literals, and `m - 1` ANDs
between `m` clauses. -/
def CNF.connectiveCount (φ : CNF V) : ℕ :=
  (φ.length - 1) + (φ.map fun c => c.length - 1).sum

/-- The clause of the `ℓ` literals falsified by `v`: it is false exactly at `v`. -/
def Clause.excluding (v : Fin ℓ → Bool) : Clause (Fin ℓ) :=
  List.ofFn fun i => (i, !v i)

@[simp]
theorem Clause.length_excluding (v : Fin ℓ → Bool) : (Clause.excluding v).length = ℓ :=
  List.length_ofFn

/-- `Clause.excluding v` holds exactly at the assignments other than `v`. -/
theorem Clause.eval_excluding_eq_true_iff (σ v : Fin ℓ → Bool) :
    (Clause.excluding v).eval σ = true ↔ σ ≠ v := by
  simp only [Clause.eval_eq_true_iff, Clause.excluding, List.mem_ofFn, ne_eq, funext_iff,
    not_forall]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, h⟩
    exact ⟨i, by revert h; cases σ i <;> cases v i <;> simp⟩
  · rintro ⟨i, h⟩
    exact ⟨_, ⟨i, rfl⟩, by revert h; cases σ i <;> cases v i <;> simp⟩

/-- The truth-table CNF of `f`: a clause `Clause.excluding v` for each zero `v` of `f`. -/
noncomputable def CNF.ofTruthTable (f : (Fin ℓ → Bool) → Bool) : CNF (Fin ℓ) :=
  (Finset.univ.filter fun v => f v = false).toList.map Clause.excluding

/-- **The truth-table CNF computes the function.** -/
theorem CNF.eval_ofTruthTable (f : (Fin ℓ → Bool) → Bool) (σ : Fin ℓ → Bool) :
    (CNF.ofTruthTable f).eval σ = f σ := by
  rw [Bool.eq_iff_iff, CNF.ofTruthTable, CNF.eval_map_eq_true_iff]
  simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and,
    Clause.eval_excluding_eq_true_iff]
  constructor
  · intro h
    by_contra hf
    exact h σ (by simpa using hf) rfl
  · rintro hf v hv rfl
    simp [hf] at hv

/-- The truth-table CNF has at most `2 ^ ℓ` clauses. -/
theorem CNF.length_ofTruthTable_le (f : (Fin ℓ → Bool) → Bool) :
    (CNF.ofTruthTable f).length ≤ 2 ^ ℓ := by
  rw [CNF.ofTruthTable, List.length_map, Finset.length_toList]
  refine (Finset.card_filter_le _ _).trans_eq ?_
  simp

/-- Every clause of the truth-table CNF has exactly `ℓ` literals. -/
theorem CNF.length_of_mem_ofTruthTable {f : (Fin ℓ → Bool) → Bool} {c : Clause (Fin ℓ)}
    (hc : c ∈ CNF.ofTruthTable f) : c.length = ℓ := by
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hc
  exact Clause.length_excluding v

/-- The truth-table CNF has at most `ℓ * 2 ^ ℓ` literal occurrences. -/
theorem CNF.length_vars_ofTruthTable_le (f : (Fin ℓ → Bool) → Bool) :
    (CNF.ofTruthTable f).vars.length ≤ ℓ * 2 ^ ℓ :=
  (CNF.length_vars_le_mul_length fun _ hc => (CNF.length_of_mem_ofTruthTable hc).le).trans
    (Nat.mul_le_mul_left ℓ (CNF.length_ofTruthTable_le f))

/-- **Size of the truth-table CNF**: at most `ℓ * 2 ^ ℓ` AND and OR symbols. -/
theorem CNF.connectiveCount_ofTruthTable_le (f : (Fin ℓ → Bool) → Bool) :
    (CNF.ofTruthTable f).connectiveCount ≤ ℓ * 2 ^ ℓ := by
  have hsum : ((CNF.ofTruthTable f).map fun c => c.length - 1).sum =
      (CNF.ofTruthTable f).length * (ℓ - 1) := by
    rw [List.map_congr_left (g := fun _ => ℓ - 1)
      (fun c hc => by rw [CNF.length_of_mem_ofTruthTable hc])]
    simp
  have hm := CNF.length_ofTruthTable_le f
  rw [CNF.connectiveCount, hsum]
  generalize (CNF.ofTruthTable f).length = m at hm ⊢
  rcases ℓ with _ | ℓ
  · simp only [pow_zero] at hm
    omega
  · rw [Nat.add_sub_cancel]
    calc m - 1 + m * ℓ ≤ 2 ^ (ℓ + 1) + 2 ^ (ℓ + 1) * ℓ :=
          Nat.add_le_add (by omega) (Nat.mul_le_mul_right ℓ hm)
      _ = (ℓ + 1) * 2 ^ (ℓ + 1) := by
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm ℓ, Nat.add_comm]

/-- **Every Boolean function has a CNF with at most `ℓ 2 ^ ℓ` AND and OR symbols**
[Arora and Barak, draft, Claim 2.14][AroraBarak07]. -/
theorem CNF.exists_eval_eq_connectiveCount_le (f : (Fin ℓ → Bool) → Bool) :
    ∃ φ : CNF (Fin ℓ), (∀ σ, φ.eval σ = f σ) ∧ φ.connectiveCount ≤ ℓ * 2 ^ ℓ :=
  ⟨_, CNF.eval_ofTruthTable f, CNF.connectiveCount_ofTruthTable_le f⟩

end Cslib.Logic.PL
