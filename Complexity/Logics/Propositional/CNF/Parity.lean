/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity
public import Complexity.Logics.Propositional.CNF
public import Mathlib.Data.Finset.Powerset

/-!
# Parity constraints in conjunctive normal form

The constraint that the parity of the variables in a finite set `B` is `c` has a formula in
conjunctive normal form with one clause for each assignment to `B` of the other parity, excluding
that assignment (`CNF.parityOnEq`); assignments to `B` are indexed by the subsets of `B` on which
they are true. Its clauses have `#B` literals each, and there are at most
`2 ^ #B` of them (`CNF.length_parityOnEq_le`).

## Main definitions

* `Cslib.Logic.PL.Clause.exclude`: the clause excluding the values of an assignment on a set of
  variables.
* `Cslib.Logic.PL.CNF.parityOnEq`: the parity constraint on a finite set of variables.

## Main results

* `Cslib.Logic.PL.CNF.eval_parityOnEq_eq_true_iff`: `CNF.parityOnEq B c` holds exactly when the
  parity of the variables in `B` is `c`.
* `Cslib.Logic.PL.CNF.length_parityOnEq_le`: it has at most `2 ^ #B` clauses.

## References

* [A. Urquhart, *Hard examples for resolution*][Urquhart1987], for parity constraints in
  conjunctive normal form as the clauses of Tseitin formulas
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset

variable {ι : Type*}

/-- The clause excluding the values of `y` on `B`: it holds when the assignment differs from `y` at
some variable in `B`. -/
noncomputable def Clause.exclude (B : Finset ι) (y : ι → Bool) : Clause ι :=
  B.toList.map fun i => (i, !y i)

/-- `Clause.exclude B y` holds under `x` if and only if `x` differs from `y` on some variable in
`B`. -/
theorem Clause.eval_exclude_eq_true_iff (B : Finset ι) (y x : ι → Bool) :
    (Clause.exclude B y).eval x = true ↔ ∃ i ∈ B, x i ≠ y i := by
  simp [Clause.exclude, Clause.eval_eq_true_iff, Bool.eq_not_iff]

/-- `Clause.exclude B y` has `#B` literals. -/
@[simp] theorem Clause.length_exclude (B : Finset ι) (y : ι → Bool) :
    (Clause.exclude B y).length = #B := by
  simp [Clause.exclude]

/-- The literals of `Clause.exclude B y` are the variables of `B`, with the polarity opposite to
their values in `y`. -/
theorem Clause.mem_exclude {B : Finset ι} {y : ι → Bool} {l : Literal ι} :
    l ∈ Clause.exclude B y ↔ l.1 ∈ B ∧ l.2 = !y l.1 := by
  obtain ⟨i, b⟩ := l
  simp only [Clause.exclude, List.mem_map, mem_toList, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, rfl, rfl⟩
    exact ⟨hj, rfl⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨i, hi, rfl, rfl⟩

variable [DecidableEq ι]

/-- A formula in conjunctive normal form saying that the parity of the variables in `B` is `c`: for
each subset `A` of `B` such that the assignment true on `A` and false on the rest of `B` has the
other parity, a clause excludes that assignment. -/
noncomputable def CNF.parityOnEq (B : Finset ι) (c : Bool) : CNF ι :=
  ({A ∈ B.powerset | parityOn B (fun i => decide (i ∈ A)) ≠ c}).toList.map fun A =>
    Clause.exclude B fun i => decide (i ∈ A)

/-- **The semantics of parity constraints**: `CNF.parityOnEq B c` holds exactly when the parity of
the variables in `B` is `c`. -/
theorem CNF.eval_parityOnEq_eq_true_iff (B : Finset ι) (c : Bool) (x : ι → Bool) :
    (CNF.parityOnEq B c).eval x = true ↔ parityOn B x = c := by
  simp only [CNF.parityOnEq, CNF.eval_map_eq_true_iff, mem_toList, mem_filter, mem_powerset,
    Clause.eval_exclude_eq_true_iff, and_imp]
  constructor
  · intro h
    by_contra hne
    -- the assignment of `x` to `B` is excluded
    have hx (i : ι) (hi : i ∈ B) : decide (i ∈ {j ∈ B | x j = true}) = x i := by
      cases hxi : x i <;> simp [hi, hxi]
    obtain ⟨i, hi, hxi⟩ := h _ (filter_subset _ _)
      ((parityOn_congr hx).trans_ne hne)
    exact hxi (hx i hi).symm
  · intro hx A _ hA
    by_contra h
    push Not at h
    exact hA ((parityOn_congr h).symm.trans hx)

/-- A clause of `CNF.parityOnEq B c` excludes an assignment to `B`. -/
theorem CNF.exists_eq_exclude_of_mem_parityOnEq {B : Finset ι} {c : Bool} {d : Clause ι}
    (hd : d ∈ CNF.parityOnEq B c) : ∃ y : ι → Bool, d = Clause.exclude B y := by
  obtain ⟨A, -, rfl⟩ := List.mem_map.1 hd
  exact ⟨_, rfl⟩

/-- The clauses of `CNF.parityOnEq B c` have `#B` literals. -/
theorem CNF.length_of_mem_parityOnEq {B : Finset ι} {c : Bool} {d : Clause ι}
    (hd : d ∈ CNF.parityOnEq B c) : d.length = #B := by
  obtain ⟨y, rfl⟩ := CNF.exists_eq_exclude_of_mem_parityOnEq hd
  exact Clause.length_exclude B y

/-- `CNF.parityOnEq B c` has at most `2 ^ #B` clauses: one per subset of `B`. -/
theorem CNF.length_parityOnEq_le (B : Finset ι) (c : Bool) :
    (CNF.parityOnEq B c).length ≤ 2 ^ #B := by
  rw [CNF.parityOnEq, List.length_map, length_toList, ← card_powerset]
  exact card_filter_le _ _

end Cslib.Logic.PL
