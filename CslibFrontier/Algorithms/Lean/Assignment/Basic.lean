/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Logic.Equiv.Defs

/-!
# The assignment problem: duality and `ε`-complementary slackness

The (square, complete) assignment problem asks for a permutation `σ` of a finite type `ι`
minimising the total cost `∑ i, c (i, σ i)`; person `i` receives object `σ i`. Its
linear-programming dual maximises `∑ i, u i + ∑ j, v j` over potentials with
`u i + v j ≤ c (i, j)`.

This module records the duality facts used by the auction algorithm of [Bertsekas1988]
(`CslibFrontier.Algorithms.Lean.Assignment.Auction`), in the cost-minimisation form (Bertsekas
maximises benefits `a = -c`). Object prices `p` play the role of the column potentials `-p`. A
complete assignment `σ` and prices `p` satisfy **`ε`-complementary slackness**
([Bertsekas1998], (7.1)) if each person's object is within `ε` of a least reduced cost
`c (i, k) + p k`.

Everything is stated over an arbitrary finite index type and a linearly ordered additive commutative
group, so the lemmas apply to integer, rational and real costs alike.

## Main definitions

* `IsEpsCompSlack c ε σ p`: `σ` and `p` satisfy `ε`-complementary slackness for the cost `c`.
* `rowPotential c p`: the row potentials `i ↦ min_k (c (i, k) + p k)` induced by prices `p`.

## Main results

* `sum_add_sum_le_sum_perm`: weak duality over permutations.
* `IsEpsCompSlack.sum_le_sum_add`: an `ε`-complementary-slack assignment costs at most
  `card ι • ε` more than every assignment ([Bertsekas1998], Prop. 1.4).
* `rowPotential_add_neg_le`, `IsEpsCompSlack.sum_le_rowPotential`: prices give feasible dual
  potentials `(rowPotential c p, -p)`, whose total is within `card ι • ε` of the cost of an
  `ε`-complementary-slack assignment (an approximate dual certificate).

## References

* [Bertsekas1988]
* [Bertsekas1998]
-/

public section

namespace Cslib.Algorithms.Lean.Assignment

open Finset

variable {ι α : Type*} [Fintype ι] [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- A complete assignment `σ` (person `i` gets object `σ i`) and object prices `p` satisfy
**`ε`-complementary slackness** for the cost `c` if every person's object has reduced cost
`c (i, σ i) + p (σ i)` within `ε` of every other reduced cost `c (i, k) + p k`
([Bertsekas1998], (7.1), stated for costs `c = -a`). -/
@[expose] def IsEpsCompSlack (c : ι × ι → α) (ε : α) (σ : Equiv.Perm ι) (p : ι → α) : Prop :=
  ∀ i k, c (i, σ i) + p (σ i) ≤ c (i, k) + p k + ε

/-- **Weak duality** for the assignment problem: the total of potentials `u`, `v` with
`u i + v j ≤ c (i, j)` is at most the cost of every assignment. -/
theorem sum_add_sum_le_sum_perm {c : ι × ι → α} {u v : ι → α}
    (h : ∀ i j, u i + v j ≤ c (i, j)) (τ : Equiv.Perm ι) :
    ∑ i, u i + ∑ j, v j ≤ ∑ i, c (i, τ i) := by
  calc ∑ i, u i + ∑ j, v j = ∑ i, (u i + v (τ i)) := by
        rw [sum_add_distrib, Equiv.sum_comp τ v]
    _ ≤ ∑ i, c (i, τ i) := sum_le_sum fun i _ => h i (τ i)

/-- **`nε`-optimality** ([Bertsekas1998], Prop. 1.4): a complete assignment satisfying
`ε`-complementary slackness with some prices costs at most `card ι • ε` more than every
assignment. -/
theorem IsEpsCompSlack.sum_le_sum_add {c : ι × ι → α} {ε : α} {σ : Equiv.Perm ι} {p : ι → α}
    (h : IsEpsCompSlack c ε σ p) (τ : Equiv.Perm ι) :
    ∑ i, c (i, σ i) ≤ ∑ i, c (i, τ i) + Fintype.card ι • ε := by
  have key := sum_le_sum fun i (_ : i ∈ univ) => h i (τ i)
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, Equiv.sum_comp σ p,
    Equiv.sum_comp τ p, sum_const, card_univ, add_right_comm] at key
  exact le_of_add_le_add_right key

/-- The row potentials of prices `p`: the least reduced cost `min_k (c (i, k) + p k)` of row `i`.
Together with the column potentials `-p` they are feasible for the dual of the assignment problem
(`rowPotential_add_neg_le`). -/
@[expose] def rowPotential (c : ι × ι → α) (p : ι → α) (i : ι) : α :=
  univ.inf' ⟨i, mem_univ i⟩ fun k => c (i, k) + p k

/-- Prices give **feasible dual potentials**: `rowPotential c p i + -p j ≤ c (i, j)`. -/
theorem rowPotential_add_neg_le (c : ι × ι → α) (p : ι → α) (i j : ι) :
    rowPotential c p i + -p j ≤ c (i, j) := by
  have h : rowPotential c p i ≤ c (i, j) + p j := inf'_le (fun k => c (i, k) + p k) (mem_univ j)
  rw [← sub_eq_add_neg, sub_le_iff_le_add]
  exact h

/-- **Approximate dual certificate**: if `σ` and `p` satisfy `ε`-complementary slackness, the
feasible potentials `rowPotential c p` and `-p` have total within `card ι • ε` of the cost of
`σ`. With `sum_add_sum_le_sum_perm` this certifies `IsEpsCompSlack.sum_le_sum_add`. -/
theorem IsEpsCompSlack.sum_le_rowPotential {c : ι × ι → α} {ε : α} {σ : Equiv.Perm ι}
    {p : ι → α} (h : IsEpsCompSlack c ε σ p) :
    ∑ i, c (i, σ i) ≤ ∑ i, rowPotential c p i + ∑ j, -p j + Fintype.card ι • ε := by
  have hrow : ∀ i, c (i, σ i) + p (σ i) - ε ≤ rowPotential c p i := fun i =>
    le_inf' _ _ fun k _ => sub_le_iff_le_add.2 (h i k)
  have key := sum_le_sum fun i (_ : i ∈ univ) => hrow i
  rw [sum_sub_distrib, sum_add_distrib, Equiv.sum_comp σ p, sum_const, card_univ,
    sub_le_iff_le_add] at key
  rw [sum_neg_distrib, ← sub_eq_add_neg, sub_add_eq_add_sub, le_sub_iff_add_le]
  exact key

end Cslib.Algorithms.Lean.Assignment
