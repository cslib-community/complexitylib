/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod

/-!
# Pigeonhole formulas

The **pigeonhole formula** `PHP^m_n` (`CNF.pigeonhole m n`) has a variable `(i, j)` for every
pigeon `i : Fin m` and hole `j : Fin n`, read as "pigeon `i` sits in hole `j`". Its *pigeon
clauses* (`CNF.pigeonClause`) say that every pigeon sits in some hole, and its *hole clauses*
(`CNF.holeClause`) that no two pigeons sit in the same hole. By the pigeonhole principle it is
satisfiable exactly when `m ≤ n` (`CNF.satisfiable_pigeonhole_iff`); for `m > n` it is the classical
family of unsatisfiable formulas that are hard for resolution [Haken][Haken1985].

## Main definitions

* `Cslib.Logic.PL.CNF.pigeonClause`, `Cslib.Logic.PL.CNF.holeClause`: the two kinds of clauses.
* `Cslib.Logic.PL.CNF.pigeonhole`: the pigeonhole formula `PHP^m_n`.

## Main results

* `Cslib.Logic.PL.CNF.eval_pigeonhole_eq_true_iff`: the semantics of the pigeonhole formula.
* `Cslib.Logic.PL.CNF.satisfiable_pigeonhole_iff`: `PHP^m_n` is satisfiable exactly when `m ≤ n`.
* `Cslib.Logic.PL.CNF.length_le_of_mem_pigeonhole`,
  `Cslib.Logic.PL.CNF.length_pigeonhole_le`: clause-length and formula-size bounds for `PHP^m_n`.

## References

* [A. Haken, *The intractability of resolution*][Haken1985]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 18][Jukna2012]
-/

@[expose] public section

namespace Cslib.Logic.PL

namespace CNF

variable {m n : ℕ}

/-- The **pigeon clause** of pigeon `i`: it sits in one of the holes `Fin n`. -/
def pigeonClause (n : ℕ) (i : Fin m) : Clause (Fin m × Fin n) :=
  (List.finRange n).map fun j => ((i, j), true)

/-- The **hole clause** of pigeons `i`, `i'` and hole `j`: `i` and `i'` do not both sit in
`j`. -/
def holeClause (i i' : Fin m) (j : Fin n) : Clause (Fin m × Fin n) :=
  [((i, j), false), ((i', j), false)]

/-- The **pigeonhole formula** `PHP^m_n`: every pigeon `i : Fin m` sits in a hole `j : Fin n`, and
no two pigeons `i < i'` sit in the same hole. -/
def pigeonhole (m n : ℕ) : CNF (Fin m × Fin n) :=
  (List.finRange m).map (pigeonClause n) ++
    (List.finRange n).flatMap fun j => (List.finRange m).flatMap fun i =>
      ((List.finRange m).filter (i < ·)).map fun i' => holeClause i i' j

/-- The clauses of `PHP^m_n` are its pigeon clauses and its hole clauses. -/
theorem mem_pigeonhole {c : Clause (Fin m × Fin n)} :
    c ∈ pigeonhole m n ↔
      (∃ i, c = pigeonClause n i) ∨ ∃ i i' j, i < i' ∧ c = holeClause i i' j := by
  simp only [pigeonhole, List.mem_append, List.mem_map, List.mem_finRange, true_and,
    List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (⟨i, rfl⟩ | ⟨j, i, i', hii', rfl⟩)
    exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨i, i', j, hii', rfl⟩]
  · rintro (⟨i, rfl⟩ | ⟨i, i', j, hii', rfl⟩)
    exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨j, i, i', hii', rfl⟩]

/-- `pigeonClause n i` evaluates to `true` under `σ` iff `σ (i, j) = true` for some hole `j`. -/
@[simp] theorem eval_pigeonClause (σ : Fin m × Fin n → Bool) (i : Fin m) :
    (pigeonClause n i).eval σ = true ↔ ∃ j, σ (i, j) = true := by
  simp [pigeonClause, Clause.eval_eq_true_iff]

/-- `holeClause i i' j` evaluates to `true` under `σ` iff at least one of `(i, j)` or `(i', j)` is
`false`. -/
@[simp] theorem eval_holeClause (σ : Fin m × Fin n → Bool) (i i' : Fin m) (j : Fin n) :
    (holeClause i i' j).eval σ = true ↔ σ (i, j) = false ∨ σ (i', j) = false := by
  simp [holeClause]

/-- **The semantics of the pigeonhole formula**: an assignment satisfies `PHP^m_n` when it puts
every pigeon in some hole and no two pigeons in the same hole. -/
theorem eval_pigeonhole_eq_true_iff (σ : Fin m × Fin n → Bool) :
    (pigeonhole m n).eval σ = true ↔
      (∀ i, ∃ j, σ (i, j) = true) ∧
        ∀ i i' j, σ (i, j) = true → σ (i', j) = true → i = i' := by
  rw [eval_eq_true_iff]
  constructor
  · intro h
    refine ⟨fun i => (eval_pigeonClause σ i).1 (h _ (mem_pigeonhole.2 (Or.inl ⟨i, rfl⟩))),
      fun i i' j hi hi' => ?_⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := (eval_holeClause σ i i' j).1 (h _ (mem_pigeonhole.2 (Or.inr ⟨i, i', j, hlt, rfl⟩)))
      simp_all
    · have := (eval_holeClause σ i' i j).1 (h _ (mem_pigeonhole.2 (Or.inr ⟨i', i, j, hlt, rfl⟩)))
      simp_all
  · rintro ⟨hp, hh⟩ c hc
    rcases mem_pigeonhole.1 hc with ⟨i, rfl⟩ | ⟨i, i', j, hii', rfl⟩
    · exact (eval_pigeonClause σ i).2 (hp i)
    · rw [eval_holeClause]
      by_contra! h
      exact hii'.ne (hh i i' j (Bool.not_eq_false _ ▸ h.1) (Bool.not_eq_false _ ▸ h.2))

/-- **The pigeonhole principle**: `PHP^m_n` is satisfiable exactly when there are at most as many
pigeons as holes. -/
theorem satisfiable_pigeonhole_iff : (pigeonhole m n).Satisfiable ↔ m ≤ n := by
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨hp, hh⟩ := (eval_pigeonhole_eq_true_iff σ).1 hσ
    choose g hg using hp
    by_contra! hlt
    obtain ⟨i, i', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt g (by simpa using hlt)
    exact hne (hh i i' (g i) (hg i) (heq ▸ hg i'))
  · intro hmn
    refine ⟨fun x => decide (x.1.val = x.2.val), (eval_pigeonhole_eq_true_iff _).2 ⟨fun i =>
      ⟨⟨i.val, i.isLt.trans_le hmn⟩, by simp⟩, fun i i' j hi hi' => ?_⟩⟩
    simp only [decide_eq_true_eq] at hi hi'
    exact Fin.ext (hi.trans hi'.symm)

/-- `PHP^m_n` is unsatisfiable when there are more pigeons than holes. -/
theorem not_satisfiable_pigeonhole (h : n < m) : ¬ (pigeonhole m n).Satisfiable := by
  rw [satisfiable_pigeonhole_iff]
  omega

/-- The pigeon clause for `n` holes has length `n`. -/
@[simp] theorem length_pigeonClause (n : ℕ) (i : Fin m) : (pigeonClause n i).length = n := by
  simp [pigeonClause]

/-- Every hole clause has length `2`. -/
@[simp] theorem length_holeClause (i i' : Fin m) (j : Fin n) : (holeClause i i' j).length = 2 :=
  rfl

/-- Every clause of `PHP^m_n` has at most `max n 2` literals. -/
theorem length_le_of_mem_pigeonhole {c : Clause (Fin m × Fin n)} (hc : c ∈ pigeonhole m n) :
    c.length ≤ max n 2 := by
  rcases mem_pigeonhole.1 hc with ⟨i, rfl⟩ | ⟨i, i', j, -, rfl⟩
  · simp
  · simp

private theorem length_flatMap_le {α β : Type*} {f : α → List β} {k : ℕ}
    (h : ∀ a, (f a).length ≤ k) : ∀ l : List α, (l.flatMap f).length ≤ l.length * k
  | [] => by simp
  | a :: l => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_one_mul,
      Nat.add_comm _ k]
    exact Nat.add_le_add (h a) (length_flatMap_le h l)

/-- `PHP^m_n` has at most `m + n m²` clauses. -/
theorem length_pigeonhole_le (m n : ℕ) : (pigeonhole m n).length ≤ m + n * m ^ 2 := by
  rw [pigeonhole, List.length_append, List.length_map, List.length_finRange]
  refine Nat.add_le_add_left ?_ m
  refine (length_flatMap_le (k := m ^ 2) (fun j => ?_) _).trans_eq (by simp)
  refine (length_flatMap_le (k := m) (fun i => ?_) _).trans_eq (by simp [Nat.pow_two])
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

/-- `PHP^m_n` has at most `m n` variables. -/
theorem card_toFinset_vars_pigeonhole_le (m n : ℕ) :
    (pigeonhole m n).vars.toFinset.card ≤ m * n :=
  (Finset.card_le_univ _).trans_eq (by simp)

end CNF

end Cslib.Logic.PL
