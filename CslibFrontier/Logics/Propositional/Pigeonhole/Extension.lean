/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF
public import Mathlib.Data.List.FinRange
import CslibFrontier.Logics.Propositional.Pigeonhole

/-!
# The extended pigeonhole formula

The pigeon clauses of `PHP^m_n` (`Cslib.Logic.PL.CNF.pigeonhole`) have width `n`. The
**extended pigeonhole formula** `EPHP^m_n` (`Cslib.Logic.PL.CNF.pigeonholeExt`) replaces each of
them by a chain of clauses of width at most `3` through extension variables, so that width lower
bounds for it are meaningful. Atserias and Dalmau use such a `3`-CNF encoding of the pigeonhole
principle, the standard non-deterministic extension of Alekhnovich, Ben-Sasson, Razborov and
Wigderson, to illustrate their characterization of resolution width [Atserias and Dalmau,
Section 5][AtseriasDalmau2008]. The mathematical symbols of the available copy of that paper do not
extract, so the exact form of its clauses is not quoted here; the encoding below is ours.

Besides the variables `inl (i, j)` of `PHP^m_n`, read as "pigeon `i` sits in hole `j`", there is a
variable `inr (i, j)` for every pigeon `i : Fin m` and `j : Fin (n + 1)`, read as "pigeon `i` sits
in a hole `≥ j`". The clauses say:

* `inr (i, 0)`: every pigeon sits in a hole `≥ 0` (`Cslib.Logic.PL.CNF.phpStartClause`);
* `¬ inr (i, n)`: no pigeon sits in a hole `≥ n` (`Cslib.Logic.PL.CNF.phpStopClause`);
* `¬ inr (i, j) ∨ inl (i, j) ∨ inr (i, j + 1)`: a pigeon in a hole `≥ j` sits in `j` or in a hole
  `≥ j + 1` (`Cslib.Logic.PL.CNF.phpStepClause`);
* `¬ inl (i, j) ∨ ¬ inl (i', j)` for `i < i'`: the hole clauses of `PHP^m_n`
  (`Cslib.Logic.PL.CNF.phpExtHoleClause`).

It is unsatisfiable for `m > n` (`Cslib.Logic.PL.CNF.not_satisfiable_pigeonholeExt`): following
the chain, a satisfying assignment would satisfy `PHP^m_n` on the variables `inl (i, j)`.

## Main definitions

* `Cslib.Logic.PL.CNF.PHPExtVar`: the variables of `EPHP^m_n`.
* `Cslib.Logic.PL.CNF.pigeonholeExt`: the extended pigeonhole formula `EPHP^m_n`.
* `Cslib.Logic.PL.CNF.pigeonholeExtAssign`: the assignment placing each pigeon `i` in a hole `f i`.

## Main results

* `Cslib.Logic.PL.CNF.mem_pigeonholeExt`: the clauses of `EPHP^m_n`.
* `Cslib.Logic.PL.CNF.length_le_three_of_mem_pigeonholeExt`: `EPHP^m_n` is a `3`-CNF.
* `Cslib.Logic.PL.CNF.not_satisfiable_pigeonholeExt`: `EPHP^m_n` is unsatisfiable for `m > n`.
* `Cslib.Logic.PL.CNF.eval_pigeonholeExtAssign`: an injective placement satisfies it.

## References

* [A. Atserias, V. Dalmau, *A combinatorial characterization of resolution
  width*][AtseriasDalmau2008]
* [M. Alekhnovich, E. Ben-Sasson, A. Razborov, A. Wigderson, *Space complexity in propositional
  calculus*][AlekhnovichBenSassonRazborovWigderson2002]
-/

@[expose] public section

namespace Cslib.Logic.PL

namespace CNF

variable {m n : ℕ}

/-- The variables of the extended pigeonhole formula `EPHP^m_n`: `inl (i, j)` reads "pigeon `i`
sits in hole `j`", and `inr (i, j)` reads "pigeon `i` sits in a hole `≥ j`". -/
abbrev PHPExtVar (m n : ℕ) : Type := (Fin m × Fin n) ⊕ (Fin m × Fin (n + 1))

/-- The pigeon a variable of `EPHP^m_n` is about. -/
def PHPExtVar.pigeon : PHPExtVar m n → Fin m
  | .inl x => x.1
  | .inr x => x.1

/-- The **start clause** of pigeon `i`: it sits in a hole `≥ 0`. -/
def phpStartClause (n : ℕ) (i : Fin m) : Clause (PHPExtVar m n) := [(.inr (i, 0), true)]

/-- The **stop clause** of pigeon `i`: it does not sit in a hole `≥ n`. -/
def phpStopClause (n : ℕ) (i : Fin m) : Clause (PHPExtVar m n) :=
  [(.inr (i, Fin.last n), false)]

/-- The **step clause** of pigeon `i` and hole `j`: if it sits in a hole `≥ j`, it sits in `j` or
in a hole `≥ j + 1`. -/
def phpStepClause (i : Fin m) (j : Fin n) : Clause (PHPExtVar m n) :=
  [(.inr (i, j.castSucc), false), (.inl (i, j), true), (.inr (i, j.succ), true)]

/-- The **hole clause** of pigeons `i`, `i'` and hole `j`: `i` and `i'` do not both sit in `j`. -/
def phpExtHoleClause (i i' : Fin m) (j : Fin n) : Clause (PHPExtVar m n) :=
  [(.inl (i, j), false), (.inl (i', j), false)]

/-- The **extended pigeonhole formula** `EPHP^m_n`: the pigeon clauses of `PHP^m_n` are replaced
by start, step and stop clauses on extension variables. -/
def pigeonholeExt (m n : ℕ) : CNF (PHPExtVar m n) :=
  (List.finRange m).map (phpStartClause n) ++ (List.finRange m).map (phpStopClause n) ++
    (List.finRange m).flatMap (fun i => (List.finRange n).map (phpStepClause i)) ++
    (List.finRange n).flatMap fun j => (List.finRange m).flatMap fun i =>
      ((List.finRange m).filter (i < ·)).map fun i' => phpExtHoleClause i i' j

/-- The clauses of `EPHP^m_n`. -/
theorem mem_pigeonholeExt {c : Clause (PHPExtVar m n)} :
    c ∈ pigeonholeExt m n ↔ (∃ i, c = phpStartClause n i) ∨ (∃ i, c = phpStopClause n i) ∨
      (∃ i j, c = phpStepClause i j) ∨ ∃ i i' j, i < i' ∧ c = phpExtHoleClause i i' j := by
  simp only [pigeonholeExt, List.mem_append, List.mem_map, List.mem_finRange, true_and,
    List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, j, rfl⟩) | ⟨j, i, i', hii', rfl⟩)
    exacts [Or.inl ⟨i, rfl⟩, Or.inr (Or.inl ⟨i, rfl⟩), Or.inr (Or.inr (Or.inl ⟨i, j, rfl⟩)),
      Or.inr (Or.inr (Or.inr ⟨i, i', j, hii', rfl⟩))]
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, j, rfl⟩ | ⟨i, i', j, hii', rfl⟩)
    exacts [Or.inl (Or.inl (Or.inl ⟨i, rfl⟩)), Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)),
      Or.inl (Or.inr ⟨i, j, rfl⟩), Or.inr ⟨j, i, i', hii', rfl⟩]

/-- **`EPHP^m_n` is a `3`-CNF**: its clauses have length at most `3`. -/
theorem length_le_three_of_mem_pigeonholeExt {c : Clause (PHPExtVar m n)}
    (hc : c ∈ pigeonholeExt m n) : c.length ≤ 3 := by
  rcases mem_pigeonholeExt.1 hc with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, j, rfl⟩ | ⟨i, i', j, -, rfl⟩ <;>
    simp [phpStartClause, phpStopClause, phpStepClause, phpExtHoleClause]

/-- **`EPHP^m_n` is unsatisfiable when there are more pigeons than holes**: a satisfying assignment
would satisfy `PHP^m_n` on the variables `inl (i, j)`. -/
theorem not_satisfiable_pigeonholeExt (h : n < m) : ¬ (pigeonholeExt m n).Satisfiable := by
  rintro ⟨σ, hσ⟩
  rw [eval_eq_true_iff] at hσ
  refine not_satisfiable_pigeonhole h ⟨fun x => σ (.inl x), ?_⟩
  rw [eval_pigeonhole_eq_true_iff]
  refine ⟨fun i => ?_, fun i i' j hi hi' => ?_⟩
  · by_contra! hno
    -- following the step clauses, pigeon `i` sits in a hole `≥ j` for every `j ≤ n`
    have hy : ∀ j : ℕ, (hj : j ≤ n) → σ (.inr (i, ⟨j, Nat.lt_succ_of_le hj⟩)) = true := by
      intro j
      induction j with
      | zero =>
        intro _
        simpa [phpStartClause, Clause.eval, Literal.eval] using
          hσ _ (mem_pigeonholeExt.2 (Or.inl ⟨i, rfl⟩))
      | succ j ih =>
        intro hj
        have h₁ := ih (by omega)
        have h₂ := hno ⟨j, by omega⟩
        have h₃ := hσ _ (mem_pigeonholeExt.2 (Or.inr (Or.inr (Or.inl ⟨i, ⟨j, by omega⟩, rfl⟩))))
        simp only [phpStepClause, Clause.eval, Literal.eval, List.any_cons, List.any_nil,
          Bool.or_false, Fin.castSucc_mk, Fin.succ_mk] at h₃
        simp_all
    have h₁ := hy n le_rfl
    have h₂ := hσ _ (mem_pigeonholeExt.2 (Or.inr (Or.inl ⟨i, rfl⟩)))
    simp only [phpStopClause, Clause.eval, Literal.eval, List.any_cons, List.any_nil,
      Bool.or_false] at h₂
    simp_all [Fin.last]
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hσ _ (mem_pigeonholeExt.2 (Or.inr (Or.inr (Or.inr ⟨i, i', j, hlt, rfl⟩))))
      simp_all [phpExtHoleClause, Clause.eval, Literal.eval]
    · have := hσ _ (mem_pigeonholeExt.2 (Or.inr (Or.inr (Or.inr ⟨i', i, j, hlt, rfl⟩))))
      simp_all [phpExtHoleClause, Clause.eval, Literal.eval]

/-- The assignment **placing** each pigeon `i` in the hole `f i`: `inl (i, j)` holds when
`f i = j`, and `inr (i, j)` when `j ≤ f i`. -/
def pigeonholeExtAssign (f : Fin m → Fin n) : PHPExtVar m n → Bool
  | .inl (i, j) => decide (f i = j)
  | .inr (i, j) => decide (j.val ≤ (f i).val)

/-- **An injective placement satisfies `EPHP^m_n`.** -/
theorem eval_pigeonholeExtAssign {f : Fin m → Fin n} (hf : Function.Injective f) :
    (pigeonholeExt m n).eval (pigeonholeExtAssign f) = true := by
  rw [eval_eq_true_iff]
  intro c hc
  rcases mem_pigeonholeExt.1 hc with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, j, rfl⟩ | ⟨i, i', j, hii', rfl⟩
  · simp [phpStartClause, Clause.eval, Literal.eval, pigeonholeExtAssign]
  · simp [phpStopClause, Clause.eval, Literal.eval, pigeonholeExtAssign, Fin.last]
  · simp only [phpStepClause, Clause.eval, Literal.eval, pigeonholeExtAssign, List.any_cons,
      List.any_nil, Bool.or_false, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff, Bool.or_eq_true,
      beq_iff_eq, decide_eq_false_iff_not, decide_eq_true_eq]
    omega
  · simp only [phpExtHoleClause, Clause.eval, Literal.eval, pigeonholeExtAssign, List.any_cons,
      List.any_nil, Bool.or_false]
    by_cases h₁ : f i = j
    · have : f i' ≠ j := fun h₂ => hii'.ne (hf (h₁.trans h₂.symm))
      simp [h₁, this]
    · simp [h₁]

/-- **`EPHP^m_n` is satisfiable exactly when there are at most as many pigeons as holes.** -/
theorem satisfiable_pigeonholeExt_iff : (pigeonholeExt m n).Satisfiable ↔ m ≤ n := by
  refine ⟨fun h => not_lt.1 fun hlt => not_satisfiable_pigeonholeExt hlt h, fun hmn => ?_⟩
  exact ⟨pigeonholeExtAssign (Fin.castLE hmn), eval_pigeonholeExtAssign (Fin.castLE_injective hmn)⟩

end CNF

end Cslib.Logic.PL
