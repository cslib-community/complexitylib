/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
import Complexity.Foundations.Data.List.Filter

/-!
# Splitting clauses into clauses of width three

A clause `l₁ ∨ l₂ ∨ ⋯ ∨ lₘ` with `m > 3` is equisatisfiable with the chain of width-three clauses

`(l₁ ∨ l₂ ∨ y₀) ∧ (¬y₀ ∨ l₃ ∨ y₁) ∧ ⋯ ∧ (¬yₘ₋₄ ∨ lₘ₋₁ ∨ lₘ)`

in fresh variables `y₀, …, yₘ₋₄`: in a satisfying assignment `yⱼ` can be taken to say that one of
the literals after `lⱼ₊₂` is true [Arora and Barak, Section 2.3.1][AroraBarak09]. Splitting every
clause of a formula, with the fresh variables of a clause indexed by its position, gives a formula
with clauses of width at most three that is satisfiable exactly when the original one is.

## Main definitions

* `Cslib.Logic.PL.Clause.splitAux`, `Cslib.Logic.PL.Clause.split3`: the chain of width-three
  clauses for one clause.
* `Cslib.Logic.PL.CNF.to3CNF`: every clause split, over the variables `V ⊕ (ℕ × ℕ)`.

## Main results

* `Cslib.Logic.PL.CNF.length_le_three_of_mem_to3CNF`: every clause has at most three literals.
* `Cslib.Logic.PL.CNF.satisfiable_to3CNF`: splitting preserves satisfiability.
* `Cslib.Logic.PL.CNF.length_to3CNF`,
  `Cslib.Logic.PL.CNF.countUnsat_comp_inl_le_countUnsat_to3CNF`: splitting replaces a clause of
  width `w ≥ 3` by `w - 2` clauses and keeps every falsified clause falsified.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V W : Type*}

/-! ### One clause -/

/-- The chain of width-three clauses for the clause `carry :: rest`, with auxiliary variables
`fresh j, fresh (j + 1), …`. -/
def Clause.splitAux (fresh : ℕ → W) : ℕ → Literal W → Clause W → CNF W
  | j, carry, b :: c :: d :: rest =>
    [carry, b, (fresh j, true)] :: Clause.splitAux fresh (j + 1) (fresh j, false) (c :: d :: rest)
  | _, carry, rest => [carry :: rest]

/-- The chain of width-three clauses for a clause, with auxiliary variables `fresh j,
fresh (j + 1), …`. A clause with at most three literals is kept as it is. -/
def Clause.split3 (fresh : ℕ → W) (j : ℕ) : Clause W → CNF W
  | [] => [[]]
  | carry :: rest => Clause.splitAux fresh j carry rest

private theorem Clause.length_le_three_of_mem_splitAux (fresh : ℕ → W) (j : ℕ) (carry : Literal W)
    (rest : Clause W) : ∀ d ∈ Clause.splitAux fresh j carry rest, d.length ≤ 3 := by
  induction j, carry, rest using Clause.splitAux.induct fresh with
  | case1 j carry b c d rest ih =>
    intro e he
    rw [Clause.splitAux, List.mem_cons] at he
    rcases he with rfl | he
    · simp
    · exact ih e he
  | case2 j carry rest hrest =>
    intro e he
    rw [Clause.splitAux] at he
    · simp only [List.mem_singleton] at he
      subst he
      match rest, hrest with
      | [], _ | [_], _ | [_, _], _ => simp
      | _ :: _ :: _ :: _, hrest => exact absurd rfl (hrest _ _ _ _)
    · exact hrest

/-- Resolving on the auxiliary variables: an assignment satisfying the chain satisfies the
clause. -/
private theorem Clause.eval_of_eval_splitAux (fresh : ℕ → W) (σ : W → Bool) (j : ℕ)
    (carry : Literal W) (rest : Clause W) (h : (Clause.splitAux fresh j carry rest).eval σ = true) :
    Clause.eval σ (carry :: rest) = true := by
  induction j, carry, rest using Clause.splitAux.induct fresh with
  | case1 j carry b c d rest ih =>
    rw [Clause.splitAux, CNF.eval_cons, Bool.and_eq_true] at h
    have h₂ := ih h.2
    have h₁ := h.1
    simp only [Clause.eval_cons, Literal.eval, Clause.eval_nil, Bool.or_false, Bool.or_eq_true,
      beq_iff_eq] at h₁ h₂ ⊢
    cases hf : σ (fresh j)
    · simp only [hf, Bool.false_eq_true, or_false] at h₁
      tauto
    · simp only [hf, Bool.true_eq_false, false_or] at h₂
      tauto
  | case2 j carry rest hrest =>
    rw [Clause.splitAux] at h
    · simpa using h
    · exact hrest

/-- An assignment satisfying the clause, and giving each auxiliary variable `fresh k` the value of
the literals after its position, satisfies the chain. -/
private theorem Clause.eval_splitAux (fresh : ℕ → W) (σ : W → Bool) (j : ℕ) (carry : Literal W)
    (rest : Clause W) (hfresh : ∀ k, j ≤ k → σ (fresh k) = Clause.eval σ (rest.drop (k - j + 1)))
    (h : Clause.eval σ (carry :: rest) = true) :
    (Clause.splitAux fresh j carry rest).eval σ = true := by
  induction j, carry, rest using Clause.splitAux.induct fresh with
  | case1 j carry b c d rest ih =>
    have hj : σ (fresh j) = Clause.eval σ (c :: d :: rest) := by
      simpa using hfresh j (Nat.le_refl j)
    rw [Clause.splitAux, CNF.eval_cons, Bool.and_eq_true]
    refine ⟨?_, ih (fun k hk => ?_) ?_⟩
    · simp only [Clause.eval_cons, Literal.eval, Clause.eval_nil, Bool.or_false, beq_true,
        hj] at h ⊢
      simpa [Bool.or_assoc] using h
    · rw [hfresh k (by omega), show k - j + 1 = (k - (j + 1) + 1) + 1 by omega,
        List.drop_succ_cons]
    · rw [Clause.eval_cons]
      cases hc : Clause.eval σ (c :: d :: rest)
      · simp [Literal.eval, hj, hc]
      · simp
  | case2 j carry rest hrest =>
    rw [Clause.splitAux]
    · simpa using h
    · exact hrest

/-! ### Formulas -/

/-- Split every clause of a formula, renaming its variables into the left summand and naming the
auxiliary variables of clause `i` by `(i, j)`. -/
def CNF.to3CNF (φ : CNF V) : CNF (V ⊕ (ℕ × ℕ)) :=
  φ.zipIdx.flatMap fun x =>
    Clause.split3 (fun j => Sum.inr (x.2, j)) 0 (x.1.relabel Sum.inl)

/-- Every clause in `Clause.split3 fresh j c` has at most three literals. -/
theorem Clause.length_le_three_of_mem_split3 (fresh : ℕ → W) (j : ℕ) (c : Clause W) :
    ∀ d ∈ Clause.split3 fresh j c, d.length ≤ 3 := by
  cases c with
  | nil => simp [Clause.split3]
  | cons carry rest => exact Clause.length_le_three_of_mem_splitAux fresh j carry rest

/-- Every clause of `CNF.to3CNF φ` has at most three literals. -/
theorem CNF.length_le_three_of_mem_to3CNF {φ : CNF V} {c : Clause (V ⊕ (ℕ × ℕ))}
    (hc : c ∈ φ.to3CNF) : c.length ≤ 3 := by
  obtain ⟨x, -, hc⟩ := List.mem_flatMap.1 hc
  exact Clause.length_le_three_of_mem_split3 _ _ _ c hc

/-- Any assignment satisfying `Clause.split3 fresh j c` satisfies `c`. -/
theorem Clause.eval_of_eval_split3 (fresh : ℕ → W) (σ : W → Bool) (j : ℕ) (c : Clause W)
    (h : (Clause.split3 fresh j c).eval σ = true) : c.eval σ = true := by
  cases c with
  | nil => simp [Clause.split3] at h
  | cons carry rest => exact Clause.eval_of_eval_splitAux fresh σ j carry rest h

private theorem Clause.relabel_drop (f : V → W) (c : Clause V) (n : ℕ) :
    (c.relabel f).drop n = Clause.relabel f (c.drop n) :=
  (List.map_drop ..).symm

/-- Splitting the clauses of a formula preserves satisfiability. -/
theorem CNF.satisfiable_to3CNF (φ : CNF V) : φ.to3CNF.Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨τ ∘ Sum.inl, (CNF.eval_eq_true_iff _ _).2 fun c hc => ?_⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem.1 hc
    have hmem : (c, i) ∈ φ.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]; simp [← hi.2]
    have := (CNF.eval_flatMap_eq_true_iff τ _ _).1 hτ _ hmem
    simpa using Clause.eval_of_eval_split3 _ _ _ _ this
  · rintro ⟨σ, hσ⟩
    let τ : V ⊕ (ℕ × ℕ) → Bool
      | .inl v => σ v
      | .inr (i, k) => Clause.eval σ ((φ.getD i []).drop (k + 2))
    refine ⟨τ, (CNF.eval_flatMap_eq_true_iff τ _ _).2 fun x hx => ?_⟩
    obtain ⟨c, i⟩ := x
    have hci : φ.getD i [] = c := by
      rw [List.mem_zipIdx_iff_getElem?] at hx
      simp [List.getD_eq_getElem?_getD, hx]
    have hmem : c ∈ φ := by
      rw [List.mem_zipIdx_iff_getElem?] at hx
      exact List.mem_of_getElem? (by simpa using hx)
    have hc : c.eval σ = true := (CNF.eval_eq_true_iff _ _).1 hσ c hmem
    cases c with
    | nil => simp at hc
    | cons carry rest =>
      refine Clause.eval_splitAux (rest := Clause.relabel Sum.inl rest) _ τ 0 _ (fun k _ => ?_) ?_
      · rw [Clause.relabel_drop, Clause.eval_relabel]
        simp only [τ, hci, Nat.sub_zero]
        rfl
      · change (Clause.relabel Sum.inl (carry :: rest)).eval τ = true
        rw [Clause.eval_relabel]
        exact hc

/-- The chain for a clause `carry :: rest` has `rest.length - 1` clauses, and at least one. -/
private theorem Clause.length_splitAux (fresh : ℕ → W) (j : ℕ) (carry : Literal W)
    (rest : Clause W) :
    (Clause.splitAux fresh j carry rest).length = max 1 (rest.length - 1) := by
  induction j, carry, rest using Clause.splitAux.induct fresh with
  | case1 j carry b c d rest ih =>
    rw [Clause.splitAux, List.length_cons, ih]
    simp only [List.length_cons]
    omega
  | case2 j carry rest hrest =>
    rw [Clause.splitAux]
    · match rest, hrest with
      | [], _ | [_], _ | [_, _], _ => simp
      | _ :: _ :: _ :: _, hrest => exact absurd rfl (hrest _ _ _ _)
    · exact hrest

/-- Splitting a clause of width `w` gives `w - 2` clauses, and at least one. -/
theorem Clause.length_split3 (fresh : ℕ → W) (j : ℕ) (c : Clause W) :
    (Clause.split3 fresh j c).length = max 1 (c.length - 2) := by
  cases c with
  | nil => rfl
  | cons carry rest =>
    rw [Clause.split3, Clause.length_splitAux, List.length_cons]
    rfl

/-- The number of clauses after splitting. -/
theorem CNF.length_to3CNF (φ : CNF V) :
    φ.to3CNF.length = (φ.map fun c => max 1 (c.length - 2)).sum := by
  rw [CNF.to3CNF, List.length_flatMap]
  conv_rhs => rw [← List.zipIdx_map_fst 0 φ, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  rw [Clause.length_split3, Function.comp_apply, Clause.length_relabel]

/-- **Splitting keeps falsified clauses falsified**: an assignment of the split formula falsifies
at least as many clauses as its restriction to the original variables falsifies in the original
formula. -/
theorem CNF.countUnsat_comp_inl_le_countUnsat_to3CNF (φ : CNF V) (τ : V ⊕ (ℕ × ℕ) → Bool) :
    φ.countUnsat (τ ∘ Sum.inl) ≤ φ.to3CNF.countUnsat τ := by
  have hφ : φ.countUnsat (τ ∘ Sum.inl) =
      φ.zipIdx.countP fun x => !x.1.eval (τ ∘ Sum.inl) := by
    rw [CNF.countUnsat]
    conv_lhs => rw [← List.zipIdx_map_fst 0 φ]
    rw [List.countP_map]
    rfl
  rw [hφ, CNF.countUnsat, CNF.to3CNF, List.countP_flatMap]
  refine List.countP_le_sum_map fun x _ hx => Nat.one_le_iff_ne_zero.2 fun h0 => ?_
  have h := Clause.eval_of_eval_split3 _ τ 0 _
    (CNF.countUnsat_eq_zero_iff.1 (show CNF.countUnsat τ _ = 0 from h0))
  rw [Clause.eval_relabel] at h
  simp [h] at hx

end Cslib.Logic.PL
