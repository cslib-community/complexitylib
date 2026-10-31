/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.FirstOrder
public import Complexity.Logics.FirstOrder.Ordered.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Canonical ordered first-order model checking in constant depth

A sentence of `FO.Ordered.language L` is compiled into an unbounded fan-in Boolean formula
reading only the atomic facts of the relational input vocabulary `L`. The constants `0`, `1`,
and `max`, weak order, and zero-indexed `BIT` have their canonical meanings on `Fin n`, with
`n ≥ 2`. Numeric atoms are evaluated during construction: their truth tables are not additional
input bits. Constants may occur in input-relation arguments and under quantifiers.

The same formula decides the sentence for every input structure on this canonical universe.
Its depth is bounded independently of `n`, and its size and number of leaves are polynomial in
`n`, using the measures of the order-free compiler. This is the nonuniform upper-bound direction
of the FO(≤, BIT) characterization of AC⁰. No circuit-generation or DLOGTIME-uniformity bound is
asserted. Inputs are relation-table atoms, not serialized structure encodings; the bounds are in
the universe size, including when the input vocabulary has no positive-arity relation symbol.

## Main definitions

* `Cslib.Circuits.Boolean.ModelChecking.Ordered.termValue`: canonical values of ordered terms.
* `Cslib.Circuits.Boolean.ModelChecking.Ordered.toUnbounded`: compilation reading only the input
  relation tables.

## Main results

* `Cslib.Circuits.Boolean.ModelChecking.Ordered.eval_toUnbounded_atomsOf`: correctness for
  arbitrary assignments and input structures on the canonical universe.
* `Cslib.Circuits.Boolean.ModelChecking.Ordered.exists_formula_realize`: every fixed ordered
  sentence has constant-depth, polynomial-size formulas on its input relation tables.
* `Cslib.Circuits.Boolean.ModelChecking.Ordered.leafSize_toUnbounded_le`: a polynomial leaf bound
  for subsequent substitutions.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Chapter 5. The formula-expansion argument
  is in Section 5.4, proof of Theorem 5.22, in the
  [author-hosted chapter draft](https://people.cs.umass.edu/~immerman/book/ch5.pdf); this locator
  refers to that draft. Here it is specialized to a fixed sentence and proves only the
  logical-to-circuit upper bound. The canonical numeric vocabulary follows Section 1.2,
  Provisos 1.14–1.15.
* [D. A. M. Barrington, N. Immerman, H. Straubing, *On uniformity within NC¹*]
  [BarringtonImmermanStraubing1990]. Uniformity is not proved here.
-/

public section

namespace Cslib.Circuits.Boolean.ModelChecking.Ordered

open FirstOrder FirstOrder.Language
open Cslib.Logic.FO.Ordered (language)

variable {L : Language} [L.IsRelational] {n N : ℕ} [Fact (2 ≤ n)]

/-- Evaluate an ordered term without using any input relation: terms are variables or one of
the three canonical numeric constants. -/
@[expose]
def termValue {α : Type*} (v : α → Fin n) : (language L).Term α → Fin n
  | .var x => v x
  | .func (.inl f) _ => isEmptyElim f
  | .func (.inr c) _ => ⟨c.index n, c.index_lt Fact.out⟩

/-- The relation-independent term evaluator agrees with canonical ordered term semantics. -/
@[simp]
theorem termValue_eq_realize [L.Structure (Fin n)] {α : Type*} (v : α → Fin n)
    (t : (language L).Term α) : termValue v t = t.realize v := by
  cases t with
  | var x => rfl
  | func f ts =>
    cases f with
    | inl f => exact isEmptyElim f
    | inr c => cases c <;> rfl

/-- Compile an ordered formula on `Fin n`: input relations read their original atomic facts,
numeric atoms become constants, and universal quantifiers become conjunctions over the universe.
The input enumeration contains no numeric relation tables. -/
@[expose]
def toUnbounded (e : Atom L n ≃ Fin N) :
    ∀ {k}, (language L).BoundedFormula Empty k → (Fin k → Fin n) →
      Formula Unbounded.signature N
  | _, .falsum, _ => constUnbounded false
  | _, .equal t₁ t₂, xs =>
    constUnbounded (decide (termValue (Sum.elim Empty.elim xs) t₁ =
      termValue (Sum.elim Empty.elim xs) t₂))
  | _, .rel (.inl R) ts, xs =>
    .input (e ⟨⟨_, R⟩, fun i => termValue (Sum.elim Empty.elim xs) (ts i)⟩)
  | _, .rel (.inr .le) ts, xs =>
    constUnbounded (decide (termValue (Sum.elim Empty.elim xs) (ts 0) ≤
      termValue (Sum.elim Empty.elim xs) (ts 1)))
  | _, .rel (.inr .bit) ts, xs =>
    constUnbounded ((termValue (Sum.elim Empty.elim xs) (ts 0)).val.testBit
      (termValue (Sum.elim Empty.elim xs) (ts 1)).val)
  | _, .imp φ ψ, xs =>
    .gate (.or 2) ![.gate .not ![toUnbounded e φ xs], toUnbounded e ψ xs]
  | _, .all φ, xs => .gate (.and n) fun a => toUnbounded e φ (Fin.snoc xs a)

/-- Compilation decides the formula on any input structure on `Fin n`, expanded by the actual
canonical numeric constants, weak order and zero-indexed BIT. -/
theorem eval_toUnbounded_atomsOf [L.Structure (Fin n)] (e : Atom L n ≃ Fin N) {k : ℕ}
    (φ : (language L).BoundedFormula Empty k) (xs : Fin k → Fin n) :
    (toUnbounded e φ xs).eval Unbounded.interpretation
      (atomsOf (L := L) (Equiv.refl _) ∘ e.symm) = true ↔ φ.Realize Empty.elim xs := by
  classical
  induction φ with
  | falsum => simp [toUnbounded, BoundedFormula.Realize]
  | equal t₁ t₂ =>
    simp only [toUnbounded, eval_constUnbounded, decide_eq_true_iff, BoundedFormula.Realize,
      termValue_eq_realize]
  | rel R ts =>
    cases R with
    | inl R =>
      simp only [toUnbounded, Formula.eval_input, Function.comp_apply]
      refine (iff_of_eq (congrArg
        (fun a : Atom L n => atomsOf (L := L) (Equiv.refl _) a = true)
        (e.symm_apply_apply _))).trans ?_
      simp only [atomsOf, decide_eq_true_iff, BoundedFormula.Realize, termValue_eq_realize]
      rfl
    | inr R =>
      cases R <;>
        simp only [toUnbounded, eval_constUnbounded, decide_eq_true_iff, BoundedFormula.Realize,
          termValue_eq_realize] <;> rfl
  | imp φ ψ ihφ ihψ =>
    simp only [toUnbounded, Formula.eval_gate, Unbounded.interpretation_or,
      BoundedFormula.Realize, ← ihφ, ← ihψ]
    simp [Fin.exists_fin_two, imp_iff_not_or]
  | all φ ih =>
    simp only [toUnbounded, Formula.eval_gate, Unbounded.interpretation_and, decide_eq_true_iff,
      BoundedFormula.Realize]
    exact forall_congr' fun a => ih _

/-- The compiled formula's depth is bounded independently of the universe size. -/
theorem depth_toUnbounded_le (e : Atom L n ≃ Fin N) {k : ℕ}
    (φ : (language L).BoundedFormula Empty k) (xs : Fin k → Fin n) :
    (toUnbounded e φ xs).depth ≤ foDepth φ := by
  induction φ with
  | falsum => simp [toUnbounded, constUnbounded, foDepth]
  | equal t₁ t₂ =>
    simp only [toUnbounded, constUnbounded, foDepth]
    split_ifs <;> simp
  | rel R ts =>
    cases R with
    | inl R => simp [toUnbounded, foDepth]
    | inr R =>
      cases R <;> simp only [toUnbounded, constUnbounded, foDepth] <;> split_ifs <;> simp
  | imp φ ψ ihφ ihψ =>
    rw [toUnbounded, foDepth, Formula.depth_gate]
    refine (Nat.add_le_add_right (Finset.sup_le (a := max (foDepth φ) (foDepth ψ) + 1)
      fun j _ => ?_) 1).trans (by omega)
    fin_cases j
    · change (Formula.gate _ _).depth ≤ _
      rw [Formula.depth_gate]
      refine (Nat.add_le_add_right (Finset.sup_le (a := foDepth φ) fun j _ => ?_) 1).trans
        (by omega)
      fin_cases j
      exact ihφ xs
    · exact (ihψ xs).trans (by omega)
  | all φ ih =>
    simp only [toUnbounded, Formula.depth_gate, foDepth]
    exact Nat.add_le_add_right (Finset.sup_le fun a _ => ih _) 1

/-- The compiled formula's size is polynomial in the universe size for each fixed formula. -/
theorem size_toUnbounded_le (e : Atom L n ≃ Fin N) {k : ℕ}
    (φ : (language L).BoundedFormula Empty k) (xs : Fin k → Fin n) :
    (toUnbounded e φ xs).size ≤ foSize φ * (n + 2) ^ foSize φ := by
  induction φ with
  | falsum => simp [toUnbounded, constUnbounded, foSize]
  | equal t₁ t₂ =>
    simp only [toUnbounded, constUnbounded, foSize]
    split_ifs <;> simp
  | rel R ts =>
    cases R with
    | inl R => simp [toUnbounded, foSize]
    | inr R =>
      cases R <;> simp only [toUnbounded, constUnbounded, foSize] <;> split_ifs <;> simp
  | imp φ ψ ihφ ihψ =>
    have h₁ := ihφ xs
    have h₂ := ihψ xs
    simp only [toUnbounded, Formula.size_gate, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.sum_univ_one, foSize]
    have hφ : (n + 2) ^ foSize φ ≤ (n + 2) ^ (foSize φ + foSize ψ + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hψ : (n + 2) ^ foSize ψ ≤ (n + 2) ^ (foSize φ + foSize ψ + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpos : 2 ≤ (n + 2) ^ (foSize φ + foSize ψ + 1) :=
      (show 2 ≤ n + 2 by omega).trans (Nat.le_self_pow (by omega) _)
    nlinarith [Nat.mul_le_mul_left (foSize φ) hφ, Nat.mul_le_mul_left (foSize ψ) hψ]
  | all φ ih =>
    simp only [toUnbounded, Formula.size_gate, foSize]
    have hsum : ∑ a : Fin n, (toUnbounded e φ (Fin.snoc xs a)).size ≤
        n * (foSize φ * (n + 2) ^ foSize φ) :=
      (Finset.sum_le_card_nsmul _ _ _ fun a _ => ih _).trans_eq (by simp)
    have hpos : 1 ≤ (n + 2) ^ foSize φ := Nat.one_le_pow _ _ (by omega)
    have := foSize_pos φ
    calc _ ≤ n * (foSize φ * (n + 2) ^ foSize φ) + 1 := Nat.add_le_add_right hsum 1
      _ ≤ (foSize φ + 1) * (n + 2) ^ (foSize φ + 1) := by
        rw [pow_succ]
        nlinarith

/-- The number of input leaves is polynomial in the universe size. -/
theorem leafSize_toUnbounded_le (e : Atom L n ≃ Fin N) {k : ℕ}
    (φ : (language L).BoundedFormula Empty k) (xs : Fin k → Fin n) :
    (toUnbounded e φ xs).leafSize ≤ (n + 2) ^ foSize φ := by
  induction φ with
  | falsum => simp [toUnbounded, constUnbounded]
  | equal t₁ t₂ =>
    simp only [toUnbounded, constUnbounded]
    split_ifs <;> simp
  | rel R ts =>
    cases R with
    | inl R => simp [toUnbounded, foSize]
    | inr R =>
      cases R <;> simp only [toUnbounded, constUnbounded] <;> split_ifs <;> simp
  | imp φ ψ ihφ ihψ =>
    have h₁ := ihφ xs
    have h₂ := ihψ xs
    simp only [toUnbounded, Formula.leafSize_gate, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.sum_univ_one, foSize]
    have hφ : (n + 2) ^ foSize φ ≤ (n + 2) ^ (foSize φ + foSize ψ) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hψ : (n + 2) ^ foSize ψ ≤ (n + 2) ^ (foSize φ + foSize ψ) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_succ]
    nlinarith
  | all φ ih =>
    simp only [toUnbounded, Formula.leafSize_gate, foSize]
    have hsum : ∑ a : Fin n, (toUnbounded e φ (Fin.snoc xs a)).leafSize ≤
        n * (n + 2) ^ foSize φ :=
      (Finset.sum_le_card_nsmul _ _ _ fun a _ => ih _).trans_eq (by simp)
    refine hsum.trans ?_
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ (by omega)

/-- For each universe size at least two, one constant-depth, polynomial-size formula decides
the ordered sentence on every interpretation of the input relations. Only the original input
relation tables are inputs; the canonical numeric symbols are fixed by the universe size. -/
theorem exists_formula_realize (φ : (language L).Sentence) (e : Atom L n ≃ Fin N) :
    ∃ F : Formula Unbounded.signature N,
      (∀ s : L.Structure (Fin n), letI := s;
        F.eval Unbounded.interpretation (atomsOf (L := L) (Equiv.refl _) ∘ e.symm) = true ↔
          Fin n ⊨ φ) ∧
      F.depth ≤ foDepth φ ∧ F.size ≤ foSize φ * (n + 2) ^ foSize φ := by
  refine ⟨toUnbounded e φ Fin.elim0, fun s => ?_,
    depth_toUnbounded_le e φ _, size_toUnbounded_le e φ _⟩
  let := s
  exact (eval_toUnbounded_atomsOf e φ Fin.elim0).trans (by
    rw [Sentence.Realize, Formula.Realize,
      Subsingleton.elim (Empty.elim : Empty → Fin n) default,
      Subsingleton.elim (Fin.elim0 : Fin 0 → Fin n) default])

end Cslib.Circuits.Boolean.ModelChecking.Ordered
