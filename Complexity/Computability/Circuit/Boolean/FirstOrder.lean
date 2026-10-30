/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Unbounded
public import Complexity.Computability.Circuit.Formula
public import Complexity.Logics.FirstOrder.Interpretation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# First-order model checking in constant depth

A structure for a relational first-order language `L` on the universe `Fin n` is determined by the
truth values of its atomic facts `R(a₁, …, aₗ)` (`ModelChecking.Atom`, `ModelChecking.Model`), and
every structure with `n` elements is isomorphic to one of these through an enumeration
(`ModelChecking.realize_iff_atomsOf`). Expanding each universal quantifier into a conjunction over
the `n` elements turns a first-order formula into a formula of negations and unbounded fan-in
conjunctions and disjunctions over the atomic facts (`ModelChecking.toUnbounded`), which computes
whether the structure satisfies it (`ModelChecking.eval_toUnbounded`). Its depth is bounded
independently of `n` (`ModelChecking.depth_toUnbounded_le`) and its size is polynomial in `n`
(`ModelChecking.size_toUnbounded_le`). This is the easy, nonuniform half of the characterization
of AC⁰ by first-order logic [Immerman, Chapter 5][Immerman1999],
[Barrington, Immerman and Straubing][BarringtonImmermanStraubing1990], for relational vocabularies
and without numerical predicates such as order or `BIT`; it reads as membership in AC⁰ once the
atomic facts are the input bits, which needs a relation symbol of positive arity for the number of
facts to grow with `n`.

Sentences are those of Mathlib's model theory (`FirstOrder.Language.Sentence`), and the statements
are about structures rather than an encoding of structures as bit strings.
The canonical ordered extension, including genuine `0`, `1`, and `max` constants and hardwired
`≤` and `BIT`, is in `Complexity.Computability.Circuit.Boolean.FirstOrder.Ordered`.

## Main definitions

* `Cslib.Circuits.Boolean.ModelChecking.Atom`: the atomic facts of a structure on `Fin n`.
* `Cslib.Circuits.Boolean.ModelChecking.Model`,
  `Cslib.Circuits.Boolean.ModelChecking.atomsOf`: the structure with given true atomic facts, and
  the atomic facts of an arbitrary finite structure through an enumeration.
* `Cslib.Circuits.Boolean.ModelChecking.constUnbounded`,
  `Cslib.Circuits.Boolean.ModelChecking.toUnbounded`: a Boolean constant and a first-order formula
  as formulas over the unbounded fan-in basis.
* `Cslib.Circuits.Boolean.ModelChecking.foDepth`,
  `Cslib.Circuits.Boolean.ModelChecking.foSize`: depth and node count of a first-order formula.

## Main results

* `Cslib.Circuits.Boolean.ModelChecking.exists_formula_realize_structure`: every first-order
  sentence is decided on the structures with `n` elements by unbounded fan-in formulas of constant
  depth and polynomial size.
* `Cslib.Circuits.Boolean.ModelChecking.leafSize_toUnbounded_le`: the formulas have polynomially
  many leaves.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [D. A. M. Barrington, N. Immerman, H. Straubing, *On uniformity within NC¹*]
  [BarringtonImmermanStraubing1990]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.ModelChecking

open FirstOrder FirstOrder.Language
open Cslib.Logic.FO (termVar realize_termVar)

variable {L : Language} [L.IsRelational] {n N : ℕ}

/-- The atomic facts of a structure for `L` on `Fin n`: a relation symbol and a tuple of
elements. -/
def Atom (L : Language) (n : ℕ) : Type _ :=
  Σ R : Σ l, L.Relations l, Fin R.1 → Fin n

/-- The universe `Fin n` with the structure whose true atomic facts are those given by `x`. -/
@[nolint unusedArguments]
def Model (_x : Atom L n → Bool) : Type :=
  Fin n

/-- The first-order `L.Structure` on `Model x` whose relations are given by the truth table `x`. -/
instance (x : Atom L n → Bool) : L.Structure (Model x) where
  funMap f := isEmptyElim f
  RelMap {l} R t := x ⟨⟨l, R⟩, t⟩ = true

/-- There are finitely many atomic facts on `Fin n` when `L` has finitely many relation symbols. -/
instance [Fintype (Σ l, L.Relations l)] : Fintype (Atom L n) :=
  inferInstanceAs (Fintype (Σ R : Σ l, L.Relations l, Fin R.1 → Fin n))

/-- The constant `b` as a formula over the unbounded fan-in basis. -/
def constUnbounded (b : Bool) : Formula Unbounded.signature N :=
  if b then .gate (.and 0) Fin.elim0 else .gate (.or 0) Fin.elim0

/-- `constUnbounded b` evaluates to `b` on every input. -/
@[simp] theorem eval_constUnbounded (b : Bool) (y : Fin N → Bool) :
    (constUnbounded b).eval Unbounded.interpretation y = b := by
  cases b <;> simp [constUnbounded]

/-- A first-order formula, with values `xs` for its bound variables, as a formula over the
unbounded fan-in basis reading the atomic facts through `e`: atomic formulas are inputs or
constants, an implication is a disjunction with one negated argument, and a universal quantifier
is a conjunction over the `n` elements. A term of the relational language `L` is a variable
(`Cslib.Logic.FO.termVar`), here a bound one, with value given by `xs`. -/
def toUnbounded (e : Atom L n ≃ Fin N) :
    ∀ {k}, L.BoundedFormula Empty k → (Fin k → Fin n) → Formula Unbounded.signature N
  | _, .falsum, _ => constUnbounded false
  | _, .equal t₁ t₂, xs =>
    constUnbounded (decide (Sum.elim Empty.elim xs (termVar t₁) =
      Sum.elim Empty.elim xs (termVar t₂)))
  | _, .rel R ts, xs => .input (e ⟨⟨_, R⟩, fun i => Sum.elim Empty.elim xs (termVar (ts i))⟩)
  | _, .imp φ ψ, xs =>
    .gate (.or 2) ![.gate .not ![toUnbounded e φ xs], toUnbounded e ψ xs]
  | _, .all φ, xs => .gate (.and n) fun a => toUnbounded e φ (Fin.snoc xs a)

/-- **The formula decides the first-order formula** on the structure given by its atomic facts. -/
theorem eval_toUnbounded (e : Atom L n ≃ Fin N) (x : Atom L n → Bool) {k : ℕ}
    (φ : L.BoundedFormula Empty k) (xs : Fin k → Model x) :
    (toUnbounded e φ xs).eval Unbounded.interpretation (x ∘ e.symm) = true ↔
      φ.Realize Empty.elim xs := by
  induction φ with
  | falsum => simp [toUnbounded, BoundedFormula.Realize]
  | equal t₁ t₂ =>
    simp only [toUnbounded, eval_constUnbounded, decide_eq_true_iff, BoundedFormula.Realize,
      realize_termVar]
    exact Iff.rfl
  | rel R ts =>
    simp only [toUnbounded, Formula.eval_input, Function.comp_apply, BoundedFormula.Realize,
      realize_termVar]
    exact iff_of_eq (congrArg (fun a => x a = true) (e.symm_apply_apply _))
  | imp φ ψ ihφ ihψ =>
    simp only [toUnbounded, Formula.eval_gate, Unbounded.interpretation_or,
      BoundedFormula.Realize, ← ihφ, ← ihψ]
    simp [Fin.exists_fin_two, imp_iff_not_or]
  | all φ ih =>
    simp only [toUnbounded, Formula.eval_gate, Unbounded.interpretation_and, decide_eq_true_iff,
      BoundedFormula.Realize]
    exact forall_congr' fun a => ih _

/-- A measure of the depth of a first-order formula: atomic formulas count one, an implication two
more than its arguments, and a quantifier one more than its body. -/
def foDepth : ∀ {k}, L.BoundedFormula Empty k → ℕ
  | _, .falsum => 1
  | _, .equal _ _ => 1
  | _, .rel _ _ => 1
  | _, .imp φ ψ => max (foDepth φ) (foDepth ψ) + 2
  | _, .all φ => foDepth φ + 1

/-- The number of nodes of a first-order formula. -/
def foSize : ∀ {k}, L.BoundedFormula Empty k → ℕ
  | _, .falsum => 1
  | _, .equal _ _ => 1
  | _, .rel _ _ => 1
  | _, .imp φ ψ => foSize φ + foSize ψ + 1
  | _, .all φ => foSize φ + 1

omit [L.IsRelational] in
/-- Every first-order formula has positive node count. -/
theorem foSize_pos {k : ℕ} (φ : L.BoundedFormula Empty k) : 0 < foSize φ := by
  cases φ <;> simp [foSize]

/-- **The depth does not depend on the universe.** -/
theorem depth_toUnbounded_le (e : Atom L n ≃ Fin N) {k : ℕ} (φ : L.BoundedFormula Empty k)
    (xs : Fin k → Fin n) : (toUnbounded e φ xs).depth ≤ foDepth φ := by
  induction φ with
  | falsum => simp [toUnbounded, constUnbounded, foDepth]
  | equal t₁ t₂ => simp only [toUnbounded, constUnbounded, foDepth]; split_ifs <;> simp
  | rel R ts => simp [toUnbounded, foDepth]
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

/-- **The size is polynomial in the universe.** -/
theorem size_toUnbounded_le (e : Atom L n ≃ Fin N) {k : ℕ} (φ : L.BoundedFormula Empty k)
    (xs : Fin k → Fin n) : (toUnbounded e φ xs).size ≤ foSize φ * (n + 2) ^ foSize φ := by
  induction φ with
  | falsum => simp [toUnbounded, constUnbounded, foSize]
  | equal t₁ t₂ =>
    simp only [toUnbounded, constUnbounded, foSize]
    split_ifs <;> simp
  | rel R ts => simp [toUnbounded, foSize]
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

/-- **The number of leaves is polynomial in the universe.** -/
theorem leafSize_toUnbounded_le (e : Atom L n ≃ Fin N) {k : ℕ} (φ : L.BoundedFormula Empty k)
    (xs : Fin k → Fin n) : (toUnbounded e φ xs).leafSize ≤ (n + 2) ^ foSize φ := by
  induction φ with
  | falsum => simp [toUnbounded, constUnbounded]
  | equal t₁ t₂ =>
    simp only [toUnbounded, constUnbounded]
    split_ifs <;> simp
  | rel R ts => simp [toUnbounded, foSize]
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

/-! ### Arbitrary finite structures -/

section Structures

variable {M : Type*} [L.Structure M]

open Classical in
/-- The atomic facts of a structure on `M`, read through an enumeration `e` of `M` by `Fin n`. -/
noncomputable def atomsOf (e : M ≃ Fin n) : Atom L n → Bool :=
  fun a => decide (Structure.RelMap a.1.2 (e.symm ∘ a.2))

/-- An enumeration of `M` is an isomorphism onto the structure with the atomic facts of `M`. -/
private def equivModel (e : M ≃ Fin n) : M ≃[L] Model (atomsOf (L := L) e) where
  toEquiv := e
  map_fun' f := isEmptyElim f
  map_rel' R t := by
    change atomsOf e ⟨⟨_, R⟩, e ∘ t⟩ = true ↔ Structure.RelMap R t
    simp [atomsOf, Function.comp_def]

/-- A structure satisfies a sentence exactly when the structure with its atomic facts does. -/
theorem realize_iff_atomsOf (e : M ≃ Fin n) (φ : L.Sentence) :
    M ⊨ φ ↔ Model (atomsOf (L := L) e) ⊨ φ :=
  StrongHomClass.realize_sentence (equivModel e) φ

/-- The translation of a sentence decides it on every structure, through its atomic facts. -/
theorem eval_toUnbounded_atomsOf (e : Atom L n ≃ Fin N) (eM : M ≃ Fin n) (φ : L.Sentence) :
    (toUnbounded e φ Fin.elim0).eval Unbounded.interpretation (atomsOf (L := L) eM ∘ e.symm) =
      true ↔ M ⊨ φ :=
  ((eval_toUnbounded e _ φ Fin.elim0).trans (by
      rw [Sentence.Realize, Formula.Realize,
        Subsingleton.elim (Empty.elim : Empty → Model (atomsOf (L := L) eM)) default,
        Subsingleton.elim (Fin.elim0 : Fin 0 → Model (atomsOf (L := L) eM)) default])).trans
    (realize_iff_atomsOf eM φ).symm

end Structures

/-- **First-order sentences are decided in constant depth**: for a relational language, every
sentence is decided on the structures with `n` elements, given by their atomic facts, by a formula
of negations and unbounded fan-in conjunctions and disjunctions whose depth does not depend on `n`
and whose size is polynomial in `n`. -/
theorem exists_formula_realize (φ : L.Sentence) (e : Atom L n ≃ Fin N) :
    ∃ F : Formula Unbounded.signature N,
      (∀ x : Atom L n → Bool, F.eval Unbounded.interpretation (x ∘ e.symm) = true ↔
        Model x ⊨ φ) ∧
      F.depth ≤ foDepth φ ∧ F.size ≤ foSize φ * (n + 2) ^ foSize φ :=
  ⟨toUnbounded e φ Fin.elim0, fun x => (eval_toUnbounded e x φ Fin.elim0).trans (by
      rw [Sentence.Realize, Formula.Realize,
        Subsingleton.elim (Empty.elim : Empty → Model x) default,
        Subsingleton.elim (Fin.elim0 : Fin 0 → Model x) default]),
    depth_toUnbounded_le e φ _, size_toUnbounded_le e φ _⟩

/-- The same formula decides the sentence on every structure with `n` elements, through any
enumeration of it. -/
theorem exists_formula_realize_structure (φ : L.Sentence) (e : Atom L n ≃ Fin N) :
    ∃ F : Formula Unbounded.signature N,
      (∀ (M : Type) [L.Structure M] (eM : M ≃ Fin n),
        F.eval Unbounded.interpretation (atomsOf (L := L) eM ∘ e.symm) = true ↔ M ⊨ φ) ∧
      F.depth ≤ foDepth φ ∧ F.size ≤ foSize φ * (n + 2) ^ foSize φ := by
  obtain ⟨F, hF, hd, hs⟩ := exists_formula_realize φ e
  exact ⟨F, fun M _ eM => (hF _).trans (realize_iff_atomsOf eM φ).symm, hd, hs⟩

end Cslib.Circuits.Boolean.ModelChecking
