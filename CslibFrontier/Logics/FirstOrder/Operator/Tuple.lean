/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Operator.Quantifiers
public import Mathlib.Logic.Equiv.Fin.Basic
import CslibFrontier.Tactic.FirstOrder.Simp

/-!
# Shared syntax for pulling operator formulas back to tuples

A full-tuple interpretation represents each target element by `d` source elements. Pulling an
operator formula back along it replaces each target variable by `d` coordinates and each
relation argument by a block of `d` coordinates. This module holds the operator-independent part
of that translation: named term values, existential coordinate blocks, scaled relation
variables, and the block bijection between flattened tuples and target tuples. The
least-fixed-point and transitive-closure pullbacks build on it.

## Main definitions

* `Operator.RelVar.scale`: multiply the arity of every relation variable by `d`.
* `Operator.Tuple.FOMap`: an ordinary first-order tuple pullback.
* `Operator.Tuple.termGraph`, `Operator.Tuple.applyTerms`: name target term values by fresh
  coordinates.
* `Operator.Tuple.exBlock`: bind the `d` coordinates of a newly quantified target variable.
* `Operator.Tuple.blockEquiv`: read a flattened tuple of `k` coordinate blocks as `k` targets.

## Main results

* `Operator.Tuple.realize_applyTerms`: the named coordinates have a unique witness.
* `Operator.Tuple.realize_applyTerms_rel`: pulled-back relation atoms read the related tuple.
* `Operator.Tuple.realize_exBlock`: a coordinate block quantifies over the target universe.
-/

public section

universe u v w z s

open FirstOrder Language

namespace Cslib.Logic.FO.Operator

/-- Replace each argument of a scoped relation variable by `d` coordinates. -/
@[expose] def RelVar.scale (d : ℕ) : {Γ : List ℕ} → {k : ℕ} →
    RelVar Γ k → RelVar (Γ.map (· * d)) (k * d)
  | _, _, .here => .here
  | _, _, .there r => .there (r.scale d)

namespace Tuple

variable {L L' : Language} {O : Type s} {shape : O → Shape} {d : ℕ}

/-- The ordinary first-order part of a full-tuple syntax translation. -/
abbrev FOMap (L L' : Language) (d : ℕ) :=
  {α : Type} → L'.Formula α → L.Formula (α × Fin d)

/-- Distribute coordinates over old and newly bound variables, flattening the latter. -/
@[expose] def scopeMap {α : Type w} {k : ℕ} :
    (α ⊕ Fin k) × Fin d → (α × Fin d) ⊕ Fin (k * d)
  | (.inl a, i) => .inl (a, i)
  | (.inr j, i) => .inr (finProdFinEquiv (j, i))

/-- Translate the graph of a tuple of terms, using fresh coordinates for their values. -/
@[expose] noncomputable def termGraph (f : FOMap L L' d) {α : Type} {k : ℕ}
    (args : Fin k → L'.Term α) : L.Formula ((α × Fin d) ⊕ Fin (k * d)) :=
  (f (FirstOrder.Language.Formula.iInf fun i : Fin k =>
    (Term.var (Sum.inr i)).equal ((args i).relabel Sum.inl))).relabel scopeMap

/-- Apply a formula with fresh coordinate arguments to translated target terms. -/
@[expose] noncomputable def applyTerms (f : FOMap L L' d) {Γ : List ℕ} {α : Type}
    {k : ℕ} (args : Fin k → L'.Term α)
    (φ : Formula L shape Γ ((α × Fin d) ⊕ Fin (k * d))) :
    Formula L shape Γ (α × Fin d) :=
  (Formula.conj (.ofFO (termGraph f args)) φ).exs (k * d)

/-- Bind the `d` coordinates of a newly quantified target variable. -/
@[expose] def exBlock {Γ : List ℕ} {α : Type w}
    (φ : Formula L shape Γ (Option α × Fin d)) : Formula L shape Γ (α × Fin d) :=
  (φ.relabel fun p => match p.1 with
    | none => .inr p.2
    | some a => .inl (a, p.2)).exs d

variable {Γ : List ℕ} {α : Type}

/-- Naming term values does not change dependence on scoped relations. -/
@[simp] theorem checkPolarity_applyTerms (variance : Variances shape) (f : FOMap L L' d)
    {k : ℕ} (args : Fin k → L'.Term α) (φ : Formula L shape Γ ((α × Fin d) ⊕ Fin (k * d)))
    (sign : Bool) (mark : Marking Γ) :
    (applyTerms f args φ).checkPolarity variance sign mark =
      φ.checkPolarity variance sign mark := by
  simp [applyTerms, Formula.checkPolarity]

/-- Naming term values does not change formation conditions. -/
@[simp] theorem wellFormed_applyTerms (policy : Policy shape) (f : FOMap L L' d) {k : ℕ}
    (args : Fin k → L'.Term α) (φ : Formula L shape Γ ((α × Fin d) ⊕ Fin (k * d))) :
    (applyTerms f args φ).wellFormed policy = φ.wellFormed policy := by
  simp [applyTerms, Formula.wellFormed]

/-- Binding a coordinate block does not change dependence on scoped relations. -/
@[simp] theorem checkPolarity_exBlock {β : Type w} (variance : Variances shape)
    (φ : Formula L shape Γ (Option β × Fin d)) (sign : Bool) (mark : Marking Γ) :
    (exBlock φ).checkPolarity variance sign mark = φ.checkPolarity variance sign mark := by
  simp only [exBlock, Formula.checkPolarity_exs, Formula.checkPolarity_relabel]

/-- Binding a coordinate block does not change formation conditions. -/
@[simp] theorem wellFormed_exBlock {β : Type w} (policy : Policy shape)
    (φ : Formula L shape Γ (Option β × Fin d)) :
    (exBlock φ).wellFormed policy = φ.wellFormed policy := by
  simp only [exBlock, Formula.wellFormed_exs, Formula.wellFormed_relabel]

/-- Apply an element bijection independently to the blocks of a flattened relation tuple. -/
@[expose] def blockEquiv {M N : Type*} (e : (Fin d → M) ≃ N) (k : ℕ) :
    (Fin (k * d) → M) ≃ (Fin k → N) where
  toFun xs i := e (fun j => xs (finProdFinEquiv (i, j)))
  invFun ys p := e.symm (ys (finProdFinEquiv.symm p).1) (finProdFinEquiv.symm p).2
  left_inv xs := by
    funext p
    simp only [Equiv.symm_apply_apply, Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv ys := by
    funext i
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- Each target of `blockEquiv` is the image of one coordinate block. -/
theorem blockEquiv_apply {M N : Type*} (e : (Fin d → M) ≃ N) {k : ℕ}
    (xs : Fin (k * d) → M) (i : Fin k) :
    blockEquiv e k xs i = e (fun j => xs (finProdFinEquiv (i, j))) := rfl

variable {M N : Type} [L.Structure M] [L'.Structure N]
  (f : FOMap L L' d) (e : (Fin d → M) ≃ N)
  (hf : ∀ {α : Type} (φ : L'.Formula α) (v : α × Fin d → M),
    (f φ).Realize v ↔ φ.Realize (fun a => e (fun i => v (a, i))))

include hf in
/-- The translated term graph identifies precisely the encoded values of its arguments. -/
theorem realize_termGraph {k : ℕ} (args : Fin k → L'.Term α)
    (v : α × Fin d → M) (xs : Fin (k * d) → M) :
    (termGraph f args).Realize (Sum.elim v xs) ↔
      ∀ i, blockEquiv e k xs i = (args i).realize (fun a => e (fun j => v (a, j))) := by
  rw [termGraph, FirstOrder.Language.Formula.realize_relabel, hf,
    FirstOrder.Language.Formula.realize_iInf]
  apply forall_congr'
  intro i
  fo_simp
  rfl

include hf in
/-- Existential term naming has a unique coordinate witness, even for constants and nullary
argument tuples. -/
theorem realize_applyTerms (I : Interpretation shape M) {k : ℕ}
    (args : Fin k → L'.Term α) (φ : Formula L shape Γ ((α × Fin d) ⊕ Fin (k * d)))
    (ρ : RelEnv Γ M) (v : α × Fin d → M) :
    (applyTerms f args φ).Realize I ρ v ↔
      φ.Realize I ρ (Sum.elim v ((blockEquiv e k).symm
        (fun i => (args i).realize (fun a => e (fun j => v (a, j)))))) := by
  fo_simp [applyTerms, realize_termGraph f e hf]
  constructor
  · rintro ⟨xs, hx, hφ⟩
    have heq := congrArg (blockEquiv e k).symm (funext hx)
    rw [Equiv.symm_apply_apply] at heq
    exact heq ▸ hφ
  · intro hφ
    exact ⟨_, fun i => congrFun ((blockEquiv e k).apply_symm_apply _) i, hφ⟩

include hf in
/-- A pulled-back relation atom holds exactly when the related target valuation contains the
evaluated target arguments. -/
theorem realize_applyTerms_rel {O' : Type s} {shape' : O' → Shape}
    (I : Interpretation shape M) (I' : Interpretation shape' N) {k : ℕ}
    (r : RelVar Γ k) (args : Fin k → L'.Term α)
    (ρs : RelEnv (Γ.map (· * d)) M) (ρt : RelEnv Γ N)
    (hρ : ∀ xs, xs ∈ ρs (r.scale d) ↔ blockEquiv e k xs ∈ ρt r) (v : α × Fin d → M) :
    (applyTerms f args (.rel (r.scale d) (fun i => .var (.inr i)))).Realize I ρs v ↔
      (Formula.rel (L := L') (shape := shape') r args).Realize I' ρt
        (fun a => e (fun i => v (a, i))) := by
  rw [realize_applyTerms f e hf]
  simpa only [Formula.Realize, Term.realize_var, Sum.elim_inr, Equiv.apply_symm_apply] using
    hρ ((blockEquiv e _).symm (fun i => (args i).realize (fun a => e (fun j => v (a, j)))))

/-- A coordinate block ranges over the target universe through the element bijection. -/
theorem realize_exBlock {β : Type} (I : Interpretation shape M)
    (φ : Formula L shape Γ (Option β × Fin d)) (ρ : RelEnv Γ M) (v : β × Fin d → M)
    (P : (Option β → N) → Prop)
    (hφ : ∀ w : Option β × Fin d → M, φ.Realize I ρ w ↔ P (fun a => e (fun i => w (a, i)))) :
    (exBlock φ).Realize I ρ v ↔ ∃ x, P (Option.elim · x fun a => e (fun i => v (a, i))) := by
  simp only [exBlock, Formula.realize_exs, Formula.realize_relabel, hφ]
  constructor
  · rintro ⟨xs, hx⟩
    refine ⟨e xs, ?_⟩
    convert hx using 2 with a
    cases a <;> rfl
  · rintro ⟨x, hx⟩
    refine ⟨e.symm x, ?_⟩
    convert hx using 2 with a
    cases a with
    | none => exact e.apply_symm_apply x
    | some a => rfl

end Tuple

end Cslib.Logic.FO.Operator
