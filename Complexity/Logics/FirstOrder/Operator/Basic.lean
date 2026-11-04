/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Basic

/-!
# First-order logic with scoped operators

An operator has finitely many formula bodies, each with its own first-order and relation
binders, and a tuple of term arguments. This separates binding from the meaning of an operator:
least fixed points, tuple transitive closure, and language quantifiers share the same syntax.
Ordinary terms, formulas, and structures are Mathlib's first-order objects.

`Formula` is raw syntax. An interpretation gives it a total meaning; an operator's formation
conditions (such as positive recursion) are a separate layer. In particular, this interface does
not assume that every operator is monotone or that every structure is finite or ordered.

## Main definitions

* `RelVar`, `RelEnv`: scoped, arity-indexed relation variables and their valuations.
* `Binder`, `Shape`: the binding and application interface of an operator.
* `Formula`, `Formula.Realize`: common syntax and interpretation.
* `Formula.relabel`, `Formula.realize_relabel`: capture-avoiding renaming of free variables.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [Z. Ésik and K. G. Larsen, *Regular Languages Definable by Lindström
  Quantifiers*][EsikLarsen2003], Section 2, for multiple scoped bodies
  in regular-language quantifiers.
-/

public section

universe u v w z s

open FirstOrder Language

namespace Cslib.Logic.FO.Operator

/-- A relation variable whose arity is recorded in its context. The head is the nearest binder. -/
inductive RelVar : List ℕ → ℕ → Type
  | here {Γ : List ℕ} {k : ℕ} : RelVar (k :: Γ) k
  | there {Γ : List ℕ} {k l : ℕ} : RelVar Γ k → RelVar (l :: Γ) k

namespace RelVar

/-- Distinguish a locally bound relation variable from a variable in the outer context. -/
@[expose] def split {Γ : List ℕ} {k : ℕ} (Δ : List ℕ) :
    RelVar (Δ ++ Γ) k → RelVar Δ k ⊕ RelVar Γ k :=
  match Δ with
  | [] => fun r => .inr r
  | _ :: Δ => fun r => match r with
    | .here => .inl .here
    | .there r => match split Δ r with
      | .inl r => .inl (.there r)
      | .inr r => .inr r

/-- Lift an outer relation variable through a list of new binders. -/
@[expose] def lift {Γ : List ℕ} {k : ℕ} (Δ : List ℕ) (r : RelVar Γ k) :
    RelVar (Δ ++ Γ) k :=
  match Δ with
  | [] => r
  | _ :: Δ => .there (lift Δ r)

/-- Splitting a lifted variable recovers the outer variable. -/
@[simp] theorem split_lift {Γ : List ℕ} {k : ℕ} (Δ : List ℕ) (r : RelVar Γ k) :
    split Δ (lift Δ r) = .inr r := by
  induction Δ with
  | nil => rfl
  | cons _ _ ih => simp [split, lift, ih]

end RelVar

/-- An interpretation of all relation variables in a context. -/
abbrev RelEnv (Γ : List ℕ) (M : Type z) := ∀ {k}, RelVar Γ k → Set (Fin k → M)

namespace RelEnv

/-- The unique valuation of an empty relation context. -/
@[expose] def empty {M : Type z} : RelEnv [] M := fun r => nomatch r

/-- Extend a relation valuation by local relations, without changing the outer relations. -/
@[expose] def append {Γ Δ : List ℕ} {M : Type z} (δ : RelEnv Δ M)
    (outer : RelEnv Γ M) : RelEnv (Δ ++ Γ) M :=
  fun r => Sum.elim (fun r => δ r) (fun r => outer r) (r.split Δ)

/-- Add one relation as the nearest binder. -/
@[expose] def cons {Γ : List ℕ} {M : Type z} {k : ℕ} (R : Set (Fin k → M))
    (outer : RelEnv Γ M) : RelEnv (k :: Γ) M
  | _, .here => R
  | _, .there r => outer r

/-- Extending by an empty context leaves a valuation unchanged. -/
@[simp] theorem append_empty {Γ : List ℕ} {M : Type z} (outer : RelEnv Γ M) :
    @append Γ [] M (@empty M) outer = @outer := rfl

/-- Outer relation variables retain their meanings under a binder. -/
@[simp] theorem append_lift {Γ Δ : List ℕ} {M : Type z} (δ : RelEnv Δ M)
    (outer : RelEnv Γ M) {k : ℕ} (r : RelVar Γ k) :
    append δ outer (r.lift Δ) = outer r := by
  simp [append]

end RelEnv

/-- The local variables available in one body of a logical operator. -/
structure Binder where
  /-- Arities of locally bound relation variables, nearest first. -/
  relations : List ℕ
  /-- Number of locally bound first-order variables. -/
  vars : ℕ

/-- The finite binding interface of a logical operator. -/
structure Shape where
  /-- Number of terms at which the operator's resulting relation is applied. -/
  arity : ℕ
  /-- Number of formula bodies. -/
  slots : ℕ
  /-- Local binding context of each body. -/
  binder : Fin slots → Binder

/-- The meaning of a body as a function of its locally bound relations and variables. -/
abbrev BodyValue (b : Binder) (M : Type z) :=
  RelEnv b.relations M → (Fin b.vars → M) → Prop

/-- An operator interpretation. It may use additional structure on `M` supplied by its caller. -/
abbrev Interpretation {O : Type s} (shape : O → Shape) (M : Type z) :=
  (o : O) → ((i : Fin (shape o).slots) → BodyValue ((shape o).binder i) M) →
    (Fin (shape o).arity → M) → Prop

/-- First-order syntax extended by an arbitrary family of scoped logical operators. -/
inductive Formula (L : Language.{u, v}) {O : Type s} (shape : O → Shape) :
    List ℕ → Type w → Type (max u v (w + 1) s)
  | ofFO {Γ α} : L.Formula α → Formula L shape Γ α
  | rel {Γ α k} : RelVar Γ k → (Fin k → L.Term α) → Formula L shape Γ α
  | neg {Γ α} : Formula L shape Γ α → Formula L shape Γ α
  | conj {Γ α} : Formula L shape Γ α → Formula L shape Γ α → Formula L shape Γ α
  | ex {Γ α} : Formula L shape Γ (Option α) → Formula L shape Γ α
  | op {Γ α} (o : O)
      (body : (i : Fin (shape o).slots) →
        Formula L shape (((shape o).binder i).relations ++ Γ)
          (α ⊕ Fin ((shape o).binder i).vars))
      (args : Fin (shape o).arity → L.Term α) : Formula L shape Γ α

namespace Formula

variable {L : Language.{u, v}} {O : Type s} {shape : O → Shape}
  {Γ : List ℕ} {α β : Type w} {M : Type z} [L.Structure M]

/-- Interpret a formula, capturing the ambient free-variable assignment in every operator body. -/
@[expose] def Realize (I : Interpretation shape M) :
    {Γ : List ℕ} → {α : Type w} → Formula L shape Γ α → RelEnv Γ M → (α → M) → Prop
  | _, _, .ofFO φ, _, v => φ.Realize v
  | _, _, .rel r args, ρ, v => (fun i => (args i).realize v) ∈ ρ r
  | _, _, .neg φ, ρ, v => ¬ φ.Realize I ρ v
  | _, _, .conj φ ψ, ρ, v => φ.Realize I ρ v ∧ ψ.Realize I ρ v
  | _, _, .ex φ, ρ, v => ∃ x, φ.Realize I ρ (Option.elim · x v)
  | _, _, .op o body args, ρ, v =>
    I o (fun i δ xs => (body i).Realize I (δ.append ρ) (Sum.elim v xs))
      (fun i => (args i).realize v)

/-- Capture-avoiding relabeling of free first-order variables. -/
@[expose] def relabel : {Γ : List ℕ} → {α β : Type w} →
    (α → β) → Formula L shape Γ α → Formula L shape Γ β
  | _, _, _, f, .ofFO φ => .ofFO (φ.relabel f)
  | _, _, _, f, .rel r args => .rel r (fun i => (args i).relabel f)
  | _, _, _, f, .neg φ => .neg (φ.relabel f)
  | _, _, _, f, .conj φ ψ => .conj (φ.relabel f) (ψ.relabel f)
  | _, _, _, f, .ex φ => .ex (φ.relabel (Option.map f))
  | _, _, _, f, .op o body args =>
    .op o (fun i => (body i).relabel (Sum.map f id)) (fun i => (args i).relabel f)

/-- Embedded first-order formulas keep their original semantics. -/
@[simp, fo_realize] theorem realize_ofFO (I : Interpretation shape M) (φ : L.Formula α)
    (ρ : RelEnv Γ M) (v : α → M) : (ofFO φ).Realize I ρ v ↔ φ.Realize v := Iff.rfl

/-- Relation variables are applied to the interpreted term arguments. -/
@[simp, fo_realize] theorem realize_rel (I : Interpretation shape M) {k : ℕ}
    (r : RelVar Γ k) (args : Fin k → L.Term α) (ρ : RelEnv Γ M) (v : α → M) :
    (rel r args).Realize I ρ v ↔ (fun i => (args i).realize v) ∈ ρ r := Iff.rfl

/-- Semantic negation. -/
@[simp, fo_realize] theorem realize_neg (I : Interpretation shape M) (φ : Formula L shape Γ α)
    (ρ : RelEnv Γ M) (v : α → M) : (neg φ).Realize I ρ v ↔ ¬ φ.Realize I ρ v := Iff.rfl

/-- Semantic conjunction. -/
@[simp, fo_realize] theorem realize_conj (I : Interpretation shape M)
    (φ ψ : Formula L shape Γ α) (ρ : RelEnv Γ M) (v : α → M) :
    (conj φ ψ).Realize I ρ v ↔ φ.Realize I ρ v ∧ ψ.Realize I ρ v := Iff.rfl

/-- Existential binding changes only the new variable. -/
@[simp, fo_realize] theorem realize_ex (I : Interpretation shape M)
    (φ : Formula L shape Γ (Option α)) (ρ : RelEnv Γ M) (v : α → M) :
    (ex φ).Realize I ρ v ↔ ∃ x, φ.Realize I ρ (Option.elim · x v) := Iff.rfl

/-- Relabeling is interpreted by precomposing the free-variable assignment. -/
@[simp, fo_realize] theorem realize_relabel (I : Interpretation shape M)
    (φ : Formula L shape Γ α) (f : α → β) (ρ : RelEnv Γ M) (v : β → M) :
    (φ.relabel f).Realize I ρ v ↔ φ.Realize I ρ (v ∘ f) := by
  induction φ generalizing β with
  | ofFO φ => simp [relabel]
  | rel r args => simp [relabel, Realize, Term.realize_relabel]
  | neg φ ih => exact not_congr (ih f ρ v)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ f ρ v) (ihψ f ρ v)
  | ex φ ih =>
    simp only [relabel, realize_ex, ih]
    apply exists_congr
    intro x
    apply iff_of_eq
    congr 1
    funext y
    cases y <;> rfl
  | op o body args ih =>
    simp only [relabel, Realize, Term.realize_relabel]
    simp_rw [ih]
    apply iff_of_eq
    congr 1
    funext i δ xs
    congr 1
    funext y
    cases y <;> rfl

/-- Disjunction as a derived connective. -/
@[expose] def disj (φ ψ : Formula L shape Γ α) : Formula L shape Γ α :=
  .neg (.conj (.neg φ) (.neg ψ))

/-- Universal quantification as a derived connective. -/
@[expose] def all (φ : Formula L shape Γ (Option α)) : Formula L shape Γ α :=
  .neg (.ex (.neg φ))

/-- Derived disjunction has the usual classical semantics. -/
@[simp, fo_realize] theorem realize_disj (I : Interpretation shape M)
    (φ ψ : Formula L shape Γ α) (ρ : RelEnv Γ M) (v : α → M) :
    (disj φ ψ).Realize I ρ v ↔ φ.Realize I ρ v ∨ ψ.Realize I ρ v := by
  simp only [disj, realize_neg, realize_conj]
  tauto

/-- Derived universal quantification has the usual classical semantics. -/
@[simp, fo_realize] theorem realize_all (I : Interpretation shape M)
    (φ : Formula L shape Γ (Option α)) (ρ : RelEnv Γ M) (v : α → M) :
    (all φ).Realize I ρ v ↔ ∀ x, φ.Realize I ρ (Option.elim · x v) := by
  simp [all]

end Formula

end Cslib.Logic.FO.Operator
