/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Operator.Basic

/-!
# Variance and formation rules for first-order operators

Operator bodies may be monotone, antitone, or arbitrary. Positivity propagates through this
variance, not just through negations: an arbitrary operator (for example, a parity quantifier)
must not introduce a hidden negative dependency into a least fixed point.

`Formula.checkPolarity` is a decidable syntactic check. `Formula.realize_checkPolarity` proves
its semantic guarantee from the operator interpretation's variance law. `Policy` separately
specifies which locally bound relations must occur positively; `Formula.wellFormed` checks this
condition at every nested operator. Raw interpretation itself does not assume well-formedness.

## Main definitions

* `Variance`, `Interpretation.Respects`: the semantic extension contract.
* `Policy`, `Formula.wellFormed`, `CheckedFormula`: formation rules and checked formulas.
* `Formula.checkPolarity`: syntactic dependence on a marked set of relation variables.

## Main results

* `Formula.realize_checkPolarity`: syntactic polarity implies semantic monotonicity or antitonicity.
* `Formula.wellFormed_relabel`: free-variable renaming preserves formation conditions.
-/

public section

universe u v w z s

open FirstOrder Language

namespace Cslib.Logic.FO.Operator

/-- The variance of an operator in one of its body predicates. -/
inductive Variance
  | positive
  | negative
  | arbitrary
  deriving DecidableEq

/-- The pointwise relation on body predicates required by a variance annotation. -/
@[expose] def Variance.Relates : Variance → Prop → Prop → Prop
  | .positive, p, q => p → q
  | .negative, p, q => q → p
  | .arbitrary, p, q => p ↔ q

/-- A Boolean marking of relation variables. -/
abbrev Marking (Γ : List ℕ) := ∀ {k}, RelVar Γ k → Bool

namespace Marking

/-- Mark only outer variables when passing under a binder. -/
@[expose] def outer {Γ : List ℕ} (Δ : List ℕ) (mark : Marking Γ) : Marking (Δ ++ Γ) :=
  fun r => Sum.elim (fun _ => false) (fun r => mark r) (r.split Δ)

/-- Mark only the selected locally bound variables. -/
@[expose] def inner {Γ Δ : List ℕ} (mark : Marking Δ) : Marking (Δ ++ Γ) :=
  fun r => Sum.elim (fun r => mark r) (fun _ => false) (r.split Δ)

/-- An empty marking stays empty under any number of relation binders. -/
@[simp] theorem outer_false {Γ : List ℕ} (Δ : List ℕ) :
    @outer Γ Δ (fun {_} _ => false) = (fun {_} _ => false) := by
  funext k r
  simp only [outer]
  cases r.split Δ <;> rfl

end Marking

/-- The declared variance of every body of every operator. -/
abbrev Variances {O : Type s} (shape : O → Shape) :=
  (o : O) → Fin (shape o).slots → Variance

/-- An interpretation obeys the declared body variances. Arbitrary bodies must be equivalent. -/
@[expose] def Interpretation.Respects {O : Type s} {shape : O → Shape} {M : Type z}
    (I : Interpretation shape M) (variance : Variances shape) : Prop :=
  ∀ o F G, (∀ i δ xs, (variance o i).Relates (F i δ xs) (G i δ xs)) →
    ∀ args, I o F args → I o G args

/-- Operator-specific formation conditions, separate from binding and interpretation. -/
structure Policy {O : Type s} (shape : O → Shape) where
  /-- How an operator depends on each body. -/
  variance : Variances shape
  /-- Locally bound relations required to occur positively in each body. -/
  positive : (o : O) → (i : Fin (shape o).slots) → Marking ((shape o).binder i).relations

namespace Formula

variable {L : Language.{u, v}} {O : Type s} {shape : O → Shape}

/-- Check positive (`true`) or negative (`false`) dependence on the marked relations.
Arbitrary operator slots require both checks, conservatively excluding marked dependencies. -/
@[expose] def checkPolarity (variance : Variances shape) :
    {Γ : List ℕ} → {α : Type w} → Formula L shape Γ α → Bool → Marking Γ → Bool
  | _, _, .ofFO _, _, _ => true
  | _, _, .rel r _, sign, mark => sign || !mark r
  | _, _, .neg φ, sign, mark => φ.checkPolarity variance (!sign) mark
  | _, _, .conj φ ψ, sign, mark =>
    φ.checkPolarity variance sign mark && ψ.checkPolarity variance sign mark
  | _, _, .ex φ, sign, mark => φ.checkPolarity variance sign mark
  | _, _, .op o body _, sign, mark => decide (∀ i,
    (match variance o i with
    | .positive => (body i).checkPolarity variance sign
        (mark.outer ((shape o).binder i).relations)
    | .negative => (body i).checkPolarity variance (!sign)
        (mark.outer ((shape o).binder i).relations)
    | .arbitrary => (body i).checkPolarity variance true
        (mark.outer ((shape o).binder i).relations) &&
        (body i).checkPolarity variance false
        (mark.outer ((shape o).binder i).relations)) = true)

/-- Check the local positivity requirements and recursively check all nested bodies. -/
@[expose] def wellFormed (policy : Policy shape) :
    {Γ : List ℕ} → {α : Type w} → Formula L shape Γ α → Bool
  | _, _, .ofFO _ => true
  | _, _, .rel _ _ => true
  | _, _, .neg φ => φ.wellFormed policy
  | _, _, .conj φ ψ => φ.wellFormed policy && ψ.wellFormed policy
  | _, _, .ex φ => φ.wellFormed policy
  | _, _, .op o body _ => decide (∀ i, (body i).wellFormed policy = true ∧
    (body i).checkPolarity policy.variance true (Marking.inner (policy.positive o i)) = true)

/-- Every formula has both polarities when no relation variable is marked. -/
@[simp] theorem checkPolarity_false {Γ : List ℕ} {α : Type w}
    (variance : Variances shape) (φ : Formula L shape Γ α) (sign : Bool) :
    φ.checkPolarity variance sign (fun {_} _ => false) = true := by
  induction φ generalizing sign with
  | ofFO _ => rfl
  | rel _ _ => simp [checkPolarity]
  | neg φ ih => exact ih _
  | conj φ ψ ihφ ihψ => simp [checkPolarity, ihφ, ihψ]
  | ex φ ih => exact ih _
  | op o body args ih =>
    simp only [checkPolarity, Marking.outer_false, ih, Bool.and_self, decide_eq_true_eq]
    intro i
    cases variance o i <;> rfl

/-- A checker's result does not depend on the names of free first-order variables. -/
@[simp] theorem checkPolarity_relabel {Γ : List ℕ} {α β : Type w}
    (variance : Variances shape) (φ : Formula L shape Γ α) (f : α → β)
    (sign : Bool) (mark : Marking Γ) :
    (φ.relabel f).checkPolarity variance sign mark = φ.checkPolarity variance sign mark := by
  induction φ generalizing β sign with
  | ofFO _ => rfl
  | rel _ _ => rfl
  | neg φ ih => exact ih _ _ _
  | conj φ ψ ihφ ihψ => simp only [relabel, checkPolarity, ihφ, ihψ]
  | ex φ ih => exact ih _ _ _
  | op o body args ih => simp only [relabel, checkPolarity, ih]

/-- Renaming free first-order variables preserves operator formation conditions. -/
@[simp] theorem wellFormed_relabel {Γ : List ℕ} {α β : Type w}
    (policy : Policy shape) (φ : Formula L shape Γ α) (f : α → β) :
    (φ.relabel f).wellFormed policy = φ.wellFormed policy := by
  induction φ generalizing β with
  | ofFO _ => rfl
  | rel _ _ => rfl
  | neg φ ih => exact ih _
  | conj φ ψ ihφ ihψ => simp only [relabel, wellFormed, ihφ, ihψ]
  | ex φ ih => exact ih _
  | op o body args ih => simp only [relabel, wellFormed, ih, checkPolarity_relabel]

end Formula

/-- A formula together with its checked operator formation conditions. -/
abbrev CheckedFormula (L : Language.{u, v}) {O : Type s} {shape : O → Shape}
    (policy : Policy shape) (Γ : List ℕ) (α : Type w) :=
  {φ : Formula L shape Γ α // φ.wellFormed policy = true}

namespace RelEnv

/-- Increase marked relations, keeping every unmarked relation fixed. -/
@[expose] def LeOn {Γ : List ℕ} {M : Type z} (mark : Marking Γ)
    (ρ σ : RelEnv Γ M) : Prop :=
  ∀ {k} (r : RelVar Γ k) xs, (xs ∈ ρ r → xs ∈ σ r) ∧
    (mark r = false → xs ∈ σ r → xs ∈ ρ r)

/-- Equal local valuations preserve the comparison of the outer valuations. -/
theorem LeOn.append {Γ Δ : List ℕ} {M : Type z} {mark : Marking Γ} {ρ σ : RelEnv Γ M}
    (h : LeOn mark ρ σ) (δ : RelEnv Δ M) :
    LeOn (mark.outer Δ) (δ.append ρ) (δ.append σ) := by
  intro k r xs
  simp only [RelEnv.append, Marking.outer]
  cases r.split Δ with
  | inl r => exact ⟨id, fun _ => id⟩
  | inr r => exact h r xs

end RelEnv

/-- The implication direction selected by a polarity. -/
@[expose] def Directed : Bool → Prop → Prop → Prop
  | true, p, q => p → q
  | false, p, q => q → p

namespace Formula

variable {L : Language.{u, v}} {O : Type s} {shape : O → Shape}
  {Γ : List ℕ} {α : Type w} {M : Type z} [L.Structure M]

/-- The syntactic polarity check implies the corresponding semantic implication.
This includes nested operators and does not assume that raw syntax is well-formed. -/
theorem realize_checkPolarity {variance : Variances shape} (I : Interpretation shape M)
    (hI : I.Respects variance) (φ : Formula L shape Γ α)
    {sign : Bool} {mark : Marking Γ} {ρ σ : RelEnv Γ M}
    (hφ : φ.checkPolarity variance sign mark = true) (hρ : RelEnv.LeOn mark ρ σ)
    (v : α → M) : Directed sign (φ.Realize I ρ v) (φ.Realize I σ v) := by
  induction φ generalizing sign with
  | ofFO φ => cases sign <;> exact id
  | rel r args =>
    cases sign with
    | false =>
      have hm : mark r = false := by simpa [checkPolarity] using hφ
      exact (hρ r _).2 hm
    | true => exact (hρ r _).1
  | neg φ ih =>
    cases sign with
    | false => exact fun h hp => h (ih hφ hρ v hp)
    | true => exact fun h hp => h (ih hφ hρ v hp)
  | conj φ ψ ihφ ihψ =>
    have ⟨hφ, hψ⟩ : φ.checkPolarity variance sign mark = true ∧
        ψ.checkPolarity variance sign mark = true := by simpa [checkPolarity] using hφ
    cases sign <;> exact fun h => ⟨ihφ hφ hρ v h.1, ihψ hψ hρ v h.2⟩
  | ex φ ih =>
    cases sign <;> exact fun ⟨x, hx⟩ => ⟨x, ih hφ hρ _ hx⟩
  | op o body args ih =>
    simp only [checkPolarity, decide_eq_true_eq] at hφ
    have hbody := hφ
    cases sign with
    | true =>
      apply hI o
      intro i δ xs
      have hi := hbody i
      cases hv : variance o i with
      | positive =>
        simp only [hv] at hi
        exact ih i hi (hρ.append δ) _
      | negative =>
        simp only [hv] at hi
        exact ih i hi (hρ.append δ) _
      | arbitrary =>
        simp only [hv, Bool.and_eq_true] at hi
        exact ⟨ih i hi.1 (hρ.append δ) _, ih i hi.2 (hρ.append δ) _⟩
    | false =>
      apply hI o
      intro i δ xs
      have hi := hbody i
      cases hv : variance o i with
      | positive =>
        simp only [hv] at hi
        exact ih i hi (hρ.append δ) _
      | negative =>
        simp only [hv] at hi
        exact ih i hi (hρ.append δ) _
      | arbitrary =>
        simp only [hv, Bool.and_eq_true] at hi
        exact ⟨ih i hi.2 (hρ.append δ) _, ih i hi.1 (hρ.append δ) _⟩

end Formula

end Cslib.Logic.FO.Operator
