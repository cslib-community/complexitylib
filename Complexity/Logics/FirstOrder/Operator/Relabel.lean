/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Operator.Polarity

/-!
# Renaming and weakening free relation variables

`Formula.relabelRel` renames outer relation variables by an arity-preserving map, leaving every
locally bound relation and all first-order variables unchanged. `Formula.weakenRel` specializes
this to adding an unused relation context, so reusable formulas can move beneath new binders
without reconstructing their relation atoms.

## Main results

* `Formula.realize_relabelRel`: renaming pulls back the relation valuation.
* `Formula.checkPolarity_relabelRel`: polarity checks pull back the marking.
* `Formula.wellFormed_relabelRel`: renaming preserves formation checks, even for noninjective maps.
* `Formula.realize_weakenRel`: new relation values do not affect a weakened formula.
-/

public section

universe u v w z s

open FirstOrder Language

namespace Cslib.Logic.FO.Operator

/-- Extend an arity-preserving renaming beneath a fixed prefix of local relation binders. -/
@[expose] def RelVar.mapUnder {Γ Δ : List ℕ}
    (Λ : List ℕ) (f : ∀ {k}, RelVar Γ k → RelVar Δ k) :
    ∀ {k}, RelVar (Λ ++ Γ) k → RelVar (Λ ++ Δ) k :=
  match Λ with
  | [] => f
  | _ :: Λ => fun r => match r with
    | .here => .here
    | .there r => .there (mapUnder Λ f r)

/-- Renaming beneath a binder leaves local variables fixed and maps only outer variables. -/
@[simp] theorem RelVar.split_mapUnder {Γ Δ : List ℕ}
    (Λ : List ℕ) (f : ∀ {k}, RelVar Γ k → RelVar Δ k)
    {k : ℕ} (r : RelVar (Λ ++ Γ) k) :
    (mapUnder Λ f r).split Λ = Sum.map id f (r.split Λ) := by
  induction Λ with
  | nil => rfl
  | cons _ Λ ih =>
    cases r with
    | here => rfl
    | there r =>
      simp only [mapUnder, split, ih]
      cases r.split Λ <;> rfl

private theorem pull_append {Γ Δ Λ : List ℕ} {M : Type z}
    (f : ∀ {k}, RelVar Γ k → RelVar Δ k) (δ : RelEnv Λ M) (ρ : RelEnv Δ M) :
    (fun {k} (r : RelVar (Λ ++ Γ) k) => δ.append ρ (RelVar.mapUnder Λ f r)) =
      @RelEnv.append Γ Λ M δ (fun {_} r => ρ (f r)) := by
  funext k r
  simp only [RelEnv.append, RelVar.split_mapUnder]
  cases r.split Λ <;> rfl

private theorem pull_outer {Γ Δ : List ℕ} (Λ : List ℕ)
    (f : ∀ {k}, RelVar Γ k → RelVar Δ k) (mark : Marking Δ) :
    (fun {k} (r : RelVar (Λ ++ Γ) k) => mark.outer Λ (RelVar.mapUnder Λ f r)) =
      @Marking.outer Γ Λ (fun {_} r => mark (f r)) := by
  funext k r
  simp only [Marking.outer, RelVar.split_mapUnder]
  cases r.split Λ <;> rfl

private theorem pull_inner {Γ Δ Λ : List ℕ}
    (f : ∀ {k}, RelVar Γ k → RelVar Δ k) (mark : Marking Λ) :
    (fun {k} (r : RelVar (Λ ++ Γ) k) => mark.inner (RelVar.mapUnder Λ f r)) =
      (mark.inner : Marking (Λ ++ Γ)) := by
  funext k r
  simp only [Marking.inner, RelVar.split_mapUnder]
  cases r.split Λ <;> rfl

namespace Formula

variable {L : Language.{u, v}} {O : Type s} {shape : O → Shape}
  {Γ Δ : List ℕ} {α : Type w} {M : Type z} [L.Structure M]

/-- Rename only free relation variables, fixing local binders and all first-order variables. -/
@[expose] def relabelRel : {Γ Δ : List ℕ} → {α : Type w} →
    (∀ {k}, RelVar Γ k → RelVar Δ k) → Formula L shape Γ α → Formula L shape Δ α
  | _, _, _, _, .ofFO φ => .ofFO φ
  | _, _, _, f, .rel r args => .rel (f r) args
  | _, _, _, f, .neg φ => .neg (φ.relabelRel f)
  | _, _, _, f, .conj φ ψ => .conj (φ.relabelRel f) (ψ.relabelRel f)
  | _, _, _, f, .ex φ => .ex (φ.relabelRel f)
  | _, _, _, f, .op o body args =>
    .op o (fun i => (body i).relabelRel (RelVar.mapUnder ((shape o).binder i).relations f)) args

/-- Relabeling relations is interpreted by pulling back their valuation. -/
@[simp, fo_realize] theorem realize_relabelRel (I : Interpretation shape M)
    (φ : Formula L shape Γ α) (f : ∀ {k}, RelVar Γ k → RelVar Δ k)
    (ρ : RelEnv Δ M) (v : α → M) :
    (φ.relabelRel f).Realize I ρ v ↔ φ.Realize I (fun {_} r => ρ (f r)) v := by
  induction φ generalizing Δ with
  | ofFO _ => rfl
  | rel _ _ => rfl
  | neg φ ih => exact not_congr (ih _ _ _)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ _ _ _) (ihψ _ _ _)
  | ex φ ih => exact exists_congr fun _ => ih _ _ _
  | op o body args ih => simp only [relabelRel, Realize, ih, pull_append]

/-- The polarity of renamed relations is checked using the pulled-back marking. -/
@[simp] theorem checkPolarity_relabelRel (variance : Variances shape)
    (φ : Formula L shape Γ α) (f : ∀ {k}, RelVar Γ k → RelVar Δ k)
    (sign : Bool) (mark : Marking Δ) :
    (φ.relabelRel f).checkPolarity variance sign mark =
      φ.checkPolarity variance sign (fun {_} r => mark (f r)) := by
  induction φ generalizing Δ sign with
  | ofFO _ => rfl
  | rel _ _ => rfl
  | neg φ ih => exact ih _ _ _
  | conj φ ψ ihφ ihψ => simp only [relabelRel, checkPolarity, ihφ, ihψ]
  | ex φ ih => exact ih _ _ _
  | op o body args ih => simp only [relabelRel, checkPolarity, ih, pull_outer]

/-- Relation renaming leaves all locally checked formation conditions unchanged. -/
@[simp] theorem wellFormed_relabelRel (policy : Policy shape)
    (φ : Formula L shape Γ α) (f : ∀ {k}, RelVar Γ k → RelVar Δ k) :
    (φ.relabelRel f).wellFormed policy = φ.wellFormed policy := by
  induction φ generalizing Δ with
  | ofFO _ => rfl
  | rel _ _ => rfl
  | neg φ ih => exact ih _
  | conj φ ψ ihφ ihψ => simp only [relabelRel, wellFormed, ihφ, ihψ]
  | ex φ ih => exact ih _
  | op o body args ih =>
    simp only [relabelRel, wellFormed, ih, checkPolarity_relabelRel, pull_inner]

/-- Add unused relation binders to the outer context of a reusable formula. -/
@[expose] def weakenRel (Λ : List ℕ) (φ : Formula L shape Γ α) :
    Formula L shape (Λ ++ Γ) α := φ.relabelRel (RelVar.lift Λ)

/-- New relation values do not affect a weakened formula. -/
@[simp, fo_realize] theorem realize_weakenRel (I : Interpretation shape M)
    (Λ : List ℕ) (φ : Formula L shape Γ α) (δ : RelEnv Λ M) (ρ : RelEnv Γ M)
    (v : α → M) : (φ.weakenRel Λ).Realize I (δ.append ρ) v ↔ φ.Realize I ρ v := by
  simp only [weakenRel, realize_relabelRel, RelEnv.append_lift]

/-- Adding unused relation binders preserves well-formedness. -/
@[simp] theorem wellFormed_weakenRel (policy : Policy shape)
    (Λ : List ℕ) (φ : Formula L shape Γ α) :
    (φ.weakenRel Λ).wellFormed policy = φ.wellFormed policy :=
  wellFormed_relabelRel policy φ _

end Formula

end Cslib.Logic.FO.Operator
