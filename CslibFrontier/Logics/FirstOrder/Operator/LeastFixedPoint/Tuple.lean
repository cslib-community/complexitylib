/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Operator.LeastFixedPoint
public import CslibFrontier.Logics.FirstOrder.Operator.Tuple

/-!
# Pulling least-fixed-point formulas back to tuples

An interpretation of target elements by full tuples lifts from ordinary first-order formulas
to FO(LFP). Relation arities are multiplied by the tuple dimension. Existentially named term
values let the construction reuse an ordinary first-order pullback, including its handling
of target constants. It preserves both formation and syntactic polarity. The
operator-independent pieces are shared with the transitive-closure pullback through
`CslibFrontier.Logics.FirstOrder.Operator.Tuple`.

The semantic theorem uses a bijection between source tuples and target elements. Thus the
relation spaces are also in bijection, and the intersection of pre-fixed relations is preserved.
-/

public section

open FirstOrder Language

namespace Cslib.Logic.FO

namespace LFP.Tuple

open Operator.Tuple

variable {L L' : Language} {d : ℕ}

/-- Extend an ordinary first-order tuple pullback to scoped FO(LFP) syntax. -/
@[expose] noncomputable def onFormula (f : FOMap L L' d) :
    {Γ : List ℕ} → {α : Type} → RawFormula L' Γ α →
      RawFormula L (Γ.map (· * d)) (α × Fin d)
  | _, _, .ofFO φ => .ofFO (f φ)
  | _, _, .rel r args =>
    applyTerms f args (.rel (r.scale d) (fun i => .var (.inr i)))
  | _, _, .neg φ => .neg (onFormula f φ)
  | _, _, .conj φ ψ => .conj (onFormula f φ) (onFormula f ψ)
  | _, _, .ex φ => exBlock (onFormula f φ)
  | _, _, .op _k body args =>
    applyTerms f args (lfp
      (((onFormula f (body 0)).relabel scopeMap).relabel (Sum.map Sum.inl id))
      (fun i => .var (.inr i)))

variable {Γ : List ℕ} {α : Type}

private theorem scale_outer {k : ℕ} (mark : Operator.Marking (Γ.map (· * d))) :
    (fun {j} (r : Operator.RelVar (k :: Γ) j) =>
      mark.outer [k * d] (r.scale d)) =
      @Operator.Marking.outer Γ [k]
        (fun {j} (r : Operator.RelVar Γ j) => mark (r.scale d)) := by
  funext j r
  cases r <;> rfl

private theorem scale_head {k : ℕ} :
    (fun {j} (r : Operator.RelVar (k :: Γ) j) => headMark (r.scale d)) =
      (headMark : Operator.Marking (k :: Γ)) := by
  funext j r
  cases r <;> rfl

/-- Tuple pullback preserves the syntactic polarity check. -/
@[simp] theorem checkPolarity_onFormula (f : FOMap L L' d) (φ : RawFormula L' Γ α)
    (sign : Bool) (mark : Operator.Marking (Γ.map (· * d))) :
    (onFormula f φ).checkPolarity policy.variance sign mark =
      φ.checkPolarity policy.variance sign (fun {_} r => mark (r.scale d)) := by
  induction φ generalizing sign with
  | ofFO φ => rfl
  | rel r args => simp only [onFormula, checkPolarity_applyTerms, Operator.Formula.checkPolarity]
  | neg φ ih => exact ih _ _
  | conj φ ψ ihφ ihψ => simp only [onFormula, Operator.Formula.checkPolarity, ihφ, ihψ]
  | ex φ ih => simp only [onFormula, checkPolarity_exBlock, Operator.Formula.checkPolarity, ih]
  | op k body args ih =>
    rename_i Γ' α'
    rw [onFormula, checkPolarity_applyTerms]
    change decide (∀ i : Fin 1,
      ((((onFormula f (body 0)).relabel scopeMap).relabel (Sum.map Sum.inl id)).checkPolarity
        policy.variance sign (mark.outer [k * d])) = true) =
      decide (∀ i : Fin 1, (body i).checkPolarity policy.variance sign
        (Operator.Marking.outer [k] (fun {_} r => mark (r.scale d))) = true)
    simp only [Operator.Formula.checkPolarity_relabel, ih, Fin.forall_fin_one]
    have hc := congrArg
      (fun m : Operator.Marking (k :: Γ') => (body 0).checkPolarity policy.variance sign m)
      (scale_outer (k := k) mark)
    exact congrArg (fun b : Bool => decide (b = true)) hc

/-- Tuple pullback preserves the formation check at every nested fixed-point binder. -/
@[simp] theorem wellFormed_onFormula (f : FOMap L L' d) (φ : RawFormula L' Γ α) :
    (onFormula f φ).wellFormed policy = φ.wellFormed policy := by
  induction φ with
  | ofFO φ => rfl
  | rel r args => simp only [onFormula, wellFormed_applyTerms, Operator.Formula.wellFormed]
  | neg φ ih => exact ih
  | conj φ ψ ihφ ihψ => simp only [onFormula, Operator.Formula.wellFormed, ihφ, ihψ]
  | ex φ ih => simp only [onFormula, wellFormed_exBlock, Operator.Formula.wellFormed, ih]
  | op k body args ih =>
    rename_i Γ' α'
    apply Bool.eq_iff_iff.mpr
    simp only [onFormula, wellFormed_applyTerms, wellFormed_lfp,
      Operator.Formula.wellFormed_relabel, Positive, Operator.Formula.checkPolarity_relabel,
      checkPolarity_onFormula, ih, Operator.Formula.wellFormed,
      decide_eq_true_eq, Fin.forall_fin_one, inner_positive_eq_headMark]
    have hc := congrArg
      (fun m : Operator.Marking (k :: Γ') => (body 0).checkPolarity policy.variance true m)
      (scale_head (Γ := Γ') (d := d) (k := k))
    exact and_congr Iff.rfl (iff_of_eq (congrArg (fun b : Bool => b = true) hc))

end LFP.Tuple
end Cslib.Logic.FO
