/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.SQL.Typing

/-!
# Equivalence of SQL expressions

Two expressions are equivalent in a typing context `Γ` (`Expr.Equiv Γ e₁ e₂`) when, on every row
conforming to `Γ`, they both fail or both succeed with the same datum. Equivalence observes
`Except.toOption`: whether evaluation succeeds and with what, not which error it raises, since
strict evaluation fixes one order of evaluation among those SQL permits and the error an engine
reports may differ.

Equivalence is an equivalence relation (`Expr.equivSetoid`) and a congruence for every expression
constructor. It is compatible with renaming (`Expr.Equiv.rename`), with replacing the substituted
expressions by equivalent ones (`Expr.Equiv.subst_right`), and with substituting into equivalent
expressions, provided the substituted expressions are safe and have the column types
(`Expr.Equiv.subst`). The side condition is needed: `TRUE` and `x IS NULL OR x IS NOT NULL` are
equivalent, but substituting `1 / 0` for `x` makes only the second fail.

It adapts and redesigns the expression equivalence of `sql_equiv` (revision `38030a6b`) by Evelyn
Mitchell, which quantified over all rows and compared results including errors; here equivalence
quantifies over the rows of a typing context and does not distinguish errors.

## Main definitions

* `Cslib.SQL.Expr.Equiv`: equivalence of expressions over the rows conforming to a typing context.
* `Cslib.SQL.Expr.equivSetoid`: the corresponding setoid.

## Main results

* `Cslib.SQL.Expr.Equiv.unary`, `Cslib.SQL.Expr.Equiv.binary`, `Cslib.SQL.Expr.Equiv.inList`,
  `Cslib.SQL.Expr.Equiv.caseWhen`: congruence.
* `Cslib.SQL.Expr.Equiv.rename`, `Cslib.SQL.Expr.Equiv.subst`, `Cslib.SQL.Expr.Equiv.subst_right`:
  compatibility with renaming and substitution.
* `Cslib.SQL.Expr.Equiv.evalTruth`: equivalent predicates select the same rows.
-/

@[expose] public section

namespace Cslib.SQL

namespace Expr

variable {n m : ℕ}

/-- Expressions `e₁` and `e₂` are equivalent in the typing context `Γ`: on every row conforming
to `Γ`, both fail or both succeed with the same datum. -/
def Equiv (Γ : Fin n → SqlType) (e₁ e₂ : Expr n) : Prop :=
  ∀ r : Row n, r.Conforms Γ → (e₁.eval r).toOption = (e₂.eval r).toOption

namespace Equiv

variable {Γ : Fin n → SqlType}

@[refl] theorem refl (e : Expr n) : Equiv Γ e e := fun _ _ => rfl

@[symm] theorem symm {e₁ e₂ : Expr n} (h : Equiv Γ e₁ e₂) : Equiv Γ e₂ e₁ :=
  fun r hr => (h r hr).symm

theorem trans {e₁ e₂ e₃ : Expr n} (h₁₂ : Equiv Γ e₁ e₂) (h₂₃ : Equiv Γ e₂ e₃) :
    Equiv Γ e₁ e₃ :=
  fun r hr => (h₁₂ r hr).trans (h₂₃ r hr)

theorem equivalence (Γ : Fin n → SqlType) : Equivalence (Equiv Γ) :=
  ⟨refl, symm, trans⟩

/-- Expressions with the same evaluation on every conforming row are equivalent. -/
theorem of_eval_eq {e₁ e₂ : Expr n} (h : ∀ r : Row n, r.Conforms Γ → e₁.eval r = e₂.eval r) :
    Equiv Γ e₁ e₂ :=
  fun r hr => congrArg Except.toOption (h r hr)

/-- Equivalent predicates have the same truth value, or both fail, on every conforming row; so a
`WHERE` or `ON` clause keeps the same rows with either. -/
theorem evalTruth {e₁ e₂ : Expr n} (h : Equiv Γ e₁ e₂) {r : Row n} (hr : r.Conforms Γ) :
    (e₁.evalTruth r).toOption = (e₂.evalTruth r).toOption := by
  simp only [Expr.evalTruth, Except.toOption_bind, h r hr]

/-! ### Congruence -/

theorem unary (op : UnOp) {e e' : Expr n} (h : Equiv Γ e e') :
    Equiv Γ (unary op e) (unary op e') := by
  intro r hr
  simp only [eval_unary, Except.toOption_bind, h r hr]

theorem binary (op : BinOp) {e₁ e₁' e₂ e₂' : Expr n} (h₁ : Equiv Γ e₁ e₁')
    (h₂ : Equiv Γ e₂ e₂') : Equiv Γ (binary op e₁ e₂) (binary op e₁' e₂') := by
  intro r hr
  simp only [eval_binary, Except.toOption_bind, h₁ r hr, h₂ r hr]

theorem inList {e e' : Expr n} (h : Equiv Γ e e') (vs : List Datum) :
    Equiv Γ (inList e vs) (inList e' vs) := by
  intro r hr
  simp only [eval_inList, Except.toOption_bind, h r hr]

theorem caseWhen {c c' a a' b b' : Expr n} (hc : Equiv Γ c c') (ha : Equiv Γ a a')
    (hb : Equiv Γ b b') : Equiv Γ (caseWhen c a b) (caseWhen c' a' b') := by
  intro r hr
  simp only [eval_caseWhen, Except.toOption_bind, apply_ite Except.toOption, hc r hr, ha r hr,
    hb r hr]

/-! ### Renaming and substitution -/

/-- Expressions equivalent over the reindexed context stay equivalent after renaming. -/
theorem rename {Γ : Fin m → SqlType} {e₁ e₂ : Expr n} (ρ : Fin n → Fin m)
    (h : Equiv (Γ ∘ ρ) e₁ e₂) : Equiv Γ (e₁.rename ρ) (e₂.rename ρ) := by
  intro r hr
  simp only [eval_rename]
  exact h (r ∘ ρ) (hr.comp ρ)

/-- Substituting equivalent expressions gives equivalent results. -/
theorem subst_right {Δ : Fin m → SqlType} {σ σ' : Fin n → Expr m} (h : ∀ i, Equiv Δ (σ i) (σ' i))
    (e : Expr n) : Equiv Δ (e.subst σ) (e.subst σ') :=
  fun r hr => toOption_eval_subst_congr (fun i => h i r hr) e

/-- Substituting into equivalent expressions gives equivalent results, when the substituted
expressions are `divSafe` and have the column types. Without this side condition the substituted
expressions may fail where an equivalent expression does not evaluate them. -/
theorem subst {Δ : Fin m → SqlType} {σ : Fin n → Expr m} (hσ : ∀ i, (σ i).typeOf Δ = some (Γ i))
    (hσs : ∀ i, (σ i).divSafe) {e₁ e₂ : Expr n} (h : Equiv Γ e₁ e₂) :
    Equiv Δ (e₁.subst σ) (e₂.subst σ) := by
  intro r hr
  choose d hd hdτ using fun i => exists_eval_eq_ok_of_divSafe hr (hσ i) (hσs i)
  rw [eval_subst hd, eval_subst hd]
  exact h d hdτ

end Equiv

/-- Equivalence in a typing context, as a setoid. -/
def equivSetoid (Γ : Fin n → SqlType) : Setoid (Expr n) := ⟨Equiv Γ, Equiv.equivalence Γ⟩

end Expr

end Cslib.SQL
