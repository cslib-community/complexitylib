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

The laws that the expression simplifier (`Cslib.SQL.Expr.simplify`) applies are proved here, each
with the side condition strict evaluation needs: `NOT` over a comparison or a null test, double
negation of a boolean or an integer, `TRUE` and `FALSE` as operands of `AND` and `OR`, the
identities of `+`, `-` and `*`, `IN` over an empty or one-element list, and `CASE` with a literal
condition. A law that inspects an operand's value needs the operand's type (`p AND TRUE` is `p`
only for a boolean `p`), and a law that drops an operand needs it to be safe (`p AND FALSE` is
`FALSE` only when `p` cannot fail).

It adapts and redesigns the expression equivalence of `sql_equiv` (revision `38030a6b`) by Evelyn
Mitchell, which quantified over all rows and compared results including errors; here equivalence
quantifies over the rows of a typing context and does not distinguish errors.

## Main definitions

* `Cslib.SQL.Expr.Equiv`: equivalence of expressions over the rows conforming to a typing context.
* `Cslib.SQL.Expr.equivSetoid`: the corresponding setoid.

## Main results

* `Cslib.SQL.Expr.Equiv.unary`, `Cslib.SQL.Expr.Equiv.binary`, `Cslib.SQL.Expr.Equiv.inList`,
  `Cslib.SQL.Expr.Equiv.caseWhen`: congruence.
* `Cslib.SQL.Expr.Equiv.binary_comm`: commutative operators commute on expressions.
* `Cslib.SQL.Expr.Equiv.rename`, `Cslib.SQL.Expr.Equiv.subst`, `Cslib.SQL.Expr.Equiv.subst_right`:
  compatibility with renaming and substitution.
* `Cslib.SQL.Expr.Equiv.evalTruth`: equivalent predicates select the same rows.
* `Cslib.SQL.Expr.Equiv.of_eval_eq_ok`: an expression with the same value on every row is that
  literal (constant folding).
* `Cslib.SQL.Expr.Equiv.not_cmp`, `Cslib.SQL.Expr.Equiv.not_not`, `Cslib.SQL.Expr.Equiv.and_true`,
  `Cslib.SQL.Expr.Equiv.and_false`, `Cslib.SQL.Expr.Equiv.add_zero`,
  `Cslib.SQL.Expr.Equiv.inList_nil`, `Cslib.SQL.Expr.Equiv.inList_singleton`,
  `Cslib.SQL.Expr.Equiv.caseWhen_true` and their siblings: the simplifier's laws.
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

instance : Trans (Equiv (n := n) Γ) (Equiv Γ) (Equiv Γ) := ⟨trans⟩

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

/-- A binary operator whose observations do not depend on the order of its operands is
commutative on expressions. It applies to `AND` and `OR` (`evalBinOp_and_comm`, …), whose two
sides may raise different first errors, so `Equiv.of_eval_eq` cannot prove them. -/
theorem binary_comm {op : BinOp}
    (hop : ∀ a b, (evalBinOp op a b).toOption = (evalBinOp op b a).toOption) (e₁ e₂ : Expr n) :
    Equiv Γ (Expr.binary op e₁ e₂) (Expr.binary op e₂ e₁) := by
  intro r _
  simp only [eval_binary, Except.toOption_bind]
  rcases e₁.eval r with _ | a <;> rcases e₂.eval r with _ | b <;> simp [hop]

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

/-! ### Laws

The rewrites of the expression simplifier (`Cslib.SQL.Expr.simplify`). A law that inspects an
operand's value needs the operand's type; a law that drops an operand needs it to be safe, since
strict evaluation fails when the dropped operand fails. -/

/-- An expression that succeeds with the same datum on every conforming row is that literal. -/
theorem of_eval_eq_ok {e : Expr n} {d : Datum} (h : ∀ r : Row n, r.Conforms Γ → e.eval r = .ok d)
    (τ : SqlType) : Equiv Γ e (ofDatum τ d) :=
  of_eval_eq fun r hr => (h r hr).trans (eval_ofDatum τ d r).symm

/-- A rewrite whose left side evaluates `e` and continues with `g`, where `g` returns its argument
on datums of `e`'s type. -/
private theorem of_eval_bind_eq_self {e e' : Expr n} {τ : SqlType} (he : e.typeOf Γ = some τ)
    {g : Datum → Except EvalError Datum} (hrw : ∀ r, e'.eval r = e.eval r >>= g)
    (hg : ∀ d, d.HasType τ → g d = .ok d) : Equiv Γ e' e :=
  of_eval_eq fun r hr => by
    rw [hrw]
    rcases h : e.eval r with err | d
    · rfl
    · exact hg d (hasType_of_eval_eq_ok hr he h)

/-- A rewrite whose left side evaluates the `divSafe` expression `e` and continues with `g`, where
`g` returns `c` on datums of `e`'s type, and whose right side is `c`. -/
private theorem of_eval_bind_eq_const {e e' e'' : Expr n} {τ : SqlType}
    (he : e.typeOf Γ = some τ) (hs : e.divSafe) {g : Datum → Except EvalError Datum} {c : Datum}
    (hrw : ∀ r, e'.eval r = e.eval r >>= g) (hg : ∀ d, d.HasType τ → g d = .ok c)
    (hc : ∀ r, e''.eval r = .ok c) : Equiv Γ e' e'' :=
  of_eval_eq fun r hr => by
    obtain ⟨d, hd, hdτ⟩ := exists_eval_eq_ok_of_divSafe hr he hs
    rw [hrw, hd, hc]
    exact hg d hdτ

/-- `NOT (a op b)` is `a (negate op) b`; for instance `NOT (a < b)` is `a >= b`. -/
theorem not_cmp (op : CmpOp) (a b : Expr n) :
    Equiv Γ (Expr.unary .not (Expr.binary (.cmp op) a b)) (Expr.binary (.cmp op.negate) a b) :=
  of_eval_eq fun r _ => by
    simp only [eval_unary, eval_binary, evalBinOp_cmp_negate, bind_assoc]

/-- `NOT (e IS NULL)` is `e IS NOT NULL`. -/
theorem not_isNull (e : Expr n) :
    Equiv Γ (Expr.unary .not (Expr.unary .isNull e)) (Expr.unary .isNotNull e) :=
  of_eval_eq fun r _ => by
    simp only [eval_unary, bind_assoc, not_evalUnOp_isNull]

/-- `NOT (e IS NOT NULL)` is `e IS NULL`. -/
theorem not_isNotNull (e : Expr n) :
    Equiv Γ (Expr.unary .not (Expr.unary .isNotNull e)) (Expr.unary .isNull e) :=
  of_eval_eq fun r _ => by
    simp only [eval_unary, bind_assoc, not_evalUnOp_isNotNull]

/-- `NOT (NOT p)` is `p` for a boolean `p`. -/
theorem not_not {p : Expr n} (hp : p.typeOf Γ = some .bool) :
    Equiv Γ (Expr.unary .not (Expr.unary .not p)) p :=
  of_eval_bind_eq_self hp (fun r => by simp only [eval_unary, bind_assoc]) fun _ hd =>
    evalUnOp_not_not hd

/-- `-(-x)` is `x` for an integer `x`. -/
theorem neg_neg {x : Expr n} (hx : x.typeOf Γ = some .int) :
    Equiv Γ (Expr.unary .neg (Expr.unary .neg x)) x :=
  of_eval_bind_eq_self hx (fun r => by simp only [eval_unary, bind_assoc]) fun _ hd =>
    evalUnOp_neg_neg hd

/-- `p AND TRUE` is `p` for a boolean `p`. -/
theorem and_true {p : Expr n} (hp : p.typeOf Γ = some .bool) :
    Equiv Γ (Expr.binary .and p (lit (.bool true))) p :=
  of_eval_bind_eq_self hp (fun _ => rfl) fun _ hd => evalBinOp_and_true hd

/-- `TRUE AND p` is `p` for a boolean `p`. -/
theorem true_and {p : Expr n} (hp : p.typeOf Γ = some .bool) :
    Equiv Γ (Expr.binary .and (lit (.bool true)) p) p :=
  of_eval_bind_eq_self hp (fun _ => rfl) fun _ hd =>
    (evalBinOp_and_comm _ _).trans (evalBinOp_and_true hd)

/-- `p OR FALSE` is `p` for a boolean `p`. -/
theorem or_false {p : Expr n} (hp : p.typeOf Γ = some .bool) :
    Equiv Γ (Expr.binary .or p (lit (.bool false))) p :=
  of_eval_bind_eq_self hp (fun _ => rfl) fun _ hd => evalBinOp_or_false hd

/-- `FALSE OR p` is `p` for a boolean `p`. -/
theorem false_or {p : Expr n} (hp : p.typeOf Γ = some .bool) :
    Equiv Γ (Expr.binary .or (lit (.bool false)) p) p :=
  of_eval_bind_eq_self hp (fun _ => rfl) fun _ hd =>
    (evalBinOp_or_comm _ _).trans (evalBinOp_or_false hd)

/-- `p AND FALSE` is `FALSE` for a safe predicate `p`. Safety is needed: `(1 / 0 = 1) AND FALSE`
fails. -/
theorem and_false {p : Expr n} (hp : p.IsSafePredicate Γ) :
    Equiv Γ (Expr.binary .and p (lit (.bool false))) (lit (.bool false)) :=
  of_eval_bind_eq_const hp.1 hp.2 (fun _ => rfl) (fun _ hd => evalBinOp_and_false hd)
    fun _ => rfl

/-- `FALSE AND p` is `FALSE` for a safe predicate `p`. -/
theorem false_and {p : Expr n} (hp : p.IsSafePredicate Γ) :
    Equiv Γ (Expr.binary .and (lit (.bool false)) p) (lit (.bool false)) :=
  of_eval_bind_eq_const hp.1 hp.2 (fun _ => rfl)
    (fun _ hd => (evalBinOp_and_comm _ _).trans (evalBinOp_and_false hd)) fun _ => rfl

/-- `p OR TRUE` is `TRUE` for a safe predicate `p`. -/
theorem or_true {p : Expr n} (hp : p.IsSafePredicate Γ) :
    Equiv Γ (Expr.binary .or p (lit (.bool true))) (lit (.bool true)) :=
  of_eval_bind_eq_const hp.1 hp.2 (fun _ => rfl) (fun _ hd => evalBinOp_or_true hd)
    fun _ => rfl

/-- `TRUE OR p` is `TRUE` for a safe predicate `p`. -/
theorem true_or {p : Expr n} (hp : p.IsSafePredicate Γ) :
    Equiv Γ (Expr.binary .or (lit (.bool true)) p) (lit (.bool true)) :=
  of_eval_bind_eq_const hp.1 hp.2 (fun _ => rfl)
    (fun _ hd => (evalBinOp_or_comm _ _).trans (evalBinOp_or_true hd)) fun _ => rfl

/-- `x + 0` is `x` for an integer `x`. -/
theorem add_zero {x : Expr n} (hx : x.typeOf Γ = some .int) :
    Equiv Γ (Expr.binary (.arith .add) x (lit (.int 0))) x :=
  of_eval_bind_eq_self hx (fun _ => rfl) fun _ hd => evalBinOp_add_zero hd

/-- `0 + x` is `x` for an integer `x`. -/
theorem zero_add {x : Expr n} (hx : x.typeOf Γ = some .int) :
    Equiv Γ (Expr.binary (.arith .add) (lit (.int 0)) x) x :=
  of_eval_bind_eq_self hx (fun _ => rfl) fun _ hd =>
    (evalBinOp_add_comm _ _).trans (evalBinOp_add_zero hd)

/-- `x - 0` is `x` for an integer `x`. -/
theorem sub_zero {x : Expr n} (hx : x.typeOf Γ = some .int) :
    Equiv Γ (Expr.binary (.arith .sub) x (lit (.int 0))) x :=
  of_eval_bind_eq_self hx (fun _ => rfl) fun _ hd => evalBinOp_sub_zero hd

/-- `x * 1` is `x` for an integer `x`. -/
theorem mul_one {x : Expr n} (hx : x.typeOf Γ = some .int) :
    Equiv Γ (Expr.binary (.arith .mul) x (lit (.int 1))) x :=
  of_eval_bind_eq_self hx (fun _ => rfl) fun _ hd => evalBinOp_mul_one hd

/-- `1 * x` is `x` for an integer `x`. -/
theorem one_mul {x : Expr n} (hx : x.typeOf Γ = some .int) :
    Equiv Γ (Expr.binary (.arith .mul) (lit (.int 1)) x) x :=
  of_eval_bind_eq_self hx (fun _ => rfl) fun _ hd =>
    (evalBinOp_mul_comm _ _).trans (evalBinOp_mul_one hd)

/-- `e IN ()` is `FALSE` for a safe `e`, also when `e` is `NULL`. -/
theorem inList_nil {e : Expr n} (he : e.IsSafe Γ) :
    Equiv Γ (Expr.inList e []) (lit (.bool false)) :=
  have ⟨_, hτ⟩ := Option.isSome_iff_exists.mp he.1
  of_eval_bind_eq_const hτ he.2 (fun _ => rfl) (fun _ _ => rfl) fun _ => rfl

/-- `e IN (v)` is `e = v`. -/
theorem inList_singleton (e : Expr n) (v : Datum) (τ : SqlType) :
    Equiv Γ (Expr.inList e [v]) (Expr.binary (.cmp .eq) e (ofDatum τ v)) :=
  of_eval_eq fun r _ => by
    simp only [eval_inList, eval_binary, eval_ofDatum, Datum.inList_singleton]
    rcases e.eval r with _ | d
    · rfl
    · rcases CmpOp.eq.eval d v <;> rfl

/-- `CASE WHEN TRUE THEN a ELSE b END` is `a`. -/
theorem caseWhen_true (a b : Expr n) : Equiv Γ (Expr.caseWhen (lit (.bool true)) a b) a :=
  of_eval_eq fun r _ => eval_caseWhen_of_true r rfl a b

/-- `CASE WHEN FALSE THEN a ELSE b END` is `b`. -/
theorem caseWhen_false (a b : Expr n) : Equiv Γ (Expr.caseWhen (lit (.bool false)) a b) b :=
  of_eval_eq fun r _ => eval_caseWhen_of_ne_true r rfl (by decide) a b

/-- `CASE WHEN NULL THEN a ELSE b END` is `b`. -/
theorem caseWhen_null (τ : SqlType) (a b : Expr n) : Equiv Γ (Expr.caseWhen (null τ) a b) b :=
  of_eval_eq fun r _ => eval_caseWhen_of_ne_true r rfl (by decide) a b

end Equiv

/-- Equivalence in a typing context, as a setoid. -/
def equivSetoid (Γ : Fin n → SqlType) : Setoid (Expr n) := ⟨Equiv Γ, Equiv.equivalence Γ⟩

end Expr

end Cslib.SQL
