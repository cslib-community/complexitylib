/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Operator.Polarity
public import Complexity.Foundations.Order.FiniteFixedPoint

/-!
# First-order logic with least fixed points

FO(LFP) is an instance of the common first-order operator syntax. An arity-`k` binder adds one
`k`-ary relation and `k` first-order variables to its body. Other free variables are parameters,
fixed throughout the iteration. Terms at the application site are evaluated in the outer scope.

`RawFormula` includes unchecked syntax; its total interpretation takes the intersection of
pre-fixed relations. For nonpositive bodies this need not be a fixed point. `Formula` bundles
the decidable well-formedness condition, checking positive recursion at every nested binder.
All fixed-point laws explicitly require positivity, which is proved to imply monotonicity.
Negation outside a fixed-point binder and arbitrary nesting remain available.

## Main definitions

* `shape`, `policy`, `interpretation`: the LFP instance of the shared operator interface.
* `RawFormula`, `Formula`, `lfp`, `Formula.lfp`: raw and checked FO(LFP) constructors.
* `step`, `stepHom`: the induced relation operator with fixed first-order parameters.

## Main results

* `step_monotone`: syntactic positivity implies semantic monotonicity.
* `realize_lfp`: LFP semantics agrees with Mathlib's `OrderHom.lfp`.
* `step_lfp`, `lfp_le`: fixed-point and leastness laws.
* `iterate_card_pow_eq_lfp`: on a domain of size `n`, arity `k` stabilizes at stage `n^k`.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Chapter 4.
* [N. Immerman, *Relational Queries Computable in Polynomial Time*][Immerman1986],
  Section 1 (positive nested syntax) and Section 2, Fact 2.1 (the finite-stage bound).

This implements the logic and finite-stage semantics. A native polynomial-time evaluator and
the Immerman–Vardi capturing theorem require separate machine and encoding developments.
-/

public section

universe u v w z

open FirstOrder Language

namespace Cslib.Logic.FO.LFP

/-- A least fixed point binds a relation and a tuple of the same arity. -/
abbrev shape (k : ℕ) : Operator.Shape :=
  ⟨k, 1, fun _ => ⟨[k], k⟩⟩

/-- Least fixed points are monotone in their body and require positive self-reference. -/
@[expose] def policy : Operator.Policy shape where
  variance _ _ := .positive
  positive _ _ {_} _ := true

/-- FO(LFP) syntax before its recursive positivity conditions have been checked. -/
abbrev RawFormula (L : Language.{u, v}) (Γ : List ℕ) (α : Type w) :=
  Operator.Formula L shape Γ α

/-- FO(LFP) syntax with positive recursion at every nested binder. -/
abbrev Formula (L : Language.{u, v}) (Γ : List ℕ) (α : Type w) :=
  Operator.CheckedFormula L policy Γ α

/-- Total raw semantics: intersect all pre-fixed relations. The fixed-point laws below require
positive bodies; no fixed-point claim is made for invalid raw syntax. -/
@[expose] def interpretation {M : Type z} : Operator.Interpretation shape M :=
  fun k F xs => xs ∈ sInf {R : Set (Fin k → M) |
    ∀ ys, F (0 : Fin 1) (Operator.RelEnv.cons R Operator.RelEnv.empty) ys → ys ∈ R}

/-- Raw LFP interpretation is monotone in the body transformer, even before checking positivity. -/
theorem interpretation_respects {M : Type z} :
    (interpretation (M := M)).Respects policy.variance := by
  intro k F G h xs hx
  apply Set.mem_of_subset_of_mem ?_ hx
  apply sInf_le_sInf
  intro R hR ys hy
  exact hR ys (h (0 : Fin 1) (Operator.RelEnv.cons R Operator.RelEnv.empty) ys hy)

variable {L : Language.{u, v}} {Γ : List ℕ} {α : Type w} {k : ℕ}

/-- Apply a raw least-fixed-point binder to a tuple of terms. -/
@[expose] def lfp (body : RawFormula L (k :: Γ) (α ⊕ Fin k))
    (args : Fin k → L.Term α) : RawFormula L Γ α :=
  .op k (fun _ => body) args

/-- Mark just the newly bound relation, leaving all outer relations fixed. -/
@[expose] def headMark : Operator.Marking (k :: Γ)
  | _, .here => true
  | _, .there _ => false

/-- A body is syntactically positive in the relation bound by this LFP. -/
@[expose] def Positive (body : RawFormula L (k :: Γ) (α ⊕ Fin k)) : Prop :=
  body.checkPolarity policy.variance true headMark = true

/-- Positivity is a decidable syntactic property. -/
instance (body : RawFormula L (k :: Γ) (α ⊕ Fin k)) : Decidable (Positive body) :=
  inferInstanceAs (Decidable (_ = true))

/-- The generic local marking specializes to the nearest LFP relation. -/
theorem inner_positive_eq_headMark :
    @Operator.Marking.inner Γ [k] (policy.positive k (0 : Fin 1)) = @headMark Γ k := by
  funext n r
  cases r with
  | here => rfl
  | there r => rfl

/-- An LFP is well formed exactly when its body is well formed and positive in its own relation. -/
@[simp] theorem wellFormed_lfp (body : RawFormula L (k :: Γ) (α ⊕ Fin k))
    (args : Fin k → L.Term α) :
    (lfp body args).wellFormed policy = true ↔ body.wellFormed policy = true ∧ Positive body := by
  simp only [lfp, Operator.Formula.wellFormed, decide_eq_true_eq]
  change (∀ i : Fin 1, body.wellFormed policy = true ∧
    body.checkPolarity policy.variance true
      (Operator.Marking.inner (policy.positive k i)) = true) ↔ _
  simp only [Fin.forall_fin_one, Positive]
  have hcheck := congrArg
    (fun mark : Operator.Marking (k :: Γ) => body.checkPolarity policy.variance true mark)
    (inner_positive_eq_headMark (Γ := Γ) (k := k))
  rw [hcheck]

namespace Formula

/-- Construct a checked least fixed point from a checked, positive body. -/
@[expose] def lfp (body : Formula L (k :: Γ) (α ⊕ Fin k)) (hpos : Positive body.val)
    (args : Fin k → L.Term α) : Formula L Γ α :=
  ⟨LFP.lfp body.val args, (wellFormed_lfp _ _).2 ⟨body.property, hpos⟩⟩

/-- Realization of a checked FO(LFP) formula. -/
@[expose] def Realize {M : Type z} [L.Structure M] (φ : Formula L Γ α)
    (ρ : Operator.RelEnv Γ M) (v : α → M) : Prop :=
  φ.val.Realize interpretation ρ v

end Formula

variable {M : Type z} [L.Structure M]

/-- The relation operator induced by a body, with its outer assignment and relations fixed. -/
@[expose] def step (body : RawFormula L (k :: Γ) (α ⊕ Fin k))
    (ρ : Operator.RelEnv Γ M) (v : α → M) (R : Set (Fin k → M)) : Set (Fin k → M) :=
  {xs | body.Realize interpretation (Operator.RelEnv.cons R ρ) (Sum.elim v xs)}

/-- Positive recursion induces a monotone relation operator. -/
theorem step_monotone (body : RawFormula L (k :: Γ) (α ⊕ Fin k)) (hpos : Positive body)
    (ρ : Operator.RelEnv Γ M) (v : α → M) : Monotone (step body ρ v) := by
  intro R S hRS xs hx
  apply Operator.Formula.realize_checkPolarity interpretation interpretation_respects body
    hpos ?_ (Sum.elim v xs) hx
  intro n r ys
  cases r with
  | here => exact ⟨fun hy => hRS hy, by simp [headMark]⟩
  | there r => exact ⟨id, fun _ => id⟩

/-- Bundle the syntactically certified relation operator as a Mathlib order homomorphism. -/
@[expose] def stepHom (body : RawFormula L (k :: Γ) (α ⊕ Fin k)) (hpos : Positive body)
    (ρ : Operator.RelEnv Γ M) (v : α → M) : Set (Fin k → M) →o Set (Fin k → M) :=
  ⟨step body ρ v, step_monotone body hpos ρ v⟩

private theorem append_singleton (R : Set (Fin k → M)) (ρ : Operator.RelEnv Γ M) :
    @Operator.RelEnv.append Γ [k] M (@Operator.RelEnv.cons [] M k R
      (@Operator.RelEnv.empty M)) ρ = @Operator.RelEnv.cons Γ M k R ρ := by
  funext n r
  cases r <;> rfl

/-- A positive raw LFP has the standard least-fixed-point semantics. This rewrites syntax to
the mathematical fixed point without recursively unfolding its defining equation. -/
@[fo_realize]
theorem realize_lfp (body : RawFormula L (k :: Γ) (α ⊕ Fin k)) (hpos : Positive body)
    (args : Fin k → L.Term α) (ρ : Operator.RelEnv Γ M) (v : α → M) :
    (lfp body args).Realize interpretation ρ v ↔
      (fun i => (args i).realize v) ∈ (stepHom body hpos ρ v).lfp := by
  simp only [lfp, Operator.Formula.Realize, interpretation, shape, stepHom, OrderHom.lfp,
    OrderHom.coe_mk, append_singleton, step, Set.subset_def, Set.mem_ofPred_eq]

/-- The checked constructor exposes the same fixed-point semantics directly to simplification. -/
@[simp, fo_realize] theorem Formula.realize_lfp
    (body : Formula L (k :: Γ) (α ⊕ Fin k)) (hpos : Positive body.val)
    (args : Fin k → L.Term α) (ρ : Operator.RelEnv Γ M) (v : α → M) :
    (Formula.lfp body hpos args).Realize ρ v ↔
      (fun i => (args i).realize v) ∈ (stepHom body.val hpos ρ v).lfp :=
  LFP.realize_lfp body.val hpos args ρ v

/-- The denotation is a fixed point of the body's actual relation operator. -/
theorem step_lfp (body : RawFormula L (k :: Γ) (α ⊕ Fin k)) (hpos : Positive body)
    (ρ : Operator.RelEnv Γ M) (v : α → M) :
    step body ρ v (stepHom body hpos ρ v).lfp = (stepHom body hpos ρ v).lfp :=
  (stepHom body hpos ρ v).map_lfp

/-- The denotation is contained in every pre-fixed relation: the useful LFP induction rule. -/
theorem lfp_le (body : RawFormula L (k :: Γ) (α ⊕ Fin k)) (hpos : Positive body)
    (ρ : Operator.RelEnv Γ M) (v : α → M) {R : Set (Fin k → M)}
    (hR : step body ρ v R ⊆ R) : (stepHom body hpos ρ v).lfp ⊆ R :=
  (stepHom body hpos ρ v).lfp_le hR

/-- A `k`-ary positive operator on a domain of size `n` reaches its least fixed point after
`n^k` applications from the empty relation. This includes empty domains and nullary relations. -/
theorem iterate_card_pow_eq_lfp [Fintype M]
    (body : RawFormula L (k :: Γ) (α ⊕ Fin k)) (hpos : Positive body)
    (ρ : Operator.RelEnv Γ M) (v : α → M) :
    ((step body ρ v)^[Fintype.card M ^ k]) ∅ = (stepHom body hpos ρ v).lfp := by
  simpa only [Fintype.card_fun, Fintype.card_fin, stepHom, OrderHom.coe_mk, Set.bot_eq_empty] using
    (stepHom body hpos ρ v).iterate_card_bot_eq_lfp

end Cslib.Logic.FO.LFP
