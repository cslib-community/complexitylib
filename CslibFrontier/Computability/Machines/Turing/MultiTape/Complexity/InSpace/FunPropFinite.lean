/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-!
# Finite values and conditions within a fixed workspace budget

These `fun_prop` rules extend those of `InSpace.FunProp` to values of finite types. A function of
a value of a finite type (`budget_finite`) costs no workspace beyond the value. Conditions may be
decidable propositions (`budget_iteProp`), their negations (`budget_decideNot`), equalities on a
finite type (`budget_decideEq`) or Boolean connectives.

The rules reach `fun_prop` only where this module is imported, directly or through
`CslibFrontier.Tactic.Space`. A direct `fun_prop` client that needs them imports this module.

The intermediate encoding of `budget_finite` and `budget_decideEq` is not determined by the goal.
When no premise determines it, as for a finite function of a component of a finite value,
`budget_finite_encFinite` and `budget_decideEq_encFinite` pass through the canonical encoding
`encFinite`. Several finite values combined into one argument still need their encoding stated,
for example `have := budget_finite (encC := encFinEnum Guard) Ref.guardOf hr`.

`budget_decideEq_encFinite`, conjunctions and disjunctions (`budget_decideAnd`, `budget_decideOr`)
and comparisons `≤` of numbers (`budget_natLe`) are not registered: each would be tried, and fail,
on every decidable condition, which doubles the search on small certificates. The `space` tactic
adds them when a first search without them fails; a direct `fun_prop` client can use
`attribute [local fun_prop]`.

## Main results

* `budget_iteProp`, `budget_decideNot`, `budget_decideEq`: decidable conditions within the budget.
* `budget_finite_encFinite`: a function of a finite value, through its canonical encoding.
* `budget_decideEq_encFinite`, `budget_decideAnd`, `budget_decideOr`, `budget_natLe`: further
  conditions, which `space` tries after the registered rules.
* `budget_boolNot`, `budget_boolAnd`, `budget_boolOr`: Boolean connectives within the budget.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

attribute [fun_prop] budget_finite budget_finMod

variable {α β γ : Type} {encIn : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {Bs : α → ℕ}

/-- A conditional on a decidable proposition, within the budget. -/
@[fun_prop]
theorem budget_iteProp {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hc : ComputableInSpace (fun x => decide (p x)) encIn encBool Bs)
    (hf : ComputableInSpace f encIn encB Bs) (hg : ComputableInSpace g encIn encB Bs) :
    ComputableInSpace (fun x => if p x then f x else g x) encIn encB Bs :=
  (budget_ite hc hf hg).of_enc_eq fun x => by simp only [decide_eq_true_eq]

/-- The negation of a decidable proposition, within the budget. This covers `≠` conditions. -/
@[fun_prop]
theorem budget_decideNot {p : α → Prop} [DecidablePred p]
    (hp : ComputableInSpace (fun x => decide (p x)) encIn encBool Bs) :
    ComputableInSpace (fun x => decide ¬p x) encIn encBool Bs :=
  (budget_finite (encC := encBool) (fun b : Bool => !b) hp).of_enc_eq fun x => by
    simp only [decide_not]

/-- Equality of two values of a finite type, within the budget. -/
@[fun_prop]
theorem budget_decideEq [Finite β] [DecidableEq β] {f g : α → β}
    (hf : ComputableInSpace f encIn encB Bs) (hg : ComputableInSpace g encIn encB Bs) :
    ComputableInSpace (fun x => decide (f x = g x)) encIn encBool Bs :=
  budget_finite (fun p : β × β => decide (p.1 = p.2)) (budget_prod hf hg)

/-- The negation of a Boolean, within the budget. -/
@[fun_prop]
theorem budget_boolNot {a : α → Bool} (ha : ComputableInSpace a encIn encBool Bs) :
    ComputableInSpace (fun x => !a x) encIn encBool Bs :=
  budget_finite (fun b : Bool => !b) ha

/-- The conjunction of two Booleans, within the budget. -/
@[fun_prop]
theorem budget_boolAnd {a b : α → Bool} (ha : ComputableInSpace a encIn encBool Bs)
    (hb : ComputableInSpace b encIn encBool Bs) :
    ComputableInSpace (fun x => a x && b x) encIn encBool Bs :=
  budget_finite (fun p : Bool × Bool => p.1 && p.2) (budget_prod ha hb)

/-- The disjunction of two Booleans, within the budget. -/
@[fun_prop]
theorem budget_boolOr {a b : α → Bool} (ha : ComputableInSpace a encIn encBool Bs)
    (hb : ComputableInSpace b encIn encBool Bs) :
    ComputableInSpace (fun x => a x || b x) encIn encBool Bs :=
  budget_finite (fun p : Bool × Bool => p.1 || p.2) (budget_prod ha hb)

/-- A function of a value of a finite type, through the canonical encoding of the value. -/
@[fun_prop]
theorem budget_finite_encFinite {f : α → β} [Finite β] (g : β → γ)
    (hf : ComputableInSpace f encIn (encFinite β) Bs) :
    ComputableInSpace (fun x => g (f x)) encIn encC Bs :=
  budget_finite g hf

/-- Equality of two values of a finite type, through the canonical encoding of the type. Not
registered with `fun_prop`; `space` tries it after the registered rules. -/
theorem budget_decideEq_encFinite [Finite β] [DecidableEq β] {f g : α → β}
    (hf : ComputableInSpace f encIn (encFinite β) Bs)
    (hg : ComputableInSpace g encIn (encFinite β) Bs) :
    ComputableInSpace (fun x => decide (f x = g x)) encIn encBool Bs :=
  budget_decideEq hf hg

/-- The conjunction of two decidable propositions, within the budget. Not registered with
`fun_prop`; `space` tries it after the registered rules. -/
theorem budget_decideAnd {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : ComputableInSpace (fun x => decide (p x)) encIn encBool Bs)
    (hq : ComputableInSpace (fun x => decide (q x)) encIn encBool Bs) :
    ComputableInSpace (fun x => decide (p x ∧ q x)) encIn encBool Bs :=
  (budget_boolAnd hp hq).of_enc_eq fun x => by simp only [Bool.decide_and]

/-- The disjunction of two decidable propositions, within the budget. Not registered with
`fun_prop`; `space` tries it after the registered rules. -/
theorem budget_decideOr {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : ComputableInSpace (fun x => decide (p x)) encIn encBool Bs)
    (hq : ComputableInSpace (fun x => decide (q x)) encIn encBool Bs) :
    ComputableInSpace (fun x => decide (p x ∨ q x)) encIn encBool Bs :=
  (budget_boolOr hp hq).of_enc_eq fun x => by simp only [Bool.decide_or]

/-- The comparison `≤` of numbers, within the budget. Not registered with `fun_prop`; `space`
tries it after the registered rules. -/
theorem budget_natLe {a b : α → ℕ} (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs) :
    ComputableInSpace (fun x => decide (a x ≤ b x)) encIn encBool Bs :=
  (budget_boolNot (budget_natLt hb ha)).of_enc_eq fun x => by
    simp only [← Nat.not_lt, decide_not]

end Turing.MultiTapeTM.ComputableInSpace
