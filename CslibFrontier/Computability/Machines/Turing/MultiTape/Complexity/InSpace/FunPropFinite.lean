/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp

/-!
# Finite values and conditions within a fixed workspace budget

These `fun_prop` rules extend those of `InSpace.FunProp` to values of finite types. A function of
a value of a finite type (`budget_finite`) costs no workspace beyond the value. Conditions may be
decidable propositions (`budget_iteProp`), equalities on a finite type (`budget_decideEq`) or
Boolean connectives.

The rules reach `fun_prop` only where this module is imported, directly or through
`CslibFrontier.Tactic.Space`. A direct `fun_prop` client that needs them imports this module.

The intermediate encoding of `budget_finite` is not determined by its goal. When the finite value
is a projection of a hypothesis, state that projection first, for example
`have := budget_finite (encC := encFinEnum Guard) Ref.guardOf hr`.

## Main results

* `budget_iteProp`, `budget_decideEq`: decidable conditions within the budget.
* `budget_boolNot`, `budget_boolAnd`, `budget_boolOr`: Boolean connectives within the budget.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

attribute [fun_prop] budget_finite budget_finMod

variable {α β : Type} {encIn : α ↪ List Bool} {encB : β ↪ List Bool} {Bs : α → ℕ}

/-- A conditional on a decidable proposition, within the budget. -/
@[fun_prop]
theorem budget_iteProp {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hc : ComputableInSpace (fun x => decide (p x)) encIn encBool Bs)
    (hf : ComputableInSpace f encIn encB Bs) (hg : ComputableInSpace g encIn encB Bs) :
    ComputableInSpace (fun x => if p x then f x else g x) encIn encB Bs :=
  (budget_ite hc hf hg).of_enc_eq fun x => by simp only [decide_eq_true_eq]

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

end Turing.MultiTapeTM.ComputableInSpace
