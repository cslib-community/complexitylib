/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Mathlib.Tactic.FunProp

/-!
# Composing computations within a fixed workspace budget

The `fun_prop` rules in this module preserve the budget in `ComputableInSpace`. They compose
existing arithmetic, list, option and conditional certificates. Composition uses a routine
whose workspace is linear in its own encoded argument; the caller's certificate pays for that
argument. No rule infers a bound on the states of an iteration.

Constants and the identity require the input encoding length to fit the requested budget.
That side condition is explicit, including when the budget is not the input length.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

attribute [fun_prop] ComputableInSpace
attribute [fun_prop] budget_comp_linear budget_prod fst' snd' budget_ite budget_const
attribute [fun_prop] budget_natSucc budget_natPred budget_natIsZero budget_natEq
  budget_natAdd budget_natMul budget_natDiv budget_natSub budget_natMod budget_natLt budget_natPow
attribute [fun_prop] budget_cons budget_snoc budget_headD budget_tail budget_isEmpty budget_length
  budget_optionSome budget_optionGetD budget_optionIsSome

/-- Copy an encoded value when the caller's budget covers its input length. -/
@[fun_prop]
theorem budget_id {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    (h : (fun a => (enc a).length) ≼ S) : ComputableInSpace (fun a => a) enc enc S :=
  (of_inO (ComputableInO.of_eq fun _ => rfl)).weaken h

end Turing.MultiTapeTM.ComputableInSpace
