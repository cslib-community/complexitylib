/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-! Charged-space budget clients: reachable-state iteration, output charge and removed API. -/

open Lean Elab Command in
run_cmd do
  for name in #[
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_comp,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_comp_lin,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_comp_linear,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_cons,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_const,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_finMod,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_finite,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_headD,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_isEmpty,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_ite,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_iterate,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_length,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_natAdd,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_natDiv,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_natEq,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_natIsZero,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_natLt,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_natMod,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_natMul,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_natPow,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_natPred,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_natSub,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_natSucc,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_optionSome,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_prod,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.budget_tail,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.dispatch,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.divStep,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.divStep_inSpace,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.encSetState,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.foldl_setStep,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.getD,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.iterate_cons,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.iterate_divStep,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.iterate_divStep_self,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.length,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.length_encList_set_le,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.linear_mul,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.linear_succ,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.natAdd,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.natDiv,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.natDivMod,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.natEq,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.natIsZero,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.natLt,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.natMod,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.natMul,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.natPred,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.natSub,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.natSucc,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.replicate,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.set,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.setStep,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.setStep_inSpace,
      `Turing.MultiTapeTM.ComputableTidilyInSpace.set_eq_mapIdx] do
    if (← getEnv).contains name then
      throwError "Retired space compatibility declaration was imported: {name}"

open Turing.MultiTapeTM ComputableInSpace

/-- Counting from zero retains the bound on every reachable state, including the final state. -/
example : ComputableInSpace (fun n : ℕ => (· + 1)^[n] 0) encNat encNat
    (fun n => (encNat n).length) := by
  have hid : ComputableInSpace (id : ℕ → ℕ) encNat encNat
      (fun n => (encNat n).length) := of_inO (.of_eq fun _ => rfl)
  have hstep := natSucc.weaken linear_succ
  apply budget_iterate hid (budget_const 0 (.refl _)) hstep
    (B := fun n => (encNat n).length) _ (.refl _)
  intro n k hk
  simpa only [id, ComputableInO.iterate_succ_eq, zero_add, length_encNat_eq_size] using
    Nat.size_le_size hk

/-- The same growing loop cannot be justified with an empty reachable-state window. -/
example : ¬(∀ n k : ℕ, k ≤ n → (encNat ((· + 1)^[k] 0)).length ≤ 0) := by
  intro h
  exact (by decide : ¬(encNat ((· + 1)^[1] 0)).length ≤ 0) (h 1 1 le_rfl)

example : (· + 1)^[0] (0 : ℕ) = 0 ∧ (· + 1)^[17] (0 : ℕ) = 17 := by decide

/-- A zero-workspace streaming copy cannot satisfy a constant charged-space certificate. -/
example : ¬ComputableInSpace (id : List Bool → List Bool) encBits encBits (fun _ => 0) := by
  rintro ⟨_, c, _, hl⟩
  simpa [encBits] using hl (List.replicate (c + 1) true)

/-- Budget composition uses both independent operands; no certificate can be inferred for an
arbitrary second function. -/
example {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {f g : α → ℕ}
    (hf : ComputableInSpace f enc encNat S) (hg : ComputableInSpace g enc encNat S) :
    ComputableInSpace (fun a => (f a / g a, f a % g a, f a * g a)) enc
      (encPair encNat (encPair encNat encNat)) S := by
  fail_if_success
    have : ComputableInSpace (fun a => f a / g a) enc encNat S := budget_natDiv hf hf
  exact budget_prod (budget_natDiv hf hg)
    (budget_prod (budget_natMod hf hg) (budget_natMul hf hg))

example : (17 / 0, 17 % 0, 17 * 0) = (0, 17, 0) ∧
    ([1, 2, 3] : List ℕ).set 1 5 = [1, 5, 3] ∧
    ([1, 2, 3] : List ℕ).set 4 5 = [1, 2, 3] := by decide
