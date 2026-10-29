/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Logics.Propositional.CNF.Gadgets

/-! Concrete shared-variable and private-variable tests of finite gadget assembly. -/

namespace ComplexityTests.CNFGadgets

open Cslib.Logic.PL

private def equalityGadget : CNF (Unit ⊕ Unit) :=
  [[(.inl (), false), (.inr (), true)], [(.inr (), false), (.inl (), true)]]

private def conflict (b : Bool) : CNF (Unit ⊕ Unit) := [[(.inl (), b)]]

-- Shared boundary variables with distinct private variables, repeated sites, individually
-- satisfiable gadgets conflicting on a shared variable, and empty gadget lists.
example (b : Bool) :
    CNF.glue [false, true] (fun _ => equalityGadget) =
      [[(.inl (), false), (.inr (false, ()), true)],
        [(.inr (false, ()), false), (.inl (), true)],
        [(.inl (), false), (.inr (true, ()), true)],
        [(.inr (true, ()), false), (.inl (), true)]] ∧
    (CNF.glue [false, true] (fun _ => equalityGadget)).Satisfiable ∧
    (CNF.glue [false, true] (fun _ => equalityGadget)).vars.length = 8 ∧
    CNF.glue [false, false] (fun _ => equalityGadget) =
      CNF.glue [false] (fun _ => equalityGadget) ++
        CNF.glue [false] (fun _ => equalityGadget) ∧
    (conflict b).Satisfiable ∧
    ¬(CNF.glue [false, true] conflict).Satisfiable ∧
    (CNF.glue ([] : List Empty) (fun _ => equalityGadget)).Satisfiable := by
  refine ⟨rfl, ⟨fun _ => false, by decide⟩, by decide, rfl,
    ⟨fun _ => b, by cases b <;> decide⟩, ?_, ⟨fun _ => false, rfl⟩⟩
  rintro ⟨σ, hσ⟩
  have h := (CNF.eval_glue [false, true] conflict σ).mp hσ
  have hf : σ (.inl ()) = false := by
    simpa [conflict, CNF.eval, Clause.eval, Literal.eval] using h false (by simp)
  have ht : σ (.inl ()) = true := by
    simpa [conflict, CNF.eval, Clause.eval, Literal.eval] using h true (by simp)
  exact Bool.false_ne_true (hf.symm.trans ht)

end ComplexityTests.CNFGadgets
