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

-- Two sites share the boundary variable but have different private variables.
example : CNF.glue [false, true] (fun _ => equalityGadget) =
    [[(.inl (), false), (.inr (false, ()), true)],
      [(.inr (false, ()), false), (.inl (), true)],
      [(.inl (), false), (.inr (true, ()), true)],
      [(.inr (true, ()), false), (.inl (), true)]] := rfl

example : (CNF.glue [false, true] (fun _ => equalityGadget)).Satisfiable :=
  ⟨fun _ => false, by decide⟩

example : (CNF.glue [false, true] (fun _ => equalityGadget)).vars.length = 8 := by decide

-- A repeated site repeats constraints, retaining the same private-variable names.
example : CNF.glue [false, false] (fun _ => equalityGadget) =
    CNF.glue [false] (fun _ => equalityGadget) ++
      CNF.glue [false] (fun _ => equalityGadget) := rfl

private def conflict (b : Bool) : CNF (Unit ⊕ Unit) := [[(.inl (), b)]]

-- The gadgets are individually satisfiable; they cannot disagree on a shared variable.
example (b : Bool) : (conflict b).Satisfiable :=
  ⟨fun _ => b, by cases b <;> decide⟩

example : ¬(CNF.glue [false, true] conflict).Satisfiable := by
  rintro ⟨σ, hσ⟩
  have h := (CNF.eval_glue [false, true] conflict σ).mp hσ
  have hf : σ (.inl ()) = false := by
    simpa [conflict, CNF.eval, Clause.eval, Literal.eval] using h false (by simp)
  have ht : σ (.inl ()) = true := by
    simpa [conflict, CNF.eval, Clause.eval, Literal.eval] using h true (by simp)
  exact Bool.false_ne_true (hf.symm.trans ht)

-- No gadgets impose no constraints, even when the index type is empty.
example : (CNF.glue ([] : List Empty) (fun _ => equalityGadget)).Satisfiable :=
  ⟨fun _ => false, rfl⟩

end ComplexityTests.CNFGadgets
