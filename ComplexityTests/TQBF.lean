/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Space.TQBF
import Complexity.Computability.Complexity.Classes.Space.TQBF.PolyTime
import Complexity.Computability.Complexity.Classes.Space.Savitch

/-!
# Tests: `TQBF` is `PSPACE`-complete

Concrete true and false closed formulas, prenex and not, with shadowed quantifiers and formulas
without variables; formulas with a free variable, which are never in `TQBF` even when valid; the
empty and zero-variable boundaries of the derived connectives; the encoding of a formula; complete
runs of the explicit-stack evaluator, including the flag for an unbound variable and an exhausted
input; Savitch's formula on concrete graphs, true and false, and on words of width zero; reductions
of concrete classes to `TQBF`; and the axioms of the headline theorems.
-/

namespace ComplexityTests.TQBF

open Cslib Cslib.Complexity Cslib.Logic.PL Cslib.Complexity.TQBF Cslib.Reachability
open Turing.MultiTapeTM (encBits ComputableTidilyInPolyTime)

/-- `∀ x, ∃ y, x ↔ y`, with `x = 0` and `y = 1`. -/
private def forallExistsIff : QBF ℕ := .all 0 (.ex 1 (QBF.iff (.var 0) (.var 1)))

/-- `∃ x, ∀ y, x ↔ y`. -/
private def existsForallIff : QBF ℕ := .ex 0 (.all 1 (QBF.iff (.var 0) (.var 1)))

/-! ### Concrete formulas -/

example : forallExistsIff ∈ TQBF := ⟨by decide, rfl⟩

example : existsForallIff ∉ TQBF := fun h => absurd h.2 (by decide)

/-- A formula not in prenex form: `(∃ x, x) ∧ ¬∀ y, y`. -/
example : (QBF.ex 0 (.var 0)).and (QBF.all 1 (.var 1)).not ∈ TQBF := ⟨by decide, rfl⟩

/-- The inner quantifier shadows the outer one: `∃ x, ∀ x, x` is false and `∀ x, ∃ x, x` is true. -/
example : QBF.ex 0 (.all 0 (.var 0)) ∉ TQBF := fun h => absurd h.2 (by decide)

example : QBF.all 0 (.ex 0 (.var 0)) ∈ TQBF := ⟨by decide, rfl⟩

/-- A valid formula with a free variable is not in `TQBF`. -/
example : (QBF.var 0).or (QBF.var 0).not ∉ TQBF := fun h => absurd h.1 (by decide)

/-- A free variable under a quantifier over another variable. -/
example : QBF.all 1 ((QBF.var 0).or (QBF.var 0).not) ∉ TQBF := fun h => absurd h.1 (by decide)

/-! ### Formulas without variables and empty connectives -/

example : QBF.top ∈ TQBF := top_mem_TQBF

example : QBF.bot ∉ TQBF := bot_notMem_TQBF

example : QBF.var 7 ∉ TQBF := var_notMem_TQBF 7

example : (QBF.top.and QBF.bot).not ∈ TQBF := ⟨by decide, rfl⟩

/-- A quantifier over a variable that does not occur. -/
example : QBF.all 3 QBF.top ∈ TQBF := ⟨by decide, rfl⟩

example : QBF.conj ([] : List (QBF ℕ)) = .top := rfl

example : QBF.ofClause ([] : Clause ℕ) = .bot := rfl

example : QBF.ofCNF ([] : CNF ℕ) = .top := rfl

example : QBF.ofCNF [[]] ∉ TQBF := fun h => absurd h.2 (by decide)

example (φ : QBF ℕ) : QBF.exs [] φ = φ := rfl

example (φ : QBF ℕ) : QBF.alls [] φ = φ := rfl

/-! ### The encoding -/

example : QBF.top.tokens = [(.top, 0)] := rfl

example : encQBF .top = [true, true, true, true, true, false, false] := rfl

example : forallExistsIff.tokens = [(.all, 0), (.ex, 1), (.or, 0), (.and, 0), (.var, 0), (.var, 1),
    (.and, 0), (.not, 0), (.var, 0), (.not, 0), (.var, 1)] := rfl

/-- No formula has an empty encoding. -/
example (φ : QBF ℕ) : encQBF φ ≠ [] := by
  intro h
  have := three_mul_length_tokens_le φ
  rw [h] at this
  exact QBF.tokens_ne_nil φ (List.eq_nil_of_length_eq_zero (by simpa using this))

example : encQBF existsForallIff ≠ encQBF forallExistsIff :=
  fun h => absurd (encQBF.injective h) (by decide)

/-! ### Runs of the evaluator -/

example : callSteps forallExistsIff = 77 := by decide

/-- The complete run on `∀ x, ∃ y, x ↔ y` returns `true`, with every variable bound. -/
example : step^[77] (init forallExistsIff) = ⟨[], [], some true, true⟩ := rfl

/-- The complete run on `∃ x, ∀ y, x ↔ y` returns `false`. -/
example : step^[77] (init existsForallIff) = ⟨[], [], some false, true⟩ := rfl

/-- A run on `∃ x, x` reads both passes of the quantifier. -/
example : step^[5] (init (.ex 0 (.var 0))) = ⟨[], [], some true, true⟩ := rfl

/-- An unbound variable clears the flag. -/
example : step (init (.var 3)) = ⟨[], [], some false, false⟩ := rfl

example : (step^[7] (init ((QBF.var 0).or (QBF.var 0).not))).answer = false := rfl

/-- Reading past the end of the input returns `false`. -/
example : step ⟨[], [], none, true⟩ = ⟨[], [], some false, true⟩ := rfl

example : evaluate forallExistsIff = true := evaluate_eq_true_iff.mpr ⟨by decide, rfl⟩

example : evaluate existsForallIff = false := by
  rw [evaluate_eq]
  decide

/-- The evaluator runs long enough on every formula. -/
example (φ : QBF ℕ) : callSteps φ ≤ 2 ^ (encQBF φ).length := callSteps_le φ

/-- The states of every run are small. -/
example (n : ℕ) :
    (encState (step^[n] (init forallExistsIff))).length ≤
      16 * ((encQBF forallExistsIff).length + 1) ^ 2 :=
  length_encState_le (good_iterate_step _ n)

/-! ### Savitch's formula on concrete graphs -/

/-- On words of width `1` with every edge, `top` is a formula of level `0`. -/
private theorem base_top (σ : ℕ → Bool) :
    QBF.top.eval σ = reach (fun _ _ => true) 1 0 (block σ 1 0 0) (block σ 1 1 0) := by
  simp [reach]

private theorem freeVars_top :
    ∀ x ∈ (QBF.top : QBF ℕ).freeVars, x ∈ blockVars 1 0 0 ∨ x ∈ blockVars 1 1 0 := by
  simp

example : savitchFormula 1 1 .top [false] [true] ∈ TQBF := by
  rw [mem_TQBF_iff_of_closed (closed_savitchFormula freeVars_top 1 _ _) (fun _ => false),
    eval_savitchFormula base_top 1 rfl rfl]
  decide

/-- On words of width `1` without edges, equality of the blocks is a formula of level `0`. -/
private theorem base_eq (σ : ℕ → Bool) :
    (eqBlock 1 0 0 1 0).eval σ = reach (fun _ _ => false) 1 0 (block σ 1 0 0) (block σ 1 1 0) := by
  simp [reach, eval_eqBlock]

private theorem freeVars_eq :
    ∀ x ∈ (eqBlock 1 0 0 1 0).freeVars, x ∈ blockVars 1 0 0 ∨ x ∈ blockVars 1 1 0 :=
  fun _ hx => mem_freeVars_eqBlock hx

/-- Without edges, `[true]` is not reachable from `[false]`, at any depth. -/
example : savitchFormula 1 2 (eqBlock 1 0 0 1 0) [false] [true] ∉ TQBF := by
  rw [mem_TQBF_iff_of_closed (closed_savitchFormula freeVars_eq 2 _ _) (fun _ => false),
    eval_savitchFormula base_eq 2 rfl rfl]
  decide

/-- Without edges, every word is reachable from itself. -/
example : savitchFormula 1 2 (eqBlock 1 0 0 1 0) [true] [true] ∈ TQBF := by
  rw [mem_TQBF_iff_of_closed (closed_savitchFormula freeVars_eq 2 _ _) (fun _ => false),
    eval_savitchFormula base_eq 2 rfl rfl]
  decide

/-- Words of width zero: the blocks have no variables, and the empty word reaches itself. -/
example : savitchFormula 0 3 .top [] [] ∈ TQBF := by
  have hbase (σ : ℕ → Bool) :
      QBF.top.eval σ = reach (fun _ _ => false) 0 0 (block σ 0 0 0) (block σ 0 1 0) := by
    simp [reach, block, blockVars]
  rw [mem_TQBF_iff_of_closed (closed_savitchFormula (by simp) 3 _ _) (fun _ => false),
    eval_savitchFormula hbase 3 rfl rfl]
  decide

example (w : ℕ) (base : QBF ℕ) : midpoint w base 0 = base := rfl

/-! ### Reductions to `TQBF` -/

example {α : Type} (enc : α ↪ List Bool) (A : Set α) (hA : A ∈ P enc) :
    PolyTimeReducible enc encQBF A TQBF :=
  TQBF_pspaceHard enc A (P_subset_PSPACE hA)

example {α : Type} (enc : α ↪ List Bool) (A : Set α) (hA : A ∈ NPSPACE enc) :
    PolyTimeReducible enc encQBF A TQBF :=
  TQBF_pspaceHard enc A (NPSPACE_subset_PSPACE hA)

example : PolyTimeReducible encBits encQBF (∅ : Set (List Bool)) TQBF :=
  TQBF_pspaceHard encBits ∅
    (P_subset_PSPACE ⟨fun _ => false, .const false, fun _ => by simp⟩)

/-- `PSPACE`-hardness of `TQBF` transfers to every problem `TQBF` reduces to, `TQBF` itself
included. -/
example : PSPACEHard encQBF TQBF :=
  TQBF_pspaceHard.trans (PolyTimeReducible.refl encQBF TQBF)

example : PSPACEComplete encQBF TQBF := TQBF_pspaceComplete

/-! ### Axioms -/

/--
info: 'Cslib.Logic.PL.QBF.tokens_append_inj' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.QBF.tokens_append_inj

/--
info: 'Cslib.Complexity.TQBF.evaluate_eq_true_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.TQBF.evaluate_eq_true_iff

/--
info: 'Cslib.Complexity.TQBF.exists_computableInO_evaluate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.TQBF.exists_computableInO_evaluate

/--
info: 'Cslib.Complexity.TQBF_mem_PSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.TQBF_mem_PSPACE

/--
info: 'Cslib.Complexity.TQBF.eval_savitchFormula' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.TQBF.eval_savitchFormula

/--
info: 'Cslib.Complexity.TQBF.closed_savitchFormula' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.TQBF.closed_savitchFormula

/--
info: 'Cslib.Complexity.CookLevin.exists_eval_tableau_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.exists_eval_tableau_iff

/--
info: 'Cslib.Complexity.TQBF.reduce_mem_TQBF_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.TQBF.reduce_mem_TQBF_iff

/--
info: 'Cslib.Complexity.TQBF.computableInPolyTime_reduce' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.TQBF.computableInPolyTime_reduce

/--
info: 'Cslib.Complexity.TQBF.computableInPolyTime_edgeTest' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.TQBF.computableInPolyTime_edgeTest

/--
info: 'Cslib.Complexity.TQBF_pspaceHard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.TQBF_pspaceHard

/--
info: 'Cslib.Complexity.TQBF_pspaceComplete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.TQBF_pspaceComplete

end ComplexityTests.TQBF
