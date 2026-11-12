/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Inputization
import Cslib.Computability.Circuit.Boolean.Basic
import Mathlib.Tactic.FinCases

/-!
# Tests for gate inputization and projection-aware deduplication

Concrete De Morgan instances of `CslibFrontier.Computability.Circuit.Inputization`:

1. `g = (x₀ ∧ x₁, x₁, x₀ ∧ x₁)` has a projection component and a repeated component, so
   `#(nonInputComponents g) = 1`, and `C(g) = 1` since one AND gate computes it.
2. A three-gate program whose first gate is the projection `x₀ ∧ x₀` and whose last two gates both
   compute `x₀ ∧ x₁`: computing all three gates costs exactly one gate.
3. With `f = ¬x₁`, `C(g, f) = 1 + C(f | g)`, and `C(f | g) ≤ 1`.
4. Edge cases: a function made only of projections, and one with no components, cost nothing.
5. A circuit with one gate whose second output is an input wire still has a gate computing the
   non-input component of `g`.
-/

namespace CslibFrontierTests.CircuitInputization

open Cslib.Circuits Finset

private abbrev I := Boolean.interpretation

private def andFun (x : Fin 2 → Bool) : Bool := x 0 && x 1

/-- A line computing the conjunction of two wires. -/
private def andLine {n s : ℕ} (a b : Wire n s) : Line Boolean.signature n s :=
  ⟨.and, ![a, b]⟩

/-- One AND gate on the two inputs. -/
private def andProgram : Program Boolean.signature 2 1 :=
  .gate .empty (andLine (.input 0) (.input 1))

@[simp] private theorem andProgram_eval (x : Fin 2 → Bool) (t : Fin 1) :
    andProgram.eval I x t = andFun x := by
  fin_cases t
  rfl

private theorem andFun_ne_input (i : Fin 2) : andFun ≠ fun x => x i := by
  intro h
  fin_cases i
  · simpa [andFun] using congrFun h ![true, false]
  · simpa [andFun] using congrFun h ![false, true]

/-! ### A projection component and a repeated component -/

private def g : (Fin 2 → Bool) → Fin 3 → Bool := fun x => ![andFun x, x 1, andFun x]

private theorem nonInputComponents_g : nonInputComponents g = {andFun} := by
  ext h
  simp only [mem_nonInputComponents, mem_singleton]
  constructor
  · rintro ⟨⟨j, rfl⟩, hproj⟩
    fin_cases j
    · rfl
    · exact absurd rfl (hproj 1)
    · rfl
  · rintro rfl
    exact ⟨⟨0, rfl⟩, andFun_ne_input⟩

example : #(nonInputComponents g) = 1 := by
  rw [nonInputComponents_g, card_singleton]

/-- The AND gate computes every component of `g`, so `C(g)` is its number of non-input
components. -/
private theorem ecomplexity_g : ecomplexity I g = #(nonInputComponents g) := by
  refine ecomplexity_eq_card_nonInputComponents I andProgram g (fun j => ?_)
    fun t _ => ⟨0, funext fun x => by simp [g]⟩
  fin_cases j
  · exact ⟨.gate 0, funext fun x => by simp [g]⟩
  · exact ⟨.input 1, rfl⟩
  · exact ⟨.gate 0, funext fun x => by simp [g]⟩

/-- `C(g) = 1`: one AND gate, and the AND is not free. -/
example : ecomplexity I g = 1 := by
  rw [ecomplexity_g, nonInputComponents_g, card_singleton, Nat.cast_one]

/-! ### A projection gate and a duplicate gate -/

/-- Gate 0 computes `x₀ ∧ x₀ = x₀` and gate 1 computes `x₀ ∧ x₁`. -/
private def dupPrefix : Program Boolean.signature 2 2 :=
  .gate (.gate .empty (andLine (.input 0) (.input 0))) (andLine (.input 0) (.input 1))

private theorem dupPrefix_eval (x : Fin 2 → Bool) : dupPrefix.eval I x = ![x 0, andFun x] := by
  funext t
  fin_cases t
  · change dupPrefix.eval I x (Fin.castSucc (Fin.last 0)) = x 0
    rw [dupPrefix, Program.eval_gate_castSucc, Program.eval_gate_last]
    simp [andLine, Line.eval, Boolean.interpretation]
  · change dupPrefix.eval I x (Fin.last 1) = andFun x
    rw [dupPrefix, Program.eval_gate_last]
    simp [andLine, Line.eval, Boolean.interpretation, andFun]

/-- Gate 2 computes `x₁ ∧ x₀ = x₀ ∧ x₁` again, reading `x₀` through the projection gate 0. -/
private def dupProgram : Program Boolean.signature 2 3 :=
  .gate dupPrefix (andLine (.input 1) (.gate 0))

private theorem dupProgram_eval (x : Fin 2 → Bool) :
    dupProgram.eval I x = ![x 0, andFun x, andFun x] := by
  funext t
  fin_cases t
  · change dupProgram.eval I x (Fin.castSucc 0) = x 0
    rw [dupProgram, Program.eval_gate_castSucc, dupPrefix_eval]
    rfl
  · change dupProgram.eval I x (Fin.castSucc 1) = andFun x
    rw [dupProgram, Program.eval_gate_castSucc, dupPrefix_eval]
    rfl
  · change dupProgram.eval I x (Fin.last 2) = andFun x
    rw [dupProgram, Program.eval_gate_last]
    simp [andLine, Line.eval, Boolean.interpretation, andFun, dupPrefix_eval, Bool.and_comm]

private theorem nonInputComponents_dupProgram :
    nonInputComponents (dupProgram.eval I) = {andFun} := by
  ext h
  simp only [mem_nonInputComponents, mem_singleton, dupProgram_eval]
  constructor
  · rintro ⟨⟨j, rfl⟩, hproj⟩
    fin_cases j
    · exact absurd rfl (hproj 0)
    · rfl
    · rfl
  · rintro rfl
    exact ⟨⟨1, rfl⟩, andFun_ne_input⟩

/-- Three gates, but computing all of them costs one gate. -/
example : ecomplexity I (dupProgram.eval I) = 1 := by
  rw [ecomplexity_eval_eq_card_nonInputComponents, nonInputComponents_dupProgram, card_singleton,
    Nat.cast_one]

/-! ### Computing `g` together with another function -/

private def notLast : (Fin 2 → Bool) → Fin 1 → Bool := fun x _ => !x 1

/-- `C(g, ¬x₁) = 1 + C(¬x₁ | g)`. -/
example : ecomplexity I (fun x => Fin.append (g x) (notLast x)) =
    1 + ecomplexityGiven I notLast g := by
  rw [ecomplexity_append_eq_card_nonInputComponents_add_ecomplexityGiven I notLast
    ecomplexity_g.le, nonInputComponents_g, card_singleton, Nat.cast_one]

/-- `¬x₁` costs one gate given `g`. -/
example : ecomplexityGiven I notLast g ≤ 1 := by
  refine (ecomplexityGiven_le_of_eval notLast g
    ⟨.gate .empty ⟨Boolean.Op.not, ![Wire.input (Fin.natAdd 2 1)]⟩, fun _ => .gate (Fin.last 0)⟩
    fun x => ?_).trans (by simp)
  funext j
  simp only [Circuit.eval, Function.comp_apply, Program.trace, Wire.elim_gate,
    Program.eval_gate_last]
  -- The `¬` gate reads the second value of `g`, which is `x₁`.
  simp only [Line.eval]
  rfl

/-! ### Edge cases -/

/-- A function made only of input projections has no non-input components and costs nothing. -/
example : ecomplexity I (fun x : Fin 2 → Bool => ![x 1, x 0, x 1]) = 0 := by
  have hempty : nonInputComponents (fun x : Fin 2 → Bool => ![x 1, x 0, x 1]) = ∅ := by
    refine eq_empty_of_forall_notMem fun h hh => ?_
    obtain ⟨⟨j, rfl⟩, hproj⟩ := mem_nonInputComponents.mp hh
    fin_cases j
    · exact hproj 1 rfl
    · exact hproj 0 rfl
    · exact hproj 1 rfl
  rw [ecomplexity_eq_card_nonInputComponents I (.empty : Program Boolean.signature 2 0) _, hempty,
    card_empty, Nat.cast_zero]
  · intro j
    fin_cases j
    · exact ⟨.input 1, rfl⟩
    · exact ⟨.input 0, rfl⟩
    · exact ⟨.input 1, rfl⟩
  · exact fun t => t.elim0

/-- No components: nothing to count. -/
example : #(nonInputComponents (fun _ : Fin 2 → Bool => (Fin.elim0 : Fin 0 → Bool))) = 0 :=
  Nat.le_zero.mp (card_nonInputComponents_le _)

/-- A circuit with one gate whose second output is the input wire `x₁`: its gate computes the one
non-input component of `g`. -/
example : 1 ≤ #((⟨andProgram, ![.gate 0, .input 1]⟩ : Circuit Boolean.signature 2 2).program
    |>.componentGates I g) := by
  have h := Circuit.card_nonInputComponents_le_card_componentGates
    (⟨andProgram, ![.gate 0, .input 1]⟩ : Circuit Boolean.signature 2 2) (I := I) (g := g)
    fun j => by
      fin_cases j
      · exact ⟨0, fun x => by simp [Circuit.eval, Program.trace, g]⟩
      · exact ⟨1, fun x => by simp [Circuit.eval, Program.trace, g]⟩
      · exact ⟨0, fun x => by simp [Circuit.eval, Program.trace, g]⟩
  rwa [nonInputComponents_g, card_singleton] at h

end CslibFrontierTests.CircuitInputization
