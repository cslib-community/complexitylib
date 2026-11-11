/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.XORSAT

/-! Affine normal forms and native XOR-SAT, including degenerate systems and sparse labels. -/

open Cslib Cslib.Logic Cslib.Logic.PL Cslib.Complexity

-- Equality is a nonconstant affine relation; inequality is its other affine coset.
example (a : Fin 2 → Bool) :
    AffineEquation.Holds ([0, 1], false) a ↔ a 0 = a 1 := by
  cases h0 : a 0 <;> cases h1 : a 1 <;>
    simp [AffineEquation.Holds, h0, h1, Bool.add_eq_xor, Bool.zero_eq_false]

example (a : Fin 2 → Bool) :
    AffineEquation.Holds ([0, 1], true) a ↔ a 0 ≠ a 1 := by
  cases h0 : a 0 <;> cases h1 : a 1 <;>
    simp [AffineEquation.Holds, h0, h1, Bool.add_eq_xor, Bool.zero_eq_false]

-- Repeated occurrences cancel on every assignment, beyond the solver's concrete examples.
example (a : ℕ → Bool) :
    AffineEquation.Holds ([5, 5, 8], true) a ↔ a 8 = true := by
  rw [AffineEquation.holds_cons_cons]
  simp [AffineEquation.Holds]

-- Both nullary relations have explicit affine definitions.
example (a : Empty → Bool) :
    AffineSystem.Holds ([] : AffineSystem Empty) a ∧
      ¬AffineSystem.Holds [([], true)] a := by
  simp [AffineSystem.Holds, AffineEquation.Holds, Bool.zero_eq_false]

example : IsPolymorphism (parity 3) (∅ : Set (Empty → Bool)) := by
  intro _ ha
  exact (ha 0).elim

-- Binary disjunction fails preservation: 10, 01 and 11 sum to 00.
private theorem or_not_parity : ¬IsPolymorphism (parity 3)
    {a : Fin 2 → Bool | a 0 || a 1 = true} := by
  intro h
  have hp := isPolymorphism_parity_iff.mp h
    ![true, false] (by decide) ![false, true] (by decide) ![true, true] (by decide)
  change false = true at hp
  exact Bool.false_ne_true hp

-- Thus no conjunction of affine equations on these two coordinates defines disjunction.
example : ¬∃ F : AffineSystem (Fin 2), ∀ a, (a 0 || a 1 = true) ↔ F.Holds a := by
  intro h
  exact or_not_parity ((isPolymorphism_parity_iff_exists_affineSystem _).mpr h)

-- Empty systems and both constant equations work at width zero.
example : XORSAT.solve [] = true := by decide
example : XORSAT.solve [([], false)] = true := by decide
example : XORSAT.solve [([], true)] = false := by decide

-- An inconsistent pair and a repeated-variable contradiction are both rejected.
example : XORSAT.solve [([7], true), ([7], false)] = false := by decide
example : XORSAT.solve [([5, 5], false)] = true := by decide
example : XORSAT.solve [([5, 5], true)] = false := by decide

-- A dependent third equation becomes 0=0 or 0=1 during elimination.
example : XORSAT.solve
    [([0, 1], true), ([1, 2], true), ([0, 2], false)] = true := by decide
example : XORSAT.solve
    [([0, 1], true), ([1, 2], true), ([0, 2], true)] = false := by decide

-- Compression compares binary labels and allocates two columns, regardless of their values.
example : (XORSAT.compile [([1048576, 17, 1048576], true)]).width = 2 := by decide
example : XORSAT.solve
    [([1048576, 17, 1048576], true), ([17], false)] = false := by decide
example : XORSAT.solve
    [([1048576, 17, 1048576], true), ([17], true)] = true := by decide

-- A zero leading column is skipped; malformed dense widths are rejected.
example : XORSAT.Dense.decide ⟨2, [⟨[false, true], true⟩]⟩ = true := by decide
example : XORSAT.Dense.decide ⟨2, [⟨[true], true⟩]⟩ = false := by decide

-- `encRow` and `encInput` satisfy extensionality and expose `fun_prop` rules.
example (r₁ r₂ : XORSAT.Dense.Row) (hc : r₁.coeffs = r₂.coeffs) (hr : r₁.rhs = r₂.rhs) :
    r₁ = r₂ :=
  XORSAT.Dense.Row.ext hc hr

example (q₁ q₂ : XORSAT.Dense.Input) (hw : q₁.width = q₂.width) (hr : q₁.rows = q₂.rows) :
    q₁ = q₂ :=
  XORSAT.Dense.Input.ext hw hr

section DenseTests

open Turing.MultiTapeTM Cslib.Complexity.XORSAT.Dense

example : ComputableInPolyTime
    (fun q : Input => q.rows) encInput encSystem := by
  fun_prop

example : ComputableInPolyTime
    (fun r : Row => Row.mk r.coeffs (!r.rhs)) encRow encRow := by
  fun_prop

end DenseTests

-- The semantic endpoint produces actual models of ordinary sparse systems.
example : ∃ a : ℕ → Bool,
    AffineSystem.Holds [([0, 1], true), ([1, 2], true), ([0, 2], false)] a :=
  (XORSAT.solve_eq_true_iff _).mp (by decide)

example : ¬∃ a : ℕ → Bool, AffineSystem.Holds [([5, 5], true)] a := by
  intro h
  have ht := (XORSAT.solve_eq_true_iff _).mpr h
  have hf : XORSAT.solve [([5, 5], true)] = false := by decide
  exact Bool.false_ne_true (hf.symm.trans ht)
