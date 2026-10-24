/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Formula
public import Complexity.Computability.Circuit.Evaluation
public import Complexity.Foundations.Data.BitString.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Shared Boolean minterms

The circuit computes the indicator of every assignment to its input bits. Each stage retains
the preceding minterms and extends them by one new bit. Sharing the preceding table gives a
linear bound in the number of assignments, including all constants and negations.

## Main definitions

* `Cslib.Circuits.Boolean.mintermExtension`: one-step formula extending a tail minterm by testing
  the head bit.
* `Cslib.Circuits.Boolean.mintermCircuit`: all assignment indicators in `BitString.equivFin` order.

## Main results

* `Cslib.Circuits.Boolean.eval_mintermCircuit`: the output is the indicator of the input's index.
* `Cslib.Circuits.Boolean.size_mintermCircuit_add_three_le`: at most `4 * 2 ^ n - 3` gates.

## References

* Adapted from MassProduction/ShannonCircuit.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- One extension reads a preceding minterm and tests the new head bit. -/
def mintermExtension (n : ℕ) (a : Fin (2 ^ (n + 1))) : Formula signature (2 ^ n + 1) :=
  (Formula.input
    (Fin.castAdd 1 (BitString.equivFin n (Fin.tail ((BitString.equivFin _).symm a))))).and
    (if (BitString.equivFin _).symm a 0 then Formula.input (Fin.last (2 ^ n))
     else (Formula.input (Fin.last (2 ^ n))).not)

private theorem size_mintermExtension_le (n : ℕ) (a : Fin (2 ^ (n + 1))) :
    (mintermExtension n a).size ≤ 2 := by
  unfold mintermExtension
  cases (BitString.equivFin (n + 1)).symm a 0 <;> simp

/-- Shared indicators of all `n`-bit assignments, indexed least significant bit first. -/
def mintermCircuit : (n : ℕ) → Circuit signature n (2 ^ n)
  | 0 => (Formula.const true).toCircuit
  | n + 1 =>
    (Circuit.pi fun a => (mintermExtension n a).toCircuit).comp
      (((mintermCircuit n).comp (Circuit.wiring signature Fin.succ)).append
        (Circuit.wiring signature fun _ : Fin 1 => (0 : Fin (n + 1))))

/-- A complete assignment is determined by its head and tail. -/
private theorem assignment_eq_iff {n : ℕ} (x : BitString (n + 1))
    (a : Fin (2 ^ (n + 1))) :
    BitString.equivFin (n + 1) x = a ↔
      BitString.equivFin n (Fin.tail x) =
        BitString.equivFin n (Fin.tail ((BitString.equivFin _).symm a)) ∧
      x 0 = (BitString.equivFin _).symm a 0 := by
  rw [← Equiv.eq_symm_apply, Equiv.apply_eq_iff_eq]
  constructor
  · intro h
    subst x
    exact ⟨rfl, rfl⟩
  · rintro ⟨ht, hh⟩
    rw [← Fin.cons_self_tail x, ht, hh, Fin.cons_self_tail]

/-- Each output is true precisely for the assignment bearing that index. -/
@[simp] theorem eval_mintermCircuit (n : ℕ) (x : BitString n) (a : Fin (2 ^ n)) :
    (mintermCircuit n).eval interpretation x a = decide (BitString.equivFin n x = a) := by
  induction n with
  | zero =>
    have h : BitString.equivFin 0 x = a := Subsingleton.elim (α := Fin 1) _ _
    simp [mintermCircuit, h]
  | succ n ih =>
    simp only [mintermCircuit, Circuit.eval_comp, Circuit.eval_pi, Formula.eval_toCircuit]
    simp only [mintermExtension, Formula.eval_and, Circuit.eval_append, Circuit.eval_comp,
      Circuit.eval_wiring, Formula.eval_input, Fin.append_left, ih]
    have hlast : Fin.last (2 ^ n) = Fin.natAdd (2 ^ n) (0 : Fin 1) := rfl
    cases hb : (BitString.equivFin (n + 1)).symm a 0 <;>
      simp [hb, hlast, Formula.eval_not, Formula.eval_input, assignment_eq_iff, Fin.tail_def,
        Function.comp_def]

/-- All minterms together use at most `4 * 2 ^ n - 3` gates, counting constants too. -/
theorem size_mintermCircuit_add_three_le (n : ℕ) :
    (mintermCircuit n).size + 3 ≤ 4 * 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hsum : (∑ a : Fin (2 ^ (n + 1)), (mintermExtension n a).size) ≤ 2 * 2 ^ (n + 1) := by
      simpa [Nat.mul_comm] using Finset.sum_le_sum
        (s := Finset.univ) (f := fun a => (mintermExtension n a).size) (g := fun _ => 2)
        (fun a _ => size_mintermExtension_le n a)
    simp only [mintermCircuit, Circuit.size_comp, Circuit.size_append, Circuit.size_wiring,
      Circuit.size_pi, Formula.size_toCircuit, Nat.add_zero]
    have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ _ _
    lia

end Cslib.Circuits.Boolean
