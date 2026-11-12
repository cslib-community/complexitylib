/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Formula
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting the restrictions of a formula

A formula over Boolean values that has `a` leaves labelled by inputs in a set `U` takes at most
`2 ^ a` forms as a function of the other inputs, when the inputs in `U` are fixed in all possible
ways (`Formula.card_image_eval_piecewise_le`). Each leaf in `U` contributes one bit, and an
operation node combines the forms of its arguments. Rows of a communication matrix given by a
formula are counted this way, as in [ChukhinKulikovMihajlinSmal2026], proof of Theorem 1.5.

## Main results

* `Cslib.Circuits.Formula.card_image_eval_piecewise_le`: at most `2 ^ a` restrictions.
-/

public section

namespace Cslib.Circuits.Formula

variable {σ : Signature} {n : ℕ}

open Classical in
/-- A formula over Boolean values has at most `2 ^ a` distinct restrictions to the inputs in `U`,
for `a` its leaves in `U`: as functions of the other inputs, the values `F (U.piecewise x y)` for
varying `x` take at most `2 ^ a` forms. -/
theorem card_image_eval_piecewise_le (I : Interpretation σ Bool) (U : Finset (Fin n))
    (F : Formula σ n) :
    (Finset.univ.image fun x : Fin n → Bool => fun y => F.eval I (U.piecewise x y)).card ≤
      2 ^ F.leafSizeIn U := by
  induction F with
  | input i =>
    by_cases hi : i ∈ U
    · simp only [eval_input, Finset.piecewise_eq_of_mem _ _ _ hi, leafSizeIn_input, hi,
        ite_true, pow_one]
      calc _ ≤ (Finset.univ.image fun b : Bool => fun _ : Fin n → Bool => b).card :=
            Finset.card_le_card fun g hg => by
              obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hg
              exact Finset.mem_image.2 ⟨x i, Finset.mem_univ _, rfl⟩
        _ ≤ 2 := Finset.card_image_le.trans (by simp)
    · simp only [eval_input, Finset.piecewise_eq_of_notMem _ _ _ hi, leafSizeIn_input, hi,
        ite_false, pow_zero]
      exact Finset.card_le_one.2 fun a ha b hb => by
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨x', -, rfl⟩ := Finset.mem_image.1 hb
        rfl
  | gate op args ih =>
    simp only [eval_gate, leafSizeIn_gate]
    set T : (j : Fin (σ.Arity op)) → Finset ((Fin n → Bool) → Bool) := fun j =>
      Finset.univ.image fun x : Fin n → Bool => fun y => (args j).eval I (U.piecewise x y)
    calc _ ≤ ((Fintype.piFinset T).image fun g => fun y => I op fun j => g j y).card :=
          Finset.card_le_card fun g hg => by
            obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hg
            exact Finset.mem_image.2 ⟨fun j => fun y => (args j).eval I (U.piecewise x y),
              Fintype.mem_piFinset.2 fun j => Finset.mem_image.2 ⟨x, Finset.mem_univ _, rfl⟩,
              rfl⟩
      _ ≤ (Fintype.piFinset T).card := Finset.card_image_le
      _ = ∏ j, (T j).card := Fintype.card_piFinset T
      _ ≤ ∏ j, 2 ^ (args j).leafSizeIn U := Finset.prod_le_prod fun j _ => ih j
      _ = 2 ^ ∑ j, (args j).leafSizeIn U := Finset.prod_pow_eq_pow_sum _ _ _

end Cslib.Circuits.Formula
