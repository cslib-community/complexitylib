/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.Propagation
import CslibFrontier.Computability.Circuit.Evaluation
import CslibFrontier.Foundations.Data.BitString.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Order.PiLex

/-!
# Segmented propagation clients

Check resets, the ignored first link, multiple sources, sorted equal-key runs, empty inputs,
and distinct operation weights. Exhaustive circuit checks use the connected-source
characterization independently of the functional recurrence.
-/

namespace CslibFrontierTests.Propagation

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

example (source link : ℕ → Bool) : BitString.propagate source link 0 = false := rfl

example (source link : ℕ → Bool) : BitString.propagate source link 1 = source 0 := by
  simp [BitString.propagate]

private def keys (i : ℕ) : ℕ := if i < 6 then i / 2 else 0

-- Only the processed prefix must be sorted; the key drops back to zero afterward.
example (source : ℕ → Bool) :
    BitString.propagate source (BitString.keyLinks keys) 6 = true ↔
      ∃ start, start < 6 ∧ source start = true ∧ keys start = keys 5 := by
  apply BitString.propagate_sorted_eq_true_iff keys source 6
  intro a ha b hb hab
  change a < 6 at ha
  change b < 6 at hb
  simp only [keys, ite_eq_left ha, ite_eq_left hb]
  exact Nat.div_le_div_right hab

-- The executable equality test can be chosen independently of the order instance.
example {κ : Type*} [LinearOrder κ] [DecidableEq κ] (key : ℕ → κ)
    (source : ℕ → Bool) (count : ℕ) (sorted : MonotoneOn key (Set.Iio count)) :
    BitString.propagate source (BitString.keyLinks key) count = true ↔
      ∃ start, start < count ∧ source start = true ∧ key start = key (count - 1) := by
  rw [BitString.propagate_sorted_eq_true_iff key source count sorted]

-- Lexicographic keys have their own inferred equality; an ordinary lambda needs no transport.
example {k : ℕ} (key : ℕ → BitString k) (source : ℕ → Bool) (count : ℕ)
    (sorted : MonotoneOn (fun i => toLex (key i)) (Set.Iio count)) :
    BitString.propagate source (BitString.keyLinks (fun i => toLex (key i))) count = true ↔
      ∃ start, start < count ∧ source start = true ∧ key start = key (count - 1) := by
  rw [BitString.propagate_sorted_eq_true_iff _ _ _ sorted]
  simp only [toLex_inj]

-- Composition spelling uses the same theorem and inferred equality.
example {k : ℕ} (key : ℕ → BitString k) (source : ℕ → Bool) (count : ℕ)
    (sorted : MonotoneOn (toLex ∘ key) (Set.Iio count)) :
    BitString.propagate source (BitString.keyLinks (toLex ∘ key)) count = true ↔
      ∃ start, start < count ∧ source start = true ∧ key start = key (count - 1) := by
  rw [BitString.propagate_sorted_eq_true_iff _ _ _ sorted]
  simp only [Function.comp_apply, toLex_inj]

example {n : ℕ} (source link : BitString n) (j : Fin n) :
    (propagateCircuit n).eval interpretation (Fin.append source link) j = true ↔
      ∃ start : Fin n, start ≤ j ∧ source start = true ∧
        ∀ i : Fin n, start < i → i ≤ j → link i = true :=
  eval_propagateCircuit_eq_true_iff source link j

example (n : ℕ) : (propagateCircuit n).size = 1 + 2 * n := size_propagateCircuit n

example : (propagateCircuit 0).program.cost (fun _ => 11) = 11 := rfl

/-- info: #[true, true, false, true, true] -/
#guard_msgs in
#eval ((propagateCircuit 5).evalVector interpretation
  (Fin.append ![true, false, false, true, false] ![false, true, false, true, true])).toArray

-- No sources: even a fully linked run remains false.
/-- info: #[false, false, false, false] -/
#guard_msgs in
#eval ((propagateCircuit 4).evalVector interpretation
  (Fin.append ![false, false, false, false] ![true, true, true, true])).toArray

/-- info: #[] -/
#guard_msgs in
#eval ((propagateCircuit 0).evalVector interpretation Fin.elim0).toArray

/-- info: 51 -/
#guard_msgs in
#eval (propagateCircuit 5).program.cost fun
  | .const false => 11
  | .const true => 13
  | .not => 7
  | .and => 3
  | .or => 5

-- All source/link arrays of lengths zero through six: 5461 circuit evaluations.
/-- info: true -/
#guard_msgs in
#eval
  (List.range 7).all fun n =>
    let c := propagateCircuit n
    (List.finRange (2 ^ (n + n))).all fun raw =>
      let input := (BitString.equivFin (n + n)).symm raw
      let output := (c.evalVector interpretation input).get
      (List.finRange n).all fun j =>
        let expected := (List.finRange n).any fun start =>
          decide (start ≤ j) && input (Fin.castAdd n start) &&
            (List.finRange n).all fun i =>
              !(decide (start < i ∧ i ≤ j)) || input (Fin.natAdd n i)
        output j == expected

end CslibFrontierTests.Propagation
