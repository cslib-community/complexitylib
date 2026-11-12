/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Circuit.Boolean.CarrySave.MultiplicationQuery

/-! Padded multiplication leaves and the complete carry-save multiplication semantics. -/

namespace CslibFrontierTests.CarrySaveMultiplicationQuery

open Cslib Cslib.Circuits.Boolean Cslib.Circuits.Boolean.CarrySaveQuery
open Multiplication

/-- A shifted partial-product leaf queries exactly two runtime operand bits. -/
example (a b : BitString 5) : component (partialPair a b 2) false 4 = (a 2 && b 2) := by
  simp [component_partialPair_sum]

/-- Bits below the shift vanish, regardless of runtime inputs. -/
example (a b : BitString 5) : component (partialPair a b 3) false 1 = false := by
  simp [component_partialPair_sum]

/-- The non-power-of-two width five has three padding leaves in its eight-leaf tree. -/
example (a b : BitString 5) : leaves a b [true, false, true] = fun _ => false := by
  funext i
  change Fin.append (fun _ : Fin 5 => false) (fun _ : Fin 5 => false) i = false
  unfold Fin.append Fin.addCases
  split <;> simp

/-- Width zero has no partial-product contribution. -/
example (a b : BitString 0) : pairVal (partialPair a b 0) = 0 :=
  pairVal_partialPair_of_le a b (by decide)

/-- All widths and runtime operands obey exact modular multiplication after finishing. -/
example (w : ℕ) (a b : BitString w) :
    (BitString.equivFin w (product a b) : ℕ) =
      ((BitString.equivFin w a : ℕ) * (BitString.equivFin w b : ℕ)) % 2 ^ w :=
  val_product a b

/-- Overflow is discarded at width three: seven times seven gives one. -/
example : (BitString.equivFin 3 (product (fun _ => true) (fun _ => true)) : ℕ) = 1 := by
  rw [val_product]
  decide

/-- A zero operand remains zero through the non-power-of-two-width tree and finish. -/
example (a : BitString 5) : (BitString.equivFin 5 (product a (fun _ => false)) : ℕ) = 0 := by
  rw [val_product, BitString.val_equivFin_false]
  simp

end CslibFrontierTests.CarrySaveMultiplicationQuery
