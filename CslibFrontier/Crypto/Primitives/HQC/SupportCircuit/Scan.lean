/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Collision
public import CslibFrontier.Foundations.Data.BitString.Block
import Cslib.Foundations.Data.Fin.Tuple

/-!
# Scanning corrected support entries

The circuit retains the corrected suffix while comparing its entries with the current word.
Every comparison is an actual collision-correction circuit; all other entries are wired through.

## Main definitions

* `Cslib.Crypto.HQC.headCollisionCircuit`: correct the head against one suffix entry.
* `Cslib.Crypto.HQC.collisionScanCircuit`: scan a specified list of suffix positions.

## Main results

* `Cslib.Crypto.HQC.eval_collisionScanCircuit`: exact ordered fold, retaining the suffix.
* `Cslib.Crypto.HQC.size_collisionScanCircuit`: exact cost, including repeated comparisons.

## References

[HQC version 5.1][HQC2026], `SampleSupport2`, p. 19, lines 8–10. The circuit construction and
its cost theorems are original bridges to the existing Boolean compiler.
-/

public section

namespace Cslib.Crypto.HQC

open Circuits Circuits.Boolean BitString

/-- Correct the head against suffix entry `j`, retaining every suffix bit. -/
@[expose] def headCollisionCircuit (bits offset count : ℕ) (j : Fin count) :
    Circuit signature (bits + count * bits) (bits + count * bits) :=
  ((collisionStepCircuit bits offset).comp
    (Circuit.wiring signature (Fin.append (Fin.castAdd (count * bits))
      (fun i => Fin.natAdd bits (finProdFinEquiv (j, i)))))).append
    (Circuit.wiring signature (Fin.natAdd bits))

/-- One correction changes only the head word. -/
theorem eval_headCollisionCircuit (bits offset count : ℕ) (j : Fin count)
    (a : BitString bits) (later : Fin count → BitString bits) :
    (headCollisionCircuit bits offset count j).eval interpretation
      (Fin.append a (blocksEquiv.symm later)) =
      Fin.append (if a = later j then (fun i => offset.testBit i.val) else a)
        (blocksEquiv.symm later) := by
  simp only [headCollisionCircuit, Circuit.eval_append, Circuit.eval_comp,
    Circuit.eval_wiring, Fin.comp_append, Fin.append_comp_castAdd, Fin.append_comp_natAdd]
  have h : Fin.append a (blocksEquiv.symm later) ∘
      (fun i : Fin bits => Fin.natAdd bits (finProdFinEquiv (j, i))) = later j := by
    funext i
    simp [Function.comp_apply]
  rw [h, eval_collisionStepCircuit]

/-- A suffix lookup and its unchanged copy add no Boolean gates. -/
theorem size_headCollisionCircuit (bits offset count : ℕ) (j : Fin count) :
    (headCollisionCircuit bits offset count j).size = 13 * bits + 6 := by
  simp only [headCollisionCircuit, Circuit.size_append, Circuit.size_comp,
    Circuit.size_wiring, Nat.zero_add, Nat.add_zero, size_collisionStepCircuit]

/-- Scan suffix positions in the specified order, preserving the full suffix between steps. -/
@[expose] def collisionScanCircuit (bits offset count : ℕ) : List (Fin count) →
    Circuit signature (bits + count * bits) (bits + count * bits)
  | [] => Circuit.id signature _
  | j :: js => (collisionScanCircuit bits offset count js).comp
      (headCollisionCircuit bits offset count j)

/-- The compiled scan is precisely the ordered source inner loop on fixed-width words. -/
theorem eval_collisionScanCircuit (bits offset count : ℕ) (js : List (Fin count))
    (a : BitString bits) (later : Fin count → BitString bits) :
    (collisionScanCircuit bits offset count js).eval interpretation
      (Fin.append a (blocksEquiv.symm later)) =
      Fin.append (js.foldl (fun current j =>
        if current = later j then (fun i => offset.testBit i.val) else current) a)
        (blocksEquiv.symm later) := by
  induction js generalizing a with
  | nil => rfl
  | cons j js ih =>
    rw [collisionScanCircuit, Circuit.eval_comp, eval_headCollisionCircuit, ih, List.foldl_cons]

/-- Every scan position contributes exactly one collision circuit. -/
theorem size_collisionScanCircuit (bits offset count : ℕ) (js : List (Fin count)) :
    (collisionScanCircuit bits offset count js).size = js.length * (13 * bits + 6) := by
  induction js with
  | nil => simp [collisionScanCircuit, Circuit.id]
  | cons j js ih =>
    rw [collisionScanCircuit, Circuit.size_comp, ih, size_headCollisionCircuit, List.length_cons]
    ring

end Cslib.Crypto.HQC
