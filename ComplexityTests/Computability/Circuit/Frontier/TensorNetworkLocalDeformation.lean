/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.LocalDeformation
public import Complexity.Foundations.NumberTheory.Padics.RatValuation

/-!
# Tests for the deformed contraction in local coordinates

The two-edge network of the Cauchy-mode tests, with tensors over `ℤ_(2)`: one packet of two
slots (`a = 1`), at the grid point `t = 1`. Its local deformation is a polynomial over `ℤ_(2)` of
degree at most `2 (2 * 2 - 1) = 6`; in `ℚ` it is `F(1 + 4 z)`, and modulo `4` its value at `ζ` is
the deformed contraction along the Cauchy matrix at `T = 1 + 4 ζ`.
-/

@[expose] public section

namespace ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.LocalDeformation

open Cslib.Circuits.Frontier TensorNetwork Polynomial

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

/-- The two-edge network over `ℤ_(2)`, with tensor `(1, 2)` on the bit of the edge at each
vertex. -/
def net : TensorNetwork ℤ₍₂₎ Bool (Fin 4) (Fin 2) where
  src e := ⟨e.val, by omega⟩
  tgt e := ⟨e.val + 2, by omega⟩
  tensor v x := if x ⟨v.val % 2, Nat.mod_lt _ (by decide)⟩ then 2 else 1
  tensor_congr v x y h := by rw [h _ (by fin_cases v <;> decide)]

/-- The rows `0, 1`. -/
def side (v : Fin 4) : Bool := decide (v.val < 2)

/-- Edge `e` sits in slot `e` of the single packet. -/
def slot (e : Fin 2) : ℕ := e.val

theorem hslot (e : Fin 2) : slot e < 2 ^ 1 := by fin_cases e <;> decide

/-- The degree bound `M (2 L - 1)`. -/
example : (net.localDeformation side (RingHom.id _) 1 1 (fun _ => ()) slot).natDegree ≤ 6 :=
  natDegree_localDeformation_le net side (RingHom.id _) hslot (by decide)

/-- In `ℚ`, the local deformation is `F(1 + 4 z)` for the deformed contraction `F(T)` along the
Cauchy matrix. -/
example : (net.localDeformation side (RingHom.id _) 1 1 (fun _ => ()) slot).map (ℤ₍₂₎).subtype =
    (((net.map (ℤ₍₂₎).subtype).map C).deformedContraction side
      ((cauchyMatrix (2 ^ 1) (fun _ => ()) slot).map (mapRingHom (algebraMap ℚ ℚ)))).comp
        (C ((1 : ℤ) : ℚ) + C (2 ^ (1 + 1)) * X) :=
  map_localDeformation net side (RingHom.id _) (ℤ₍₂₎).subtype rfl hslot (by decide)

/-- Modulo `4`, its value at `ζ` is the deformed contraction along the Cauchy matrix at
`T = 1 + 4 ζ`. -/
example (ζ : ZMod (2 ^ 2)) :
    (net.localDeformation side (RingHom.id _) 1 1 (fun _ => ()) slot).eval₂
        (Rat.padicIntegerToZModPow 2 2) ζ =
      (net.map (Rat.padicIntegerToZModPow 2 2)).deformedContraction side
        (cauchyValueMatrix (Rat.padicIntegerToZModPow 2 2) ζ 1 1 (fun _ => ()) slot) :=
  eval₂_localDeformation net side (RingHom.id _) _ ζ 1 1 _ slot

end ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.LocalDeformation
