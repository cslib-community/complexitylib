/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.CauchyModes
public import Complexity.Foundations.NumberTheory.Padics.RatValuation

/-!
# Tests for the modes of the Cauchy kernel

One packet of two slots (`a = 1`), oriented in coordinate `i = 0`, with groups `false` and `true`:
edge `0`, in slot `0`, runs from row `0` of group `false` to column `2` of group `true`, and edge
`1`, in slot `1`, from row `1` of group `true` to column `3` of group `false`. At the grid point
`t = 1`, of valuation `0`, over `ℤ / 4` (`p = 2`), the Cauchy matrix at `T = 1 + 4 ζ` has four
modes `(packet, tile, b)`: the tiles are `y₀ ∈ {0, 1}` and `b < 2`, of weight `b + 1`.
-/

@[expose] public section

namespace ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.CauchyModes

open Cslib.Circuits.Frontier TensorNetwork

/-- The two-edge network over `ℤ / 4`, with tensor `(1, v + 1)` on the bit of the edge at `v`. -/
def net : TensorNetwork (ZMod (2 ^ 2)) Bool (Fin 4) (Fin 2) where
  src e := ⟨e.val, by omega⟩
  tgt e := ⟨e.val + 2, by omega⟩
  tensor v x := if x ⟨v.val % 2, Nat.mod_lt _ (by decide)⟩ then (v.val + 1 : ZMod (2 ^ 2)) else 1
  tensor_congr v x y h := by rw [h _ (by fin_cases v <;> decide)]

/-- The rows `0, 1`. -/
def side (v : Fin 4) : Bool := decide (v.val < 2)

/-- Groups: rows `0` and column `3` are `false`, row `1` and column `2` are `true`. -/
def group (v : Fin 4) : Bool := decide (v = 1 ∨ v = 2)

/-- Edge `e` sits in slot `e` of the single packet. -/
def slot (e : Fin 2) : ℕ := e.val

/-- The packet's pair of groups, oriented as at slot `0`. -/
def sym (_ : Unit) : Bool × Bool := (false, true)

theorem horient (e : Fin 2) : (group (net.src e), group (net.tgt e)) =
    if (slot e).testBit 0 then (sym ((fun _ => ()) e)).swap else sym ((fun _ => ()) e) := by
  fin_cases e <;> decide

/-- Reduction of `ℤ_(2)` modulo `4`. -/
noncomputable abbrev κ := Rat.padicIntegerToZModPow 2 2

/-- **The child identity (D.16)** at `T = 1 + 4 ζ`: the deformed contraction along the Cauchy matrix
is a sum over the mode tuples of total weight below two of products of child contractions. -/
example (ζ : ZMod (2 ^ 2)) :
    net.deformedContraction side (cauchyValueMatrix κ ζ 1 1 (fun _ => ()) slot) =
      ∑ β ∈ modeBudget (fun Z : Unit × Fin (2 ^ (0 + 1)) × Fin 2 => (Z.2.2 : ℕ) + 1) 2,
        ∏ g, ((cauchyModeSplitting (sym := sym) (i := 0) side (by decide) (by decide) horient
          (a := 1) (fun e => by fin_cases e <;> decide) (by decide) κ ζ (p := 2) (by decide)
          (t := 1) (by decide) (by decide) (by decide)).child β g).contraction :=
  deformedContraction_cauchyValueMatrix_eq_sum side (by decide) (by decide) horient
    (fun e => by fin_cases e <;> decide) (by decide) κ ζ (by decide) (by decide) (by decide)
    (by decide)

/-- The budget keeps the zero tuple and the two weight-one modes `b = 0`. -/
example :
    (modeBudget (fun Z : Unit × Fin (2 ^ (0 + 1)) × Fin 2 => (Z.2.2 : ℕ) + 1) 2).card = 3 := by
  decide

/-- Column `1`, in slot `1`, is in tile `1` with `j = 0`, so the mode `((), 1, 0)` reads it with
coefficient `j ^ 0 = 1`, and the mode of tile `0` does not read it. -/
example : cauchyModeForm (ZMod (2 ^ 2)) 0 (fun _ : Fin 2 => ()) slot sym (p := 2) ((), 1, 0) 1 = 1 ∧
    cauchyModeForm (ZMod (2 ^ 2)) 0 (fun _ : Fin 2 => ()) slot sym (p := 2) ((), 0, 0) 1 = 0 := by
  decide

/-- Row `0` has digit `0`, so it only carries the modes of tile `0`, whose columns cross from the
other group. -/
example (ζ : ZMod (2 ^ 2)) :
    cauchyModeCoeff κ ζ 1 0 1 (fun _ : Fin 2 => ()) slot sym (p := 2) 0 ((), 1, 0) = 0 := by
  simp [cauchyModeCoeff, slot]

/-- A crossing coefficient has weight `b + 1`. -/
example (ζ : ZMod (2 ^ 2)) :
    (2 : ZMod (2 ^ 2)) ^ 2 ∣ cauchyModeCoeff κ ζ 1 0 1 (fun _ : Fin 2 => ()) slot sym (p := 2) 0
      ((), 0, 1) :=
  two_pow_dvd_cauchyModeCoeff (fun e => by fin_cases e <;> decide) (by decide) κ ζ (by decide)
    (by decide) (by decide) 0 ((), 0, 1)

end ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.CauchyModes
