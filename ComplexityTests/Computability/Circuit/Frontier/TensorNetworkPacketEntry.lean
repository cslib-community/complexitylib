/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.KernelProduct
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.PacketEntry
public import ComplexityTests.Computability.Circuit.Frontier.TensorNetworkCauchyModes

/-!
# Tests for the entries of the child networks

The network of the Cauchy mode tests: one packet of two slots, oriented in coordinate `0`, with
groups `false` and `true`. Edge `0` runs from row `0` (group `false`) to column `2` (group
`true`), and edge `1` from row `1` (group `true`) to column `3` (group `false`). So the packet
vertex of the child of group `false` has one row port, edge `0` in slot `0`, and one column port,
edge `1` in slot `1`.
-/

@[expose] public section

namespace ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.PacketEntry

open Cslib.Circuits.Frontier TensorNetwork
open ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.CauchyModes

/-- Coefficient extraction: the coefficient of `m` in `(2 + 3 m) (5 + 7 m)` is `2 · 7 + 3 · 5`. -/
example : listCoeff (R := ℤ) ({()} : Finset Unit)
    [fun o => o.elim 2 fun _ => 3, fun o => o.elim 5 fun _ => 7] (fun _ => 1) = 29 := by
  simp [listCoeff]

/-- The coefficient of `m ^ 2` is `3 · 7`, and there is no `m ^ 3` term. -/
example : listCoeff (R := ℤ) ({()} : Finset Unit)
      [fun o => o.elim 2 fun _ => 3, fun o => o.elim 5 fun _ => 7] (fun _ => 2) = 21 ∧
    listCoeff (R := ℤ) ({()} : Finset Unit)
      [fun o => o.elim 2 fun _ => 3, fun o => o.elim 5 fun _ => 7] (fun _ => 3) = 0 := by
  simp [listCoeff]

/-- The Cauchy mode splitting of the test network at `T = 1 + 4 ζ`. -/
noncomputable abbrev split (ζ : ZMod (2 ^ 2)) :=
  cauchyModeSplitting (sym := sym) (i := 0) side (by decide) (by decide) horient (a := 1)
    (fun e => by fin_cases e <;> decide) (by decide) κ ζ (p := 2) (by decide) (t := 1) (by decide)
    (by decide) (by decide)

/-- **The packet entry of the child of group `false`**, at the bits `y`, is `packetEntry` on its row
port (edge `0`, slot `0`) and its column port (edge `1`, slot `1`). -/
example (ζ : ZMod (2 ^ 2)) (β : Unit × Fin (2 ^ (0 + 1)) × Fin 2 → ℕ)
    (y : {e // (split ζ).group (net.src e) = false} ⊕ {e // (split ζ).group (net.tgt e) = false} →
      Bool) :
    ((split ζ).child β false).tensor (.inr ()) y =
      packetEntry κ ζ 1 0 1 true false true (fun Z => β ((), Z))
        ([0].map fun e => (slot e, if h : _ = false then y (.inl ⟨e, h⟩) else false))
        ([1].map fun e => (slot e, if h : _ = false then y (.inr ⟨e, h⟩) else false)) :=
  child_tensor_inr_cauchyModeSplitting side (by decide) (by decide) horient
    (fun e => by fin_cases e <;> decide) (by decide) κ ζ (by decide) (by decide) (by decide)
    (by decide) β false () y (rows := [0]) (cols := [1]) (by decide)
    (fun e => by fin_cases e <;> decide) (by decide) (fun e => by fin_cases e <;> decide)

/-- With no ports and zero exponents, a packet entry is `1`. -/
example (ζ : ZMod (2 ^ 2)) :
    packetEntry (p := 2) κ ζ 1 0 1 true false true (fun _ => 0) [] [] = 1 := by
  simp [packetEntry]

/-- Packet entries reduce along `ℤ / 4 → ℤ / 2`. -/
example (ζ : ZMod (2 ^ 2)) (β : Fin (2 ^ (0 + 1)) × Fin 2 → ℕ) (rows cols : List (ℕ × Bool)) :
    ZMod.castHom (by decide : 2 ∣ 2 ^ 2) (ZMod 2)
        (packetEntry κ ζ 1 0 1 true false true β rows cols) =
      packetEntry ((ZMod.castHom (by decide : 2 ∣ 2 ^ 2) (ZMod 2)).comp κ)
        (ZMod.castHom (by decide : 2 ∣ 2 ^ 2) (ZMod 2) ζ) 1 0 1 true false true β rows cols :=
  map_packetEntry _ (n := 2) (by decide) κ ζ (by decide) (by decide) (by decide) _ _ _ β rows cols

/-- **Kernel values as products of units**, on the grid `{-2, -1, 0, 1}` of two slots: the value
`W_0(1 + 4 ζ)` is `κ(kernelUnit 1)` times `2 ^ (2 - v₂(1)) ζ` times the factors at `q = -2, -1`. -/
example (ζ : ZMod (2 ^ 2)) :
    kernelValue κ ζ 1 1 0 = κ (kernelUnit 1) * (2 ^ (1 + 1 - padicValInt 2 (1 - 0)) * ζ) *
      ∏ q ∈ ((cauchyGrid (2 ^ 1)).erase 0).erase 1,
        (((1 - q) / 2 ^ padicValInt 2 (1 - q) : ℤ) + 2 ^ (1 + 1 - padicValInt 2 (1 - q)) * ζ) := by
  rw [kernelValue_eq_prod κ ζ (by decide) (by decide), ite_eq_right (by decide)]

/-- The valuations of `1 - q`, `q ∈ {-2, -1, 0}`, sum to those of `0 - q`, `q ∈ {-2, -1, 1}`. -/
example : ∑ q ∈ (cauchyGrid (2 ^ 1)).erase 1, padicValInt 2 (1 - q) =
    ∑ q ∈ (cauchyGrid (2 ^ 1)).erase 0, padicValInt 2 (0 - q) :=
  sum_padicValInt_sub_eq (by decide)

end ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.PacketEntry
