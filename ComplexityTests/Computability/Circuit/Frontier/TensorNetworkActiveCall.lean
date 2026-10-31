/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ActiveCall

/-!
# Tests for one active call of the contraction recursion

* **The packing bridge.** The two-edge network of the Cauchy-mode tests with a hand-made packing
  into one packet of two slots (`a = 1`, `r = 2`) satisfies the orientation hypothesis of the
  child identity, its groups have one port per side, and the children of a mode splitting along
  its packets have packet degree at most `2 L`.
* **Non-vacuity of the active call.** A one-edge network over `ℤ_(2)` (`M = 1`, `a = 0`, so
  `M (2 L - 1) = 1`), with the two interpolation points `0` and `1`, `u = 1` and `h = 3`: values
  equal to `F(t + α ζ)` recover the contraction modulo every `2 ^ p`.
-/

@[expose] public section

namespace ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.ActiveCall

open Cslib.Circuits.Frontier TensorNetwork

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

/-! ### The packing bridge -/

/-- Edge `e` runs from row `e` to column `e + 2`, with the all-one tensors. -/
def net : TensorNetwork ℤ Bool (Fin 4) (Fin 2) where
  src e := ⟨e.val, by omega⟩
  tgt e := ⟨e.val + 2, by omega⟩
  tensor _ _ := 1
  tensor_congr _ _ _ _ := rfl

/-- The rows `0, 1`. -/
def side (v : Fin 4) : Bool := decide (v.val < 2)

/-- One packet of two slots; edge `e` in slot `e`. Row `1` and column `2` have symbol `1`, so
edge `0` (slot `0`) runs from symbol `0` to `1` and edge `1` (slot `1`) the other way. -/
def packing : Cslib.PacketPacking.Packing net.src net.tgt 1 2 where
  rowLabel v _ := if v = 1 then 1 else 0
  colLabel v _ := if v = 2 then 1 else 0
  numPackets := 1
  packet _ := 0
  slot e := ⟨e.val, by have := e.isLt; simp; omega⟩
  symbols _ _ := (0, 1)
  injective e e' h := by fin_cases e <;> fin_cases e' <;> simp_all
  labels_eq e i := by fin_cases e <;> fin_cases i <;> decide

example (e : Fin 2) :
    (packingGroup side packing 0 (net.src e), packingGroup side packing 0 (net.tgt e)) =
      if (packing.slot e : ℕ).testBit 0 then (packing.symbols (packing.packet e) 0).swap
      else packing.symbols (packing.packet e) 0 :=
  packingGroup_src_tgt side (fun e => by fin_cases e <;> decide)
    (fun e => by fin_cases e <;> decide) packing 0 e

example : Finset.card {e | packingGroup side packing 0 (net.src e) = 1} = 1 := by
  rw [card_packingGroup_src side (fun e => by fin_cases e <;> decide)]
  decide

/-- **Child invariants.** For any mode splitting of `net` along the packets of `packing`, a packet
vertex of a child has at most `2 L = 4` ports. -/
example {M : Type} [Fintype M] [DecidableEq M] {W : Matrix (Fin 2) (Fin 2) ℤ}
    (S : net.ModeSplitting W (Fin 2) (Fin 1) M) (hS : S.packet = packing.packet) (β : M → ℕ)
    (g : Fin 2) (q : Fin 1) :
    Finset.card {x | (S.child β g).tgt x = .inr q} ≤ 2 * 2 ^ 1 :=
  S.card_child_tgt_inr_le (packing_slot_lt packing)
    (by rw [hS]; exact packing_slot_injective packing) β g q

/-! ### Non-vacuity of the active call -/

/-- One edge from row `0` to column `1`, with tensor `(1, 2)` at the row and `(1, 1)` at the
column. -/
def net₁ : TensorNetwork ℤ₍₂₎ Bool (Fin 2) (Fin 1) where
  src _ := 0
  tgt _ := 1
  tensor v x := if v = 0 ∧ x 0 then 2 else 1
  tensor_congr v x y h := by rw [h 0 (by fin_cases v <;> simp)]

/-- The interpolation points `0, 1`, whose difference is a unit. -/
def ζ (k : Fin 2) : ℤ₍₂₎ := k.val

theorem hζ : Pairwise fun k l => IsUnit (ζ k - ζ l) := by
  intro k l hkl
  fin_cases k <;> fin_cases l
  · exact absurd rfl hkl
  · simp [ζ]
  · simp [ζ]
  · exact absurd rfl hkl

/-- Exact values of `F(t + α ζ)` recover the contraction modulo every `2 ^ p`. -/
example (p : ℕ) : ∃ b ∈ ℤ₍₂₎,
    recoverFromValues ℤ₍₂₎ 0 1 3 ζ (fun t k =>
      (net₁.localDeformation (fun v => decide (v = 0)) (integerHom ℤ₍₂₎ fun _ hc => hc) 0 t
        (fun _ => ()) (fun _ => 0)).eval (ζ k)) =
      ((net₁.contraction : ℤ₍₂₎) : ℚ) + 2 ^ p * b :=
  exists_recoverFromValues_eq_add_of_mk (K := ℚ) ℤ₍₂₎ (fun _ hc => hc) net₁ _
    (fun _ => by decide) (fun e e' _ _ => Subsingleton.elim e e') le_rfl le_rfl (by simp)
    (by simp) ζ hζ (by simp) _ fun t _ _ k =>
      mk_eval_localDeformation net₁ _ _ 0 t _ _ _ (ζ k)

end ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.ActiveCall
