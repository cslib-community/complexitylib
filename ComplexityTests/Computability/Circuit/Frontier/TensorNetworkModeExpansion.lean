/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ModeExpansion

/-!
# Tests for the mode expansion and the child identity

Two edges `0 : 0 → 2` and `1 : 1 → 3`, from the rows `0, 1` to the columns `2, 3`, in one packet.
Vertex `v` is in group `v % 2`, so edge `e` joins two vertices of group `e`, and the entries of the
matrix `W = !![1, 2; 2, 3]` off the diagonal cross between the groups. Over `ZMod 4` they become two
modes of weight one, since `2 ∣ 2` and `2 ^ 2 = 0`: mode `Z` reads the column bit of edge `1 - Z`
and enters the form of row port `Z`. The child identity (D.16) then writes the deformed
contraction as a sum over the three tuples `β` of total weight below two.
-/

@[expose] public section

namespace ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.ModeExpansion

open Cslib.Circuits.Frontier TensorNetwork

/-- The edge at a vertex: vertices `0` and `2` are the ends of edge `0`, and `1` and `3` of
edge `1`. -/
def edgeAt (v : Fin 4) : Fin 2 := ⟨v.val % 2, Nat.mod_lt _ (by decide)⟩

/-- The two-edge network, with tensor `(1, v + 1)` on the bit of the edge at `v`. -/
def net : TensorNetwork (ZMod 4) Bool (Fin 4) (Fin 2) where
  src e := ⟨e.val, by omega⟩
  tgt e := ⟨e.val + 2, by omega⟩
  tensor v x := if x (edgeAt v) then (v.val + 1 : ZMod 4) else 1
  tensor_congr v x y h := by rw [h (edgeAt v) (by fin_cases v <;> decide)]

/-- The matrix: the identity on the diagonal, and `2` between the groups. -/
def W : Matrix (Fin 2) (Fin 2) (ZMod 4) := !![1, 2; 2, 3]

/-- The splitting of `W` into its diagonal and two modes. -/
def S : net.ModeSplitting W (Fin 2) Unit (Fin 2) where
  side v := decide (v.val < 2)
  group := edgeAt
  packet _ := ()
  localPart e e' := if e = e' then W e e else 0
  modePacket _ := ()
  source Z := Z + 1
  target Z := Z
  coeff e Z := if e = Z then W Z (Z + 1) else 0
  form Z e' := if e' = Z + 1 then 1 else 0
  side_src := by decide
  side_tgt := by decide
  apply_eq e e' := by fin_cases e <;> fin_cases e' <;> decide
  localPart_ne_zero e e' := by fin_cases e <;> fin_cases e' <;> decide
  coeff_ne_zero e Z := by fin_cases e <;> fin_cases Z <;> decide
  form_ne_zero Z e := by fin_cases Z <;> fin_cases e <;> decide

/-- Both modes have coefficients divisible by `2`. -/
theorem two_dvd_coeff (e Z : Fin 2) : 2 ^ 1 ∣ S.coeff e Z := by
  have h : S.coeff e Z = 2 * (if e = Z then 1 else 0) := by
    fin_cases e <;> fin_cases Z <;> decide
  rw [h, pow_one]
  exact dvd_mul_right _ _

/-- **The child identity** for this splitting, with weights one and `2 ^ 2 = 0` in `ZMod 4`. -/
theorem deformedContraction_eq :
    net.deformedContraction S.side W =
      ∑ β ∈ modeBudget (fun _ : Fin 2 => 1) 2, ∏ g, (S.child β g).contraction :=
  S.deformedContraction_eq_sum_prod_contraction_child _ (fun _ => Nat.one_pos)
    (by decide : (2 : ZMod 4) ^ 2 = 0) two_dvd_coeff

/-- The budget holds the three tuples of total weight below two. -/
example : modeBudget (fun _ : Fin 2 => 1) 2 = {![0, 0], ![1, 0], ![0, 1]} := by decide

/-- The deformed contraction is `2`. -/
example : net.deformedContraction S.side W = 2 := by decide

/-- Without modes, the child of group `0` contracts to `1 + 3 = 0` and that of group `1` to `1`.
With mode `0`, whose coefficient `2` enters the row form of group `0`, the child of group `0`
vanishes. -/
example : (S.child ![0, 0] 0).contraction = 0 ∧ (S.child ![0, 0] 1).contraction = 1 ∧
    (S.child ![1, 0] 0).contraction = 0 := by
  decide

/-- With mode `1`, the child of group `0` carries the mode value `L(X) = X₀` on its packet and
contracts to `3`, and the child of group `1` carries the coefficient `±2` and contracts to `2`. So
the only surviving term of (D.16) is `3 * 2 = 2`, the deformed contraction. -/
example : (S.child ![0, 1] 0).contraction = 3 ∧ (S.child ![0, 1] 1).contraction = 2 := by
  decide

/-- The children are bipartite. -/
example (β : Fin 2 → ℕ) (g : Fin 2) : (S.child β g).IsBipartite := S.isBipartite_child β g

/-- Each child has the row port and the column port of its group. -/
example (g : Fin 2) :
    Fintype.card ({e // S.group (net.src e) = g} ⊕ {e // S.group (net.tgt e) = g}) = 2 := by
  rw [S.card_edges_child]
  fin_cases g <;> decide

end ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.ModeExpansion
