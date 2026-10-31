/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.PacketEvaluator

/-!
# Tests for packet entries on coefficient lists

Tiny packets of `2 ^ 1` slots over `A_3 = (ℤ / 8)[U] / (U ^ 2 + U + 1)`, at the grid point `t = 1`
of valuation `i = 0`. The kernel unit and one kernel value are checked by hand; the packet entry
with one row port and zero exponents is the local form, a single kernel value; and the
correctness theorem applies to these packets.
-/

@[expose] public section

namespace ComplexityTests.TensorNetworkPacketEvaluator

open Cslib Cslib.Circuits.Frontier Cslib.Circuits.Frontier.NativePacket
  Cslib.Circuits.Frontier.TensorNetwork

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

-- The valuation by halving.
example : twoVal 12 = 2 ∧ twoVal (-8) = 3 ∧ twoVal 0 = 0 := by decide

-- The grid of `2 ^ 1` slots is `-2, -1, 0, 1`; the odd parts of `0 - q` for `q ≠ 0` are
-- `1, 1, -1`, so `C'(0)` has odd part `-1`, and its inverse is `-1 ≡ 7`.
example : kernelUnitList 3 [1, 1] 2 = [7, 0] := by decide

-- `W_1(1 + 4 U)`: the factors for `q = -2, -1, 0` are `3 + 4 U`, `1 + 2 U` and `1 + 4 U`, whose
-- product is `3 + 6 U` modulo `8`; times `-1` it is `5 + 2 U`.
example : kernelValueList 3 [1, 1] 1 2 1 1 [0, 1] = [5, 2] := by decide

-- For `d ≠ t` the kernel value has the factor `2 ^ (a + 1 - v_d) ζ`, which vanishes at `ζ = 0`.
example : kernelValueList 3 [1, 1] 1 2 1 0 [0, 0] = [0, 0] := by decide

-- The cross ratio at `d₀ = 0` and `ζ = 1`: `2` times the inverse of `1 + 4 = 5`, which is `5`
-- modulo `8`, so `10 ≡ 2`.
example : crossRatioList 3 [1, 1] 1 0 1 0 [1, 0] = [2, 0] := by decide

-- One row port in slot `0` set to one, one column port in slot `1` set to one, and zero
-- exponents: the entry is the local form `W_{1 - 0}(T)`.
example : packetEntryList 3 [1, 1] 1 2 0 1 2 true false true (fun _ => 0) [(0, true)] [(1, true)]
    [0, 1] = kernelValueList 3 [1, 1] 1 2 1 1 [0, 1] := by
  decide

-- With the row port set to zero, the entry is `1 - W_1(T)`.
example : packetEntryList 3 [1, 1] 1 2 0 1 2 true false true (fun _ => 0) [(0, false)] [(1, true)]
    [0, 1] = GaloisRingArith.sub 3 [1, 1] (GaloisRingArith.one [1, 1])
      (kernelValueList 3 [1, 1] 1 2 1 1 [0, 1]) := by
  decide

-- Exponent `1` at the mode `(0, 1)`, of dense index `1 + 2 * 0 = 1`, which targets the group
-- (digit `0` of `y₀ = 0` selects the first symbol): the single row factor contributes the
-- coefficient of that mode, and no source mode has a positive exponent.
example : packetEntryList 3 [1, 1] 1 2 0 1 2 true false true (fun k => if k = 1 then 1 else 0)
    [(0, true)] [(1, true)] [0, 1] = modeCoeffList 3 [1, 1] 1 2 0 1 true 0 0 1 [0, 1] := by
  decide

/-- The hypotheses of the correctness theorem hold for these packets. -/
theorem val_packetEntryList_tiny (β : ℕ → ℕ) (ζ : List ℕ) :
    GaloisRingArith.val 3 [1, 1] (packetEntryList 3 [1, 1] 1 2 0 1 2 true false true β
        [(0, true), (1, false)] [(1, true), (0, true)] ζ) =
      packetEntry (p := 2) (scalarHom 3 [1, 1]) (GaloisRingArith.val 3 [1, 1] ζ) 1 0 1 true false
        true (fun Z => β (finProdFinEquiv Z)) [(0, true), (1, false)] [(1, true), (0, true)] :=
  val_packetEntryList (by norm_num) (by norm_num) (by simp [mem_cauchyGrid]) (by norm_num)
    (by norm_num) 2 true false true β (by simp) (by simp) ζ

-- Transported to any ring with `2` nilpotent, at any ring map from `ℤ_(2)`.
example {S : Type} [CommRing S] (ψ : GaloisRingArith.Ring 3 [1, 1] →+* S) {n : ℕ}
    (hn : (2 : S) ^ n = 0) (κ : ℤ₍₂₎ →+* S) (β : ℕ → ℕ) (ζ : List ℕ) :
    ψ (GaloisRingArith.val 3 [1, 1] (packetEntryList 3 [1, 1] 1 2 0 1 2 true false true β
        [(0, true)] [(1, true)] ζ)) =
      packetEntry (p := 2) κ (ψ (GaloisRingArith.val 3 [1, 1] ζ)) 1 0 1 true false true
        (fun Z => β (finProdFinEquiv Z)) [(0, true)] [(1, true)] :=
  map_val_packetEntryList ψ hn κ (by norm_num) (by norm_num) (by simp [mem_cauchyGrid])
    (by norm_num) (by norm_num) 2 true false true β (by simp) (by simp) ζ

end ComplexityTests.TensorNetworkPacketEvaluator
