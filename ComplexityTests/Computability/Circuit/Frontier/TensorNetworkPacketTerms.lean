/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.PacketTerms

/-!
# Tests for the native packet evaluator

The tiny packet of the packet-evaluator tests: `2 ^ 1` slots over
`A_3 = (ℤ / 8)[U] / (U ^ 2 + U + 1)`, the grid point `t = 1` of valuation `i = 0`, two exponents
per tile, one row port in slot `0` and one column port in slot `1` set to one, `ζ = U`. The
native entry, through the stack recursion, agrees with `packetEntryList`, and the correctness
theorem and the certificate apply.
-/

@[expose] public section

namespace ComplexityTests.TensorNetworkPacketTerms

open Cslib Cslib.Circuits.Frontier Cslib.Circuits.Frontier.NativePacket
  Cslib.Circuits.Frontier.TensorNetwork

/-- The context of the tiny packet. -/
def ctx : PacketCtx :=
  ⟨3, [1, 1], 1, 2, 0, 2, 1, 2, true, false, true, [(1, true)], [0, 1]⟩

-- Zero exponents: the entry is the local form, the kernel value `W_1(T) = 5 + 2 U`.
example : packetEntryNative ctx [(0, true)] [0, 0, 0, 0] = [5, 2] := by decide

-- It agrees with `packetEntryList`, here also as lists.
example : packetEntryNative ctx [(0, true)] [0, 0, 0, 0] =
    packetEntryList 3 [1, 1] 1 2 0 1 2 true false true (fun _ => 0) [(0, true)] [(1, true)]
      [0, 1] := by
  decide

-- Exponent `1` at the target mode of dense index `1`: the mode coefficient.
example : packetEntryNative ctx [(0, true)] [0, 1, 0, 0] =
    modeCoeffList 3 [1, 1] 1 2 0 1 true 0 0 1 [0, 1] := by
  decide

/-- The correctness theorem applies to the tiny packet. -/
theorem val_ctx (β : List ℕ) :
    GaloisRingArith.val 3 [1, 1] (packetEntryNative ctx [(0, true)] β) =
      packetEntry (p := 2) (scalarHom 3 [1, 1]) (GaloisRingArith.val 3 [1, 1] [0, 1]) 1 0 1 true
        false true (fun Z => β.getD (finProdFinEquiv Z) 0) [(0, true)] [(1, true)] :=
  val_packetEntryNative_eq ctx (by decide) (by decide) (by decide)
    (by simp [ctx, mem_cauchyGrid]) (by norm_num [ctx]) (by norm_num [ctx]) (by simp)
    (by simp [ctx]) β

-- One native machine computes the native entry.
noncomputable example : Cslib.GenericRAM.NativeCertificate
    (fun q : PacketCtx × (List (ℕ × Bool) × List ℕ) => packetEntryNative q.1 q.2.1 q.2.2)
    encEntryInput (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat) :=
  entryCertificate

/-- The descriptor of the tiny packet vertex: a row port in slot `0`, then a column port in slot
`1`, and zero exponents. Its column ports are read from the bits. -/
def desc : PacketDesc := (ctx, ([(true, 0), (false, 1)], [0, 0, 0, 0]))

-- At the bits `1, 1` on its ports, the entry is the kernel value `5 + 2 U`.
example : packetVertexEntry desc [true, true] = [5, 2] := by decide

-- With the column bit `0`, the local form vanishes, and the row factor at bit `1` is `0`.
example : packetVertexEntry desc [true, false] = [0, 0] := by decide

/-- The correctness theorem applies to the descriptor. -/
theorem val_desc (bs : List Bool) :
    GaloisRingArith.val 3 [1, 1] (packetVertexEntry desc bs) =
      packetEntry (p := 2) (scalarHom 3 [1, 1]) (GaloisRingArith.val 3 [1, 1] [0, 1]) 1 0 1 true
        false true (fun Z => [0, 0, 0, 0].getD (finProdFinEquiv Z) 0) (sidePorts desc.2.1 bs true)
        (sidePorts desc.2.1 bs false) :=
  val_packetVertexEntry desc bs (by decide) (by decide) (by decide)
    (by simp [desc, ctx, mem_cauchyGrid]) (by norm_num [desc, ctx]) (by norm_num [desc, ctx])
    (by decide)

end ComplexityTests.TensorNetworkPacketTerms
