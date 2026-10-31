/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ChildEntries
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ReductionLift

/-!
# Tests for vertex descriptors and the entries of child networks

A table descriptor reads its table little-endian and is a constant in `A_p`. A packet descriptor
over the tiny packet of the packet-evaluator tests (`2 ^ 1` slots over
`A_3 = (ℤ / 8)[U] / (U ^ 2 + U + 1)`, `t = 1`, `ζ = U`) with one row port in slot `0` and one
column port in slot `1` evaluates to the kernel value `5 + 2 U` at zero exponents, whatever the
column ports of its context, since they are read from the tags. The ports of one side of a tagged
list come out in order. Reducing an element of `O` to `A_n` and mapping back along
`reductionLift` gives its class modulo `2 ^ n`.
-/

@[expose] public section

namespace ComplexityTests.TensorNetworkVertexDesc

open Cslib Cslib.Circuits.Frontier Cslib.Circuits.Frontier.NativePacket

/-! ### Tables -/

-- The bits `[true, false]` index the table at `1`.
example : VertexDesc.entry (.inl [3, 5, 7, 9]) [true, false] = [5] := by decide

example : VertexDesc.entry (.inl [3, 5, 7, 9]) [false, true] = [7] := by decide

-- A table has no modes and no row ports.
example : VertexDesc.modes (.inl [3, 5]) = 0 := rfl

example : VertexDesc.rowPorts (.inl [3, 5]) [true] = 0 := rfl

-- A table entry is a constant in `A_p`.
example : GaloisRingArith.val 3 [1, 1] (VertexDesc.entry (.inl [3, 5]) [true]) =
    ((5 : ℕ) : GaloisRingArith.Ring 3 [1, 1]) :=
  VertexDesc.val_entry_inl 3 [1, 1] [3, 5] [true]

/-! ### Packets -/

/-- The context of the tiny packet, with no column ports of its own. -/
def ctx : PacketCtx :=
  ⟨3, [1, 1], 1, 2, 0, 2, 1, 2, true, false, true, [], [0, 1]⟩

/-- The descriptor: a row port in slot `0` and a column port in slot `1`, zero exponents. -/
def desc : VertexDesc := .inr (ctx, [(true, 0), (false, 1)], [0, 0, 0, 0])

-- The column ports are read from the tags and the bits: the entry is `W_1(T) = 5 + 2 U`.
example : VertexDesc.entry desc [true, true] = [5, 2] := by decide

example : VertexDesc.rowPorts desc [true, true] = 1 := by decide

/-! ### Tagged ports -/

example : sidePorts [(true, 3), (false, 1), (true, 2)] [true, false, false] true =
    [(3, true), (2, false)] := by decide

example : sidePorts [(true, 3), (false, 1), (true, 2)] [true, false, false] false =
    [(1, false)] := by decide

-- The same, through `sidePorts_map` on a list tagged by parity.
example : sidePorts ([4, 1, 2].map fun c => (decide (c % 2 = 0), c)) ([4, 1, 2].map fun c => c < 3)
    true = [(4, false), (2, true)] := by
  rw [sidePorts_map]
  decide

/-! ### Resources -/

example : ∃ K : ℕ, ∀ (q : VertexDesc × List Bool) (Rv : ℕ), q.1.ReducedLE Rv →
    VertexDesc.entryCertificate.time q ≤ K * (q.1.modes + 2) ^ q.1.rowPorts q.2 *
        ((Turing.MultiTapeTM.encPair VertexDesc.enc Turing.MultiTapeTM.encBits q).length +
          q.1.modes + Rv + 2) ^ K ∧
      VertexDesc.entryCertificate.space q ≤
        K * ((Turing.MultiTapeTM.encPair VertexDesc.enc Turing.MultiTapeTM.encBits q).length +
          q.1.modes + Rv + 2) ^ K :=
  VertexDesc.entryCertificate_le

/-! ### Back from `A_n` to `O / (2 ^ n)` -/

example {f : Polynomial ℤ} (hf : f.Monic)
    (hirr : Irreducible (f.map (Int.castRingHom (ZMod 2)))) (n : ℕ)
    (x : (AdjoinRoot.padicValuation 2 hf hirr).integer) :
    reductionLift hf hirr n (AdjoinRoot.reduction hf hirr n x) = Ideal.Quotient.mk _ x :=
  reductionLift_reduction hf hirr n x

end ComplexityTests.TensorNetworkVertexDesc
