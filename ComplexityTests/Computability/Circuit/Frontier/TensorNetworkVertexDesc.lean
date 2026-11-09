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
open Turing.MultiTapeTM (encList encNat encPair encBits)
open Cslib.GenericRAM (NativeCertificate)

/-! ### Tables -/

-- The bits `[true, false]` index the table at `1`.
example : VertexDesc.entry tableEntry (.inl [3, 5, 7, 9]) [true, false] = [5] := by decide

example : VertexDesc.entry tableEntry (.inl [3, 5, 7, 9]) [false, true] = [7] := by decide

-- A table has no modes and no row ports.
example : VertexDesc.modes (.inl [3, 5]) = 0 := rfl

example : VertexDesc.rowPorts (.inl [3, 5]) [true] = 0 := rfl

-- A table entry is a constant in `A_p`.
example : GaloisRingArith.val 3 [1, 1] (VertexDesc.entry tableEntry (.inl [3, 5]) [true]) =
    ((5 : ℕ) : GaloisRingArith.Ring 3 [1, 1]) :=
  VertexDesc.val_entry_inl 3 [1, 1] [3, 5] [true]

/-! ### Packets -/

/-- The context of the tiny packet, with no column ports of its own. -/
def ctx : PacketCtx :=
  ⟨3, [1, 1], 1, 2, 0, 2, 1, 2, true, false, true, [], [0, 1]⟩

/-- The descriptor: a row port in slot `0` and a column port in slot `1`, zero exponents. -/
def desc : VertexDesc (List ℕ) := .inr (ctx, [(true, 0), (false, 1)], [0, 0, 0, 0])

-- The column ports are read from the tags and the bits: the entry is `W_1(T) = 5 + 2 U`.
example : VertexDesc.entry tableEntry desc [true, true] = [5, 2] := by decide

example : VertexDesc.rowPorts desc [true, true] = 1 := by decide

/-! ### Other root descriptors -/

-- A root descriptor of any type is read by its entry procedure, here a number read as the
-- coefficient list `[n, 1]`.
example : VertexDesc.entry (fun (n : ℕ) _ => [n, 1]) (.inl 7) [true] = [7, 1] := rfl

-- A packet descriptor reads the same entry whatever the type of the root descriptors.
example : VertexDesc.entry (fun (n : ℕ) _ => [n])
    (.inr (ctx, [(true, 0), (false, 1)], [0, 0, 0, 0])) [true, true] = [5, 2] := by decide

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

-- The bounds of the evaluator, for every native certificate of the entry procedure of the roots:
-- the root's own time and space are added.
example {T : Type} {encT : T ↪ List Bool} {ev : T → List Bool → List ℕ}
    (ce : NativeCertificate (fun q : T × List Bool => ev q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    ∃ K : ℕ, ∀ (q : VertexDesc T × List Bool) (Rv E ES : ℕ), q.1.ReducedLE Rv →
      (∀ t, q.1 = .inl t → ce.time (t, q.2) ≤ E ∧ ce.space (t, q.2) ≤ ES) →
      (VertexDesc.entryCertificate ce).time q ≤ K * (q.1.modes + 2) ^ q.1.rowPorts q.2 *
          ((encPair (VertexDesc.enc encT) encBits q).length + q.1.modes + Rv + 2) ^ K + E ∧
        (VertexDesc.entryCertificate ce).space q ≤
          K * ((encPair (VertexDesc.enc encT) encBits q).length + q.1.modes + Rv + 2) ^ K + ES :=
  VertexDesc.entryCertificate_le ce

-- The entry procedure of tables has a polynomial native certificate.
example : tableEntryCertificate.IsPolynomial := tableEntryCertificate_isPolynomial

/-! ### Back from `A_n` to `O / (2 ^ n)` -/

example {f : Polynomial ℤ} (hf : f.Monic)
    (hirr : Irreducible (f.map (Int.castRingHom (ZMod 2)))) (n : ℕ)
    (x : (AdjoinRoot.padicValuation 2 hf hirr).integer) :
    reductionLift hf hirr n (AdjoinRoot.reduction hf hirr n x) = Ideal.Quotient.mk _ x :=
  reductionLift_reduction hf hirr n x

end ComplexityTests.TensorNetworkVertexDesc
