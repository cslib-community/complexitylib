/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.NativeChildPolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends

public section

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.NativeChild Cslib.GaloisRingArith
  Turing.MultiTapeTM

namespace Cslib.Tests.TensorNetworkNativeChildPolyTime

/-! ### Ranks of ports past the edges

A port past the edges reads the edge `(0, 0)`, so the rank of a large port counts it. -/

example : portRank [0, 1] 0 [(0, 1)] Prod.fst 3 = 3 := by decide

example : portRank [0, 1] 0 [(0, 1)] Prod.fst 3 =
    (List.range (min 1 3)).countP (fun e' => decide ([0, 1].getD (([(0, 1)].getD e' (0, 0)).1) 0 =
      0)) + (3 - 1) * (if [0, 1].getD ((0, 0) : ℕ × ℕ).1 0 = 0 then 1 else 0) :=
  portRank_eq_countP _ _ _ _ _

/-! ### The shape of a small child

The path of `TensorNetworkNativeChild` with one row joined to two columns. The child of group `0`
keeps the row and the column `1` and adds one packet. -/

/-- The tables of the vertices. -/
def table (n : ℕ) : VertexDesc := .inl (List.replicate n 1)

/-- The row `0` with ports `1, 0`, the columns `1` and `2`. -/
def path : DescribedNetwork VertexDesc :=
  ⟨2, [([1, 0], table 4), ([0], table 2), ([1], table 2)]⟩

/-- The packing: the row and the column `1` in group `0`, the column `2` in group `1`, both edges
in packet `0`. -/
def packing : (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ) :=
  (([[0]], [[0], [1]]), 1, [(0, 0), (0, 1)])

example : (nativeChild [1] 1 0 3 (-1) [0] 1 path packing [] 0).numEdges ≤ 2 * path.numEdges :=
  numEdges_nativeChild_le _ _ _ _ _ _ _ _ _ _ _

example : (nativeChild [1] 1 0 3 (-1) [0] 1 path packing [] 0).vertices.length = 3 := by
  rw [length_vertices_nativeChild]
  decide

/-! ### Polynomial time on a concrete input

The composition form applies to an input carrying a parent, its packing words and placements,
and its number of packets in unary, with the other parameters fixed. -/

/-- A parent, the packing words, the number of packets and the placements. -/
abbrev Input : Type :=
  DescribedNetwork VertexDesc × (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ)

/-- The encoding of `Input`, with the number of packets in unary. -/
abbrev encInput : Input ↪ List Bool :=
  encPair (DescribedNetwork.encDescribed VertexDesc.enc)
    (encPair (encPair (encList (encList encNat)) (encList (encList encNat)))
      (encPair encUnary (encList (encPair encNat encNat))))

example : ComputableInPolyTime (fun x : Input =>
    nativeChild [1] 1 0 3 (-1) [0] 1 x.1 x.2 [] 0) encInput
    (DescribedNetwork.encDescribed VertexDesc.enc) := by
  have hpk : ComputableInPolyTime (fun x : Input => x.2) encInput
      PacketPacking.encNativePacking :=
    ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)).prod
      ((ComputableInPolyTime.unary_to_binary.comp ((ComputableInPolyTime.fst _ _).comp
        ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)))).prod
        ((ComputableInPolyTime.snd _ _).comp
          ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _))))
  exact computableInPolyTime_nativeChild (ComputableInPolyTime.const _)
    (ComputableInPolyTime.const _) (ComputableInPolyTime.const _) (ComputableInPolyTime.const _)
    (ComputableInPolyTime.const _) (ComputableInPolyTime.const _) (ComputableInPolyTime.const _)
    (ComputableInPolyTime.const _) (ComputableInPolyTime.const _) (ComputableInPolyTime.fst _ _)
    hpk ((ComputableInPolyTime.fst _ _).comp
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)))
    (ComputableInPolyTime.const _) (ComputableInPolyTime.const _)

/-- With the native parent packing, the number of rows and `a` are the only further inputs. -/
example : ComputableInPolyTime (fun D : DescribedNetwork VertexDesc =>
    nativeChild [1] 1 0 3 (-1) [0] 1 D (nativeParentPacking 1 1 D) [] 0)
    (DescribedNetwork.encDescribed VertexDesc.enc)
    (DescribedNetwork.encDescribed VertexDesc.enc) :=
  computableInPolyTime_nativeChild_nativeParentPacking (ComputableInPolyTime.const _)
    (ComputableInPolyTime.const _) (ComputableInPolyTime.const _) (ComputableInPolyTime.const _)
    (ComputableInPolyTime.const _) (ComputableInPolyTime.const _) (ComputableInPolyTime.const _)
    (ComputableInPolyTime.const _) (ComputableInPolyTime.const _) ComputableInPolyTime.id'
    (ComputableInPolyTime.const _) (ComputableInPolyTime.const _)

example : (nativeParentPacking 1 0 path).2.1 ≤ 2 :=
  (numPackets_nativeParentPacking_le 1 0 path).trans (by decide)

/-! ### Binary-digit points

The digits below `e = 2` of `0, 1, 2` are the lists of the interpolation points. -/

example : ((List.range 3).map fun k => (List.range 2).map fun j => if k.testBit j then 1 else 0) =
    [[0, 0], [1, 0], [0, 1]] := by decide

example (hirr : Irreducible ((monicOf [1, 1]).map (Int.castRingHom (ZMod 2)))) :
    Pairwise fun i j : Fin ((List.range 3).map fun k =>
        (List.range [1, 1].length).map fun j => if k.testBit j then 1 else 0).length =>
      IsUnit (liftO hirr (((List.range 3).map fun k =>
          (List.range [1, 1].length).map fun j => if k.testBit j then 1 else 0).getD i []) -
        liftO hirr (((List.range 3).map fun k =>
          (List.range [1, 1].length).map fun j => if k.testBit j then 1 else 0).getD j [])) :=
  pairwise_isUnit_liftO_sub_digits hirr (by decide)

end Cslib.Tests.TensorNetworkNativeChildPolyTime
