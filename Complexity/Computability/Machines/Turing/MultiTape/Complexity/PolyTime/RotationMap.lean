/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import Complexity.Foundations.Combinatorics.Expander.AffinePlane
public import Complexity.Foundations.Combinatorics.Expander.Contraction
public import Complexity.Foundations.Combinatorics.Expander.Zigzag
public import Complexity.Foundations.Combinatorics.Expander.Reindex

/-!
# Compositional certificates for graph rotations

Tensor and zig-zag rotations are straight-line programs calling their constituent rotations.
Their certificates charge the complete vertex and edge-label encodings, including copying and
intermediate pairs. The affine-plane rotation similarly composes multiplication and subtraction.

These rules certify a rotation call. They do not enumerate a graph or certify an unbounded
recursive tower. In particular, a certificate for a fixed finite base is not a uniform efficiency
theorem for a varying field size or tower depth.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.rotationMap_tensor`: tensor rotations.
* `Turing.MultiTapeTM.ComputableInPolyTime.rotationMap_zigzag`: zig-zag rotations.
* `Turing.MultiTapeTM.ComputableInPolyTime.rotationMap_affinePlane`: arithmetic rotations.
* `Turing.MultiTapeTM.ComputableInPolyTime.rotationMap_contract`: contraction through
  efficiently encoded and decoded slots, including the unused-slot branch.
* `Turing.MultiTapeTM.ComputableInPolyTime.rotationMap_reindex`: change the vertex encoding
  using efficient forward and inverse maps.

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

open Cslib

variable {V D W E : Type} {vertex : V ↪ List Bool} {label : D ↪ List Bool}
  {otherVertex : W ↪ List Bool} {otherLabel : E ↪ List Bool}

/-- A tensor rotation makes two certified calls and rearranges their complete encoded results. -/
@[fun_prop]
theorem rotationMap_tensor {G : RotationMap V D} {H : RotationMap W E}
    (hG : ComputableInPolyTime G.rot (encPair vertex label) (encPair vertex label))
    (hH : ComputableInPolyTime H.rot
      (encPair otherVertex otherLabel) (encPair otherVertex otherLabel)) :
    ComputableInPolyTime (G.tensor H).rot
      (encPair (encPair vertex otherVertex) (encPair label otherLabel))
      (encPair (encPair vertex otherVertex) (encPair label otherLabel)) := by
  unfold RotationMap.tensor RotationMap.tensorRot
  fun_prop

/-- A zig-zag rotation makes two small-graph calls and one large-graph call, retaining labels. -/
@[fun_prop]
theorem rotationMap_zigzag {G : RotationMap V D} {H : RotationMap D E}
    (hG : ComputableInPolyTime G.rot (encPair vertex label) (encPair vertex label))
    (hH : ComputableInPolyTime H.rot
      (encPair label otherLabel) (encPair label otherLabel)) :
    ComputableInPolyTime (G.zigzag H).rot
      (encPair (encPair vertex label) (encPair otherLabel otherLabel))
      (encPair (encPair vertex label) (encPair otherLabel otherLabel)) := by
  unfold RotationMap.zigzag RotationMap.zigzagRot
  fun_prop

/-- Field multiplication and subtraction suffice to certify the affine-plane rotation. -/
@[fun_prop]
theorem rotationMap_affinePlane {K : Type} [Field K] {encode : K ↪ List Bool}
    (hmul : ComputableInPolyTime (fun p : K × K => p.1 * p.2)
      (encPair encode encode) encode)
    (hsub : ComputableInPolyTime (fun p : K × K => p.1 - p.2)
      (encPair encode encode) encode) :
    ComputableInPolyTime (RotationMap.affinePlane K).rot
      (encPair (encPair encode encode) encode) (encPair (encPair encode encode) encode) := by
  unfold RotationMap.affinePlane RotationMap.affinePlaneRot
  fun_prop

/-- Contraction charges slot decoding, the occupied-slot rotation and re-encoding, and the
unused-slot fallback, with all complete vertex and label encodings. -/
@[fun_prop]
theorem rotationMap_contract {I : Type} {slot : I ↪ List Bool}
    {encode : V → W × I} {decode : W × I → Option V}
    {rotate : V × D → V × D}
    (hencode : ComputableInPolyTime encode vertex (encPair otherVertex slot))
    (hdecode : ComputableInPolyTime decode
      (encPair otherVertex slot) (encOption vertex))
    (hrotate : ComputableInPolyTime rotate (encPair vertex label) (encPair vertex label)) :
    ComputableInPolyTime (RotationMap.contractRot encode decode rotate)
      (encPair otherVertex (encPair slot label))
      (encPair otherVertex (encPair slot label)) := by
  unfold RotationMap.contractRot RotationMap.contractDart
  fun_prop

/-- Vertex renaming charges the forward and backward maps and the complete rotation. -/
@[fun_prop]
theorem rotationMap_reindex {forward : V → W} {backward : W → V}
    {rotate : V × D → V × D}
    (hrotate : ComputableInPolyTime rotate (encPair vertex label) (encPair vertex label))
    (hforward : ComputableInPolyTime forward vertex otherVertex)
    (hbackward : ComputableInPolyTime backward otherVertex vertex) :
    ComputableInPolyTime (RotationMap.reindexRot forward backward rotate)
      (encPair otherVertex label) (encPair otherVertex label) := by
  unfold RotationMap.reindexRot
  fun_prop

end Turing.MultiTapeTM.ComputableInPolyTime
