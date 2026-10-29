/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-!
# Bounded-fiber graph contraction

A five-vertex complete graph contracts to three vertices, with one unoccupied slot. The
rotation examples exercise both branches, including return labels. Generic certificates retain
arbitrary encodings, and option elimination also handles unbounded words and empty value types.
-/

namespace ComplexityTests.ExpanderContraction

open Cslib Turing.MultiTapeTM

private def completeFive : RotationMap (Fin 5) (Fin 5) where
  rot := Prod.swap
  rot_involutive := Prod.swap_swap

private def threeVertices : RotationMap (Fin 3) (Fin 2 × Fin 5) :=
  completeFive.contractFin (by decide)

-- Occupied slot (0, 1) represents old vertex 3; the edge labelled 1 leads to old vertex 1.
example : threeVertices.rot (0, (1, 1)) = (1, (0, 3)) := by decide
example : threeVertices.rot (1, (0, 3)) = (0, (1, 1)) := by decide

-- Slot (2, 1) would represent vertex 5 and is therefore an unused-slot self-loop.
example : threeVertices.rot (2, (1, 4)) = (2, (1, 4)) := by decide
example : RotationMap.finSlotDecode (m := 5) ((2, 1) : Fin 3 × Fin 2) = none := by decide

private theorem spectralExpansion_completeFive : completeFive.spectralExpansion = 0 := by
  apply le_antisymm ?_ completeFive.spectralExpansion_nonneg
  apply RotationMap.spectralExpansion_le le_rfl
  intro f hf
  simp [RotationMap.walk_apply, RotationMap.neighbor, completeFive, hf]

example : threeVertices.lazy.spectralExpansion ≤ 63 / 64 := by
  have h := completeFive.spectralExpansion_contractFin_lazy_le (by decide : 5 ≤ 2 * 3)
    (by decide) (by decide)
  norm_num [spectralExpansion_completeFive] at h
  exact h

-- Slot `(0, 1)` decodes to `some 3` through the partial-inverse law `isPartialInv_finSlots`.
example : RotationMap.finSlotDecode (m := 5) ((0, 1) : Fin 3 × Fin 2) = some 3 :=
  (RotationMap.isPartialInv_finSlots (by decide : 5 ≤ 2 * 3) 3 (0, 1)).mpr (by decide)

-- Zero-size contractions are total, without an arbitrary inhabitant of the vertex type.
example : Function.IsPartialInv (RotationMap.finSlotEncode (by decide : 0 ≤ 0 * 0))
    (RotationMap.finSlotDecode (m := 0)) := RotationMap.isPartialInv_finSlots _

-- Actual finite witnesses for the complete contraction certificate.
example : ComputableInPolyTime threeVertices.rot
    (encPair (encFinEnum (Fin 3)) (encPair (encFinEnum (Fin 2)) (encFinEnum (Fin 5))))
    (encPair (encFinEnum (Fin 3)) (encPair (encFinEnum (Fin 2)) (encFinEnum (Fin 5)))) := by
  have he : ComputableInPolyTime (RotationMap.finSlotEncode (by decide : 5 ≤ 2 * 3))
      (encFinEnum (Fin 5)) (encPair (encFinEnum (Fin 3)) (encFinEnum (Fin 2))) := .of_finite _
  have hd : ComputableInPolyTime (RotationMap.finSlotDecode (m := 5))
      (encPair (encFinEnum (Fin 3)) (encFinEnum (Fin 2)))
      (encOption (encFinEnum (Fin 5))) := .of_finite _
  have hg : ComputableInPolyTime completeFive.rot
      (encPair (encFinEnum (Fin 5)) (encFinEnum (Fin 5)))
      (encPair (encFinEnum (Fin 5)) (encFinEnum (Fin 5))) := .of_finite _
  exact ComputableInPolyTime.rotationMap_contract he hd hg

example {V W I D : Type} (G : RotationMap V D) (encode : V → W × I)
    (decode : W × I → Option V) (hinv : Function.IsPartialInv encode decode)
    (ev : V ↪ List Bool) (ew : W ↪ List Bool) (ei : I ↪ List Bool) (ed : D ↪ List Bool)
    (he : ComputableInPolyTime encode ev (encPair ew ei))
    (hd : ComputableInPolyTime decode (encPair ew ei) (encOption ev))
    (hg : ComputableInPolyTime G.rot (encPair ev ed) (encPair ev ed)) :
    ComputableInPolyTime
      (fun p : (W × (I × D)) × Bool => ((RotationMap.contract encode decode hinv G).rot p.1, !p.2))
      (encPair (encPair ew (encPair ei ed)) encBool)
      (encPair (encPair ew (encPair ei ed)) encBool) := by
  dsimp only [RotationMap.contract, RotationMap.contractRot, RotationMap.contractDart]
  fail_if_success (clear he; fun_prop)
  fail_if_success (clear hd; fun_prop)
  fail_if_success (clear hg; fun_prop)
  fun_prop

-- Captured optional values may contain unbounded words, with raw or framed word encodings.
example : ComputableInPolyTime
    (fun p : Option (List Bool) × List Bool => p.1.elim p.2 (fun word => word ++ p.2))
    (encPair (encOption encBits) encBits) encBits := by fun_prop

example : ComputableInPolyTime
    (fun p : Option (List Bool) × List Bool =>
      let fallback := p.2
      p.1.elim fallback (fun word => word ++ fallback))
    (encPair (encOption encBits) encBits) encBits := by fun_prop

example : ComputableInPolyTime
    (fun p : Option (List Bool) × List Bool =>
      match p.1 with
      | none => p.2
      | some word => word ++ p.2)
    (encPair (encOption encBits) encBits) encBits := by
  have h : ComputableInPolyTime
      (fun p : Option (List Bool) × List Bool => p.1.elim p.2 (fun word => word ++ p.2))
      (encPair (encOption encBits) encBits) encBits := by fun_prop
  convert h using 1
  funext p
  cases p.1 <;> rfl

example : ComputableInPolyTime
    (fun p : Option (List Bool) × List Bool => p.1.elim p.2 (fun word => word ++ p.2))
    (encPair (encOption (encList encBool)) (encList encBool)) (encList encBool) := by fun_prop

example : ComputableInPolyTime
    (fun p : Option (Fin 0) × List Bool => p.1.elim p.2 (fun v => Fin.elim0 v))
    (encPair (encOption (encFinEnum (Fin 0))) encBits) encBits := by
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.optionElimWithInput
  · fun_prop
  · fun_prop
  · exact .of_finite _

end ComplexityTests.ExpanderContraction
