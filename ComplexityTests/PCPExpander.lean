/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.Family
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Tactic.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Fin

/-! Concrete executable clients for tower tables. The small base tests the uniform algorithm;
it has no asserted spectral gap. The arithmetic family's spectral instance is separate. -/

open Cslib Cslib.RotationMap Turing.MultiTapeTM

namespace ComplexityTests.PCPExpander

example : ComputableInPolyTime
    (fun index : ℕ => (⟨index % 1, Nat.mod_lt _ (by decide)⟩ : Fin 1))
    encUnary (encFinEnum (Fin 1)) :=
  ComputableInPolyTime.unary_finMod (by decide) _

-- The fixed finite output may use binary indices instead of the finite-rank encoding.
example :
    let output : Fin 3 ↪ List Bool :=
      ⟨fun index => encNat index.val, fun _ _ h => Fin.val_injective (encNat.injective h)⟩
    ComputableInPolyTime
      (fun index : ℕ => (⟨index % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3)) encUnary output :=
  ComputableInPolyTime.unary_finMod (by decide) _

private def base : RotationMap (Fin 16) (Fin 2) := .loops _ _

private def coordinates : Fin 16 ≃ (Fin 2 → Fin 2 × Fin 2) :=
  (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm |>.trans
    (((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm.prodCongr
      (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm).trans
        (finTwoArrowEquiv (Fin 2 × Fin 2)).symm)

example : ComputableInPolyTime (TowerTable.build base coordinates (by decide))
    encUnary (TowerTable.encoding (encFinEnum (Fin 2))) :=
  TowerTable.polytime_build base coordinates (by decide) _

-- Equivalent call spellings and captured inputs use the same uniform certificate.
example : ComputableInPolyTime
    (fun p : Bool × ℕ => TowerTable.build base coordinates (by decide) (p.2 + 1))
    (encPair encBool encUnary) (TowerTable.encoding (encFinEnum (Fin 2))) := by
  have h := TowerTable.polytime_build base coordinates (by decide) (encFinEnum (Fin 2))
  polytime

example : (TowerTable.build base coordinates (by decide) 0).length = 16 := by decide
example : (TowerTable.build base coordinates (by decide) 1).length = 16 := by decide
example : (TowerTable.build base coordinates (by decide) 17).length = 256 := by
  rw [TowerTable.length_build]
  decide

-- Squaring reverses both return labels, even when the base neighbors are self-loops.
example : (TowerTable.build base coordinates (by decide) 1).lookup 3 (0, 1) =
    (3, (1, 0)) := by decide

example : (TowerTable.build base coordinates (by decide) 17).lookup 0 (0, 1) =
    (0, (1, 0)) := by decide

-- Lookup outside the complete table is total and retains its fallback label.
example : (TowerTable.build base coordinates (by decide) 1).lookup 16 (0, 1) =
    (0, (0, 1)) := by decide

example :
    (TowerTable.build (base.reindex (Equiv.refl _)) ((Equiv.refl _).symm.trans coordinates)
      (by decide) 17).lookup 0 (0, 1) =
      let target := ((zigzagTower base coordinates (Nat.clog 16 17 - 1)).reindex
        (ZigzagTowerVertex.equivFin (Equiv.refl _) (Nat.clog 16 17 - 1))).rot
          (⟨0, by decide⟩, (0, 1))
      (target.1.val, target.2) :=
  TowerTable.lookup_build base coordinates (Equiv.refl _) (by decide) 17 ⟨0, by decide⟩ (0, 1)

example : ComputableInPolyTime (TowerTable.rotateFamily base coordinates (by decide))
    (encPair encUnary (encPair encUnary
      (encFinEnum ((Fin 16 × (Fin 2 × Fin 2)) ⊕ (Fin 16 × (Fin 2 × Fin 2))))))
    (encPair encUnary (encFinEnum ((Fin 16 × (Fin 2 × Fin 2)) ⊕
      (Fin 16 × (Fin 2 × Fin 2))))) :=
  TowerTable.polytime_rotateFamily base coordinates (by decide) _

example : TowerTable.rotateFamily base coordinates (by decide)
    (0, 3, .inl (0, (0, 1))) = (3, .inl (0, (0, 1))) := by decide

example : TowerTable.rotateFamily base coordinates (by decide)
    (1, 0, .inl (4, (0, 1))) = (0, .inl (4, (0, 1))) := by decide

-- An occupied slot keeps the return slot and reverses the two base-walk labels.
example : TowerTable.rotateFamily base coordinates (by decide)
    (2, 1, .inl (0, (0, 1))) = (1, .inl (0, (1, 0))) := by decide

-- The unused tail slots and lazy labels both remain self-loops.
example : TowerTable.rotateFamily base coordinates (by decide)
    (3, 2, .inl (5, (0, 1))) = (2, .inl (5, (0, 1))) := by decide

example : TowerTable.rotateFamily base coordinates (by decide)
    (2, 1, .inr (7, (0, 1))) = (1, .inr (7, (0, 1))) := by decide

example (label : AffinePlaneFamilyLabel (ZMod 257) 257) :
    arithmeticExpanderRotate (1, 0, label) = (0, label) := rfl

-- The positive-gap family itself has the uniform machine certificate, independently of size.
local instance : FinEnum (ZMod 257) :=
  FinEnum.ofEquiv (Fin 257) (ZMod.finEquiv 257).toEquiv.symm

example : ComputableInPolyTime arithmeticExpanderRotate
    (encPair encUnary (encPair encUnary
      (encFinEnum (AffinePlaneFamilyLabel (ZMod 257) 257))))
    (encPair encUnary (encFinEnum (AffinePlaneFamilyLabel (ZMod 257) 257))) :=
  polytime_arithmeticExpanderRotate _

end ComplexityTests.PCPExpander
