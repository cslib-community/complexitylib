/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.TowerTable
public import Complexity.Foundations.Combinatorics.Expander.AffineFamily
import Mathlib.Tactic.NormNum.Prime

/-!
# Tabulated rotations of the arbitrary-size arithmetic family

Build the selected tower's complete rotation table, contract through quotient/remainder slots,
and add laziness. The total functional program agrees with the existing family on valid vertex
names, including its return label. Polynomial machine certificates are supplied separately in
`Computability/Machines/Turing/MultiTape/Complexity/PolyTime/RotationMap/Family`.

## Main definitions

* `Cslib.RotationMap.TowerTable.contract`: contract the rows of a table to `size` vertices, with
  self-loops at unoccupied slots.
* `Cslib.RotationMap.TowerTable.rotateFamily`: the total program on every requested vertex count.
* `Cslib.RotationMap.arithmeticExpanderRotate`: the concrete arithmetic instance.

## Main results

* `Cslib.RotationMap.TowerTable.contract_eq`: contracted table rotations agree with
  quotient/remainder contraction of the graph (`contractFin`).
* `Cslib.RotationMap.TowerTable.rotateFamily_eq`: exact rotation and return-label agreement.
* `Cslib.RotationMap.arithmeticExpanderRotate_eq`: the concrete instance realizes the same family.

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002], Sections 1.2 and 5.1.
-/

@[expose] public section

namespace Cslib.RotationMap.TowerTable

variable {D : Type} {b : ℕ}

/-- Contract occupied rows to slots over `size` vertices; unoccupied slots are self-loops. -/
def contract (hb : 0 < b) (table : TowerTable D) (size : ℕ)
    (p : ℕ × (Fin b × (D × D))) : ℕ × (Fin b × (D × D)) :=
  let index := p.1 + size * p.2.1.val
  if index < table.length then
    let target := table.lookup index p.2.2
    (target.1 % size, (⟨(target.1 / size) % b, Nat.mod_lt _ hb⟩, target.2))
  else p

/-- Rotate a requested arbitrary-size family member, with the vertex count supplied at runtime. -/
def rotateFamily (H : RotationMap (Fin b) D) (e : Fin b ≃ (Fin 2 → D × D)) (hb : 0 < b)
    (p : ℕ × (ℕ × ((Fin b × (D × D)) ⊕ (Fin b × (D × D))))) :
    ℕ × ((Fin b × (D × D)) ⊕ (Fin b × (D × D))) :=
  if 2 ≤ p.1 then
    p.2.2.elim
      (fun label => let target := contract hb (build H e hb p.1) p.1 (p.2.1, label)
        (target.1, .inl target.2))
      (fun label => (p.2.1, .inr label))
  else p.2

/-- Contracted table rotations agree with quotient/remainder contraction of the graph. -/
theorem contract_eq {m n : ℕ} (G : RotationMap (Fin m) (D × D))
    (hb : 0 < b) (hcap : m ≤ b * n) (table : TowerTable D)
    (hlength : table.length = m)
    (hlookup : ∀ (vertex : Fin m) label, table.lookup vertex.val label =
      ((G.rot (vertex, label)).1.val, (G.rot (vertex, label)).2))
    (vertex : Fin n) (label : Fin b × (D × D)) :
    contract hb table n (vertex.val, label) =
      (((G.contractFin hcap).rot (vertex, label)).1.val,
        ((G.contractFin hcap).rot (vertex, label)).2) := by
  have hdecode : finSlotDecode (m := m) (vertex, label.1) =
      if hindex : vertex.val + n * label.1.val < m then
        some (⟨vertex.val + n * label.1.val, hindex⟩ : Fin m) else none := rfl
  unfold contract contractFin
  simp only [contractRot, hdecode, hlength]
  split <;> rename_i hindex
  · simp only [hlookup ⟨vertex.val + n * label.1.val, hindex⟩ label.2]
    simp only [contractDart, finSlotEncode]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Fin.ext
        exact Nat.mod_eq_of_lt (Fin.divNat (Fin.castLE hcap
          (G.rot (⟨vertex.val + n * label.1.val, hindex⟩, label.2)).1)).isLt
      · rfl
  · rfl

/-- The total rotation program realizes the existing arbitrary-size tower family. -/
theorem rotateFamily_eq {B : Type*} (H : RotationMap B D) (e : B ≃ (Fin 2 → D × D))
    (numbering : B ≃ Fin b) (hb : 1 < b) (size : ℕ) (vertex : Fin size)
    (label : (Fin b × (D × D)) ⊕ (Fin b × (D × D))) :
    rotateFamily (H.reindex numbering) (numbering.symm.trans e) (by lia)
      (size, vertex.val, label) =
      (((zigzagTowerFamily H e numbering hb size).rot (vertex, label)).1.val,
        ((zigzagTowerFamily H e numbering hb size).rot (vertex, label)).2) := by
  unfold rotateFamily zigzagTowerFamily
  by_cases hsize : 2 ≤ size
  · simp only [hsize, ite_true, dite_true]
    cases label with
    | inl label =>
      have h := contract_eq
        ((zigzagTower H e (Nat.clog b size - 1)).reindex
          (ZigzagTowerVertex.equivFin numbering (Nat.clog b size - 1)))
        (by lia) (zigzagTower_size_bounds hb hsize).2
        (build (H.reindex numbering) (numbering.symm.trans e) (by lia) size)
        (length_build _ _ _ _) (lookup_build H e numbering (by lia) size) vertex label
      exact congrArg (fun target : ℕ × (Fin b × (D × D)) =>
        (target.1, Sum.inl target.2)) h
    | inr label => rfl
  · simp only [hsize, ite_false, dite_false]
    rfl

end Cslib.RotationMap.TowerTable

namespace Cslib.RotationMap

/-- A total executable rotation program for the arithmetic expander family. The first runtime
input is the unary vertex count; fixed edge labels retain their full return-port information. -/
def arithmeticExpanderRotate
    (p : ℕ × (ℕ × AffinePlaneFamilyLabel (ZMod 257) 257)) :
    ℕ × AffinePlaneFamilyLabel (ZMod 257) 257 :=
  have : Fact (Nat.Prime 257) := ⟨by norm_num⟩
  let numbering := affinePlaneTowerBaseNumbering (ZMod.finEquiv 257).toEquiv.symm
  TowerTable.rotateFamily ((affinePlaneTowerBase (ZMod 257)).reindex numbering)
    (numbering.symm.trans (affinePlaneTowerBaseEquiv (ZMod 257))) (by decide) p

/-- The efficient program computes exactly the existing arithmetic expander rotation. -/
theorem arithmeticExpanderRotate_eq (size : ℕ) (vertex : Fin size)
    (label : AffinePlaneFamilyLabel (ZMod 257) 257) :
    arithmeticExpanderRotate (size, vertex.val, label) =
      (((arithmeticExpander size).rot (vertex, label)).1.val,
        ((arithmeticExpander size).rot (vertex, label)).2) := by
  have : Fact (Nat.Prime 257) := ⟨by norm_num⟩
  exact TowerTable.rotateFamily_eq (affinePlaneTowerBase (ZMod 257))
    (affinePlaneTowerBaseEquiv (ZMod 257))
    (affinePlaneTowerBaseNumbering (ZMod.finEquiv 257).toEquiv.symm) (by decide)
    size vertex label

end Cslib.RotationMap
