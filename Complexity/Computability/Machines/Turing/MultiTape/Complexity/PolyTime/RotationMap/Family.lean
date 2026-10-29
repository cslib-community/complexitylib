/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.TowerTable.Family
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.Tower
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Fin
import Mathlib.Tactic.NormNum.Prime

/-!
# Polynomial-time rotations of the arithmetic expander family

The uniform program charges the requested size, complete intermediate tables, copying, lookups,
and quotient/remainder slot conversions. The vertex count is unary: the result is polynomial in
the number of vertices, not in the bit length of their names. Fixed-base and edge-label constants
are enormous, so the certificate makes no claim of practical execution.

## Main results

* `Cslib.RotationMap.TowerTable.polytime_contract`: slot contraction runs in polynomial time.
* `Cslib.RotationMap.TowerTable.polytime_rotateFamily`: the generic numbered-base family.
* `Cslib.RotationMap.polytime_arithmeticExpanderRotate`: the concrete arithmetic family.

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002], Sections 1.2 and 5.1.
-/

@[expose] public section

namespace Cslib.RotationMap.TowerTable

open Turing.MultiTapeTM

variable {D : Type} {b : ℕ}

section Efficiency

variable [Fintype D]

/-- Slot contraction charges its runtime size, table lookup, division and both returned labels. -/
@[fun_prop]
theorem polytime_contract (hb : 0 < b) (label : D ↪ List Bool)
    (slot : (Fin b × (D × D)) ↪ List Bool) :
    ComputableInPolyTime
      (fun p : TowerTable D × (ℕ × (ℕ × (Fin b × (D × D)))) =>
        contract hb p.1 p.2.1 p.2.2)
      (encPair (encoding label) (encPair encUnary (encPair encUnary slot)))
      (encPair encUnary slot) := by
  have htable := ComputableInPolyTime.fst (encoding label)
    (encPair encUnary (encPair encUnary slot))
  have hrest := ComputableInPolyTime.snd (encoding label)
    (encPair encUnary (encPair encUnary slot))
  have hsize := hrest.fst'
  have hvertex := hrest.snd'.fst'
  have hlabel := hrest.snd'.snd'
  have hparts : ComputableInPolyTime (fun edge : Fin b × (D × D) =>
      (edge.1.val, edge.2)) slot (encPair encUnary (encPair label label)) := .of_finite _
  have hdecoded := hparts.comp hlabel
  have hindex := ComputableInPolyTime.unary_add.comp (hvertex.prod
    (ComputableInPolyTime.unary_mul.comp (hsize.prod hdecoded.fst')))
  have htarget := (polytime_lookup label).comp
    (htable.prod (hindex.prod hdecoded.snd'))
  have hslot := (ComputableInPolyTime.unary_finMod hb (encFinEnum (Fin b))).comp
    (ComputableInPolyTime.unary_div.comp (htarget.fst'.prod hsize))
  have hencode : ComputableInPolyTime (id : (Fin b × (D × D)) → _)
      (encPair (encFinEnum (Fin b)) (encPair label label)) slot := .of_finite _
  have hresult := (ComputableInPolyTime.unary_mod.comp
    (htarget.fst'.prod hsize)).prod (hencode.comp (hslot.prod htarget.snd'))
  have hlength := (ComputableInPolyTime.length_list
    (encPi (encPair encUnary (encPair label label)))).comp htable
  exact (ComputableInPolyTime.unary_lt.comp (hindex.prod hlength)).ite_decide
    hresult (hvertex.prod hlabel)

omit [Fintype D] in
/-- The full contracted lazy family has one uniform polynomial-time rotation program.
The runtime vertex count is unary and all complete intermediate tables are included. -/
@[fun_prop]
theorem polytime_rotateFamily [Finite D] (H : RotationMap (Fin b) D)
    (e : Fin b ≃ (Fin 2 → D × D)) (hb : 1 < b)
    (edge : ((Fin b × (D × D)) ⊕ (Fin b × (D × D))) ↪ List Bool) :
    ComputableInPolyTime (rotateFamily H e (by lia))
      (encPair encUnary (encPair encUnary edge)) (encPair encUnary edge) := by
  let _ := Fintype.ofFinite D
  let label := encFinite D
  let slot := encFinite (Fin b × (D × D))
  have hsize := ComputableInPolyTime.fst encUnary (encPair encUnary edge)
  have hvertex := (ComputableInPolyTime.snd encUnary (encPair encUnary edge)).fst'
  have hlabel := (ComputableInPolyTime.snd encUnary (encPair encUnary edge)).snd'
  have hbound := ComputableInPolyTime.unary_le.comp
    ((ComputableInPolyTime.const 2).prod hsize)
  have hbranches (choice : (Fin b × (D × D)) ⊕ (Fin b × (D × D))) :
      ComputableInPolyTime (fun p : ℕ × (ℕ × _ ) =>
        rotateFamily H e (by lia) (p.1, p.2.1, choice))
        (encPair encUnary (encPair encUnary edge)) (encPair encUnary edge) := by
    cases choice with
    | inl choice =>
      have hcall := (polytime_contract (by lia) label slot).comp
        (((polytime_build H e hb label).comp hsize).prod
          (hsize.prod (hvertex.prod (ComputableInPolyTime.const choice))))
      have hinl : ComputableInPolyTime (Sum.inl : (Fin b × (D × D)) → _)
          slot edge := .of_finite _
      exact hbound.ite_decide (hcall.fst'.prod (hinl.comp hcall.snd'))
        (hvertex.prod (ComputableInPolyTime.const (encOut := edge) (Sum.inl choice)))
    | inr choice =>
      exact hbound.ite_decide
        (hvertex.prod (ComputableInPolyTime.const (encOut := edge) (Sum.inr choice)))
        (hvertex.prod (ComputableInPolyTime.const (encOut := edge) (Sum.inr choice)))
  exact hlabel.finite_cases hbranches

end Efficiency

end Cslib.RotationMap.TowerTable

namespace Cslib.RotationMap

open Turing.MultiTapeTM

/-- Arithmetic expander rotations have a uniform machine-backed polynomial-time certificate
in the unary vertex count, with any fixed encoding of their constant edge-label type. -/
@[fun_prop]
theorem polytime_arithmeticExpanderRotate
    (label : AffinePlaneFamilyLabel (ZMod 257) 257 ↪ List Bool) :
    ComputableInPolyTime arithmeticExpanderRotate
      (encPair encUnary (encPair encUnary label)) (encPair encUnary label) := by
  have : Fact (Nat.Prime 257) := ⟨by norm_num⟩
  exact TowerTable.polytime_rotateFamily _ _ (by decide) label

end Cslib.RotationMap
