/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Pack
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Codes
public import Complexity.Foundations.Data.Nat.OfDigits
public import Complexity.Foundations.Data.Finset.OrderedFilter

/-!
# Wanted query codes and the existing output strings

## Main results

* `Wanted.pack_output_list`: packing the inner mask and compressed outer digits recovers
  the existing pruned evaluator's output numbering, including repeated zero digits.
* `Wanted.pack_outStrOfPos`: the computed mask and the ordinary row/column offsets give
  exactly the original thin-product query, without a caller-supplied output string.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.Algorithms.MatrixMultiplication.Schonhage
open QueryDigits PrunedQuery

/-- The pruned evaluator uses row-major digits for ordinary outer outputs. -/
theorem outputDigits_outer (i j : Fin 3) :
    (outputDigits.symm (.z i j)).val = 3 * i.val + j.val := by decide +revert

/-- Its inner output is the existing private term numbered nine. -/
theorem outputDigits_inner : (outputDigits.symm .z0).val = 9 := by decide

/-- The arithmetic recurrence reconstructs every output list from its inner flags and
the two outer-coordinate lists. It does not need a supplied cardinality certificate. -/
theorem pack_output_list (zs : List OutVar) :
    pack zs.length (Nat.ofDigits 2 (zs.map fun z => if z.IsInner then 1 else 0))
      (Nat.ofDigits 3 ((zs.filter fun z => ¬z.IsInner).map fun z => z.rowIndex.val))
      (Nat.ofDigits 3 ((zs.filter fun z => ¬z.IsInner).map fun z => z.colIndex.val)) =
      Nat.ofDigits 10 (zs.map fun z => (outputDigits.symm z).val) := by
  induction zs with
  | nil => simp [pack]
  | cons z zs ih =>
    cases z with
    | z i j =>
      have hi : i.val < 3 := i.isLt
      have hj : j.val < 3 := j.isLt
      simpa [pack, OutVar.IsInner, OutVar.rowIndex, OutVar.colIndex, Nat.ofDigits,
        Nat.add_mul_mod_self_left, Nat.add_mul_div_left, Nat.mod_eq_of_lt hi,
        Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj,
        outputDigits_outer] using congrArg (fun t => 3 * i.val + j.val + 10 * t) ih
    | z0 =>
      simpa [pack, OutVar.IsInner, Nat.ofDigits, Nat.add_mul_mod_self_left,
        Nat.add_mul_div_left, outputDigits_inner] using ih

private theorem outer_list {L m : ℕ} (w : OutStr L) (h : (innerSetO w).card = m)
    (f : OutVar → Fin 3) :
    ((List.ofFn w).filter fun z => ¬z.IsInner).map (fun z => (f z).val) =
      List.ofFn (fun k => (f (w ((innerSetO w)ᶜ.orderEmbOfFin
        (Finset.card_compl_of_card_eq _ h) k))).val) := by
  rw [Finset.ofFn_orderEmbOfFin (innerSetO w)ᶜ
    (Finset.card_compl_of_card_eq _ h) (fun i => (f (w i)).val),
    Finset.sort_eq_filter_finRange,
    List.ofFn_eq_map, List.filter_map, List.map_map]
  have hp : (fun i : Fin L => decide (¬(w i).IsInner)) =
      (fun i => decide (i ∈ (innerSetO w)ᶜ)) := by
    funext i
    simp [innerSetO]
  simp only [Function.comp_def, hp]

/-- A packed mask and the ordered outer coordinates recover every original output code. -/
theorem pack_queryIndex {L m : ℕ} (w : OutStr L) (h : (innerSetO w).card = m) :
    pack L (MaskTable.maskCode (innerSetO w)).val
      (finFunctionFinEquiv (rowO w h)).val (finFunctionFinEquiv (colO w h)).val =
      (queryIndex w).val := by
  have hm : Nat.ofDigits 2 ((List.ofFn w).map fun z => if z.IsInner then 1 else 0) =
      (MaskTable.maskCode (innerSetO w)).val := by
    rw [List.map_ofFn]
    calc
      _ = Nat.ofDigits 2 (List.ofFn fun i =>
          ((if i ∈ innerSetO w then 1 else 0) : Fin 2).val) := by
        congr 2
        funext i
        by_cases hi : (w i).IsInner <;> simp [innerSetO, hi]
      _ = _ := Nat.ofDigits_finFunctionFinEquiv _
  have hr : Nat.ofDigits 3 (((List.ofFn w).filter fun z => ¬z.IsInner).map
      fun z => z.rowIndex.val) = (finFunctionFinEquiv (rowO w h)).val := by
    rw [outer_list w h OutVar.rowIndex, Nat.ofDigits_finFunctionFinEquiv]
    rfl
  have hc : Nat.ofDigits 3 (((List.ofFn w).filter fun z => ¬z.IsInner).map
      fun z => z.colIndex.val) = (finFunctionFinEquiv (colO w h)).val := by
    rw [outer_list w h OutVar.colIndex, Nat.ofDigits_finFunctionFinEquiv]
    rfl
  have ho : Nat.ofDigits 10 ((List.ofFn w).map fun z => (outputDigits.symm z).val) =
      (queryIndex w).val := by
    rw [List.map_ofFn]
    exact Nat.ofDigits_finFunctionFinEquiv (fun i => outputDigits.symm (w i))
  simpa only [List.length_ofFn, hm, hr, hc, ho] using pack_output_list (List.ofFn w)

/-- The actual deterministic table mask and the original offsets compute precisely
`outStrOfPos`, in the unchanged pruned evaluator's least-significant-first numbering. -/
theorem pack_outStrOfPos {L m : ℕ} (hm : m ≤ L) (I J : ℕ) :
    pack L (MaskTable.selectedMask
      (blockOf (MaskTable.layout hm) I, blockOf (MaskTable.layout hm) J)).val
      (I % N0 L m) (J % N0 L m) =
      (queryIndex (outStrOfPos (MaskTable.layout hm) I J)).val := by
  let lay := MaskTable.layout hm
  let Q := lay.table (blockOf lay I, blockOf lay J)
  have hQ : Q.card = m := lay.table_card _
  have h := pack_queryIndex (outStrOfPos lay I J)
    (by simpa only [outStrOfPos, innerSetO_outStrOf] using hQ)
  unfold outStrOfPos at h
  rw [rowO_outStrOf, colO_outStrOf, innerSetO_outStrOf] at h
  change pack L (MaskTable.maskCode (MaskTable.maskSet
    (MaskTable.selectedMask (blockOf lay I, blockOf lay J)))).val
    (finFunctionFinEquiv (finFunctionFinEquiv.symm (offsetOf L m I))).val
    (finFunctionFinEquiv (finFunctionFinEquiv.symm (offsetOf L m J))).val = _ at h
  simpa only [MaskTable.maskCode_maskSet, Equiv.apply_symm_apply, offsetOf, N0,
    outStrOfPos, lay] using h

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
