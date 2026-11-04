/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerNative
public import Complexity.Foundations.Data.BitString.Block
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Exact register points requested by the raw controller

Dropping the target register and concatenating the remaining bank in cyclic order gives the
existing typed child-register point, with the original modulus padding on every cell.
-/

public section

namespace Cslib.TreeEval.Ary.Packed.RawController

/-- The physical request point contains exactly the cyclic typed registers, still padded. -/
theorem point_ofRegs {p d r : ℕ} (S : Ary.State (ZMod p) d r) (t : Fin (d + 1)) :
    point d r t.val (ofRegs S) = List.ofFn
      (fun a : Fin (d * r) => p +
        (Cslib.BitString.blocksEquiv.symm (fun j => S (Ary.reg t j)) a).val) := by
  have hlength := length_point (ofRegs S) (length_ofRegs S) t
  apply List.ext_getElem (hlength.trans List.length_ofFn.symm)
  intro a ha _
  let ai : Fin (d * r) := ⟨a, by omega⟩
  rcases hpair : finProdFinEquiv.symm ai with ⟨j, i⟩
  have hai : finProdFinEquiv (j, i) = ai := by
    rw [← hpair, Equiv.apply_symm_apply]
  have hav : i.val + r * j.val = a := congrArg Fin.val hai
  have hread := point_getD (ofRegs S) (length_ofRegs S) t j i
  rw [reg_eq] at hread
  change (point d r t.val (ofRegs S)).getD (i.val + r * j.val) 0 =
    (ofRegs S).getD (i.val + r * (Ary.reg t j).val) 0 at hread
  rw [hav] at hread
  rw [← List.getD_eq_getElem _ _ ha]
  rw [hread]
  change (ofRegs S).getD (finProdFinEquiv (Ary.reg t j, i)).val 0 = _
  rw [ofRegs, List.getD_ofFn_of_lt _ (finProdFinEquiv (Ary.reg t j, i)).isLt 0]
  simp only [List.getElem_ofFn]
  change p + (S (finProdFinEquiv.symm (finProdFinEquiv (Ary.reg t j, i))).1
      (finProdFinEquiv.symm (finProdFinEquiv (Ary.reg t j, i))).2).val =
    p + (S (Ary.reg t (finProdFinEquiv.symm ai).1) (finProdFinEquiv.symm ai).2).val
  rw [Equiv.symm_apply_apply]
  rw [hpair]

end Cslib.TreeEval.Ary.Packed.RawController
