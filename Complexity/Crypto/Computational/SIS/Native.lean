/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.SIS.Polynomial.Coefficients
public import Complexity.Computability.PolyTime.Int.Negacyclic

/-!
# Native coefficient multiplication for the existing Module-SIS ring

The total list operation is identified with `negacyclicMul`, including degree zero and
positive composite coefficient moduli. This is original supporting representation algebra;
it supplies neither a new encryption algorithm nor a security claim.

## Main results

* `negacyclicMulResidues_ofFn`: exact canonical coefficients for positive moduli.
-/

public section

namespace Cslib.Crypto

open Polynomial

/-- The native list product returns precisely the canonical coefficients of the existing
negacyclic multiplication. Positive composite moduli and modulus one are allowed. -/
theorem negacyclicMulResidues_ofFn {n q : ℕ} (hq : 0 < q)
    (a b : Fin n → ZMod q) :
    negacyclicMulResidues n q (List.ofFn fun i => (a i).val)
      (List.ofFn fun i => (b i).val) =
        List.ofFn fun i => (negacyclicMul a b i).val := by
  let : NeZero q := ⟨by omega⟩
  let ai : Fin n → ℤ := fun i => (a i).val
  let bi : Fin n → ℤ := fun i => (b i).val
  have hcast (i : Fin n) : ((negacyclicMul ai bi i : ℤ) : ZMod q) = negacyclicMul a b i := by
    have h := congrFun (map_negacyclicMul (Int.castRingHom (ZMod q)) ai bi) i
    simpa [ai, bi, Function.comp_def] using h
  have haTake : (List.ofFn fun i => (a i).val).take n = List.ofFn fun i => (a i).val :=
    List.take_of_length_le (by simp)
  have hbTake : (List.ofFn fun i => (b i).val).take n = List.ofFn fun i => (b i).val :=
    List.take_of_length_le (by simp)
  apply List.ext_getElem (by simp)
  intro i hi hj
  have hin : i < n := by simpa using hi
  simp only [negacyclicMulResidues, haTake, hbTake, List.map_ofFn,
    List.getElem_map, List.getElem_range, List.getElem_ofFn]
  change (((mulZJet (2 * n) (List.ofFn ai) (List.ofFn bi)).getD i 0 -
    (mulZJet (2 * n) (List.ofFn ai) (List.ofFn bi)).getD (n + i) 0) % (q : ℤ)).toNat = _
  rw [← coeff_ofCoeffList, coeff_ofCoeffList_mulZJet (by omega),
    ← coeff_ofCoeffList, coeff_ofCoeffList_mulZJet (by omega),
    ← negacyclicMul_eq_coeff_mul ai bi ⟨i, hin⟩, ← ZMod.val_intCast]
  simpa only [Int.toNat_natCast] using congrArg ZMod.val (hcast ⟨i, hin⟩)

end Cslib.Crypto
