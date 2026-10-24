/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.Runtime.Lift.Defs
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Mathlib.Data.List.GetD

/-!
# Magnitude bounds and polynomial-time certificates for the integer lift tables

`Complexity/Computability/Circuit/Rational/Runtime/Lift/Defs.lean` defines the list-level programs
`coeffRow`, `testRows`,
`liftTable`, and `liftRows` that materialize the integer Taylor test matrices and integer lift
tables at a grid point. This file bounds the magnitude and bit length of every value those programs
compute: each coefficient, each shift-and-add intermediate, each power, each partial product and
term, every prefix sum, and every entry. For `n + 1` matrices, `M` residues and grid coordinates at
most `H`, all of them have at most `Rational.liftBits n M H` bits, which at the generator's
parameters is `Rational.PolynomialBounds.logarithmic n s + 2`. Using these bounds, it certifies that
`coeffRows`, `testRows`, `liftTable`, and `liftRows` are computable in polynomial time on
multi-tape Turing machines.

## Main definitions

* `Cslib.Circuits.Rational.liftBits`: the bit-length budget of the lift program.
* `Cslib.Circuits.Rational.coeffEntryBound`, `Cslib.Circuits.Rational.coeffRowBound`: encoded
  length bounds on intermediate coefficient rows.

## Main results

* `Cslib.Circuits.Rational.intBits_coeffRow_le`, `Cslib.Circuits.Rational.intBits_test_le`,
  `Cslib.Circuits.Rational.intBits_lift_le`, `Cslib.Circuits.Rational.intBits_le_of_mem_liftRows`:
  the bit-length bounds.
* `Cslib.Circuits.Rational.intBits_le_of_mem_liftRows_parameters`: at the generator's parameters,
  every entry has at most `logConstant * (n + s + 1) ^ 22 + 2` bits.
* `Cslib.Circuits.Rational.length_encList_coeffRow_le`: encoded length bound on intermediate
  coefficient rows.
* `Cslib.Circuits.Rational.computableInPolyTime_coeffRow`,
  `Cslib.Circuits.Rational.computableInPolyTime_testRows`,
  `Cslib.Circuits.Rational.computableInPolyTime_liftTable`,
  `Cslib.Circuits.Rational.computableInPolyTime_liftRows`,
  `Cslib.Circuits.Rational.liftRows_polytime`: polynomial-time certificates for the coefficient
  rows, the Taylor test matrix and the integer lift tables.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (files
  lean/OAI/Computability/RationalHitting/TaylorComputation.lean and LiftComputation.lean), via
  the complexitylib port [Schlesinger2026RationalHitting] at revision
  add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Rational

/-! ### Magnitude bounds -/

private lemma natAbs_pow_le {z : ℤ} {H : ℕ} (hH : 1 ≤ H) (hz : z.natAbs ≤ H) {q M : ℕ}
    (hq : q ≤ M) :
    (z ^ q).natAbs ≤ H ^ M := by
  rw [Int.natAbs_pow]
  exact (Nat.pow_le_pow_left hz q).trans (Nat.pow_le_pow_right hH hq)

section CoeffBounds

variable {c : ℤ} {w : ℕ} (hw : 1 ≤ w) (hc : c.natAbs ≤ w)
include hw hc

/-- The coefficients of `(X + c) ^ k` are at most `(2 * w) ^ k` in absolute value, by
`IntegralTest.coeff_bound`. -/
private theorem natAbs_getD_coeffRow_le (k i : ℕ) :
    ((coeffRow c k).getD i 0).natAbs ≤ (2 * w) ^ k := by
  have h := IntegralTest.coeff_bound c w k k i hw
    (by rw [Int.abs_eq_natAbs]; exact_mod_cast hc) le_rfl
  rw [← getD_coeffRow, Int.abs_eq_natAbs] at h
  exact_mod_cast h

/-- The values computed by the shift-and-add step from `coeffRow c k`: the shifted coefficient,
the scaled coefficient and their sum. -/
private theorem natAbs_shiftAdd_le (k i : ℕ) :
    ((0 :: coeffRow c k).getD i 0).natAbs ≤ (2 * w) ^ (k + 1) ∧
      (c * (coeffRow c k).getD i 0).natAbs ≤ (2 * w) ^ (k + 1) ∧
      ((0 :: coeffRow c k).getD i 0 + c * (coeffRow c k).getD i 0).natAbs ≤
        (2 * w) ^ (k + 1) := by
  have hrow := natAbs_getD_coeffRow_le hw hc k
  refine ⟨?_, ?_, ?_⟩
  · cases i with
    | zero => simp
    | succ i =>
      rw [List.getD_cons_succ]
      exact (hrow i).trans (Nat.pow_le_pow_right (by omega) (by omega))
  · rw [Int.natAbs_mul, pow_succ, Nat.mul_comm c.natAbs]
    exact Nat.mul_le_mul (hrow i) (by omega)
  · rw [← getD_shiftAddRow, ← coeffRow_succ]
    exact natAbs_getD_coeffRow_le hw hc (k + 1) i

private theorem natAbs_rowEntry_coeffRows_le (M k i : ℕ) :
    (rowEntry (coeffRows c M) k i).natAbs ≤ (2 * w) ^ M := by
  rw [rowEntry_coeffRows]
  split_ifs with h
  · exact (natAbs_getD_coeffRow_le hw hc k i).trans (Nat.pow_le_pow_right (by omega) h.le)
  · simp

end CoeffBounds

section TestBounds

variable {M : ℕ} {a t : ℤ} {w H : ℕ} (hw : 1 ≤ w) (ha : a.natAbs ≤ w) (hH : 1 ≤ H)
  (ht : t.natAbs ≤ H)

include hw ha in
private theorem natAbs_coeffProduct_le (k u v q : ℕ) :
    (rowEntry (coeffRows (-a) M) k u * rowEntry (coeffRows a M) v q).natAbs ≤
      (2 * w) ^ (2 * M) := by
  rw [Int.natAbs_mul, show 2 * M = M + M by omega, pow_add]
  exact Nat.mul_le_mul (natAbs_rowEntry_coeffRows_le hw (by simpa using ha) M k u)
    (natAbs_rowEntry_coeffRows_le hw ha M v q)

include hw ha hH ht

private theorem natAbs_testTerm_le {q : ℕ} (hq : q ≤ M) (u v : ℕ) :
    (testTerm M (coeffRows (-a) M) (coeffRows a M) t u v q).natAbs ≤
      (2 * w) ^ (2 * M) * H ^ M := by
  rw [testTerm, Int.natAbs_mul]
  exact Nat.mul_le_mul (natAbs_coeffProduct_le hw ha ..) (natAbs_pow_le hH ht hq)

/-- Every prefix sum of the summands of a Taylor entry. -/
private theorem natAbs_testTerms_take_sum_le (u v m : ℕ) :
    ((testTerms M (coeffRows (-a) M) (coeffRows a M) t u v).take m).sum.natAbs ≤
      M * ((2 * w) ^ (2 * M) * H ^ M) := by
  refine natAbs_take_sum_le_of_length (by simp [testTerms]) (fun z hz => ?_) m
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
  exact natAbs_testTerm_le hw ha hH ht (List.mem_range.mp hq).le u v

private theorem natAbs_rowEntry_testRows_le (N u v : ℕ) :
    (rowEntry (testRows M N a t) u v).natAbs ≤ M * ((2 * w) ^ (2 * M) * H ^ M) := by
  rw [testRows, rowEntry_tabulateRows]
  split_ifs
  · rw [testEntry]
    split_ifs
    · have h := natAbs_testTerms_take_sum_le (M := M) hw ha hH ht u v M
      rwa [List.take_of_length_le (by simp [testTerms])] at h
    · simp
  · simp

end TestBounds

private lemma natAbs_signedCoeff_le (Dg z i j : ℕ) : (signedCoeff Dg z i j).natAbs ≤ 1 := by
  unfold signedCoeff
  split_ifs <;> simp [Int.natAbs_pow]

section LiftBounds

variable {M Dg : ℕ} {T : List (List ℤ)} {p r : ℤ} {A H : ℕ}
  (hT : ∀ k l, (rowEntry T k l).natAbs ≤ A) (hH : 1 ≤ H) (hp : p.natAbs ≤ H) (hr : r.natAbs ≤ H)
include hT

/-- The partial products of a lift term, for any indices. -/
private theorem natAbs_liftPartial_le (k l z i j : ℕ) :
    (rowEntry T k l * signedCoeff Dg z i j).natAbs ≤ A := by
  rw [Int.natAbs_mul]
  simpa using Nat.mul_le_mul (hT k l) (natAbs_signedCoeff_le Dg z i j)

include hH hp

private theorem natAbs_liftPartial_pow_le (k l z i j : ℕ) {α : ℕ} (hα : α ≤ M) :
    (rowEntry T k l * signedCoeff Dg z i j * p ^ α).natAbs ≤ A * H ^ M := by
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul (natAbs_liftPartial_le hT ..) (natAbs_pow_le hH hp hα)

include hr

private theorem natAbs_liftTerm_le {α : ℕ} (hα : α < M) (u v i j κ : ℕ) :
    (liftTerm M Dg T p r u v i j α κ).natAbs ≤ A * H ^ (2 * M) := by
  rw [liftTerm, Int.natAbs_mul, show 2 * M = M + M by omega, pow_add, ← Nat.mul_assoc]
  exact Nat.mul_le_mul (natAbs_liftPartial_pow_le hT hH hp _ _ _ _ _ hα.le)
    (natAbs_pow_le hH hr (Nat.mod_lt _ (by omega)).le)

/-- Every prefix sum of an inner sum of a lift entry. -/
private theorem natAbs_liftTerms_take_sum_le {α : ℕ} (hα : α < M) (u v i j m : ℕ) :
    ((liftTerms M Dg T p r u v i j α).take m).sum.natAbs ≤ M * (A * H ^ (2 * M)) := by
  refine natAbs_take_sum_le_of_length (by simp [liftTerms]) (fun z hz => ?_) m
  obtain ⟨κ, -, rfl⟩ := List.mem_map.mp hz
  exact natAbs_liftTerm_le hT hH hp hr hα u v i j κ

/-- Every prefix sum of the outer sum of a lift entry. -/
private theorem natAbs_liftSums_take_sum_le (u v i j m : ℕ) :
    ((liftSums M Dg T p r u v i j).take m).sum.natAbs ≤ M * (M * (A * H ^ (2 * M))) := by
  refine natAbs_take_sum_le_of_length (by simp [liftSums]) (fun z hz => ?_) m
  obtain ⟨α, hα, rfl⟩ := List.mem_map.mp hz
  have h := natAbs_liftTerms_take_sum_le (Dg := Dg) hT hH hp hr (List.mem_range.mp hα) u v i j M
  rwa [List.take_of_length_le (by simp [liftTerms])] at h

private theorem natAbs_liftEntry_le (u v i j : ℕ) :
    (liftEntry M Dg T p r u v i j).natAbs ≤ M * (M * (A * H ^ (2 * M))) := by
  have h := natAbs_liftSums_take_sum_le (M := M) (Dg := Dg) hT hH hp hr u v i j M
  rwa [List.take_of_length_le (by simp [liftSums])] at h

private theorem natAbs_rowEntry_liftTable_le (i j : ℕ) :
    (rowEntry (liftTable M Dg T p r) i j).natAbs ≤ M * (M * (A * H ^ (2 * M))) := by
  rw [liftTable, rowEntry_tabulateRows]
  split_ifs
  · exact natAbs_liftEntry_le hT hH hp hr ..
  · simp

end LiftBounds

/-! ### Bit lengths -/

/-- The bit-length budget of the lift program, for `n + 1` matrices, `M` residues and grid
coordinates at most `H`. At the generator's parameters it is
`PolynomialBounds.logarithmic n s + 2` (`liftBits_parameters`). -/
def liftBits (n M H : ℕ) : ℕ :=
  4 * M + 4 * M * (n + 1) + 3 * M * H + 2

/-- At the generator's parameters, `liftBits` equals `PolynomialBounds.logarithmic n s + 2`. -/
lemma liftBits_parameters (n s : ℕ) :
    liftBits n (Parameters.ambientDimension n s) (Parameters.gridSize n s) =
      PolynomialBounds.logarithmic n s + 2 :=
  rfl

/-- At the generator's parameters, the bit-length budget is polynomial in `n + s + 1`. -/
private theorem liftBits_bound (n s : ℕ) :
    liftBits n (Parameters.ambientDimension n s) (Parameters.gridSize n s) ≤
      PolynomialBounds.logConstant * (n + s + 1) ^ 22 + 2 := by
  rw [liftBits_parameters]
  exact Nat.add_le_add_right (PolynomialBounds.logarithmic_bound n s) 2

/-- Every value of magnitude at most `M ^ 3 * (2 * (n + 1)) ^ (2 * M) * H ^ (3 * M)` fits in the
budget. -/
private theorem intBits_le_liftBits {n M H : ℕ} {z : ℤ}
    (hz : z.natAbs ≤ M ^ 3 * (2 * (n + 1)) ^ (2 * M) * H ^ (3 * M)) :
    intBits z ≤ liftBits n M H := by
  have hM : M ^ 3 ≤ 2 ^ (3 * M) := by
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le 3
  have hw : (2 * (n + 1)) ^ (2 * M) ≤ 2 ^ (2 * (n + 1) * (2 * M)) := by
    rw [pow_mul 2]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  have hH : H ^ (3 * M) ≤ 2 ^ (H * (3 * M)) := by
    rw [pow_mul 2]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  have hprod : M ^ 3 * (2 * (n + 1)) ^ (2 * M) * H ^ (3 * M) ≤
      2 ^ (4 * M + 4 * M * (n + 1) + 3 * M * H) :=
    calc _ ≤ 2 ^ (3 * M) * 2 ^ (2 * (n + 1) * (2 * M)) * 2 ^ (H * (3 * M)) := by gcongr
      _ = 2 ^ (3 * M + 4 * M * (n + 1) + 3 * M * H) := by
          rw [← pow_add, ← pow_add]
          congr 1
          ring
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt : z.natAbs < 2 ^ (4 * M + 4 * M * (n + 1) + 3 * M * H + 1) :=
    (hz.trans hprod).trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _))
  exact (intBits_le_iff _ _).mpr hlt

/-- Each factor of the magnitude bound can be weakened. -/
private lemma le_liftMagnitude {M w H i j k : ℕ} (hM : 1 ≤ M) (hw : 1 ≤ w) (hH : 1 ≤ H) (hi : i ≤ 3)
    (hj : j ≤ 2 * M) (hk : k ≤ 3 * M) :
    M ^ i * (2 * w) ^ j * H ^ k ≤ M ^ 3 * (2 * w) ^ (2 * M) * H ^ (3 * M) := by
  gcongr

section Bits

variable {n M H : ℕ} (hM : 1 ≤ M) (hH : 1 ≤ H)
include hM hH

/-- The bit lengths of the coefficients of `(X + c) ^ k` for `k < M`, and of the values computed
by the shift-and-add step from them. -/
theorem intBits_coeffRow_le {c : ℤ} (hc : c.natAbs ≤ n) {k : ℕ} (hk : k < M) (i : ℕ) :
    intBits ((coeffRow c k).getD i 0) ≤ liftBits n M H ∧
      intBits ((0 :: coeffRow c k).getD i 0) ≤ liftBits n M H ∧
      intBits (c * (coeffRow c k).getD i 0) ≤ liftBits n M H ∧
      intBits ((0 :: coeffRow c k).getD i 0 + c * (coeffRow c k).getD i 0) ≤ liftBits n M H := by
  have hw : 1 ≤ n + 1 := by omega
  have hc' : c.natAbs ≤ n + 1 := by omega
  have hB (z : ℤ) (h : z.natAbs ≤ (2 * (n + 1)) ^ (k + 1)) : intBits z ≤ liftBits n M H := by
    refine intBits_le_liftBits (h.trans ?_)
    calc (2 * (n + 1)) ^ (k + 1) = M ^ 0 * (2 * (n + 1)) ^ (k + 1) * H ^ 0 := by simp
      _ ≤ _ := le_liftMagnitude hM hw hH (by omega) (by omega) (by omega)
  obtain ⟨h₁, h₂, h₃⟩ := natAbs_shiftAdd_le hw hc' k i
  exact ⟨hB _ ((natAbs_getD_coeffRow_le hw hc' k i).trans
    (Nat.pow_le_pow_right (by omega) (by omega))), hB _ h₁, hB _ h₂, hB _ h₃⟩

/-- The bit lengths of the powers `z ^ q` for `q ≤ M`; computing a power by repeated
multiplication passes only through smaller powers. -/
theorem intBits_pow_le {z : ℤ} (hz : z.natAbs ≤ H) {q : ℕ} (hq : q ≤ M) :
    intBits (z ^ q) ≤ liftBits n M H := by
  refine intBits_le_liftBits ((natAbs_pow_le hH hz hq).trans ?_)
  calc H ^ M = M ^ 0 * (2 * (n + 1)) ^ 0 * H ^ M := by simp
    _ ≤ _ := le_liftMagnitude hM (by omega) hH (by omega) (by omega) (by omega)

/-- The bit lengths of the values computed for the Taylor test matrix `testRows M N a t`: the
products of coefficients, the terms, every prefix sum of the terms of an entry, and the
entries. -/
theorem intBits_test_le {a t : ℤ} (ha : a.natAbs ≤ n) (ht : t.natAbs ≤ H) (N k u v q m : ℕ)
    (hq : q < M) :
    intBits (rowEntry (coeffRows (-a) M) k u * rowEntry (coeffRows a M) v q) ≤ liftBits n M H ∧
      intBits (testTerm M (coeffRows (-a) M) (coeffRows a M) t u v q) ≤ liftBits n M H ∧
      intBits ((testTerms M (coeffRows (-a) M) (coeffRows a M) t u v).take m).sum ≤
        liftBits n M H ∧
      intBits (rowEntry (testRows M N a t) u v) ≤ liftBits n M H := by
  have hw : 1 ≤ n + 1 := by omega
  have ha' : a.natAbs ≤ n + 1 := by omega
  have hB (i j k' : ℕ) (hi : i ≤ 3) (hj : j ≤ 2 * M) (hk : k' ≤ 3 * M) {z : ℤ}
      (h : z.natAbs ≤ M ^ i * (2 * (n + 1)) ^ j * H ^ k') : intBits z ≤ liftBits n M H :=
    intBits_le_liftBits (h.trans (le_liftMagnitude hM hw hH hi hj hk))
  refine ⟨hB 0 (2 * M) 0 (by omega) le_rfl (by omega) ?_, hB 0 (2 * M) M (by omega) le_rfl
    (by omega) ?_, hB 1 (2 * M) M (by omega) le_rfl (by omega) ?_,
    hB 1 (2 * M) M (by omega) le_rfl (by omega) ?_⟩
  · exact (natAbs_coeffProduct_le hw ha' k u v q).trans_eq (by ring)
  · exact (natAbs_testTerm_le hw ha' hH ht hq.le u v).trans_eq (by ring)
  · exact (natAbs_testTerms_take_sum_le hw ha' hH ht u v m).trans_eq (by ring)
  · exact (natAbs_rowEntry_testRows_le hw ha' hH ht N u v).trans_eq (by ring)

/-- The bit lengths of the values computed for the integer lift with the Taylor test matrix
`testRows M N a t`: the partial products and the terms, every prefix sum of an inner sum and of
the outer sum, the entries and the entries of the lift table. -/
theorem intBits_lift_le {a t p r : ℤ} (ha : a.natAbs ≤ n) (ht : t.natAbs ≤ H)
    (hp : p.natAbs ≤ H) (hr : r.natAbs ≤ H) (N Dg u v i j k l z m : ℕ) {α κ : ℕ} (hα : α < M) :
    intBits (rowEntry (testRows M N a t) k l * signedCoeff Dg z i j) ≤ liftBits n M H ∧
      intBits (rowEntry (testRows M N a t) k l * signedCoeff Dg z i j * p ^ α) ≤
        liftBits n M H ∧
      intBits (liftTerm M Dg (testRows M N a t) p r u v i j α κ) ≤ liftBits n M H ∧
      intBits ((liftTerms M Dg (testRows M N a t) p r u v i j α).take m).sum ≤
        liftBits n M H ∧
      intBits ((liftSums M Dg (testRows M N a t) p r u v i j).take m).sum ≤ liftBits n M H ∧
      intBits (liftEntry M Dg (testRows M N a t) p r u v i j) ≤ liftBits n M H ∧
      intBits (rowEntry (liftTable M Dg (testRows M N a t) p r) k l) ≤ liftBits n M H := by
  have hw : 1 ≤ n + 1 := by omega
  have ha' : a.natAbs ≤ n + 1 := by omega
  have hT := natAbs_rowEntry_testRows_le hw ha' hH ht (M := M) N
  have hB (i j k' : ℕ) (hi : i ≤ 3) (hj : j ≤ 2 * M) (hk : k' ≤ 3 * M) {z : ℤ}
      (h : z.natAbs ≤ M ^ i * (2 * (n + 1)) ^ j * H ^ k') : intBits z ≤ liftBits n M H :=
    intBits_le_liftBits (h.trans (le_liftMagnitude hM hw hH hi hj hk))
  refine ⟨hB 1 (2 * M) M (by omega) le_rfl (by omega) ?_,
    hB 1 (2 * M) (2 * M) (by omega) le_rfl (by omega) ?_,
    hB 1 (2 * M) (3 * M) (by omega) le_rfl le_rfl ?_,
    hB 2 (2 * M) (3 * M) (by omega) le_rfl le_rfl ?_,
    hB 3 (2 * M) (3 * M) le_rfl le_rfl le_rfl ?_,
    hB 3 (2 * M) (3 * M) le_rfl le_rfl le_rfl ?_,
    hB 3 (2 * M) (3 * M) le_rfl le_rfl le_rfl ?_⟩
  · exact (natAbs_liftPartial_le hT k l z i j).trans_eq (by ring)
  · exact (natAbs_liftPartial_pow_le hT hH hp k l z i j hα.le).trans_eq (by ring)
  · exact (natAbs_liftTerm_le hT hH hp hr hα u v i j κ).trans_eq (by ring)
  · exact (natAbs_liftTerms_take_sum_le (Dg := Dg) hT hH hp hr hα u v i j m).trans_eq (by ring)
  · exact (natAbs_liftSums_take_sum_le (Dg := Dg) hT hH hp hr u v i j m).trans_eq (by ring)
  · exact (natAbs_liftEntry_le (Dg := Dg) hT hH hp hr u v i j).trans_eq (by ring)
  · exact (natAbs_rowEntry_liftTable_le (Dg := Dg) hT hH hp hr k l).trans_eq (by ring)

/-- Every entry of every integer lift table at a grid point with coordinates at most `H` has
at most `liftBits n M H` bits. -/
theorem intBits_le_of_mem_liftRows {N Dg t p r : ℕ} (ht : t ≤ H) (hp : p ≤ H) (hr : r ≤ H)
    {table : List (List ℤ)} (htable : table ∈ liftRows n N M Dg t p r) {row : List ℤ}
    (hrow : row ∈ table) {z : ℤ} (hz : z ∈ row) : intBits z ≤ liftBits n M H := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp htable
  obtain ⟨k, l, rfl⟩ := exists_rowEntry_eq hrow hz
  have ha' : ((a : ℕ) : ℤ).natAbs ≤ n := by
    simpa using Nat.lt_succ_iff.mp (List.mem_range.mp ha)
  exact (intBits_lift_le hM hH ha' (by simpa using ht) (by simpa using hp) (by simpa using hr)
    N Dg 0 0 0 0 k l 0 0 (α := 0) (κ := 0) hM).2.2.2.2.2.2

end Bits

/-- At the generator's parameters, every entry of every integer lift table at a grid point has
at most `logConstant * (n + s + 1) ^ 22 + 2` bits. -/
theorem intBits_le_of_mem_liftRows_parameters {n s t p r : ℕ} (ht : t ≤ Parameters.gridSize n s)
    (hp : p ≤ Parameters.gridSize n s) (hr : r ≤ Parameters.gridSize n s) {table : List (List ℤ)}
    (htable : table ∈ liftRows n (Parameters.truncation n s) (Parameters.ambientDimension n s)
      (CyclotomicRing.degree (Parameters.exponent n s)) t p r)
    {row : List ℤ} (hrow : row ∈ table) {z : ℤ} (hz : z ∈ row) :
    intBits z ≤ PolynomialBounds.logConstant * (n + s + 1) ^ 22 + 2 :=
  (intBits_le_of_mem_liftRows (by unfold Parameters.ambientDimension; exact Nat.one_le_two_pow)
    (by unfold Parameters.gridSize; omega) ht hp hr htable hrow hz).trans (liftBits_bound n s)

/-! ### Polynomial-time certificates -/

open Turing MultiTapeTM MultiTapeTM.ComputableTidilyInPolyTime

/-- Upper bound on the bit length of any entry of `coeffRow c i` for `i ≤ k`, where `L` is the
encoded length of `c`. -/
def coeffEntryBound (L k : ℕ) : ℕ := (L + 1) * k + 2

/-- Upper bound on the encoded length of `coeffRow c i` for `i ≤ k`, where `L` is the encoded
length of `c`. -/
def coeffRowBound (L k : ℕ) : ℕ := (k + 1) * (2 * coeffEntryBound L k + 1)

/-- Every intermediate coefficient row up to stage `k` has encoded length bounded by
`coeffRowBound`. -/
theorem length_encList_coeffRow_le (c : ℤ) {i k : ℕ} (hik : i ≤ k) :
    (encList encIntBin (coeffRow c i)).length ≤ coeffRowBound (encIntBin c).length k := by
  set L := (encIntBin c).length
  have hc_lt : c.natAbs < 2 ^ L := by
    rw [← intBits_le_iff, intBits_eq_length_encIntBin]
    exact Nat.le_succ L
  have h2w : 2 * (c.natAbs + 1) ≤ 2 ^ (L + 1) := by
    rw [pow_succ']
    exact Nat.mul_le_mul_left 2 hc_lt
  have hentry {z : ℤ} (hz : z ∈ coeffRow c i) :
      (encIntBin z).length ≤ coeffEntryBound L k := by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
    rw [← intBits_eq_length_encIntBin, coeffEntryBound, intBits_le_iff,
      ← List.getD_eq_getElem _ 0 hj]
    calc ((coeffRow c i).getD j 0).natAbs
        ≤ (2 * (c.natAbs + 1)) ^ i := natAbs_getD_coeffRow_le (by omega) (by omega) i j
      _ ≤ (2 ^ (L + 1)) ^ i := Nat.pow_le_pow_left h2w i
      _ = 2 ^ ((L + 1) * i) := (pow_mul 2 (L + 1) i).symm
      _ ≤ 2 ^ ((L + 1) * k) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hik)
      _ < 2 ^ ((L + 1) * k + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
  refine (length_encList_le encIntBin (coeffRow c i) fun z hz => hentry hz).trans ?_
  rw [length_coeffRow]
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hik 1)

private lemma polyBounded_coeffRowBound {α : Type} {size L k : α → ℕ}
    (hL : PolyBounded size L) (hk : PolyBounded size k) :
    PolyBounded size (fun x => coeffRowBound (L x) (k x)) := by
  have hentry : PolyBounded size (fun x => coeffEntryBound (L x) (k x)) :=
    ((hL.add (.const 1)).mul hk).add (.const 2)
  exact (hk.add (.const 1)).mul (((PolyBounded.const 2).mul hentry).add (.const 1))

variable {α : Type} {encIn : α ↪ List Bool}

@[local fun_prop]
private theorem listGetD_intBin {l : α → List ℤ} {i : α → ℕ}
    (hl : ComputableTidilyInPolyTime l encIn (encList encIntBin))
    (hi : ComputableTidilyInPolyTime i encIn encUnary) (d : ℤ) :
    ComputableTidilyInPolyTime (fun x => (l x).getD (i x) d) encIn encIntBin :=
  (listGetD (encA := encIntBin) d).comp (hl.prod hi)

@[local fun_prop]
private theorem intBin_of_unary {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => (n x : ℤ)) encIn encIntBin :=
  intBin_natCast.comp (unary_to_binary.comp hn)

/-- Equality testing of two unary-encoded natural-number functions is computable in polynomial
time. -/
@[fun_prop]
theorem unary_decide_eq {a b : α → ℕ}
    (ha : ComputableInPolyTime a encIn encUnary)
    (hb : ComputableInPolyTime b encIn encUnary) :
    ComputableInPolyTime (fun x => decide (a x = b x)) encIn encBool := by
  have ha := ha.tidy
  have hb := hb.tidy
  exact .of_tidy ((decide_eq encUnary).comp (ha.prod hb))

/-- One shift-and-add step of the coefficient recurrence is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_shiftAddRow {c : α → ℤ} {l : α → List ℤ}
    (hc : ComputableInPolyTime c encIn encIntBin)
    (hl : ComputableInPolyTime l encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => shiftAddRow (c x) (l x)) encIn (encList encIntBin) := by
  have hc := hc.tidy
  have hl := hl.tidy
  refine .of_tidy ?_
  unfold shiftAddRow
  fun_prop

/-- Computing the coefficient row `coeffRow c k` is polynomial-time for a binary integer `c` and a
unary degree `k`. -/
@[fun_prop]
theorem computableInPolyTime_coeffRow {c : α → ℤ} {k : α → ℕ}
    (hc : ComputableInPolyTime c encIn encIntBin)
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => coeffRow (c x) (k x)) encIn (encList encIntBin) := by
  have hc := hc.tidy
  have hk := hk.tidy
  exact .of_tidy (iterateWith hc hk (const [1])
    (computableInPolyTime_shiftAddRow (.of_tidy (fst _ _)) (.of_tidy (snd _ _))).tidy
    (polyBounded_coeffRowBound hc.polyBounded_length hk.polyBounded)
    fun x _ hi => length_encList_coeffRow_le (c x) hi)

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Computing the table of coefficient rows `coeffRows c M` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_coeffRows {c : α → ℤ} {M : α → ℕ}
    (hc : ComputableInPolyTime c encIn encIntBin)
    (hM : ComputableInPolyTime M encIn encUnary) :
    ComputableInPolyTime (fun x => coeffRows (c x) (M x))
      encIn (encList (encList encIntBin)) := by
  have hc := hc.tidy
  have hM := hM.tidy
  refine .of_tidy ?_
  unfold coeffRows
  fun_prop

/-- Computing one summand of a Taylor test matrix entry is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_testTerm {M u v q : α → ℕ} {minus plus : α → List (List ℤ)}
    {t : α → ℤ}
    (hM : ComputableInPolyTime M encIn encUnary)
    (hminus : ComputableInPolyTime minus encIn (encList (encList encIntBin)))
    (hplus : ComputableInPolyTime plus encIn (encList (encList encIntBin)))
    (ht : ComputableInPolyTime t encIn encIntBin)
    (hu : ComputableInPolyTime u encIn encUnary)
    (hv : ComputableInPolyTime v encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary) :
    ComputableInPolyTime
      (fun x => testTerm (M x) (minus x) (plus x) (t x) (u x) (v x) (q x))
      encIn encIntBin := by
  unfold testTerm
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Computing the list of summands of a Taylor test matrix entry is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_testTerms {M u v : α → ℕ} {minus plus : α → List (List ℤ)}
    {t : α → ℤ}
    (hM : ComputableInPolyTime M encIn encUnary)
    (hminus : ComputableInPolyTime minus encIn (encList (encList encIntBin)))
    (hplus : ComputableInPolyTime plus encIn (encList (encList encIntBin)))
    (ht : ComputableInPolyTime t encIn encIntBin)
    (hu : ComputableInPolyTime u encIn encUnary)
    (hv : ComputableInPolyTime v encIn encUnary) :
    ComputableInPolyTime
      (fun x => testTerms (M x) (minus x) (plus x) (t x) (u x) (v x))
      encIn (encList encIntBin) := by
  have hM := hM.tidy
  have hminus := hminus.tidy
  have hplus := hplus.tidy
  have ht := ht.tidy
  have hu := hu.tidy
  have hv := hv.tidy
  refine .of_tidy ?_
  unfold testTerms
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Computing one entry of the integer Taylor test matrix is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_testEntry {M N u v : α → ℕ} {minus plus : α → List (List ℤ)}
    {t : α → ℤ}
    (hM : ComputableInPolyTime M encIn encUnary)
    (hN : ComputableInPolyTime N encIn encUnary)
    (hminus : ComputableInPolyTime minus encIn (encList (encList encIntBin)))
    (hplus : ComputableInPolyTime plus encIn (encList (encList encIntBin)))
    (ht : ComputableInPolyTime t encIn encIntBin)
    (hu : ComputableInPolyTime u encIn encUnary)
    (hv : ComputableInPolyTime v encIn encUnary) :
    ComputableInPolyTime
      (fun x => testEntry (M x) (N x) (minus x) (plus x) (t x) (u x) (v x))
      encIn encIntBin := by
  have hM := hM.tidy
  have hN := hN.tidy
  have hminus := hminus.tidy
  have hplus := hplus.tidy
  have ht := ht.tidy
  have hu := hu.tidy
  have hv := hv.tidy
  refine .of_tidy ?_
  unfold testEntry
  fun_prop

/-- Computing the integer Taylor test matrix `testRows M N a t` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_testRows {M N : α → ℕ} {a t : α → ℤ}
    (hM : ComputableInPolyTime M encIn encUnary)
    (hN : ComputableInPolyTime N encIn encUnary)
    (ha : ComputableInPolyTime a encIn encIntBin)
    (ht : ComputableInPolyTime t encIn encIntBin) :
    ComputableInPolyTime (fun x => testRows (M x) (N x) (a x) (t x))
      encIn (encList (encList encIntBin)) := by
  unfold testRows
  fun_prop

/-- Computing the signed cyclotomic regular-representation coefficient is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_signedCoeff {Dg z i j : α → ℕ}
    (hDg : ComputableInPolyTime Dg encIn encUnary)
    (hz : ComputableInPolyTime z encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => signedCoeff (Dg x) (z x) (i x) (j x))
      encIn encIntBin := by
  have hDg := hDg.tidy
  have hz := hz.tidy
  have hi := hi.tidy
  have hj := hj.tidy
  refine .of_tidy ?_
  unfold signedCoeff
  fun_prop

/-- Computing one summand of an integer lift entry is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_liftTerm {M Dg u v i j a k : α → ℕ}
    {T : α → List (List ℤ)} {p r : α → ℤ}
    (hM : ComputableInPolyTime M encIn encUnary)
    (hDg : ComputableInPolyTime Dg encIn encUnary)
    (hT : ComputableInPolyTime T encIn (encList (encList encIntBin)))
    (hp : ComputableInPolyTime p encIn encIntBin)
    (hr : ComputableInPolyTime r encIn encIntBin)
    (hu : ComputableInPolyTime u encIn encUnary)
    (hv : ComputableInPolyTime v encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary)
    (ha : ComputableInPolyTime a encIn encUnary)
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime
      (fun x => liftTerm (M x) (Dg x) (T x) (p x) (r x) (u x) (v x) (i x) (j x) (a x) (k x))
      encIn encIntBin := by
  unfold liftTerm
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Computing the inner list of summands of an integer lift entry is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_liftTerms {M Dg u v i j a : α → ℕ}
    {T : α → List (List ℤ)} {p r : α → ℤ}
    (hM : ComputableInPolyTime M encIn encUnary)
    (hDg : ComputableInPolyTime Dg encIn encUnary)
    (hT : ComputableInPolyTime T encIn (encList (encList encIntBin)))
    (hp : ComputableInPolyTime p encIn encIntBin)
    (hr : ComputableInPolyTime r encIn encIntBin)
    (hu : ComputableInPolyTime u encIn encUnary)
    (hv : ComputableInPolyTime v encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary)
    (ha : ComputableInPolyTime a encIn encUnary) :
    ComputableInPolyTime
      (fun x => liftTerms (M x) (Dg x) (T x) (p x) (r x) (u x) (v x) (i x) (j x) (a x))
      encIn (encList encIntBin) := by
  have hM := hM.tidy
  have hDg := hDg.tidy
  have hT := hT.tidy
  have hp := hp.tidy
  have hr := hr.tidy
  have hu := hu.tidy
  have hv := hv.tidy
  have hi := hi.tidy
  have hj := hj.tidy
  have ha := ha.tidy
  refine .of_tidy ?_
  unfold liftTerms
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Computing the list of inner sums of an integer lift entry is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_liftSums {M Dg u v i j : α → ℕ}
    {T : α → List (List ℤ)} {p r : α → ℤ}
    (hM : ComputableInPolyTime M encIn encUnary)
    (hDg : ComputableInPolyTime Dg encIn encUnary)
    (hT : ComputableInPolyTime T encIn (encList (encList encIntBin)))
    (hp : ComputableInPolyTime p encIn encIntBin)
    (hr : ComputableInPolyTime r encIn encIntBin)
    (hu : ComputableInPolyTime u encIn encUnary)
    (hv : ComputableInPolyTime v encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime
      (fun x => liftSums (M x) (Dg x) (T x) (p x) (r x) (u x) (v x) (i x) (j x))
      encIn (encList encIntBin) := by
  have hM := hM.tidy
  have hDg := hDg.tidy
  have hT := hT.tidy
  have hp := hp.tidy
  have hr := hr.tidy
  have hu := hu.tidy
  have hv := hv.tidy
  have hi := hi.tidy
  have hj := hj.tidy
  refine .of_tidy ?_
  unfold liftSums
  fun_prop

/-- Computing one entry of the integer lift matrix is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_liftEntry {M Dg u v i j : α → ℕ}
    {T : α → List (List ℤ)} {p r : α → ℤ}
    (hM : ComputableInPolyTime M encIn encUnary)
    (hDg : ComputableInPolyTime Dg encIn encUnary)
    (hT : ComputableInPolyTime T encIn (encList (encList encIntBin)))
    (hp : ComputableInPolyTime p encIn encIntBin)
    (hr : ComputableInPolyTime r encIn encIntBin)
    (hu : ComputableInPolyTime u encIn encUnary)
    (hv : ComputableInPolyTime v encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime
      (fun x => liftEntry (M x) (Dg x) (T x) (p x) (r x) (u x) (v x) (i x) (j x))
      encIn encIntBin := by
  unfold liftEntry
  fun_prop

/-- Computing the integer lift matrix `liftTable M Dg T p r` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_liftTable {M Dg : α → ℕ}
    {T : α → List (List ℤ)} {p r : α → ℤ}
    (hM : ComputableInPolyTime M encIn encUnary)
    (hDg : ComputableInPolyTime Dg encIn encUnary)
    (hT : ComputableInPolyTime T encIn (encList (encList encIntBin)))
    (hp : ComputableInPolyTime p encIn encIntBin)
    (hr : ComputableInPolyTime r encIn encIntBin) :
    ComputableInPolyTime
      (fun x => liftTable (M x) (Dg x) (T x) (p x) (r x))
      encIn (encList (encList encIntBin)) := by
  unfold liftTable
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Computing all `n + 1` integer lift tables `liftRows n N M Dg t p r` at a grid point is
polynomial-time from unary parameters and coordinates. -/
@[fun_prop]
theorem computableInPolyTime_liftRows {n N M Dg t p r : α → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hN : ComputableInPolyTime N encIn encUnary)
    (hM : ComputableInPolyTime M encIn encUnary)
    (hDg : ComputableInPolyTime Dg encIn encUnary)
    (ht : ComputableInPolyTime t encIn encUnary)
    (hp : ComputableInPolyTime p encIn encUnary)
    (hr : ComputableInPolyTime r encIn encUnary) :
    ComputableInPolyTime
      (fun x => liftRows (n x) (N x) (M x) (Dg x) (t x) (p x) (r x))
      encIn (encList (encList (encList encIntBin))) := by
  have hn := hn.tidy
  have hN := hN.tidy
  have hM := hM.tidy
  have hDg := hDg.tidy
  have ht := ht.tidy
  have hp := hp.tidy
  have hr := hr.tidy
  refine .of_tidy ?_
  unfold liftRows
  fun_prop

/-- Standalone polynomial-time certificate for `liftRows` on a 7-tuple of unary naturals. -/
@[fun_prop]
theorem liftRows_polytime :
    ComputableInPolyTime
      (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
        liftRows q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2)
      (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary
        (encPair encUnary (encPair encUnary encUnary))))))
      (encList (encList (encList encIntBin))) := by
  fun_prop

end Rational

end Cslib.Circuits
