/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.AssignmentLabels
public import Complexity.Computability.TreeEval.Ary.Packed.Executable
public import Complexity.Foundations.Data.BitString.Binary
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.Nat.Size

/-!
# Packed assignment labels agree with the existing gate decoder

The binary slices have their full label width whenever the supplied interpolation limit pays
the requested coordinates. On the actual packed grid, a child's slice is exactly the word
produced by `unpackBits` from the existing row-major `gridDigit` assignment. Powers occur only
in semantic specifications; the runtime reader uses the explicit limit's binary representation.
-/

public section

namespace Cslib.TreeEval.Ary.Packed.AssignmentLabels

open Cslib.BitString Turing.MultiTapePTM.BlockComputation.Encoding

/-- An in-capacity label has its full requested width. -/
theorem length_label (limit counter stride width child : ℕ)
    (hcapacity : child * stride + width ≤ limit.size) :
    (label (limit, counter, stride, width, child)).length = width := by
  simp only [label, NativeEncode.word, List.length_take, List.length_drop, List.length_ofFn]
  omega

/-- Reading an in-range label coordinate reads the corresponding assignment counter bit. -/
theorem getD_label (limit counter stride width child j : ℕ)
    (hcapacity : child * stride + width ≤ limit.size) (hj : j < width) :
    (label (limit, counter, stride, width, child)).getD j false =
      counter.testBit (child * stride + j) := by
  rw [label, List.getD_take_drop _ _ hj]
  exact List.getD_ofFn_of_lt _ (by omega) _

/-- The actual packed interpolation limit has room for every child's Boolean label. -/
theorem capacity {d r m b : ℕ} (hb : b ≤ r * m) (child : Fin d) :
    child.val * (r * m) + b ≤ ((2 ^ m) ^ (d * r)).size := by
  rw [← pow_mul, Nat.size_pow]
  have hc := Nat.mul_le_mul_right (r * m) (Nat.succ_le_of_lt child.isLt)
  rw [Nat.succ_mul] at hc
  have heq : d * (r * m) = m * (d * r) := by ac_rfl
  omega

/-- A flattened grid coordinate decodes to its consecutive counter bits. -/
theorem unpackBits_gridDigit {d r m b : ℕ} (hb : b ≤ r * m) (hm : 0 < m)
    (counter : ℕ) (child : Fin d) (j : Fin b) :
    unpackBits hb (blocksEquiv (fun q : Fin (d * r) =>
      (⟨gridDigit (2 ^ m) counter q, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ m))) child) j =
      counter.testBit (child.val * (r * m) + j.val) := by
  have hj : j.val < r * m := j.isLt.trans_le hb
  have hdiv : j.val / m < r := (Nat.div_lt_iff_lt_mul hm).mpr hj
  change (equivFin m).symm
    ((blocksEquiv (fun q : Fin (d * r) =>
      (⟨gridDigit (2 ^ m) counter q, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ m))) child)
        ⟨j.val / m, hdiv⟩) ⟨j.val % m, Nat.mod_lt _ hm⟩ = _
  rw [equivFin_symm_apply]
  simp only [blocksEquiv, Equiv.coe_fn_mk, block, gridDigit, finProdFinEquiv_apply_val]
  rw [Nat.mul_comm r child.val, Nat.add_comm (j.val / m) (child.val * r)]
  rw [Nat.testBit_mod_two_pow]
  simp only [Nat.mod_lt _ hm, decide_true, Bool.true_and]
  rw [← pow_mul, Nat.testBit_div_two_pow]
  congr 1
  simp only [Nat.mul_add]
  have heq : m * (child.val * r) = child.val * (r * m) := by ac_rfl
  rw [heq]
  have hquot := Nat.mod_add_div j.val m
  omega

/-- The native slice is exactly the existing unpacked child word on every grid assignment. -/
theorem getD_label_eq_unpackBits {d r m b : ℕ} (hb : b ≤ r * m) (hm : 0 < m)
    (counter : ℕ) (child : Fin d) (j : Fin b) :
    (label ((2 ^ m) ^ (d * r), counter, r * m, b, child)).getD j false =
      unpackBits hb (blocksEquiv (fun q : Fin (d * r) =>
        (⟨gridDigit (2 ^ m) counter q, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ m))) child) j := by
  rw [getD_label _ _ _ _ _ _ (capacity hb child) j.isLt, unpackBits_gridDigit hb hm]

/-- Whole native label words agree with the packed gate decoder, including zero padding. -/
theorem label_eq_ofFn_unpackBits {d r m b : ℕ} (hb : b ≤ r * m) (hm : 0 < m)
    (counter : ℕ) (child : Fin d) :
    label ((2 ^ m) ^ (d * r), counter, r * m, b, child) =
      List.ofFn (unpackBits hb (blocksEquiv (fun q : Fin (d * r) =>
        (⟨gridDigit (2 ^ m) counter q, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ m))) child)) := by
  apply List.ext_getElem
  · simp only [length_label _ _ _ _ _ (capacity hb child), List.length_ofFn]
  · intro j hj hj'
    rw [List.getElem_ofFn]
    rw [← List.getD_eq_getElem _ (d := false) hj]
    exact getD_label_eq_unpackBits hb hm counter child
      ⟨j, by simpa only [List.length_ofFn] using hj'⟩

end Cslib.TreeEval.Ary.Packed.AssignmentLabels
