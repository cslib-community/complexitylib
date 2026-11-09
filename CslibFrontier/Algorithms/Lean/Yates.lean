/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.TimeM.Loops
public import CslibFrontier.Foundations.BooleanAnalysis.SubsetZeta
public import CslibFrontier.Foundations.Data.BitString.Binary

/-!
# Yates's algorithm on tables of size `2 ^ n`

A function on the subsets of `Fin n` is stored as a table `t : Vector M (2 ^ n)`: cell `k` holds
the value at `maskSet n k`, the set of positions of the binary digits `1` of `k`, and `maskIndex S`
is the cell of `S`. Yates's algorithm (`transformM c`) makes `n` passes over the table, one per
coordinate `i`. Pass `i` (`passM c i`) writes the new value of cell `k` as
`t[k] + c • t[k ^^^ 2 ^ i]` when bit `i` of `k` is set and as `t[k]` otherwise, following
[Williams2014], Lemma 4.2, Proof 1, and [BjorklundHusfeldtKoivisto2009], Section 2.2.

The output at `maskSet n k` is `∑_{T ⊆ maskSet n k} c ^ #(maskSet n k \ T) • F T` whenever the
input table represents `F` (`getElem_ret_transformM`). The fast zeta transform `zetaM`
(coefficient `1`) computes `subsetZeta F` and the fast Möbius transform `mobiusM` (coefficient
`-1`) computes `subsetMobius F`, each in exactly `n * 2 ^ n` ticks (`time_zetaM`, `time_mobiusM`).

## Cost model

* **Charged (`1` `TimeM` tick):** writing one cell in one pass. The tick covers testing bit `i` of
  the index `k`, computing the partner index `k ^^^ 2 ^ i`, reading the two cells, one scalar
  multiplication by `c` and one addition in `M`.
* **Uncharged:** loop control and allocating the output vector of each pass (passes are
  out-of-place).

This is a unit-cost model: indices of `n` bits and table entries are treated as words. For the
zeta transform of a table of natural numbers whose entries *sum* to at most `s` (such as the table
of AND-gate multiplicities of a circuit with `s` AND gates), every intermediate and final value is
a sum of distinct entries, hence at most `s`, so the words have `O(n + log s)` bits. A bound on the
individual entries alone does not suffice: the zeta transform of the all-ones table has top entry
`2 ^ n`. The model is not Turing-machine time; the Turing-machine-level bound is not formalized.

## Main definitions

* `Cslib.Algorithms.Lean.Yates.maskSet`, `maskIndex`: the cells of a table and the subsets of
  `Fin n`.
* `Cslib.Algorithms.Lean.Yates.passM`, `transformM`: Yates's passes in `TimeM`.
* `Cslib.Algorithms.Lean.Yates.zetaM`, `mobiusM`: the fast zeta and Möbius transforms.

## Main results

* `Cslib.Algorithms.Lean.Yates.getElem_ret_transformM`: correctness of the passes.
* `Cslib.Algorithms.Lean.Yates.getElem_ret_zetaM`, `getElem_ret_zetaM_maskIndex`: the fast zeta
  transform computes `subsetZeta`.
* `Cslib.Algorithms.Lean.Yates.getElem_ret_mobiusM`, `getElem_ret_mobiusM_maskIndex`: the fast
  Möbius transform computes `subsetMobius`.
* `Cslib.Algorithms.Lean.Yates.time_transformM`, `time_zetaM`, `time_mobiusM`: `n * 2 ^ n`
  ticks.

## References

* [A. Björklund, T. Husfeldt, M. Koivisto, *Set Partitioning via
  Inclusion–Exclusion*][BjorklundHusfeldtKoivisto2009]
* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
-/

public section

namespace Cslib.Algorithms.Lean.Yates

open Finset Cslib.Algorithms.Lean.TimeM Cslib.BitString

/-! ### Cells and subsets -/

/-- The set of positions `i < n` of the binary digits `1` of `k`. -/
@[expose] def maskSet (n k : ℕ) : Finset (Fin n) :=
  univ.filter fun i => k.testBit i

/-- The cell of the subset `S` of `Fin n`: the number whose binary digit `i` is `1` exactly when
`i ∈ S`. -/
@[expose] def maskIndex {n : ℕ} (S : Finset (Fin n)) : Fin (2 ^ n) :=
  BitString.equivFin n fun i => decide (i ∈ S)

@[simp] theorem mem_maskSet {n k : ℕ} {i : Fin n} : i ∈ maskSet n k ↔ k.testBit i = true := by
  simp only [maskSet, mem_filter, mem_univ, true_and]

/-- Flipping a binary digit `1` of the index erases its position from the set. -/
theorem maskSet_xor_two_pow {n k : ℕ} {i : Fin n} (hi : k.testBit i = true) :
    maskSet n (k ^^^ 2 ^ (i : ℕ)) = (maskSet n k).erase i := by
  ext j
  simp only [mem_maskSet, Finset.mem_erase, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hij : (i : ℕ) = j
  · have : j = i := Fin.ext hij.symm
    subst this
    simp [hi]
  · have : j ≠ i := fun h => hij (congrArg Fin.val h).symm
    simp [hij, this]

/-- The set of a cell is the set of true coordinates of the corresponding bit string. -/
theorem maskSet_eq_filter {n : ℕ} (k : Fin (2 ^ n)) :
    maskSet n k = univ.filter fun i => (BitString.equivFin n).symm k i = true := by
  ext i
  simp only [mem_maskSet, mem_filter, mem_univ, true_and, BitString.equivFin_symm_apply]

/-- The bit string of cell `k` is the indicator of the set of cell `k`. -/
theorem equivFin_symm_eq_decide_mem_maskSet {n : ℕ} (k : Fin (2 ^ n)) :
    (BitString.equivFin n).symm k = fun i => decide (i ∈ maskSet n k) := by
  funext i
  rw [BitString.equivFin_symm_apply]
  cases h : (k : ℕ).testBit i <;> simp [h]

@[simp] theorem maskSet_maskIndex {n : ℕ} (S : Finset (Fin n)) :
    maskSet n (maskIndex S) = S := by
  ext i
  rw [mem_maskSet, ← BitString.equivFin_symm_apply, maskIndex, Equiv.symm_apply_apply,
    decide_eq_true_iff]

@[simp] theorem maskIndex_maskSet {n : ℕ} (k : Fin (2 ^ n)) : maskIndex (maskSet n k) = k := by
  rw [maskIndex, ← Equiv.eq_symm_apply]
  funext i
  rw [BitString.equivFin_symm_apply]
  cases h : (k : ℕ).testBit i <;> simp [h]

/-- Every table represents the function reading the cell of each set. -/
theorem getElem_eq_maskIndex_maskSet {α : Type*} {n : ℕ} (t : Vector α (2 ^ n)) (k : ℕ)
    (hk : k < 2 ^ n) : t[k] = t[(maskIndex (maskSet n k) : ℕ)] := by
  have := maskIndex_maskSet (⟨k, hk⟩ : Fin (2 ^ n))
  simp only [this]

/-! ### The passes -/

variable {M R : Type*} [AddCommMonoid M] [Monoid R] [DistribMulAction R M]

/-- The pass of Yates's algorithm in coordinate `i` with coefficient `c`: cell `k` becomes
`t[k] + c • t[k ^^^ 2 ^ i]` when bit `i` of `k` is set, and `t[k]` otherwise, at one tick per
cell. -/
@[expose] def passM {n : ℕ} (c : R) (i : Fin n) (t : Vector M (2 ^ n)) :
    TimeM ℕ (Vector M (2 ^ n)) :=
  Vector.ofFnM fun k : Fin (2 ^ n) => do
    ✓ pure (if (k : ℕ).testBit i then
        t[(k : ℕ)] + c • t[(k : ℕ) ^^^ 2 ^ (i : ℕ)]'(Nat.xor_lt_two_pow k.isLt
          (Nat.pow_lt_pow_right (by norm_num) i.isLt))
      else t[(k : ℕ)])

/-- Yates's algorithm with coefficient `c`: the passes in coordinates `0, …, n - 1`. -/
@[expose] def transformM {n : ℕ} (c : R) (t : Vector M (2 ^ n)) : TimeM ℕ (Vector M (2 ^ n)) :=
  (List.finRange n).foldlM (fun acc i => passM c i acc) t

/-- The fast zeta transform: Yates's algorithm with coefficient `1`. -/
@[expose] def zetaM {n : ℕ} (t : Vector M (2 ^ n)) : TimeM ℕ (Vector M (2 ^ n)) :=
  transformM (1 : ℕ) t

@[simp] theorem time_passM {n : ℕ} (c : R) (i : Fin n) (t : Vector M (2 ^ n)) :
    (passM c i t).time = 2 ^ n := by
  simp only [passM, time_vectorOfFnM, time_bind, time_tick, time_pure, add_zero, sum_const,
    card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- Yates's algorithm takes `n * 2 ^ n` ticks. -/
@[simp] theorem time_transformM {n : ℕ} (c : R) (t : Vector M (2 ^ n)) :
    (transformM c t).time = n * 2 ^ n := by
  rw [transformM, time_foldlM_of_time_eq _ _ _ (fun acc i => time_passM c i acc),
    List.length_finRange]

/-- The fast zeta transform takes `n * 2 ^ n` ticks. -/
@[simp] theorem time_zetaM {n : ℕ} (t : Vector M (2 ^ n)) : (zetaM t).time = n * 2 ^ n :=
  time_transformM _ t

theorem getElem_ret_passM {n : ℕ} (c : R) (i : Fin n) (t : Vector M (2 ^ n))
    (F : Finset (Fin n) → M) (hF : ∀ (k : ℕ) (hk : k < 2 ^ n), t[k] = F (maskSet n k))
    (k : ℕ) (hk : k < 2 ^ n) :
    (passM c i t).ret[k] = yatesPass c i F (maskSet n k) := by
  rw [passM, ret_vectorOfFnM, Vector.getElem_ofFn]
  simp only [ret_bind, ret_pure, yatesPass, mem_maskSet]
  split_ifs with h
  · rw [hF, hF, maskSet_xor_two_pow h]
  · rw [hF]

private theorem getElem_ret_foldlM_passM {n : ℕ} (c : R) (l : List (Fin n))
    (t : Vector M (2 ^ n)) (F : Finset (Fin n) → M)
    (hF : ∀ (k : ℕ) (hk : k < 2 ^ n), t[k] = F (maskSet n k)) (k : ℕ) (hk : k < 2 ^ n) :
    (l.foldlM (fun acc i => passM c i acc) t).ret[k] = yatesTransform c l F (maskSet n k) := by
  induction l generalizing t F with
  | nil => exact hF k hk
  | cons i l ih =>
    rw [List.foldlM_cons, ret_bind, yatesTransform_cons]
    exact ih _ _ (getElem_ret_passM c i t F hF)

/-- **Correctness of Yates's algorithm.** If the table `t` represents `F`, the output at
`maskSet n k` is `∑_{T ⊆ maskSet n k} c ^ #(maskSet n k \ T) • F T`. -/
theorem getElem_ret_transformM {n : ℕ} (c : R) (t : Vector M (2 ^ n))
    (F : Finset (Fin n) → M) (hF : ∀ (k : ℕ) (hk : k < 2 ^ n), t[k] = F (maskSet n k))
    (k : ℕ) (hk : k < 2 ^ n) :
    (transformM c t).ret[k] = ∑ T ∈ (maskSet n k).powerset, c ^ #(maskSet n k \ T) • F T := by
  rw [transformM, getElem_ret_foldlM_passM c _ t F hF k hk,
    yatesTransform_apply_of_subset c (List.nodup_finRange n) F (by simp)]

/-- **The fast zeta transform computes the zeta transform**: if the table `t` represents `F`, the
output at `maskSet n k` is `subsetZeta F (maskSet n k)`. -/
theorem getElem_ret_zetaM {n : ℕ} (t : Vector M (2 ^ n))
    (F : Finset (Fin n) → M) (hF : ∀ (k : ℕ) (hk : k < 2 ^ n), t[k] = F (maskSet n k))
    (k : ℕ) (hk : k < 2 ^ n) :
    (zetaM t).ret[k] = subsetZeta F (maskSet n k) := by
  rw [zetaM, transformM, getElem_ret_foldlM_passM _ _ t F hF k hk,
    yatesTransform_one_apply (List.nodup_finRange n) F (by simp)]

/-- The fast zeta transform, read at the cell of `S`, is the zeta transform of the table read at
the cells of the subsets of `S`. -/
theorem getElem_ret_zetaM_maskIndex {n : ℕ} (t : Vector M (2 ^ n)) (S : Finset (Fin n)) :
    (zetaM t).ret[(maskIndex S : ℕ)] = subsetZeta (fun T => t[(maskIndex T : ℕ)]) S := by
  rw [getElem_ret_zetaM t (fun T => t[(maskIndex T : ℕ)]) (getElem_eq_maskIndex_maskSet t) _
      (maskIndex S).isLt,
    maskSet_maskIndex]

end Cslib.Algorithms.Lean.Yates

namespace Cslib.Algorithms.Lean.Yates

open Finset Cslib.Algorithms.Lean.TimeM Cslib.BitString

variable {M : Type*} [AddCommGroup M]

/-- The fast Möbius transform: Yates's algorithm with coefficient `-1`. -/
@[expose] def mobiusM {n : ℕ} (t : Vector M (2 ^ n)) : TimeM ℕ (Vector M (2 ^ n)) :=
  transformM (-1 : ℤ) t

/-- The fast Möbius transform takes `n * 2 ^ n` ticks. -/
@[simp] theorem time_mobiusM {n : ℕ} (t : Vector M (2 ^ n)) : (mobiusM t).time = n * 2 ^ n :=
  time_transformM _ t

/-- **The fast Möbius transform computes the Möbius transform**: if the table `t` represents
`F`, the output at `maskSet n k` is `subsetMobius F (maskSet n k)`. -/
theorem getElem_ret_mobiusM {n : ℕ} (t : Vector M (2 ^ n))
    (F : Finset (Fin n) → M) (hF : ∀ (k : ℕ) (hk : k < 2 ^ n), t[k] = F (maskSet n k))
    (k : ℕ) (hk : k < 2 ^ n) :
    (mobiusM t).ret[k] = subsetMobius F (maskSet n k) := by
  rw [mobiusM, transformM, getElem_ret_foldlM_passM _ _ t F hF k hk,
    yatesTransform_neg_one_apply (List.nodup_finRange n) F (by simp)]

/-- The fast Möbius transform, read at the cell of `S`, is the Möbius transform of the table read
at the cells of the subsets of `S`. -/
theorem getElem_ret_mobiusM_maskIndex {n : ℕ} (t : Vector M (2 ^ n)) (S : Finset (Fin n)) :
    (mobiusM t).ret[(maskIndex S : ℕ)] = subsetMobius (fun T => t[(maskIndex T : ℕ)]) S := by
  rw [getElem_ret_mobiusM t (fun T => t[(maskIndex T : ℕ)]) (getElem_eq_maskIndex_maskSet t) _
      (maskIndex S).isLt,
    maskSet_maskIndex]

end Cslib.Algorithms.Lean.Yates
