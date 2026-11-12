/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.IteratedQuery
public import CslibFrontier.Computability.Circuit.Boolean.Modular.Multiply
public import CslibFrontier.Foundations.Data.BitString.List.Binary

/-!
# Multiplication by streamed carry-save queries

The complete tree has `2 ^ clog 2 w` leaves. Each real leaf is one shifted partial product;
extra leaves are zero. Local leaf queries read at most two operand bits. This module proves
arithmetic semantics, not a native running-time bound or a free random-access input model.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.CarrySaveQuery.Multiplication

open BitString Modular
open scoped BigOperators

/-- A shifted partial product paired with zero, or zero padding past the input width. -/
def partialPair {w : ℕ} (a b : BitString w) (j : ℕ) : BitString (w + w) :=
  Fin.append (if h : j < w then
    (partialProduct w ⟨j, h⟩).eval interpretation (Fin.append a b) else fun _ => false)
    (fun _ => false)

/-- Binary path addresses enumerate padded partial-product leaves in order. -/
def leaves {w : ℕ} (a b : BitString w) (path : List Bool) : BitString (w + w) :=
  partialPair a b (binaryValue path)

/-- The carry component of every leaf is zero. -/
theorem component_partialPair_carry {w : ℕ} (a b : BitString w) (j : ℕ) :
    component (partialPair a b j) true = fun _ => false := by
  simp [component, partialPair]

/-- A leaf bit uses one conjunction and two comparisons, without constructing its word. -/
theorem component_partialPair_sum {w : ℕ} (a b : BitString w) (j : ℕ) (i : Fin w) :
    component (partialPair a b j) false i =
      if h : j < w then
        if hji : j ≤ i.val then a ⟨i.val - j, by omega⟩ && b ⟨j, h⟩ else false
      else false := by
  simp only [component, Bool.false_eq_true, ↓reduceIte, partialPair, fstBits]
  split <;> simp_all [eval_partialProduct]

/-- A terminal multiplication query is a local shifted conjunction or false padding. -/
theorem value_leaf {w : ℕ} (a b : BitString w) (path : List Bool)
    (carry : Bool) (i : Fin w) :
    value (leaves a b) ⟨path, 0, carry, i.val⟩ =
      if carry then false else
        if h : binaryValue path < w then
          if hji : binaryValue path ≤ i.val then
            a ⟨i.val - binaryValue path, by omega⟩ && b ⟨binaryValue path, h⟩
          else false
        else false := by
  cases carry <;>
    simp [value, tree, leaves, component_partialPair_carry, component_partialPair_sum]

/-- Padding contributes zero to the sum of leaves. -/
theorem pairVal_partialPair_of_le {w : ℕ} (a b : BitString w) {j : ℕ} (h : w ≤ j) :
    pairVal (partialPair a b j) = 0 := by
  simp [partialPair, show ¬ j < w by omega]

/-- The unpadded leaf sum is exactly the existing modular multiplier's input sum. -/
theorem sum_partialPair_mod {w : ℕ} (a b : BitString w) :
    (∑ j ∈ Finset.range w, pairVal (partialPair a b j)) % 2 ^ w =
      ((equivFin w a : ℕ) * (equivFin w b : ℕ)) % 2 ^ w := by
  have h := val_eval_multiply a b
  rw [multiply, val_eval_sumPairs] at h
  simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn] at h
  rw [← Finset.sum_nat_mod] at h
  rw [← Fin.sum_univ_eq_sum_range (fun j => pairVal (partialPair a b j))]
  convert h using 2
  apply Finset.sum_congr rfl
  intro i _
  simp [partialPair, i.isLt, eval_pairWithZero]

/-- Extending the tree to a power of two adds only zero leaves. -/
theorem sum_padded_partialPair {w : ℕ} (a b : BitString w) {n : ℕ} (h : w ≤ n) :
    (∑ j ∈ Finset.range n, pairVal (partialPair a b j)) =
      ∑ j ∈ Finset.range w, pairVal (partialPair a b j) := by
  symm
  apply Finset.sum_subset (Finset.range_mono h)
  intro j _ hj
  exact pairVal_partialPair_of_le a b (by simpa using hj)

/-- The carry-save root for the complete padded multiplication tree. -/
def rootPair {w : ℕ} (a b : BitString w) : BitString (w + w) :=
  tree (leaves a b) (Nat.clog 2 w) []

/-- Finish the two root words with the existing carry-lookahead adder. -/
def product {w : ℕ} (a b : BitString w) : BitString w :=
  (carryLookaheadAdd w).eval interpretation (rootPair a b)

/-- The logarithmic-height tree represents multiplication modulo the word precision. -/
theorem pairVal_rootPair_mod {w : ℕ} (a b : BitString w) :
    pairVal (rootPair a b) % 2 ^ w =
      ((equivFin w a : ℕ) * (equivFin w b : ℕ)) % 2 ^ w := by
  rw [rootPair, pairVal_tree_mod]
  unfold leaves
  rw [leafSum_binaryValue]
  simp only [binaryValue, List.foldl_nil, Nat.zero_mul, Nat.zero_add]
  rw [sum_padded_partialPair a b (Nat.le_pow_clog (by decide) w)]
  exact sum_partialPair_mod a b

/-- The carry-lookahead finish of the streamed tree is the modular product. -/
theorem val_product {w : ℕ} (a b : BitString w) :
    (equivFin w (product a b) : ℕ) =
      ((equivFin w a : ℕ) * (equivFin w b : ℕ)) % 2 ^ w := by
  rw [product, val_eval_carryLookaheadAdd_pair, pairVal_rootPair_mod]

end Cslib.Circuits.Boolean.CarrySaveQuery.Multiplication
