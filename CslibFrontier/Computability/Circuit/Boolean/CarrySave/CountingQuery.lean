/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.IteratedQuery
public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.Reduce

/-!
# Counting Boolean predicates through streamed carry-save queries

A complete binary tree sums the bits of a predicate on `0, …, n - 1`, padding with zero.
Every leaf query reads at most one predicate bit; its other wires are false. The final
carry-lookahead adder returns the count modulo the word precision. This supplies arithmetic
semantics for rank verification without invoking a counting-machine simulation theorem.
Predicate evaluation and native routing costs remain separate obligations.
-/

public section

namespace Cslib.Circuits.Boolean.CarrySaveQuery.Counting

open BitString
open scoped BigOperators

/-- One predicate bit in a carry-save pair, with zero padding beyond the domain. -/
@[expose] def leafPair (n w : ℕ) (predicate : ℕ → Bool) (j : ℕ) : BitString (w + w) :=
  (bitPairCircuit 1 w 0).eval interpretation (fun _ => if j < n then predicate j else false)

/-- Each leaf's value is its predicate bit modulo the precision. -/
theorem pairVal_leafPair_mod (n w : ℕ) (predicate : ℕ → Bool) (j : ℕ) :
    pairVal (leafPair n w predicate j) % 2 ^ w =
      (if j < n then (predicate j).toNat else 0) % 2 ^ w := by
  rw [leafPair, pairVal_eval_bitPairCircuit_mod]
  split_ifs <;> rfl

/-- A leaf wire reads only bit zero of the first word; all other wires are false. -/
theorem component_leafPair (n w : ℕ) (predicate : ℕ → Bool) (j : ℕ)
    (carry : Bool) (i : Fin w) :
    component (leafPair n w predicate j) carry i =
      if carry then false else if i.val = 0 ∧ j < n then predicate j else false := by
  have hw : w ≠ 0 := by have := i.isLt; omega
  cases carry <;> by_cases hi : i.val = 0 <;>
    simp [component, leafPair, bitPairCircuit, hi, Fin.append, Fin.addCases,
      Circuit.eval_oneGate, interpretation, hw, -Fin.natAdd_eq_addNat]

/-- A logarithmic-height tree, indexed by the binary path from its root. -/
@[expose] def rootPair (n w : ℕ) (predicate : ℕ → Bool) : BitString (w + w) :=
  tree (fun path => leafPair n w predicate (binaryValue path)) (Nat.clog 2 n) []

/-- Finish the two carry-save words with the existing carry-lookahead adder. -/
@[expose] def count (n w : ℕ) (predicate : ℕ → Bool) : BitString w :=
  (carryLookaheadAdd w).eval interpretation (rootPair n w predicate)

/-- The padded tree computes the predicate count modulo the word precision. -/
theorem pairVal_rootPair_mod (n w : ℕ) (predicate : ℕ → Bool) :
    pairVal (rootPair n w predicate) % 2 ^ w =
      (∑ j ∈ Finset.range n, (predicate j).toNat) % 2 ^ w := by
  rw [rootPair, pairVal_tree_mod, leafSum_binaryValue]
  simp only [binaryValue, List.foldl_nil, Nat.zero_mul, Nat.zero_add]
  rw [Finset.sum_nat_mod]
  simp only [pairVal_leafPair_mod]
  rw [← Finset.sum_nat_mod]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_iff_right_of_imp (fun h => h.trans_le (Nat.le_pow_clog (by decide) n))

/-- The finishing adder returns the count modulo the precision, including empty domains. -/
theorem val_count (n w : ℕ) (predicate : ℕ → Bool) :
    (equivFin w (count n w predicate) : ℕ) =
      (∑ j ∈ Finset.range n, (predicate j).toNat) % 2 ^ w := by
  rw [count, val_eval_carryLookaheadAdd_pair, pairVal_rootPair_mod]

/-- Enough precision for every possible count removes the modulus. -/
theorem val_count_eq (n w : ℕ) (predicate : ℕ → Bool) (h : n < 2 ^ w) :
    (equivFin w (count n w predicate) : ℕ) = ∑ j ∈ Finset.range n, (predicate j).toNat := by
  rw [val_count, Nat.mod_eq_of_lt]
  have hb : (∑ j ∈ Finset.range n, (predicate j).toNat) ≤ n := by
    calc _ ≤ ∑ _j ∈ Finset.range n, 1 := Finset.sum_le_sum fun j _ => Bool.toNat_le _
         _ = n := by simp
  exact hb.trans_lt h

end Cslib.Circuits.Boolean.CarrySaveQuery.Counting
