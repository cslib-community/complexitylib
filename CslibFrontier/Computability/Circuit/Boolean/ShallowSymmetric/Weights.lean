/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ShallowSymmetric.ShiftTest
public import CslibFrontier.Foundations.Data.BitString.Weight
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.ChineseRemainder

/-!
# Block weights and exact-weight certificates

The arithmetic of the construction of Lecomte and Ramakrishnan [LecomteRamakrishnan2026]:
partitioning input bits preserves their total weight, a residue class partition has small blocks,
and coprime modular certificates determine the exact weight. Complementing one block turns a
difference of block weights into a symmetric function.

## Main definitions

* `Cslib.Circuits.Boolean.ShallowSymmetric.blockWeight`: the weight of a block of a partition.
* `Cslib.Circuits.Boolean.ShallowSymmetric.residueBlock`: the partition into residue classes.

## Main results

* `Cslib.Circuits.Boolean.ShallowSymmetric.sum_blockWeight`: block weights sum to the weight.
* `Cslib.Circuits.Boolean.ShallowSymmetric.weight_eq_of_shiftTests`: accepting tests modulo
  coprime moduli of product larger than `n` certify the exact weight.

## References

* [V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*][LecomteRamakrishnan2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.ShallowSymmetric

open Finset BitString

/-- The weight of a partition block. -/
def blockWeight {ι G : Type*} [Fintype ι] [DecidableEq G]
    (block : ι → G) (x : ι → Bool) (a : G) : ℕ :=
  weight (fun i : {i : ι // block i = a} => x i.1)

/-- Summing the block weights recovers the total weight. -/
theorem sum_blockWeight {ι G : Type*} [Fintype ι] [Fintype G] [DecidableEq G]
    (block : ι → G) (x : ι → Bool) : ∑ a, blockWeight block x a = weight x := by
  simp only [blockWeight, weight_eq_sum_toNat]
  rw [← Fintype.sum_sigma']
  exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv block) _ _ (fun _ => rfl)

/-- Round-robin partition into `k` residue classes. -/
def residueBlock {n k : ℕ} (i : Fin n) : ZMod k := i.val

/-- Every residue block has at most `n/k + 1` positions. -/
theorem card_residueBlock_le (n k : ℕ) (a : ZMod k) :
    Fintype.card {i : Fin n // residueBlock i = a} ≤ n / k + 1 := by
  let encode (i : {i : Fin n // residueBlock i = a}) : Fin (n / k + 1) :=
    ⟨i.1.val / k, Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt i.1.isLt))⟩
  have hi : Function.Injective encode := by
    intro i j h
    have hd : i.1.val / k = j.1.val / k := congrArg Fin.val h
    have hm : i.1.val % k = j.1.val % k :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).1 (i.2.trans j.2.symm)
    apply Subtype.ext
    apply Fin.ext
    calc
      i.1.val = i.1.val % k + k * (i.1.val / k) := (Nat.mod_add_div _ _).symm
      _ = j.1.val % k + k * (j.1.val / k) := by rw [hd, hm]
      _ = j.1.val := Nat.mod_add_div _ _
  simpa using Fintype.card_le_of_injective encode hi

/-- A pair of blocks, with the second block complemented, has weight
`left + length(right) - right`. The additive form avoids natural subtraction. -/
theorem weight_pair_not_add {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → Bool) (y : κ → Bool) :
    weight (Sum.elim x (fun j => !(y j))) + weight y =
      weight x + Fintype.card κ := by
  rw [weight_sum_elim, Nat.add_assoc, weight_not_add]

/-- Modular certificates over coprime moduli larger in product than the input
length certify the exact Hamming weight. -/
theorem weight_eq_of_shiftTests {n : ℕ} {ι : Type*} [Fintype ι]
    (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) (hn : n < ∏ i, k i)
    (t : Fin (n + 1)) (x : BitString n)
    (s : (i : ι) → ZMod (k i) → ZMod (k i))
    (hs : ∀ i, ShiftTest (t.val : ZMod (k i))
      (fun a => (blockWeight residueBlock x a : ZMod (k i))) (s i)) :
    weight x = t.val := by
  classical
  have hmod : weight x ≡ t.val [MOD ∏ i, k i] := by
    rw [← prod_map_toList]
    refine (Nat.modEq_list_map_prod_iff ((nodup_toList univ).pairwise_of_forall_ne
      fun i _ j _ hij => hc hij)).2 fun i _ => ?_
    apply (ZMod.natCast_eq_natCast_iff _ _ _).1
    have h := (hs i).sound
    rw [← Nat.cast_sum, sum_blockWeight] at h
    exact h
  exact hmod.eq_of_lt_of_lt
    ((weight_le_length x).trans_lt hn) (by omega)

end Cslib.Circuits.Boolean.ShallowSymmetric
