/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Tuple

/-!
# Flattening lexicographically numbered tuples

An outer coordinate `j` followed by an inner coordinate `i` becomes coordinate `j * k + i`.
The first coordinate remains most significant: ranking the inner tuples in base `n` and then
the outer tuple in base `n ^ k` gives exactly the rank of the flattened base-`n` tuple.

## Main definitions

* `Cslib.Logic.FO.Ordered.flattenTuple`: outer-then-inner coordinate flattening.

## Main results

* `Cslib.Logic.FO.Ordered.flattenTuple_finProdFinEquiv`: flattening the blocks of a tuple
  recovers it.
* `Cslib.Logic.FO.Ordered.lexRank_flattenTuple`: exact preservation of numeric rank.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Proposition 1.28 and Remark 1.32.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

/-- Flatten nested tuples, placing the outer coordinate before the inner coordinate. -/
def flattenTuple {α : Type*} {k l : ℕ} (x : Fin l → Fin k → α) : Fin (l * k) → α :=
  fun a => x (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2

/-- Reading `flattenTuple x` at `finProdFinEquiv (j, i)` returns `x j i`. -/
@[simp] theorem flattenTuple_apply {α : Type*} {k l : ℕ} (x : Fin l → Fin k → α)
    (j : Fin l) (i : Fin k) : flattenTuple x (finProdFinEquiv (j, i)) = x j i := by
  simp [flattenTuple]

/-- Flattening the blocks of a tuple recovers it. -/
theorem flattenTuple_finProdFinEquiv {α : Type*} {k l : ℕ} (x : Fin (l * k) → α) :
    (flattenTuple fun j i => x (finProdFinEquiv (j, i))) = x := by
  funext a
  simp only [flattenTuple, Prod.mk.eta, Equiv.apply_symm_apply]

/-- Reading `flattenTuple x` at `finProdFinEquiv p` returns `x p.1 p.2`. -/
theorem flattenTuple_finProdFinEquiv_apply {α : Type*} {k l : ℕ} (x : Fin l → Fin k → α)
    (p : Fin l × Fin k) : flattenTuple x (finProdFinEquiv p) = x p.1 p.2 :=
  flattenTuple_apply x p.1 p.2

/-- Successive arbitrary-base ranks agree with the rank after outer-then-inner flattening. -/
theorem lexRank_flattenTuple {n k l : ℕ} (x : Fin l → Fin k → Fin n) :
    lexRank (flattenTuple x) = lexRank (fun j => lexEquiv (x j)) := by
  rw [lexRank_apply, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type, lexRank_apply]
  apply Finset.sum_congr rfl
  intro j _
  change _ = lexRank (x j) * (n ^ k) ^ j.rev.val
  rw [lexRank_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val + i.rev.val + 1 = k := by simp only [Fin.val_rev]; lia
  have hj : j.val + j.rev.val + 1 = l := by simp only [Fin.val_rev]; lia
  have hp : (finProdFinEquiv (j, i)).val + (finProdFinEquiv (j, i)).rev.val + 1 =
      l * k := by simp only [Fin.val_rev]; lia
  have hm := congrArg (k * ·) hj
  simp only [Nat.mul_add, Nat.mul_one] at hm
  have he : (finProdFinEquiv (j, i)).rev.val = i.rev.val + k * j.rev.val := by
    simp only [finProdFinEquiv_apply_val] at hp
    have := Nat.mul_comm l k
    lia
  simp only [flattenTuple_apply, he, pow_add, pow_mul]
  ac_rfl

end Cslib.Logic.FO.Ordered
