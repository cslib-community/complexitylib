/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate (Mathlib, entries of a product of matrices as a sum over paths)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul

/-!
# Entries of a product of matrices as a sum over paths

The entry `(a, b)` of a product `M 0 * M 1 * ⋯ * M (d - 1)` of square matrices is the sum, over
all paths `p 0, p 1, …, p d` of indices from `p 0 = a` to `p d = b`, of the products
`∏ i, M i (p i) (p (i + 1))` of the entries along the path. This is the standard expansion behind
algebraic branching programs.

## Main results

* `Matrix.list_prod_ofFn_apply`: the path expansion of an entry of `(List.ofFn M).prod`.
-/

@[expose] public section

namespace Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- **The path expansion**: the entry `(a, b)` of the product of the matrices `M 0, …, M (d - 1)`
is the sum, over the paths `p : Fin (d + 1) → ι` from `a` to `b`, of the product of the entries
`M i (p i) (p (i + 1))` along the path. -/
theorem list_prod_ofFn_apply : ∀ {d : ℕ} (M : Fin d → Matrix ι ι R) (a b : ι),
    (List.ofFn M).prod a b = ∑ p : Fin (d + 1) → ι,
      if p 0 = a ∧ p (Fin.last d) = b then ∏ i : Fin d, M i (p i.castSucc) (p i.succ) else 0
  | 0, M, a, b => by
    rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    simp only [List.ofFn_zero, List.prod_nil, Matrix.one_apply, Finset.univ_eq_empty,
      Finset.prod_empty, Equiv.funUnique_symm_apply, Fin.last_zero, uniqueElim_const]
    by_cases hab : a = b
    · subst hab
      simp
    · rw [ite_eq_right hab]
      refine (Finset.sum_eq_zero fun c _ => ite_eq_right ?_).symm
      rintro ⟨rfl, rfl⟩
      exact hab rfl
  | d + 1, M, a, b => by
    have hL : (List.ofFn M).prod a b = ∑ q : Fin (d + 1) → ι,
        if q (Fin.last d) = b then M 0 a (q 0) * ∏ i : Fin d, M i.succ (q i.castSucc) (q i.succ)
        else 0 := by
      rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
      simp only [list_prod_ofFn_apply (fun i => M i.succ), Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.sum_eq_single (q 0)]
      · simp
      · intro c _ hc
        exact ite_eq_right fun h => hc h.1.symm
      · simp
    rw [hL, ← (Fin.consEquiv (n := d + 1) fun _ => ι).sum_comp, Fintype.sum_prod_type,
      Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun q _ => ?_
      simp [Fin.prod_univ_succ, ← Fin.succ_last]
    · intro c _ hc
      refine Finset.sum_eq_zero fun q _ => ite_eq_right ?_
      simp [hc]
    · simp

end Matrix
