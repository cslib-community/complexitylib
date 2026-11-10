/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.RandomPermutation
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# Counting permutations that extend a finite partial assignment

For `k` distinct domain points `xs : Fin k ↪ α` and target values `ys : Fin k → α`, the set
`RandomPermutation.extPerms (List.ofFn fun i => (xs i, ys i))` of permutations of a finite type `α`
sending each `xs i` to `ys i` has at most `(Fintype.card α)! / (Fintype.card α).descFactorial k`
elements. Equivalently, a uniformly random permutation takes `k` prescribed values at `k` distinct
points with probability at most `1 / (|α| (|α| - 1) ⋯ (|α| - k + 1))`. These results depend only on
`RandomPermutation.extPerms`, not on any cipher construction.

## Main results

* `Cslib.RandomPermutation.extPerms_ofFn_eq`: the extensions of a `List.ofFn` cache as a filter
  over all permutations.
* `Cslib.RandomPermutation.card_extPerms_ofFn_eq`: the extension count is the same for all
  injective target tuples.
* `Cslib.RandomPermutation.sum_card_extPerms_ofFn`: the extension counts over all injective target
  tuples sum to `(Fintype.card α)!`.
* `Cslib.RandomPermutation.card_extPerms_ofFn_mul_descFactorial_le`: the falling-factorial bound
  `#extPerms * (Fintype.card α).descFactorial k ≤ (Fintype.card α)!` (original).
-/

@[expose] public section

namespace Cslib.RandomPermutation

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The extensions of the cache `List.ofFn fun i => (xs i, ys i)` are the permutations sending
every `xs i` to `ys i`. -/
theorem extPerms_ofFn_eq {k : ℕ} (xs ys : Fin k → α) :
    extPerms (List.ofFn fun i => (xs i, ys i)) =
      Finset.univ.filter fun π : Equiv.Perm α => ∀ i, π (xs i) = ys i := by
  ext π
  simp [extPerms, AgreesWith]

/-- For distinct domain points `xs`, the number of permutations extending the cache
`List.ofFn fun i => (xs i, e i)` does not depend on the injective target tuple `e`. -/
theorem card_extPerms_ofFn_eq {k : ℕ} (xs : Fin k → α) (e e' : Fin k ↪ α) :
    (extPerms (List.ofFn fun i => (xs i, e i))).card =
      (extPerms (List.ofFn fun i => (xs i, e' i))).card := by
  rw [extPerms_ofFn_eq, extPerms_ofFn_eq]
  let E : {x // x ∈ Set.range e} ≃ {x // x ∈ Set.range e'} :=
    (Equiv.ofInjective e e.injective).symm.trans (Equiv.ofInjective e' e'.injective)
  let σ : Equiv.Perm α := E.extendSubtype
  have hσ (i : Fin k) : σ (e i) = e' i := by
    dsimp [σ]
    rw [Equiv.extendSubtype_apply_of_mem E (e i) ⟨i, rfl⟩]
    have hi : (Equiv.ofInjective e e.injective).symm ⟨e i, ⟨i, rfl⟩⟩ = i :=
      e.injective (Equiv.apply_ofInjective_symm e.injective ⟨e i, ⟨i, rfl⟩⟩)
    simp only [E, Equiv.trans_apply, hi, Equiv.ofInjective_apply]
  refine Finset.card_bij (fun π _ => σ * π) ?_ ?_ ?_
  · intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    intro i; simp [hπ i, hσ]
  · intro π _ ρ _ h; simpa using h
  · intro ρ hρ
    refine ⟨σ⁻¹ * ρ, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
    intro i; rw [Equiv.Perm.mul_apply, hρ i, Equiv.Perm.inv_eq_iff_eq, hσ]

/-- Summing the extension counts over all injective target tuples `e : Fin k ↪ α` counts every
permutation of `α` exactly once. -/
theorem sum_card_extPerms_ofFn {k : ℕ} (xs : Fin k ↪ α) :
    ∑ e : Fin k ↪ α,
      (extPerms (List.ofFn fun i => (xs i, e i))).card =
        (Fintype.card α).factorial := by
  rw [← Fintype.card_perm, ← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := fun π : Equiv.Perm α => xs.trans π.toEmbedding)
      (t := Finset.univ) (by simp)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [extPerms_ofFn_eq]
  congr 1; ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => by ext i; simp [h i], fun h i => by rw [← h]; simp⟩

/-- **Falling-factorial upper bound on `k`-point `extPerms` fibers** (original):
for any `k` distinct domain points `xs : Fin k ↪ α` and any target values `ys : Fin k → α`,
`#(extPerms (List.ofFn fun i => (xs i, ys i))) * (Fintype.card α).descFactorial k
  ≤ (Fintype.card α).factorial`. -/
theorem card_extPerms_ofFn_mul_descFactorial_le {k : ℕ} (xs : Fin k ↪ α) (ys : Fin k → α) :
    (extPerms (List.ofFn fun i => (xs i, ys i))).card *
      (Fintype.card α).descFactorial k ≤ (Fintype.card α).factorial := by
  by_cases hys : Function.Injective ys
  · have hall : ∀ e : Fin k ↪ α,
        (extPerms (List.ofFn fun i => (xs i, e i))).card =
          (extPerms (List.ofFn fun i => (xs i, ys i))).card :=
      fun e => card_extPerms_ofFn_eq xs e ⟨ys, hys⟩
    rw [← sum_card_extPerms_ofFn xs]
    simp only [hall, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Fintype.card_embedding_eq, Fintype.card_fin]
    rw [mul_comm]
  · have hempty : extPerms (List.ofFn fun i => (xs i, ys i)) = ∅ := by
      rw [extPerms_ofFn_eq]
      ext π
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hys fun i j hij => xs.injective (π.injective (by rw [h i, h j, hij]))
    simp [hempty]

end Cslib.RandomPermutation
