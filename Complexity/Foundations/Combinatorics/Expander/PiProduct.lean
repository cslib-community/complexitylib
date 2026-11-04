/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.BoxProduct

/-!
# Products of finitely many permutation multigraphs

Given permutation families `σ i : K i → Equiv.Perm (V i)` for the components `i : Fin n`, the
family `piPerms σ` on the product `∀ i, V i` moves one component at a time: the move `⟨i, k⟩`
applies `σ i k` to the component `i` and leaves the others alone. Its multigraph is the product
walk that picks a component with probability proportional to its number of moves and makes one
move there.

Poincaré inequalities tensorize (`mul_expect_sq_le_piPerms`): if every component satisfies
`c 𝔼 f² ≤ ∑ k, 𝔼 (f ∘ σ i k - f)²` for functions of mean zero, then so does the product, with the
same constant. The proof iterates the binary box product (`mul_expect_sq_le_boxProdPerms`) along
`Fin.consEquiv`. In terms of the second eigenvalue (`secondEigenvalue_ofPerms_piPerms_le`), the
gap `c / (2 |K|)` of a component with `|K|` moves becomes `c / (2 ∑ i, |K i|)`: for `J` components
with the same number of moves, the gap is divided by `J`.

This is the product walk over components of the proof of Lemma 6.2 of the OpenAI preprint on
derandomizing logarithmic space [OpenAI2026LogSpace], with gap `γ / J` for `J` components.

## Main definitions

* `Cslib.RotationMap.piPerms`: the permutations of `∀ i, V i` moving one component.

## Main results

* `Cslib.RotationMap.mul_expect_sq_le_piPerms`: Poincaré inequalities tensorize over `Fin n`.
* `Cslib.RotationMap.secondEigenvalue_ofPerms_piPerms_le`: the second eigenvalue of the product.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace]
-/

public section

open Finset Function
open scoped BigOperators

namespace Cslib.RotationMap

variable {ι : Type*} [DecidableEq ι] {V K : ι → Type*}

/-- The permutations of `∀ i, V i` that move one component: `⟨i, k⟩` applies `σ i k` to the
component `i`. -/
@[expose]
def piPerms (σ : ∀ i, K i → Equiv.Perm (V i)) (k : Σ i, K i) : Equiv.Perm (∀ i, V i) :=
  Equiv.piCongrRight (update (fun _ ↦ Equiv.refl _) k.1 (σ k.1 k.2))

@[simp]
theorem piPerms_apply (σ : ∀ i, K i → Equiv.Perm (V i)) (i : ι) (k : K i) (x : ∀ i, V i) :
    piPerms σ ⟨i, k⟩ x = update x i (σ i k (x i)) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [piPerms]
  · simp [piPerms, h]

/-- **Poincaré inequalities tensorize over finitely many components**: if every component family
satisfies `c 𝔼 f² ≤ ∑ k, 𝔼 v, (f (σ i k v) - f v) ^ 2` for every function `f` of expectation zero,
then so does `piPerms σ` on the product, with the same constant. -/
theorem mul_expect_sq_le_piPerms {n : ℕ} {V K : Fin n → Type*} [∀ i, Fintype (V i)]
    [∀ i, Fintype (K i)] (σ : ∀ i, K i → Equiv.Perm (V i)) {c : ℝ}
    (hσ : ∀ i (f : V i → ℝ), 𝔼 v, f v = 0 →
      c * 𝔼 v, f v ^ 2 ≤ ∑ k, 𝔼 v, (f (σ i k v) - f v) ^ 2)
    (f : (∀ i, V i) → ℝ) (hf : 𝔼 x, f x = 0) :
    c * 𝔼 x, f x ^ 2 ≤ ∑ k, 𝔼 x, (f (piPerms σ k x) - f x) ^ 2 := by
  induction n with
  | zero =>
    have h0 (x : ∀ i, V i) : f x = 0 := by
      have : ∀ y : ∀ i, V i, f y = f x := fun y ↦ congrArg f (Subsingleton.elim y x)
      rw [← hf]
      simp only [this, Fintype.expect_const]
    simp only [h0, sub_self]
    simp
  | succ n ih =>
    -- Split off the component `0` and apply the binary box product.
    let e := Fin.consEquiv V
    set g : V 0 × (∀ i : Fin n, V i.succ) → ℝ := fun p ↦ f (e p) with hg
    have hexp (φ : (∀ i, V i) → ℝ) : 𝔼 p, φ (e p) = 𝔼 x, φ x :=
      Fintype.expect_equiv e _ _ fun _ ↦ rfl
    have hbox := mul_expect_sq_le_boxProdPerms (σ := σ 0)
      (τ := piPerms fun i : Fin n ↦ σ i.succ) (hσ 0)
      (fun g hg ↦ ih (fun i ↦ σ i.succ) (fun i ↦ hσ i.succ) g hg) g
      (by rw [hexp f]; exact hf)
    have hL : 𝔼 p, g p ^ 2 = 𝔼 x, f x ^ 2 := hexp fun x ↦ f x ^ 2
    rw [hL] at hbox
    refine hbox.trans_eq ?_
    rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma, Fin.sum_univ_succ]
    congr 1
    · refine sum_congr rfl fun k _ ↦ ?_
      rw [← hexp]
      refine expect_congr rfl fun p _ ↦ ?_
      simp only [hg, boxProdPerms_inl, piPerms_apply, e, Fin.consEquiv_apply, Fin.cons_zero,
        Fin.update_cons_zero]
    · refine sum_congr rfl fun i _ ↦ sum_congr rfl fun k _ ↦ ?_
      rw [← hexp]
      refine expect_congr rfl fun p _ ↦ ?_
      simp only [hg, boxProdPerms_inr, piPerms_apply, e, Fin.consEquiv_apply, Fin.cons_succ,
        Fin.cons_update]

/-- **The second eigenvalue of a product of permutation multigraphs**: if every component satisfies
the Poincaré inequality with constant `c`, then `λ₂ ≤ 1 - c / (2 ∑ i, |K i|)` for the product. For
`J` components with `m` moves each, the component gap `c / (2 m)` is divided by `J`. -/
theorem secondEigenvalue_ofPerms_piPerms_le {n : ℕ} {V K : Fin n → Type*} [∀ i, Fintype (V i)]
    [∀ i, Fintype (K i)] [Nonempty (Σ i, K i)]
    [Nontrivial (∀ i, V i)] (σ : ∀ i, K i → Equiv.Perm (V i)) {c : ℝ}
    (hσ : ∀ i (f : V i → ℝ), 𝔼 v, f v = 0 →
      c * 𝔼 v, f v ^ 2 ≤ ∑ k, 𝔼 v, (f (σ i k v) - f v) ^ 2) :
    (ofPerms (piPerms σ)).secondEigenvalue ≤ 1 - c / (2 * Fintype.card (Σ i, K i)) :=
  secondEigenvalue_ofPerms_le _ fun f hf ↦ mul_expect_sq_le_piPerms σ hσ f hf

end Cslib.RotationMap
