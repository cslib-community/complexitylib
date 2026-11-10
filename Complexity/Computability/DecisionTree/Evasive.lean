/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Basic
public import Complexity.Foundations.BooleanAnalysis.Fourier

/-!
# The parity criterion for evasiveness

A function is *evasive* when every decision tree computing it queries all variables on some input.
If the top Fourier coefficient `f̂([n])` of `f`, read as signs, is nonzero, then `f` is evasive in
this strong per-input sense (`DecisionTree.exists_queries_eq_univ_of_fourierCoeff_univ_ne_zero`),
so its decision tree complexity is the number of variables
(`DecisionTree.complexity_eq_card_of_fourierCoeff_univ_ne_zero`). For `n ≥ 1` the characters
`χ_{[n]}(x) = (-1) ^ |x|` sum to `0`, so `2 ^ n f̂([n]) = -2 (e - o)`, where `e` and `o` count the
inputs of even and of odd weight on which `f` is `true`. So this is the parity criterion of Rivest
and Vuillemin [Rivest and Vuillemin][RivestVuillemin1976]: a function whose `true` inputs of even
and of odd weight are not equinumerous is evasive.

The proof is an induction on the tree, over the subcubes of inputs agreeing with a base point `a`
off a set `S` of free coordinates. On the subcube, the sum of `(-1) ^ f(x) χ_S(x)` vanishes at a
leaf when `S` is nonempty, and at a node querying a free coordinate `i` it splits into the two
half-cubes with `i` fixed, so some half carries a nonzero sum for the subtree followed there. Hence
some input of the subcube is followed along a path querying all of `S`.

## Main results

* `Cslib.DecisionTree.exists_queries_eq_univ_of_fourierCoeff_univ_ne_zero`: a nonzero top Fourier
  coefficient forces every computing tree to query all variables on some input.
* `Cslib.DecisionTree.complexity_eq_card_of_fourierCoeff_univ_ne_zero`: then `D(f) = n`.

## References

* [R. L. Rivest, J. Vuillemin, *On recognizing graph properties from adjacency
  matrices*][RivestVuillemin1976]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.DecisionTree

open BitString Finset

variable {ι β : Type*} [Fintype ι] [DecidableEq ι]

/-- Summing over the inputs agreeing with `a` off `insert i S` splits into the inputs agreeing with
`a` with bit `i` set to `false`, and set to `true`, off `S`. -/
private theorem sum_filter_insert {i : ι} {S : Finset ι} (hi : i ∉ S) (a : ι → Bool)
    (g : (ι → Bool) → ℝ) :
    ∑ x ∈ univ.filter (fun x => ∀ j ∉ insert i S, x j = a j), g x =
      ∑ x ∈ univ.filter (fun x => ∀ j ∉ S, x j = Function.update a i false j), g x +
        ∑ x ∈ univ.filter (fun x => ∀ j ∉ S, x j = Function.update a i true j), g x := by
  have key (b : Bool) :
      univ.filter (fun x : ι → Bool => ∀ j ∉ S, x j = Function.update a i b j) =
        (univ.filter fun x : ι → Bool => ∀ j ∉ insert i S, x j = a j).filter
          fun x => x i = b := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, not_or]
    constructor
    · intro h
      refine ⟨fun j ⟨hji, hj⟩ => by simpa [hji] using h j hj, by simpa using h i hi⟩
    · rintro ⟨h, hb⟩ j hj
      by_cases hji : j = i
      · subst hji
        simpa using hb
      · simpa [hji] using h j ⟨hji, hj⟩
  rw [key, key, ← sum_filter_add_sum_filter_not _ (fun x => x i = false)]
  congr 2
  ext x
  simp

/-- On a subcube, the characters of the free coordinates sum to `1` if there are none and to `0`
otherwise. -/
private theorem sum_filter_chi (S : Finset ι) (a : ι → Bool) :
    ∑ x ∈ univ.filter (fun x => ∀ j ∉ S, x j = a j), chi ℝ S x = if S = ∅ then 1 else 0 := by
  induction S using Finset.induction_on generalizing a with
  | empty =>
    have : univ.filter (fun x : ι → Bool => ∀ j, x j = a j) = {a} := by
      ext x
      simp [funext_iff]
    simp [this]
  | insert i S hi ih =>
    rw [sum_filter_insert hi]
    have hchi (b : Bool) : ∑ x ∈ univ.filter (fun x => ∀ j ∉ S, x j = Function.update a i b j),
        chi ℝ (insert i S) x = signVal b * if S = ∅ then 1 else 0 := by
      rw [← ih (Function.update a i b), mul_sum]
      refine sum_congr rfl fun x hx => ?_
      have hxi : x i = b := by simpa using (mem_filter.1 hx).2 i hi
      rw [chi_eq_prod_signVal, chi_eq_prod_signVal, prod_insert hi, hxi]
    rw [hchi, hchi, signVal_false, signVal_true, ite_eq_right (insert_ne_empty i S)]
    ring

/-- **The subcube form of the parity criterion.** If on the inputs agreeing with `a` off `S` the
sum of `(-1) ^ t(x) χ_S(x)` is nonzero, some such input is followed along a path querying all of
`S`. -/
private theorem exists_subset_queries (t : DecisionTree ι Bool) :
    ∀ (S : Finset ι) (a : ι → Bool),
      ∑ x ∈ univ.filter (fun x => ∀ j ∉ S, x j = a j), signVal (t.eval x) * chi ℝ S x ≠ 0 →
        ∃ x, (∀ j ∉ S, x j = a j) ∧ S ⊆ t.queries x := by
  induction t with
  | leaf b =>
    intro S a h
    by_cases hS : S = ∅
    · subst hS
      exact ⟨a, fun _ _ => rfl, empty_subset _⟩
    · refine absurd ?_ h
      simp only [eval_leaf]
      rw [← mul_sum, sum_filter_chi, ite_eq_right hS, mul_zero]
  | node i t₀ t₁ ih₀ ih₁ =>
    intro S a h
    by_cases hiS : i ∈ S
    · -- split the subcube along the queried free coordinate `i`
      have hS : S = insert i (S.erase i) := (insert_erase hiS).symm
      have hi : i ∉ S.erase i := notMem_erase i S
      rw [hS, sum_filter_insert hi] at h
      have hhalf (b : Bool) :
          ∑ x ∈ univ.filter (fun x => ∀ j ∉ S.erase i, x j = Function.update a i b j),
            signVal ((node i t₀ t₁).eval x) * chi ℝ (insert i (S.erase i)) x =
          signVal b * ∑ x ∈ univ.filter (fun x => ∀ j ∉ S.erase i,
            x j = Function.update a i b j),
            signVal ((cond b t₁ t₀).eval x) * chi ℝ (S.erase i) x := by
        rw [mul_sum]
        refine sum_congr rfl fun x hx => ?_
        have hxi : x i = b := by simpa using (mem_filter.1 hx).2 i hi
        rw [chi_eq_prod_signVal, chi_eq_prod_signVal, prod_insert hi, hxi, eval_node, hxi]
        cases b <;> simp only [Bool.cond_false, Bool.cond_true] <;> ring
      rw [hhalf, hhalf] at h
      have hb : ∃ b : Bool, ∑ x ∈ univ.filter (fun x => ∀ j ∉ S.erase i,
          x j = Function.update a i b j),
          signVal ((cond b t₁ t₀).eval x) * chi ℝ (S.erase i) x ≠ 0 := by
        by_contra hne
        simp only [not_exists, not_not] at hne
        exact h (by rw [hne false, hne true, mul_zero, mul_zero, add_zero])
      obtain ⟨b, hb⟩ := hb
      obtain ⟨x, hxa, hxq⟩ : ∃ x, (∀ j ∉ S.erase i, x j = Function.update a i b j) ∧
          S.erase i ⊆ (cond b t₁ t₀).queries x := by
        cases b
        · exact ih₀ _ _ hb
        · exact ih₁ _ _ hb
      have hxi : x i = b := by simpa using hxa i hi
      refine ⟨x, fun j hj => ?_, ?_⟩
      · have hji : j ≠ i := fun h => hj (h ▸ hiS)
        simpa [hji] using hxa j (fun h => hj (mem_of_mem_erase h))
      · rw [queries_node, hxi, hS]
        exact insert_subset_insert i (by cases b <;> simpa using hxq)
    · -- the queried coordinate is fixed on the subcube, so the node follows one subtree
      have heval : ∀ x ∈ univ.filter (fun x => ∀ j ∉ S, x j = a j),
          (node i t₀ t₁).eval x = (cond (a i) t₁ t₀).eval x := by
        intro x hx
        rw [eval_node, (mem_filter.1 hx).2 i hiS]
        cases a i <;> rfl
      rw [sum_congr rfl fun x hx => by rw [heval x hx]] at h
      obtain ⟨x, hxa, hxq⟩ : ∃ x, (∀ j ∉ S, x j = a j) ∧ S ⊆ (cond (a i) t₁ t₀).queries x := by
        cases ha : a i <;> simp only [ha, Bool.cond_false, Bool.cond_true] at h ⊢
        · exact ih₀ _ _ h
        · exact ih₁ _ _ h
      refine ⟨x, hxa, hxq.trans ?_⟩
      rw [queries_node, hxa i hiS]
      cases a i <;> exact subset_insert i _

/-- **The parity criterion for evasiveness** [Rivest and Vuillemin][RivestVuillemin1976]: if the
top Fourier coefficient of `f`, read as signs, is nonzero, then every decision tree computing `f`
queries every variable on some input. -/
theorem exists_queries_eq_univ_of_fourierCoeff_univ_ne_zero {f : (ι → Bool) → Bool}
    (hf : fourierCoeff (fun x => signVal (f x)) univ ≠ 0) {t : DecisionTree ι Bool}
    (ht : t.Computes f) : ∃ x, t.queries x = univ := by
  obtain ⟨x, -, hx⟩ := exists_subset_queries t univ (fun _ => false) (by
    rw [filter_true_of_mem fun x _ j hj => absurd (mem_univ j) hj,
      sum_congr rfl fun x _ => by rw [ht x]]
    intro h
    exact hf (by rw [fourierCoeff_eq_sum, h, zero_div]))
  exact ⟨x, univ_subset_iff.1 hx⟩

/-- A function with a nonzero top Fourier coefficient has decision tree complexity equal to the
number of variables. -/
theorem complexity_eq_card_of_fourierCoeff_univ_ne_zero {f : (ι → Bool) → Bool}
    (hf : fourierCoeff (fun x => signVal (f x)) univ ≠ 0) : complexity f = Fintype.card ι := by
  refine le_antisymm (complexity_le_card f) ?_
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  obtain ⟨x, hx⟩ := exists_queries_eq_univ_of_fourierCoeff_univ_ne_zero hf ht
  rw [← hd, ← card_univ, ← hx]
  exact card_queries_le_depth t x

end Cslib.DecisionTree
