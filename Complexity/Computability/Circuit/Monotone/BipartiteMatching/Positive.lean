/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.BipartiteMatching.Approximator
import Complexity.Foundations.GroupTheory.Perm.Fixing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Perm

/-!
# Positive errors of matching approximators

The positive test inputs are the `n!` perfect matchings `{(i, σ i)}` of permutations `σ`
(`Cslib.Circuits.BipartiteMatching.ofPerm`). At most `(n - #E)!` of them contain a set `E` of edges
(`Cslib.Circuits.BipartiteMatching.card_filter_contains_ofPerm_le`): those containing it are a coset
of the permutations fixing its left endpoints.

Closing only adds matchings, so constants and disjunctions make no positive errors. A conjunction
errs on `σ` only if each argument has a matching in the perfect matching of `σ` but their
intersection has none. Take minimal such matchings `X` and `Y` of the two arguments: their union
lies in the perfect matching of `σ`, so it is a matching, and if it had at most `s` edges both
closed families would contain it. So it has more than `s` edges, and lies in at most `(n - s - 1)!`
of the perfect matchings. An approximator has at most `(r - 1) ^ s` minimal matchings
(`Cslib.Circuits.BipartiteMatching.Razborov.Approximator.card_minimals_le`), so a conjunction errs
on at most `(r - 1) ^ (2 s) (n - s - 1)!` of them
(`Cslib.Circuits.BipartiteMatching.Razborov.Positive.errorCap`). This is
[Jukna, Lemma 9.34][Jukna2012], with the Alon–Boppana bound in place of the sunflower bound
`s! r ^ s` on the number of minimal matchings.

## Main definitions

* `Cslib.Circuits.BipartiteMatching.ofPerm`: the perfect matching of a permutation.
* `Cslib.Circuits.BipartiteMatching.Razborov.Positive.errorCap`,
  `Cslib.Circuits.BipartiteMatching.Razborov.Positive.errorCost`,
  `Cslib.Circuits.BipartiteMatching.Razborov.Positive.exceptions`: the per-conjunction error cap,
  the per-operation error cost and the positive exceptions of a gate.
* `Cslib.Circuits.BipartiteMatching.Razborov.Positive.scheme`: the approximation scheme on perfect
  matchings.

## Main results

* `Cslib.Circuits.BipartiteMatching.card_filter_contains_ofPerm_le`: at most `(n - #E)!`
  permutations contain a set `E` of edges.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Section 9.11][Jukna2012]
* [N. Alon, R. B. Boppana, *The monotone circuit complexity of Boolean functions*][AlonBoppana1987]
-/

@[expose] public section

namespace Cslib.Circuits.BipartiteMatching

open Finset
open scoped Nat

variable {n : ℕ}

/-! ### Perfect matchings of permutations -/

/-- The perfect matching of a permutation `σ`: the graph with the edges `(i, σ i)`. -/
def ofPerm (σ : Equiv.Perm (Fin n)) : BitString (n * n) :=
  fun i => decide (σ (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm i).2)

/-- The edges of the perfect matching of `σ` are the pairs `(i, σ i)`. -/
@[simp] theorem graph_ofPerm (σ : Equiv.Perm (Fin n)) (e : Fin n × Fin n) :
    graph (ofPerm σ) e = decide (σ e.1 = e.2) := by
  simp only [graph, ofPerm, Equiv.symm_apply_apply]

/-- The perfect matching of `σ` contains `E` when `σ e.1 = e.2` for every edge `e` of `E`. -/
theorem contains_ofPerm_iff {σ : Equiv.Perm (Fin n)} {E : Finset (Fin n × Fin n)} :
    Contains (ofPerm σ) E ↔ ∀ e ∈ E, σ e.1 = e.2 := by
  simp [Contains]

/-- The perfect matching of a permutation has a perfect matching. -/
theorem bipartitePerfectMatching_ofPerm (σ : Equiv.Perm (Fin n)) :
    bipartitePerfectMatching n (ofPerm σ) = true :=
  bipartitePerfectMatching_eq_true_iff.2 ⟨σ, fun v => by simp⟩

/-- A set of edges inside a perfect matching is a matching. -/
theorem isMatching_of_contains_ofPerm {σ : Equiv.Perm (Fin n)} {E : Finset (Fin n × Fin n)}
    (h : Contains (ofPerm σ) E) : IsMatching E := by
  intro e he e' he' h'
  have h1 := contains_ofPerm_iff.1 h e he
  have h2 := contains_ofPerm_iff.1 h e' he'
  have hfst : e.1 = e'.1 := h'.elim id fun h' => σ.injective (h1.trans (h'.trans h2.symm))
  exact Prod.ext hfst (by rw [← h1, ← h2, hfst])

/-- **Permutations through a set of edges.** At most `(n - #E)!` permutations `σ` have
`σ e.1 = e.2` for every edge `e` of `E`: if `σ₀` is one, the others are `σ₀ τ` for the permutations
`τ` fixing the left endpoints of `E`. -/
theorem card_filter_contains_ofPerm_le (E : Finset (Fin n × Fin n)) :
    #{σ : Equiv.Perm (Fin n) | Contains (ofPerm σ) E} ≤ (n - E.card)! := by
  rcases (univ.filter fun σ : Equiv.Perm (Fin n) => Contains (ofPerm σ) E).eq_empty_or_nonempty
    with h | ⟨σ₀, hσ₀⟩
  · rw [h, card_empty]
    exact Nat.zero_le _
  have h₀ := (mem_filter.1 hσ₀).2
  have hU : (E.image Prod.fst).card = E.card := card_image_of_injOn fun e he e' he' h =>
    isMatching_of_contains_ofPerm h₀ e he e' he' (Or.inl h)
  have hfix := Equiv.Perm.card_filter_forall_eq_self (E.image Prod.fst)
  rw [Fintype.card_fin] at hfix
  rw [← hU, ← hfix]
  refine card_le_card_of_injOn (fun σ => σ₀⁻¹ * σ) (fun σ hσ => ?_)
    fun σ _ σ' _ h => mul_left_cancel h
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, mem_image] at hσ ⊢
  rintro _ ⟨e, he, rfl⟩
  rw [Equiv.Perm.mul_apply, contains_ofPerm_iff.1 hσ e he, Equiv.Perm.inv_eq_iff_eq,
    contains_ofPerm_iff.1 h₀ e he]

namespace Razborov.Positive

open Cslib.ImplicationClosure Approximator
open Cslib.Circuits.Monotone (signature Op interpretation_mono)

variable {r s : ℕ}

/-- The permutations whose perfect matching contains the union of a minimal matching of `F` and
one of `G` with more than `s` edges together. -/
def largeUnions (s : ℕ) (F G : Finset (Finset (Fin n × Fin n))) : Finset (Equiv.Perm (Fin n)) :=
  ((minimals F ×ˢ minimals G).filter fun p => s < (p.1 ∪ p.2).card).biUnion fun p =>
    univ.filter fun σ => Contains (ofPerm σ) (p.1 ∪ p.2)

/-- The number of positive errors charged to a conjunction. -/
def errorCap (n r s : ℕ) : ℕ :=
  (r - 1) ^ (2 * s) * (n - (s + 1))!

/-- For `r ≥ 2`, the perfect matchings containing a union of more than `s` edges of minimal
matchings of two approximators number at most `errorCap n r s`. -/
theorem card_largeUnions_le (hr : 2 ≤ r) (A B : Approximator n r s) :
    (largeUnions s A.terms B.terms).card ≤ errorCap n r s := by
  set M := (minimals A.terms ×ˢ minimals B.terms).filter fun p => s < (p.1 ∪ p.2).card
  calc (largeUnions s A.terms B.terms).card
      ≤ ∑ p ∈ M, #{σ : Equiv.Perm (Fin n) | Contains (ofPerm σ) (p.1 ∪ p.2)} := card_biUnion_le
    _ ≤ ∑ _p ∈ M, (n - (s + 1))! := sum_le_sum fun p hp =>
        (card_filter_contains_ofPerm_le _).trans
          (Nat.factorial_le (Nat.sub_le_sub_left (mem_filter.1 hp).2 n))
    _ ≤ ((r - 1) ^ s * (r - 1) ^ s) * (n - (s + 1))! := by
        rw [sum_const, smul_eq_mul]
        refine Nat.mul_le_mul_right _ ((card_filter_le _ _).trans ?_)
        rw [card_product]
        exact Nat.mul_le_mul (A.card_minimals_le hr) (B.card_minimals_le hr)
    _ = errorCap n r s := by rw [errorCap, ← pow_add, two_mul]

/-- Only conjunctions make positive errors. -/
def errorCost (n r s : ℕ) : Op → ℕ
  | .and => errorCap n r s
  | _ => 0

/-- The positive error cost of any gate is at most `errorCap n r s`. -/
theorem errorCost_le (op : Op) : errorCost n r s op ≤ errorCap n r s := by
  cases op <;> simp [errorCost]

/-- The positive errors of a gate: for a conjunction, the perfect matchings containing a union of
more than `s` edges of minimal matchings of its arguments. -/
def exceptions : (op : Op) → (Fin (signature.Arity op) → Approximator n r s) →
    Finset (Equiv.Perm (Fin n))
  | .and, A => largeUnions s (A 0).terms (A 1).terms
  | _, _ => ∅

/-- For `r ≥ 2`, the number of positive exceptions at an `op` gate is at most
`errorCost n r s op`. -/
theorem card_exceptions_le (hr : 2 ≤ r) (op : Op)
    (A : Fin (signature.Arity op) → Approximator n r s) :
    (exceptions op A).card ≤ errorCost n r s op := by
  cases op with
  | and => exact card_largeUnions_le hr (A 0) (A 1)
  | const | or => simp [exceptions]

variable [Fact (2 ≤ r)]

/-- Away from its exceptions, a gate is positively correct on perfect matchings. -/
theorem gate_correct (op : Op) (A : Fin (signature.Arity op) → Approximator n r s)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ∉ exceptions op A) :
    Monotone.interpretation op (fun i => (A i).decode (ofPerm σ)) ≤
      (Approximator.interpretation op A).decode (ofPerm σ) := by
  rw [Bool.le_iff_imp]
  intro h
  cases op with
  | const b => simpa using h
  | or =>
    rw [Monotone.interpretation_or, Bool.or_eq_true, decode_eq_true, decode_eq_true] at h
    rw [decode_eq_true, terms_interpretation_or]
    rcases h with ⟨W, hW, hσW⟩ | ⟨W, hW, hσW⟩
    · exact ⟨W, subset_closure _ (mem_union_left _ hW), hσW⟩
    · exact ⟨W, subset_closure _ (mem_union_right _ hW), hσW⟩
  | and =>
    rw [Monotone.interpretation_and, Bool.and_eq_true, decode_eq_true, decode_eq_true] at h
    obtain ⟨⟨X₀, hX₀, hσX₀⟩, ⟨Y₀, hY₀, hσY₀⟩⟩ := h
    obtain ⟨X, hX, hXX₀⟩ := exists_mem_minimals_subset hX₀
    obtain ⟨Y, hY, hYY₀⟩ := exists_mem_minimals_subset hY₀
    have hσXY : Contains (ofPerm σ) (X ∪ Y) := fun e he =>
      (mem_union.1 he).elim (fun he => hσX₀ e (hXX₀ he)) fun he => hσY₀ e (hYY₀ he)
    by_cases hXY : (X ∪ Y).card ≤ s
    · have hP : X ∪ Y ∈ matchings n s :=
        mem_matchings.2 ⟨isMatching_of_contains_ofPerm hσXY, hXY⟩
      rw [decode_eq_true, terms_interpretation_and]
      refine ⟨X ∪ Y, mem_inter.2 ⟨?_, ?_⟩, hσXY⟩
      · exact (A 0).isClosed.mem_of_subset (minimals_subset _ hX) subset_union_left hP
      · exact (A 1).isClosed.mem_of_subset (minimals_subset _ hY) subset_union_right hP
    · refine absurd (mem_biUnion.2 ⟨(X, Y), mem_filter.2 ⟨mem_product.2 ⟨hX, hY⟩, ?_⟩,
        mem_filter.2 ⟨mem_univ σ, hσXY⟩⟩) hσ
      exact not_le.1 hXY

/-- **Positive errors.** The approximation scheme on the perfect matchings of permutations: the
approximate value is at least the exact one away from the exceptions of the conjunctions. -/
def scheme (hs : 1 ≤ s) :
    Approximation.Scheme Monotone.interpretation
      (Approximator.interpretation (n := n) (r := r) (s := s))
      (fun (A : Approximator n r s) (σ : Equiv.Perm (Fin n)) => A.decode (ofPerm σ))
      ofPerm Approximator.input where
  relation := (· ≤ ·)
  relation_trans := le_trans
  map_relation op _ _ h := interpretation_mono op h
  errorCost := errorCost n r s
  exceptions := exceptions
  input_correct σ i := by rw [decode_input hs]
  gate_correct := gate_correct
  exceptions_card_le := card_exceptions_le Fact.out

end Razborov.Positive

end Cslib.Circuits.BipartiteMatching
