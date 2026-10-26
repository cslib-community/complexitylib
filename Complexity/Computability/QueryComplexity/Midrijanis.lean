/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.NisanSzegedy
import Complexity.Foundations.BooleanAnalysis.MaximalSupport
import Complexity.Foundations.BooleanAnalysis.Symmetrization

/-!
# Midrijanis's degree bound for deterministic query complexity

For every total Boolean function, `D(f) ≤ deg(f) bs(f)` [Midrijanis2004], proof of Theorem 4.
Choose a nonzero Fourier support `S` with `|S| = deg(f)` and query all its coordinates. Every
face parallel to `S` is nonconstant, so every input has a sensitive block contained in `S`
(`QueryComplexity.exists_card_eq_degree_forall_exists_isSensitiveBlock_subset`). After fixing
the answers, this block is disjoint from the sensitive blocks on the remaining coordinates.
Block sensitivity therefore drops by at least one. Restriction cannot increase the degree, and
induction on block sensitivity bounds the total number of queries by `deg(f) bs(f)`.

The Nisan–Szegedy inequality `bs(f) ≤ 2 deg(f)²` then gives `D(f) ≤ 2 deg(f)³`, the conclusion of
[Midrijanis2004], Theorem 4. All measures are those of total Boolean functions on `Fin n → Bool`;
decision tree complexity counts the maximum number of queried coordinates along a branch.

## Main results

* `Cslib.QueryComplexity.exists_card_eq_degree_forall_exists_isSensitiveBlock_subset`:
  a nonconstant function has a set of `deg(f)` coordinates containing a sensitive block at every
  input, the maximal-monomial property of [Midrijanis2004], Lemma 3.
* `Cslib.DecisionTree.complexity_le_degree_mul_blockSensitivity`: `D(f) ≤ deg(f) bs(f)`.
* `Cslib.DecisionTree.complexity_le_two_mul_degree_pow_three`: `D(f) ≤ 2 deg(f)³`.

## References

* [G. Midrijanis, *Exact quantum query complexity for total Boolean functions*][Midrijanis2004],
  Lemma 3 and Theorem 4, arXiv version 2, pp. 3–4.
* [N. Nisan, M. Szegedy, *On the degree of Boolean functions as real polynomials*][NisanSzegedy1994]
-/

@[expose] public section

namespace Cslib

open Finset BitString

variable {n : ℕ}

namespace QueryComplexity

/-- A nonconstant Boolean function has a set of `deg(f)` coordinates containing a sensitive
block at every input. This is the maximal-monomial property of [Midrijanis2004], Lemma 3,
expressed using the equivalent Fourier degree. -/
theorem exists_card_eq_degree_forall_exists_isSensitiveBlock_subset (f : BooleanFunction n)
    (hf : degree f ≠ 0) :
    ∃ S : Finset (Fin n), #S = degree f ∧
      ∀ x, ∃ B, B ⊆ S ∧ IsSensitiveBlock f x B := by
  obtain ⟨S, hScard, hScoeff⟩ := exists_card_eq_totalDegree_fourierCoeff_ne_zero hf
  change #S = degree f at hScard
  have hS : S.Nonempty := card_pos.1 (by omega)
  have hmax (T : Finset (Fin n)) (hST : S ⊂ T) :
      fourierCoeff (fun x => bitVal ℝ (f x)) T = 0 :=
    fourierCoeff_eq_zero_of_mem_lowDegree (mem_lowDegree_totalDegree _)
      (by change degree f < #T; rw [← hScard]; exact card_lt_card hST)
  refine ⟨S, hScard, fun x => ?_⟩
  obtain ⟨y, hy, hfy⟩ := exists_ne_on_face_of_fourierCoeff_maximal hS hScoeff hmax x
  refine ⟨({i | y i ≠ x i} : Finset (Fin n)), ?_, ?_⟩
  · intro i hi
    by_contra hiS
    exact (mem_filter.1 hi).2 (hy i hiS)
  · rw [IsSensitiveBlock, flipBlock_filter_ne]
    exact fun h => hfy (congrArg (bitVal ℝ) h)

end QueryComplexity

namespace DecisionTree

open QueryComplexity

/-- **Midrijanis's bound**: `D(f) ≤ deg(f) bs(f)` for every total Boolean function
[Midrijanis2004], proof of Theorem 4. Querying a maximum-degree monomial lowers block
sensitivity by at least one at every input. -/
theorem complexity_le_degree_mul_blockSensitivity (f : BooleanFunction n) :
    complexity f ≤ degree f * blockSensitivity f := by
  suffices ∀ m (f : BooleanFunction n), blockSensitivity f ≤ m →
      complexity f ≤ degree f * m from this _ f le_rfl
  intro m
  induction m with
  | zero =>
    intro f hf
    have h := complexity_le_blockSensitivity_pow_three f
    simpa [Nat.eq_zero_of_le_zero hf] using h
  | succ m ih =>
    intro f hf
    by_cases hd : degree f = 0
    · have hbs : blockSensitivity f = 0 := by
        have := blockSensitivity_le_two_mul_degree_sq f
        simp only [hd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
        exact Nat.eq_zero_of_le_zero this
      have h := complexity_le_blockSensitivity_pow_three f
      simpa [hbs, hd] using h
    obtain ⟨S, hScard, hS⟩ := exists_card_eq_degree_forall_exists_isSensitiveBlock_subset f hd
    refine (complexity_le_card_add S (d := degree f * m) fun a => ?_).trans_eq ?_
    · have hbs : blockSensitivity (fun y => f (S.piecewise a y)) ≤ m := by
        refine Finset.sup_le fun z _ => ?_
        obtain ⟨B, hBS, hB⟩ := hS (S.piecewise a z)
        have := (blockSensitivityAt_comp_piecewise_add_one_le a z hBS hB).trans
          ((blockSensitivityAt_le_blockSensitivity f _).trans hf)
        omega
      have hdeg : degree (fun y => f (S.piecewise a y)) ≤ degree f := by
        refine degree_le_iff_mem_lowDegree.2
          (comp_mem_lowDegree (φ := fun y => S.piecewise a y) ?_ (mem_lowDegree_totalDegree _))
        intro i
        by_cases hi : i ∈ S
        · simpa [hi] using const_mem_lowDegree (R := ℝ) (ι := Fin n) 1 (bitVal ℝ (a i))
        · simpa [hi] using bitVal_mem_lowDegree (R := ℝ) i
      exact (ih _ hbs).trans (Nat.mul_le_mul_right m hdeg)
    · rw [hScard, Nat.mul_succ, Nat.add_comm]

/-- **The cubic degree bound**: `D(f) ≤ 2 deg(f)³` for every total Boolean function
[Midrijanis2004], Theorem 4. -/
theorem complexity_le_two_mul_degree_pow_three (f : BooleanFunction n) :
    complexity f ≤ 2 * degree f ^ 3 :=
  (complexity_le_degree_mul_blockSensitivity f).trans
    ((Nat.mul_le_mul_left _ (blockSensitivity_le_two_mul_degree_sq f)).trans_eq (by ring))

end DecisionTree

end Cslib
