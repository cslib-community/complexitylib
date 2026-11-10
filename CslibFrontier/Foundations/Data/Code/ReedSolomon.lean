/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Basic
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Polynomial.Basic
import CslibFrontier.Foundations.Data.Code.Linear
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Lagrange

/-!
# Reed–Solomon codes

The *Reed–Solomon code* with degree bound `k` and evaluation points `α : ι → F` in a field `F`
consists of the words `i ↦ p (α i)` of values of the polynomials `p` of degree less than `k`
(`Cslib.Code.reedSolomon`) [ReedSolomon1960], [GuruswamiRudraSudan2019],
[MacWilliams and Sloane, Chapter 10][MacWilliamsSloane1977]. It is a linear code of length
`n = |ι|`. When the points are distinct, a nonzero polynomial of degree less than `k` vanishes at
fewer than `k` of them, so a nonzero codeword has weight at least `n - k + 1`
(`Cslib.Code.le_hammingNorm_of_mem_reedSolomon`); the product of `X - α i` over `k - 1` of the
points shows that this is attained, so for `1 ≤ k ≤ n` the minimum distance is exactly
`n - k + 1` (`Cslib.Code.minDist_reedSolomon`). For `k ≤ n` the polynomials of degree less
than `k` are determined by their values, so the code has dimension `k`
(`Cslib.Code.finrank_reedSolomon`). Dimension plus minimum distance is `n + 1`: Reed–Solomon codes
meet the Singleton bound `Cslib.Code.finrank_add_le_card_add_one` with equality.

## Main definitions

* `Cslib.Code.reedSolomon`: the Reed–Solomon code.

## Main results

* `Cslib.Code.mem_reedSolomon`: the codewords are the evaluations of polynomials of degree less
  than `k`.
* `Cslib.Code.le_hammingNorm_of_mem_reedSolomon`, `Cslib.Code.le_minDist_reedSolomon`: nonzero
  codewords have weight at least `n - k + 1`.
* `Cslib.Code.minDist_reedSolomon`: the minimum distance is `n - k + 1`.
* `Cslib.Code.finrank_reedSolomon`: with distinct points and `k ≤ n`, the dimension is `k`.

## References

* [I. S. Reed, G. Solomon, *Polynomial codes over certain finite fields*][ReedSolomon1960]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*]
  [GuruswamiRudraSudan2019]
* [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
  [MacWilliamsSloane1977]
-/

@[expose] public section

namespace Cslib.Code

open Finset Polynomial

variable {F ι : Type*} [Field F]

/-- The *Reed–Solomon code* with degree bound `k` and evaluation points `α`: the words `i ↦ p (α i)`
for the polynomials `p` of degree less than `k`. The points are usually distinct. -/
noncomputable def reedSolomon (α : ι → F) (k : ℕ) : Submodule F (ι → F) :=
  (degreeLT F k).map (LinearMap.pi fun i => leval (α i))

variable {α : ι → F} {k : ℕ}

/-- A word is a codeword of `reedSolomon α k` exactly when it is `i ↦ p (α i)` for a polynomial `p`
of degree less than `k`. -/
theorem mem_reedSolomon {w : ι → F} :
    w ∈ reedSolomon α k ↔ ∃ p : F[X], p.degree < k ∧ (fun i => p.eval (α i)) = w := by
  simp only [reedSolomon, Submodule.mem_map, mem_degreeLT]
  rfl

/-- The values `i ↦ p (α i)` of a polynomial `p` of degree less than `k` form a codeword of
`reedSolomon α k`. -/
theorem eval_mem_reedSolomon (α : ι → F) {p : F[X]} (hp : p.degree < k) :
    (fun i => p.eval (α i)) ∈ reedSolomon α k :=
  mem_reedSolomon.2 ⟨p, hp, rfl⟩

variable [Fintype ι] [DecidableEq F]

/-- A nonzero polynomial vanishes at no more of the distinct points `α i` than its degree. -/
private theorem card_filter_eval_eq_zero_le (hα : Function.Injective α) {p : F[X]} (hp : p ≠ 0) :
    #{i | p.eval (α i) = 0} ≤ p.natDegree := by
  rw [← card_image_of_injective _ hα]
  refine card_le_degree_of_subset_roots fun a ha => ?_
  obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
  exact (mem_roots hp).2 (mem_filter.1 hi).2

/-- With distinct points, a nonzero codeword of the Reed–Solomon code with degree bound `k` has
weight at least `n - k + 1`. -/
theorem le_hammingNorm_of_mem_reedSolomon (hα : Function.Injective α) {w : ι → F}
    (hw : w ∈ reedSolomon α k) (hw0 : w ≠ 0) : Fintype.card ι - k + 1 ≤ hammingNorm w := by
  obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.1 hw
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hw0 (funext fun _ => eval_zero)
  have hdeg : p.natDegree < k := (natDegree_lt_iff_degree_lt hp0).2 hp
  have hzero := card_filter_eval_eq_zero_le hα hp0
  have hsum : #{i | p.eval (α i) = 0} + hammingNorm (fun i => p.eval (α i)) =
      Fintype.card ι := by
    rw [hammingNorm, ← card_univ]
    exact card_filter_add_card_filter_not _
  have hpos := hammingNorm_pos_iff.2 hw0
  omega

/-- With distinct points, the Reed–Solomon code with degree bound `k` has minimum distance at
least `n - k + 1`. -/
theorem le_minDist_reedSolomon (hα : Function.Injective α) (k : ℕ) :
    ((Fintype.card ι - k + 1 : ℕ) : ℕ∞) ≤ minDist (reedSolomon α k : Set (ι → F)) :=
  (le_minDist_iff_hammingNorm _).2 fun _ hw hw0 =>
    Nat.cast_le.2 (le_hammingNorm_of_mem_reedSolomon hα hw hw0)

/-- **The distance of Reed–Solomon codes.** With distinct points, the Reed–Solomon code with
degree bound `1 ≤ k ≤ n` has minimum distance exactly `n - k + 1`. -/
theorem minDist_reedSolomon (hα : Function.Injective α) (hk : 1 ≤ k)
    (hkn : k ≤ Fintype.card ι) :
    minDist (reedSolomon α k : Set (ι → F)) = (Fintype.card ι - k + 1 : ℕ) := by
  classical
  refine le_antisymm ?_ (le_minDist_reedSolomon hα k)
  -- the polynomial vanishing exactly at `k - 1` of the points
  obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset ι)) (n := k - 1)
    (by rw [card_univ]; omega)
  have hw : (fun i => (Lagrange.nodal S α).eval (α i)) ∈ reedSolomon α k := by
    refine eval_mem_reedSolomon α ?_
    rw [Lagrange.degree_nodal, hS]
    exact_mod_cast (by omega : k - 1 < k)
  have hne : ({i | (Lagrange.nodal S α).eval (α i) ≠ 0} : Finset ι) = univ \ S := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_sdiff]
    refine ⟨fun h hi => h (Lagrange.eval_nodal_at_node hi), fun hi => ?_⟩
    exact Lagrange.eval_nodal_not_at_node fun j hj h => hi (hα h ▸ hj)
  have hnorm : hammingNorm (fun i => (Lagrange.nodal S α).eval (α i)) = Fintype.card ι - k + 1 := by
    rw [hammingNorm, hne, card_univ_sdiff, hS]
    omega
  have hw0 : (fun i => (Lagrange.nodal S α).eval (α i)) ≠ 0 := by
    rw [← hammingNorm_pos_iff, hnorm]
    omega
  calc minDist (reedSolomon α k : Set (ι → F))
      ≤ hammingDist (fun i => (Lagrange.nodal S α).eval (α i)) 0 :=
        minDist_le_hammingDist hw (Submodule.zero_mem _) hw0
    _ = (Fintype.card ι - k + 1 : ℕ) := by rw [hammingDist_zero_right, hnorm]

omit [DecidableEq F] in
/-- With distinct points, the Reed–Solomon code with degree bound `k ≤ n` has dimension `k`. -/
theorem finrank_reedSolomon (hα : Function.Injective α) (hkn : k ≤ Fintype.card ι) :
    Module.finrank F (reedSolomon α k) = k := by
  classical
  let f : F[X] →ₗ[F] ι → F := LinearMap.pi fun i => leval (α i)
  -- a polynomial of degree less than `k ≤ n` is determined by its values at the points
  have hinj : Function.Injective (f.domRestrict (degreeLT F k)) := by
    intro p q h
    refine Subtype.ext (eq_of_degree_sub_lt_of_eval_finset_eq (univ.image α) ?_ fun x hx => ?_)
    · rw [card_image_of_injective _ hα, card_univ]
      exact (mem_degreeLT.1 ((degreeLT F k).sub_mem p.2 q.2)).trans_le (by exact_mod_cast hkn)
    · obtain ⟨i, -, rfl⟩ := mem_image.1 hx
      exact congrFun h i
  rw [reedSolomon, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj,
    (degreeLTEquiv F k).finrank_eq, Module.finrank_fin_fun]

end Cslib.Code
