/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Schwartz–Zippel over any finite set of variables, and determinant degrees

Mathlib's `MvPolynomial.schwartz_zippel_totalDegree` bounds the proportion of the points of
`S ^ n` at which a nonzero polynomial in the variables `Fin n` vanishes by `totalDegree / |S|`.
`MvPolynomial.schwartz_zippel_totalDegree_fintype` transports it to the variables of any finite
type `σ`, by renaming along `Fintype.equivFin σ`.

A determinant of polynomials of total degree at most `d` has total degree at most `|ι| * d`
(`MvPolynomial.totalDegree_det_le`), since each term of the Leibniz expansion is a product of
`|ι|` entries. Together the two lemmas bound the probability that a polynomial determinant vanishes
at a random point.

## Main results

* `MvPolynomial.schwartz_zippel_totalDegree_fintype`: the Schwartz–Zippel lemma for variables
  indexed by a finite type.
* `MvPolynomial.totalDegree_det_le`: the total degree of a polynomial determinant.
-/

public section

namespace MvPolynomial

open Finset Fintype

/-- The **Schwartz–Zippel lemma** for variables indexed by a finite type `σ`: a nonzero polynomial
over an integral domain vanishes on at most a `totalDegree / |S|` proportion of the points of
`S ^ σ`. -/
theorem schwartz_zippel_totalDegree_fintype {R σ : Type*} [CommRing R] [IsDomain R]
    [DecidableEq R] [Fintype σ] [DecidableEq σ] {p : MvPolynomial σ R} (hp : p ≠ 0)
    (S : Finset R) :
    #{f ∈ piFinset fun _ : σ => S | eval f p = 0} / (#S ^ card σ : ℚ≥0) ≤
      p.totalDegree / #S := by
  set e := equivFin σ
  have hp' : rename e p ≠ 0 := fun h => hp (rename_injective _ e.injective (by rw [h, map_zero]))
  have hsz := schwartz_zippel_totalDegree hp' S
  have hdeg : (rename e p).totalDegree = p.totalDegree := totalDegree_renameEquiv e p
  rw [hdeg] at hsz
  convert hsz using 3
  refine card_bij' (fun f _ => f ∘ e.symm) (fun g _ => g ∘ e) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [mem_filter, mem_piFinset] at hf ⊢
    refine ⟨fun i => hf.1 _, ?_⟩
    rw [eval_rename, Function.comp_assoc, e.symm_comp_self, Function.comp_id]
    exact hf.2
  · intro g hg
    simp only [mem_filter, mem_piFinset] at hg ⊢
    refine ⟨fun i => hg.1 _, ?_⟩
    rw [eval_rename] at hg
    exact hg.2
  · intro f _
    funext i
    simp
  · intro g _
    funext i
    simp

/-- A determinant of polynomials of total degree at most `d` has total degree at most
`|ι| * d`. -/
theorem totalDegree_det_le {R σ ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ R)) (d : ℕ) (hA : ∀ i j, (A i j).totalDegree ≤ d) :
    A.det.totalDegree ≤ card ι * d := by
  rw [Matrix.det_apply]
  refine totalDegree_finsetSum_le fun σ _ => (totalDegree_smul_le _ _).trans ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i : ι, (A (σ i) i).totalDegree ≤ ∑ _i : ι, d := sum_le_sum fun i _ => hA _ _
    _ = card ι * d := by simp

end MvPolynomial
