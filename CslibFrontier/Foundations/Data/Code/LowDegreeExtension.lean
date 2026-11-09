/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.ReedMuller
import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Low-degree extensions

Let `h : H ↪ F` embed a finite set `H` of size `|H|` in a field `F`. Every function
`f : (Fin m → H) → F` on the grid `H ^ m` is the restriction of a polynomial of low degree: the
*low-degree extension*
`lowDegreeExtension h f x = ∑ u, f u * ∏ i, L (u i) (x i)`, where `L a` is the Lagrange basis
polynomial of the node `h a` among the nodes `h H`
[Babai, Fortnow, Levin, Szegedy][BabaiFortnowLevinSzegedy1991],
[Arora and Barak, Chapter 19][AroraBarak09]. It agrees with `f` on the grid
(`Cslib.Code.lowDegreeExtension_apply_embed`) and is a codeword of the Reed–Muller code of degree
`m * (|H| - 1)` (`Cslib.Code.lowDegreeExtension_mem_reedMuller`). Only this total degree bound is
formalized; by construction the extension also has degree less than `|H|` in each variable, and
for `H = {0, 1}` it is the multilinear extension, but neither fact is stated here.

Low-degree extensions encode truth tables into Reed–Muller codewords: the truth table of a
function on `n = m * b` bits, read as a function on `(BitString b) ^ m`, extends to a polynomial
in `m` variables of total degree at most `m * (2 ^ b - 1)` over a field with at least `2 ^ b`
elements. Informally, evaluating the extension at a point costs `|H| ^ m` terms, linear in the
size of the truth table, which is what makes encodings of functions computable in exponential time;
no running time is formalized in this module.

## Main definitions

* `Cslib.Code.lowDegreeExtension`: the low-degree extension.

## Main results

* `Cslib.Code.lowDegreeExtension_apply_embed`: it extends `f`.
* `Cslib.Code.lowDegreeExtension_mem_reedMuller`: it is a Reed–Muller codeword.

## References

* [L. Babai, L. Fortnow, L. Levin, M. Szegedy, *Checking computations in polylogarithmic time*]
  [BabaiFortnowLevinSzegedy1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
-/

@[expose] public section

namespace Cslib.Code

open Finset

variable {F : Type*} [Field F] {H : Type*} [Fintype H] [DecidableEq H] {m : ℕ}

/-- The **low-degree extension** of `f : (Fin m → H) → F` along the embedding `h : H ↪ F`. -/
noncomputable def lowDegreeExtension (h : H ↪ F) (f : (Fin m → H) → F) : (Fin m → F) → F :=
  fun x => ∑ u : Fin m → H, f u * ∏ i, (Lagrange.basis univ h (u i)).eval (x i)

/-- **The low-degree extension extends `f`**: it agrees with `f` on the grid. -/
theorem lowDegreeExtension_apply_embed (h : H ↪ F) (f : (Fin m → H) → F) (u : Fin m → H) :
    lowDegreeExtension h f (fun i => h (u i)) = f u := by
  rw [lowDegreeExtension, Finset.sum_eq_single u]
  · rw [prod_eq_one fun i _ => Lagrange.eval_basis_self h.injective.injOn (mem_univ _),
      mul_one]
  · intro u' _ hu'
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hu'
    rw [prod_eq_zero (mem_univ i) (Lagrange.eval_basis_of_ne hi (mem_univ _)), mul_zero]
  · exact fun h' => absurd (mem_univ u) h'

/-- **The low-degree extension is a Reed–Muller codeword** of degree `m * (|H| - 1)`. -/
theorem lowDegreeExtension_mem_reedMuller (h : H ↪ F) (f : (Fin m → H) → F) :
    lowDegreeExtension h f ∈ reedMuller F m (m * (Fintype.card H - 1)) := by
  classical
  let L : H → Polynomial F := fun a => Lagrange.basis univ h a
  have hL : ∀ a, (L a).natDegree = Fintype.card H - 1 := fun a => by
    rw [Lagrange.natDegree_basis h.injective.injOn (mem_univ a), card_univ]
  -- a univariate polynomial in the variable `i` has total degree at most its degree
  have hdeg : ∀ (i : Fin m) (p : Polynomial F), (p.toMvPolynomial i).totalDegree ≤ p.natDegree := by
    intro i p
    conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
    rw [map_sum]
    refine MvPolynomial.totalDegree_finsetSum_le fun k hk => ?_
    rw [map_mul, map_pow, Polynomial.toMvPolynomial_C, Polynomial.toMvPolynomial_X]
    calc (MvPolynomial.C (p.coeff k) * MvPolynomial.X i ^ k : MvPolynomial (Fin m) F).totalDegree
        ≤ (MvPolynomial.C (p.coeff k) : MvPolynomial (Fin m) F).totalDegree +
            (MvPolynomial.X i ^ k : MvPolynomial (Fin m) F).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ = k := by rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow, zero_add]
      _ ≤ p.natDegree := Nat.lt_succ_iff.1 (mem_range.1 hk)
  let P : MvPolynomial (Fin m) F := ∑ u : Fin m → H,
    MvPolynomial.C (f u) * ∏ i, (L (u i)).toMvPolynomial i
  refine mem_reedMuller.2 ⟨P, ?_, ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le fun u _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C (σ := Fin m) (f u), zero_add]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    calc ∑ i, ((L (u i)).toMvPolynomial i).totalDegree ≤ ∑ _i : Fin m, (Fintype.card H - 1) :=
          sum_le_sum fun i _ => (hdeg i _).trans (hL _).le
      _ = m * (Fintype.card H - 1) := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  · funext x
    simp only [P, lowDegreeExtension, map_sum, map_mul, MvPolynomial.eval_C, map_prod,
      MvPolynomial.eval_toMvPolynomial, L]

end Cslib.Code
