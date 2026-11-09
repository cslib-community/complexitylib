/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Basic
public import Mathlib.FieldTheory.Finite.Polynomial
public import Mathlib.RingTheory.MvPolynomial.Basic
import CslibFrontier.Foundations.Data.Code.Linear
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# Reed–Muller codes

The *Reed–Muller code* of degree `d` in `m` variables over a finite field `F` with `q` elements
consists of the evaluation tables on `Fin m → F` of the polynomials of total degree at most `d`
(`Cslib.Code.reedMuller`) [Reed1954], [Muller1954], [GuruswamiRudraSudan2019]. By the
Schwartz–Zippel lemma
`MvPolynomial.schwartz_zippel_totalDegree`, a nonzero polynomial of total degree at most `d`
vanishes on at most a `d / q` fraction of the points, so two distinct codewords differ on at least
a `1 - d / q` fraction of the `q ^ m` points
(`Cslib.Code.card_sub_mul_pow_le_mul_hammingDist_of_mem_reedMuller`). For `d < q` this is exact:
the product of `X 0 - t` over `d` field elements `t` vanishes exactly where the first coordinate
is one of them, so in `m + 1` variables the minimum distance is `(q - d) * q ^ m`
(`Cslib.Code.minDist_reedMuller`). For `d ≥ q` the bound says nothing; in particular the binary
Reed–Muller codes of degree at least two, whose distance comes from multilinear polynomials, are
not covered by it.

## Main definitions

* `Cslib.Code.reedMuller`: the Reed–Muller code.

## Main results

* `Cslib.Code.mem_reedMuller`: the codewords are the evaluation tables of polynomials of total
  degree at most `d`.
* `Cslib.Code.card_sub_mul_pow_le_mul_hammingNorm_of_mem_reedMuller`,
  `Cslib.Code.card_sub_mul_pow_le_mul_hammingDist_of_mem_reedMuller`: the Schwartz–Zippel distance
  bound.
* `Cslib.Code.le_minDist_reedMuller`: the minimum distance in `m + 1` variables is at least
  `(q - d) * q ^ m`.
* `Cslib.Code.minDist_reedMuller`: for `d < q` the minimum distance in `m + 1` variables is
  `(q - d) * q ^ m`.

## References

* [I. S. Reed, *A class of multiple-error-correcting codes and the decoding scheme*][Reed1954]
* [D. E. Muller, *Application of Boolean algebra to switching circuit design and to error
  detection*][Muller1954]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*]
  [GuruswamiRudraSudan2019]
-/

@[expose] public section

namespace Cslib.Code

open Finset MvPolynomial

variable (F : Type*) [Field F]

/-- The *Reed–Muller code* of degree `d` in `m` variables: the evaluation tables on `Fin m → F` of
the polynomials of total degree at most `d`. -/
noncomputable def reedMuller (m d : ℕ) : Submodule F ((Fin m → F) → F) :=
  (restrictTotalDegree (Fin m) F d).map (evalₗ F (Fin m))

variable {F} {m d : ℕ}

/-- A word is a codeword of the Reed–Muller code of degree `d` exactly when it is the evaluation
table of a polynomial of total degree at most `d`. -/
theorem mem_reedMuller {f : (Fin m → F) → F} :
    f ∈ reedMuller F m d ↔
      ∃ P : MvPolynomial (Fin m) F, P.totalDegree ≤ d ∧ (fun x => eval x P) = f := by
  simp only [reedMuller, Submodule.mem_map, mem_restrictTotalDegree]
  rfl

/-- The evaluation table of a polynomial of total degree at most `d` is a codeword of the
Reed–Muller code of degree `d`. -/
theorem eval_mem_reedMuller {P : MvPolynomial (Fin m) F} (hP : P.totalDegree ≤ d) :
    (fun x => eval x P) ∈ reedMuller F m d :=
  mem_reedMuller.2 ⟨P, hP, rfl⟩

variable [Fintype F] [DecidableEq F]

/-- **Schwartz–Zippel distance.** A nonzero codeword of the Reed–Muller code of degree `d` in `m`
variables over a field with `q` elements is nonzero on at least a `1 - d / q` fraction of the
`q ^ m` points: `(q - d) * q ^ m ≤ q * hammingNorm f`. -/
theorem card_sub_mul_pow_le_mul_hammingNorm_of_mem_reedMuller {f : (Fin m → F) → F}
    (hf : f ∈ reedMuller F m d) (hf0 : f ≠ 0) :
    (Fintype.card F - d) * Fintype.card F ^ m ≤ Fintype.card F * hammingNorm f := by
  obtain ⟨P, hP, rfl⟩ := mem_reedMuller.1 hf
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact hf0 (funext fun _ => map_zero _)
  have hq : 0 < Fintype.card F := Fintype.card_pos
  -- at most a `d / q` fraction of the points are zeros
  have hsz := schwartz_zippel_totalDegree hP0 (univ : Finset F)
  rw [Fintype.piFinset_univ, card_univ, div_le_div_iff₀ (by positivity) (by positivity)] at hsz
  have hzero : Fintype.card F * #{x | eval x P = 0} ≤ d * Fintype.card F ^ m := by
    have : (#{x | eval x P = 0} * Fintype.card F : ℚ≥0) ≤ d * Fintype.card F ^ m :=
      hsz.trans (by gcongr)
    rw [mul_comm]
    exact_mod_cast this
  -- the zeros and the nonzeros make up all `q ^ m` points
  have hsum : #{x | eval x P = 0} + hammingNorm (fun x => eval x P) = Fintype.card F ^ m := by
    rw [hammingNorm, card_filter_add_card_filter_not, card_univ, Fintype.card_fun,
      Fintype.card_fin]
  have hmul := congrArg (Fintype.card F * ·) hsum
  simp only [mul_add] at hmul
  rw [Nat.sub_mul]
  omega

/-- **Schwartz–Zippel distance.** Two distinct codewords of the Reed–Muller code of degree `d` in
`m` variables over a field with `q` elements differ on at least a `1 - d / q` fraction of the
`q ^ m` points: `(q - d) * q ^ m ≤ q * hammingDist f g`. -/
theorem card_sub_mul_pow_le_mul_hammingDist_of_mem_reedMuller {f g : (Fin m → F) → F}
    (hf : f ∈ reedMuller F m d) (hg : g ∈ reedMuller F m d) (hfg : f ≠ g) :
    (Fintype.card F - d) * Fintype.card F ^ m ≤ Fintype.card F * hammingDist f g := by
  rw [hammingDist_eq_hammingNorm]
  exact card_sub_mul_pow_le_mul_hammingNorm_of_mem_reedMuller
    ((reedMuller F m d).add_mem ((reedMuller F m d).neg_mem hf) hg)
    fun h => hfg (neg_add_eq_zero.1 h)

/-- The Reed–Muller code of degree `d` in `m + 1` variables over a field with `q` elements has
minimum distance at least `(q - d) * q ^ m`. -/
theorem le_minDist_reedMuller :
    (((Fintype.card F - d) * Fintype.card F ^ m : ℕ) : ℕ∞) ≤
      minDist (reedMuller F (m + 1) d : Set ((Fin (m + 1) → F) → F)) := by
  refine (le_minDist_iff_hammingNorm _).2 fun f hf hf0 => Nat.cast_le.2 ?_
  have h := card_sub_mul_pow_le_mul_hammingNorm_of_mem_reedMuller hf hf0
  rw [pow_succ, ← mul_assoc, mul_comm _ (Fintype.card F)] at h
  exact Nat.le_of_mul_le_mul_left h Fintype.card_pos

/-- **The distance of Reed–Muller codes.** For `d < q`, the Reed–Muller code of degree `d` in
`m + 1` variables over a field with `q` elements has minimum distance exactly
`(q - d) * q ^ m`. -/
theorem minDist_reedMuller (hd : d < Fintype.card F) :
    minDist (reedMuller F (m + 1) d : Set ((Fin (m + 1) → F) → F)) =
      ((Fintype.card F - d) * Fintype.card F ^ m : ℕ) := by
  refine le_antisymm ?_ le_minDist_reedMuller
  -- the product of `X 0 - t` over `d` field elements `t`
  obtain ⟨T, -, hT⟩ := exists_subset_card_eq (s := (univ : Finset F)) (n := d)
    (by rw [card_univ]; omega)
  let P : MvPolynomial (Fin (m + 1)) F := ∏ t ∈ T, (X 0 - C t)
  have hP : P.totalDegree ≤ d := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ t ∈ T, (X 0 - C t : MvPolynomial (Fin (m + 1)) F).totalDegree
        ≤ ∑ _t ∈ T, 1 :=
          sum_le_sum fun t _ => (totalDegree_sub_C_le _ _).trans (totalDegree_X 0).le
      _ = d := by rw [sum_const, smul_eq_mul, mul_one, hT]
  -- it vanishes exactly where the first coordinate is in `T`
  have hne : ({x | eval x P ≠ 0} : Finset (Fin (m + 1) → F)) =
      Fintype.piFinset (Fin.cons (univ \ T) fun _ => univ : Fin (m + 1) → Finset F) := by
    ext x
    simp [P, Fintype.mem_piFinset, Fin.forall_fin_succ, prod_ne_zero_iff, sub_eq_zero]
  have hnorm : hammingNorm (fun x => eval x P) = (Fintype.card F - d) * Fintype.card F ^ m := by
    rw [hammingNorm, hne, Fintype.card_piFinset, Fin.prod_univ_succ]
    simp [card_univ_sdiff, hT]
  have hP0 : (fun x => eval x P) ≠ 0 := by
    rw [← hammingNorm_pos_iff, hnorm]
    exact Nat.mul_pos (by omega) (pow_pos Fintype.card_pos _)
  calc minDist (reedMuller F (m + 1) d : Set ((Fin (m + 1) → F) → F))
      ≤ hammingDist (fun x => eval x P) 0 :=
        minDist_le_hammingDist (eval_mem_reedMuller hP) (Submodule.zero_mem _) hP0
    _ = ((Fintype.card F - d) * Fintype.card F ^ m : ℕ) := by
        rw [hammingDist_zero_right, hnorm]

end Cslib.Code
