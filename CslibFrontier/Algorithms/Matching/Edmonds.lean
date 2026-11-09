/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.BipartiteMatching
public import CslibFrontier.Foundations.Data.MvPolynomial.SchwartzZippel
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# The Edmonds matrix and the randomized perfect-matching test

A bipartite graph `G` on left and right vertices both indexed by a finite type `V` has the
*Edmonds matrix* `Cslib.Algorithms.Matching.edmondsMatrix G`: its entry `(i, j)` is the
indeterminate `X (i, j)` when `(i, j)` is an edge and `0` otherwise. Its determinant, a polynomial
in the variables `V × V`, is nonzero exactly when `G` has a perfect matching
(`Cslib.Algorithms.Matching.det_edmondsMatrix_ne_zero_iff`), over every nontrivial commutative
ring. In the Leibniz expansion every permutation `σ` gives the monomial `∏ v, X (v, σ v)` when its
pairs are all edges and `0` otherwise. Without a perfect matching every term vanishes. With one,
`σ`, evaluating at the indicator of the pairs `(v, σ v)` turns the matrix into the permutation
matrix of `σ`, of determinant `sign σ ≠ 0`. This is Edmonds' observation [Edmonds1967] that
underlies Lovász's randomized matching algorithm [Lovasz1979]
[Motwani and Raghavan, Section 7.3][MotwaniRaghavan95].

The randomized test substitutes values `r : V × V → R` for the indeterminates
(`Cslib.Algorithms.Matching.edmondsEval G r`) and checks whether the determinant is nonzero. Its
error is one-sided. Without a perfect matching the determinant is always `0`
(`Cslib.Algorithms.Matching.det_edmondsEval_eq_zero`). With one, over an integral domain and with
the values drawn independently and uniformly from a finite set `S`, the determinant vanishes with
probability at most `|V| / |S|`
(`Cslib.Algorithms.Matching.card_det_edmondsEval_eq_zero_div_le`), by the Schwartz–Zippel lemma,
since the determinant has total degree at most `|V|`.

## Main definitions

* `Cslib.Algorithms.Matching.edmondsMatrix`: the Edmonds matrix of a bipartite graph.
* `Cslib.Algorithms.Matching.edmondsEval`: the Edmonds matrix at given values.

## Main results

* `Cslib.Algorithms.Matching.det_edmondsMatrix_ne_zero_iff`: the determinant is nonzero exactly
  when the graph has a perfect matching.
* `Cslib.Algorithms.Matching.det_edmondsEval_eq_zero`: no false positives.
* `Cslib.Algorithms.Matching.card_det_edmondsEval_eq_zero_div_le`: false negatives with
  probability at most `|V| / |S|`.
* `Cslib.Algorithms.Matching.exists_det_edmondsEval_ne_zero`: values from any set of more than
  `|V|` elements detect a perfect matching.

## References

* [J. Edmonds, *Systems of distinct representatives and linear algebra*][Edmonds1967]
* [L. Lovász, *On determinants, matchings, and random algorithms*][Lovasz1979]
* [R. Motwani and P. Raghavan, *Randomized Algorithms*, Section 7.3][MotwaniRaghavan95]
-/

public section

namespace Cslib.Algorithms.Matching

open Finset Matrix MvPolynomial Equiv Cslib.Circuits.BipartiteMatching

variable {V : Type*} {R : Type*} [CommRing R]

/-- The **Edmonds matrix** of a bipartite graph `G` on `V × V`: the indeterminate `X (i, j)` at
each edge `(i, j)` and `0` elsewhere. -/
noncomputable def edmondsMatrix (G : V × V → Bool) : Matrix V V (MvPolynomial (V × V) R) :=
  fun i j => if G (i, j) then X (i, j) else 0

/-- The Edmonds matrix at the values `r : V × V → R`: `r (i, j)` at each edge `(i, j)` and `0`
elsewhere. -/
def edmondsEval (G : V × V → Bool) (r : V × V → R) : Matrix V V R :=
  fun i j => if G (i, j) then r (i, j) else 0

/-- An entry of the Edmonds matrix at values. -/
theorem edmondsEval_apply (G : V × V → Bool) (r : V × V → R) (i j : V) :
    edmondsEval G r i j = if G (i, j) then r (i, j) else 0 := by
  unfold edmondsEval
  rfl

/-- Substituting values for the indeterminates of the Edmonds matrix. -/
theorem map_eval_edmondsMatrix (G : V × V → Bool) (r : V × V → R) :
    (edmondsMatrix G).map (eval r) = edmondsEval G r := by
  ext i j
  simp only [map_apply, edmondsMatrix, edmondsEval]
  split_ifs <;> simp

/-- An entry of the Edmonds matrix has total degree at most `1`. -/
theorem totalDegree_edmondsMatrix_le (G : V × V → Bool) (i j : V) :
    (edmondsMatrix (R := R) G i j).totalDegree ≤ 1 := by
  unfold edmondsMatrix
  split_ifs
  · exact (totalDegree_monomial_le _ _).trans (by simp)
  · simp

variable [DecidableEq V]

/-- Evaluating the Edmonds matrix at the indicator of the pairs `(v, σ v)` of a perfect matching
`σ` gives the permutation matrix of `σ`. -/
theorem edmondsEval_indicator {G : V × V → Bool} {σ : Perm V} (hσ : ∀ v, G (v, σ v) = true) :
    edmondsEval G (fun e => if σ e.1 = e.2 then (1 : R) else 0) = σ.permMatrix R := by
  ext i j
  simp only [edmondsEval, Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  split_ifs with h1 h2 h2
  · rfl
  · rfl
  · subst h2
    simp [hσ i] at h1
  · rfl

variable [Fintype V]

/-- The determinant of the Edmonds matrix at values is the determinant polynomial evaluated at
them. -/
theorem det_edmondsEval (G : V × V → Bool) (r : V × V → R) :
    (edmondsEval G r).det = eval r (edmondsMatrix G).det := by
  rw [← map_eval_edmondsMatrix, RingHom.map_det, RingHom.mapMatrix_apply]

/-- Without a perfect matching, the determinant of the Edmonds matrix is the zero polynomial:
every term of the Leibniz expansion has a factor `0`. -/
theorem det_edmondsMatrix_eq_zero {G : V × V → Bool} (hG : ¬ HasPerfectMatching G) :
    (edmondsMatrix (R := R) G).det = 0 := by
  rw [← det_transpose, det_apply]
  refine sum_eq_zero fun σ _ => ?_
  obtain ⟨v, hv⟩ : ∃ v, G (v, σ v) = false := by
    by_contra! h
    exact hG ⟨σ, fun v => by simpa using h v⟩
  rw [prod_eq_zero (mem_univ v) (by simp [edmondsMatrix, hv]), smul_zero]

/-- **No false positives**: without a perfect matching, the Edmonds matrix has determinant `0` at
all values. -/
theorem det_edmondsEval_eq_zero {G : V × V → Bool} (hG : ¬ HasPerfectMatching G)
    (r : V × V → R) : (edmondsEval G r).det = 0 := by
  rw [det_edmondsEval, det_edmondsMatrix_eq_zero hG, map_zero]

/-- With a perfect matching, the determinant of the Edmonds matrix is a nonzero polynomial. -/
theorem det_edmondsMatrix_ne_zero [Nontrivial R] {G : V × V → Bool}
    (hG : HasPerfectMatching G) : (edmondsMatrix (R := R) G).det ≠ 0 := by
  obtain ⟨σ, hσ⟩ := hG
  intro h
  have := det_edmondsEval G (fun e : V × V => if σ e.1 = e.2 then (1 : R) else 0)
  rw [edmondsEval_indicator hσ, det_permutation, h, map_zero] at this
  rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs <;> simp [hs] at this

/-- **Edmonds' criterion** [Edmonds1967]: over a nontrivial commutative ring, the determinant of
the Edmonds matrix of a bipartite graph is a nonzero polynomial exactly when the graph has a
perfect matching. -/
theorem det_edmondsMatrix_ne_zero_iff [Nontrivial R] {G : V × V → Bool} :
    (edmondsMatrix (R := R) G).det ≠ 0 ↔ HasPerfectMatching G :=
  ⟨fun h => by_contra fun hG => h (det_edmondsMatrix_eq_zero hG), det_edmondsMatrix_ne_zero⟩

/-- The determinant of the Edmonds matrix has total degree at most `|V|`. -/
theorem totalDegree_det_edmondsMatrix_le (G : V × V → Bool) :
    (edmondsMatrix (R := R) G).det.totalDegree ≤ Fintype.card V := by
  simpa using totalDegree_det_le _ 1 (totalDegree_edmondsMatrix_le (R := R) G)

/-- **The randomized perfect-matching test**: for a bipartite graph with a perfect matching, over
an integral domain, the Edmonds matrix at values drawn independently and uniformly from a finite
set `S` is singular with probability at most `|V| / |S|`. -/
theorem card_det_edmondsEval_eq_zero_div_le [IsDomain R] [DecidableEq R] {G : V × V → Bool}
    (hG : HasPerfectMatching G) (S : Finset R) :
    #{r ∈ Fintype.piFinset fun _ : V × V => S | (edmondsEval G r).det = 0} /
        (#S ^ Fintype.card (V × V) : ℚ≥0) ≤ Fintype.card V / #S := by
  simp_rw [det_edmondsEval]
  refine (schwartz_zippel_totalDegree_fintype (det_edmondsMatrix_ne_zero hG) S).trans ?_
  gcongr
  exact_mod_cast totalDegree_det_edmondsMatrix_le G

/-- Values from any set of more than `|V|` elements of an integral domain detect a perfect
matching: some choice of them makes the Edmonds matrix nonsingular. -/
theorem exists_det_edmondsEval_ne_zero [IsDomain R] {G : V × V → Bool}
    (hG : HasPerfectMatching G) {S : Finset R} (hS : Fintype.card V < #S) :
    ∃ r : V × V → R, (∀ e, r e ∈ S) ∧ (edmondsEval G r).det ≠ 0 := by
  simp_rw [det_edmondsEval]
  exact exists_eval_ne_zero_of_totalDegree_lt_card (det_edmondsMatrix_ne_zero hG)
    ((totalDegree_det_edmondsMatrix_le G).trans_lt hS)

end Cslib.Algorithms.Matching
