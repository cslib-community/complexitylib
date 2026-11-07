/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.SimpleGraph.PermMatching
public import Complexity.Foundations.Data.MvPolynomial.SchwartzZippel
public import Complexity.Foundations.LinearAlgebra.Matrix.SkewDeterminant
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# The Tutte matrix and the randomized perfect-matching test for general graphs

A finite simple graph `G` on a linearly ordered vertex type `V` has the *Tutte matrix*
`Cslib.Algorithms.Matching.tutteMatrix G`: its entry `(i, j)` is `X s(i, j)` when `ij` is an edge
and `i < j`, `-X s(i, j)` when `ij` is an edge and `j < i`, and `0` otherwise, with one
indeterminate per unordered pair. It is skew-symmetric. **Tutte's theorem**: its determinant is a
nonzero polynomial exactly when `G` has a perfect matching
(`Cslib.Algorithms.Matching.det_tutteMatrix_ne_zero_iff`), over every nontrivial commutative ring
[Tutte1947] [Motwani and Raghavan, Section 7.3][MotwaniRaghavan95].

In the Leibniz expansion of a skew-symmetric determinant the permutations with an odd cycle cancel
(`Matrix.det_eq_sum_even_cycleType_of_transpose_eq_neg`). A surviving nonzero term is a permutation
along the edges of `G` with only even cycles, which gives a perfect matching
(`SimpleGraph.exists_isPerfectMatching_of_perm`). Conversely, at the indicator of the edges of a
perfect matching `M` the Tutte matrix is the signed permutation matrix of the involution `M`, of
determinant `±1`.

The randomized test of Lovász [Lovasz1979] substitutes values `r : Sym2 V → R` for the
indeterminates (`Cslib.Algorithms.Matching.tutteEval G r`) and checks whether the determinant is
nonzero. Its error is one-sided. Without a perfect matching the determinant is always `0`
(`Cslib.Algorithms.Matching.det_tutteEval_eq_zero`). With one, over an integral domain and with the
values drawn independently and uniformly from a finite set `S`, the determinant vanishes with
probability at most `|V| / |S|` (`Cslib.Algorithms.Matching.card_det_tutteEval_eq_zero_div_le`),
by the Schwartz–Zippel lemma.

## Main definitions

* `Cslib.Algorithms.Matching.tutteMatrix`: the Tutte matrix of a simple graph.
* `Cslib.Algorithms.Matching.tutteEval`: the Tutte matrix at given values.

## Main results

* `Cslib.Algorithms.Matching.det_tutteMatrix_ne_zero_iff`: Tutte's theorem, the determinant is
  nonzero exactly when the graph has a perfect matching.
* `Cslib.Algorithms.Matching.det_tutteEval_eq_zero`: no false positives.
* `Cslib.Algorithms.Matching.card_det_tutteEval_eq_zero_div_le`: false negatives with probability
  at most `|V| / |S|`.
* `Cslib.Algorithms.Matching.exists_det_tutteEval_ne_zero`: values from any set of more than `|V|`
  elements detect a perfect matching.

## References

* [W. T. Tutte, *The factorization of linear graphs*][Tutte1947]
* [L. Lovász, *On determinants, matchings, and random algorithms*][Lovasz1979]
* [R. Motwani and P. Raghavan, *Randomized Algorithms*, Section 7.3][MotwaniRaghavan95]
-/

public section

namespace Cslib.Algorithms.Matching

open Finset Matrix MvPolynomial Equiv

variable {V : Type*} [LinearOrder V] {R : Type*} [CommRing R] (G : SimpleGraph V)
  [DecidableRel G.Adj]

/-- The Tutte matrix of `G` at the values `r : Sym2 V → R`: `r s(i, j)` at each edge with
`i < j`, `-r s(i, j)` at each edge with `j < i`, and `0` elsewhere. -/
def tutteEval (r : Sym2 V → R) : Matrix V V R := fun i j =>
  if G.Adj i j then (if i < j then r s(i, j) else -r s(i, j)) else 0

/-- An entry of the Tutte matrix at values. -/
theorem tutteEval_apply (r : Sym2 V → R) (i j : V) :
    tutteEval G r i j = if G.Adj i j then (if i < j then r s(i, j) else -r s(i, j)) else 0 := by
  unfold tutteEval
  rfl

/-- The **Tutte matrix** of a simple graph `G`: `X s(i, j)` at each edge with `i < j`,
`-X s(i, j)` at each edge with `j < i`, and `0` elsewhere. -/
noncomputable def tutteMatrix : Matrix V V (MvPolynomial (Sym2 V) R) :=
  tutteEval G X

/-- The Tutte matrix at values is skew-symmetric. -/
theorem transpose_tutteEval (r : Sym2 V → R) : (tutteEval G r)ᵀ = -tutteEval G r := by
  ext i j
  rw [transpose_apply, Matrix.neg_apply, tutteEval_apply, tutteEval_apply]
  by_cases h : G.Adj j i
  · have hs : s(j, i) = s(i, j) := Sym2.eq_swap
    rw [ite_eq_left h, ite_eq_left h.symm, hs]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [ite_eq_right (not_lt.2 hij.le), ite_eq_left hij]
    · exact (G.irrefl h).elim
    · rw [ite_eq_left hij, ite_eq_right (not_lt.2 hij.le), neg_neg]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm), neg_zero]

/-- Substituting values for the indeterminates of the Tutte matrix. -/
theorem map_eval_tutteMatrix (r : Sym2 V → R) :
    (tutteMatrix (R := R) G).map (eval r) = tutteEval G r := by
  ext i j
  simp only [map_apply, tutteMatrix, tutteEval_apply]
  split_ifs <;> simp

/-- An entry of the Tutte matrix has total degree at most `1`. -/
theorem totalDegree_tutteMatrix_le (i j : V) : (tutteMatrix (R := R) G i j).totalDegree ≤ 1 := by
  simp only [tutteMatrix, tutteEval_apply]
  split_ifs
  · exact (totalDegree_monomial_le _ _).trans (by simp)
  · rw [totalDegree_neg]
    exact (totalDegree_monomial_le _ _).trans (by simp)
  · simp

variable [Fintype V]

/-- The determinant of the Tutte matrix at values is the determinant polynomial evaluated at
them. -/
theorem det_tutteEval (r : Sym2 V → R) :
    (tutteEval G r).det = eval r (tutteMatrix G).det := by
  rw [← map_eval_tutteMatrix, RingHom.map_det, RingHom.mapMatrix_apply]

/-- A nonzero determinant of the Tutte matrix at some values gives a perfect matching: in the
Leibniz expansion the permutations with an odd cycle cancel, and a surviving nonzero term is a
permutation along the edges of `G` with only even cycles. -/
theorem exists_isPerfectMatching_of_det_tutteEval_ne_zero {r : Sym2 V → R}
    (h : (tutteEval G r).det ≠ 0) : ∃ M : G.Subgraph, M.IsPerfectMatching := by
  rw [det_eq_sum_even_cycleType_of_transpose_eq_neg (transpose_tutteEval G r)] at h
  obtain ⟨σ, hσ, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  rw [mem_filter] at hσ
  have hadj : ∀ i, G.Adj i (σ i) := by
    intro i
    by_contra hi
    refine hne ?_
    rw [prod_eq_zero (mem_univ i) (by rw [tutteEval_apply, ite_eq_right fun h' => hi h'.symm]),
      smul_zero]
  exact SimpleGraph.exists_isPerfectMatching_of_perm σ hadj hσ.2

/-- **No false positives**: without a perfect matching, the Tutte matrix has determinant `0` at
all values. -/
theorem det_tutteEval_eq_zero (hG : ¬ ∃ M : G.Subgraph, M.IsPerfectMatching) (r : Sym2 V → R) :
    (tutteEval G r).det = 0 :=
  by_contra fun h => hG (exists_isPerfectMatching_of_det_tutteEval_ne_zero G h)

/-- Without a perfect matching, the determinant of the Tutte matrix is the zero polynomial. -/
theorem det_tutteMatrix_eq_zero (hG : ¬ ∃ M : G.Subgraph, M.IsPerfectMatching) :
    (tutteMatrix (R := R) G).det = 0 :=
  det_tutteEval_eq_zero G hG X

/-- With a perfect matching `M`, the determinant of the Tutte matrix is a nonzero polynomial: at
the indicator of the edges of `M` the Tutte matrix is the signed permutation matrix of the
involution `M`, of determinant `±1`. -/
theorem det_tutteMatrix_ne_zero [Nontrivial R] {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    (tutteMatrix (R := R) G).det ≠ 0 := by
  classical
  have hu := SimpleGraph.Subgraph.isPerfectMatching_iff.1 hM
  let τ : V → V := fun v => (hu v).choose
  have hτ : ∀ v w, M.Adj v w ↔ τ v = w := fun v w =>
    ⟨fun h => ((hu v).choose_spec.2 w h).symm, fun h => h ▸ (hu v).choose_spec.1⟩
  have hinv : Function.Involutive τ := fun v => (hτ _ _).1 ((hτ v (τ v)).2 rfl).symm
  let p : Perm V := hinv.toPerm
  have hp : ∀ i, p i = τ i := fun _ => rfl
  let r : Sym2 V → R := fun e => if e ∈ M.edgeSet then 1 else 0
  have hentry : ∀ i j, tutteEval G r i j = if τ i = j then (if i < j then 1 else -1) else 0 := by
    intro i j
    by_cases h : τ i = j
    · have hM' := (hτ i j).2 h
      simp [tutteEval_apply, r, hM', M.adj_sub hM', h]
    · have hn : ¬ M.Adj i j := fun h' => h ((hτ i j).1 h')
      simp [tutteEval_apply, r, hn, h]
  intro h0
  have hdet := det_tutteEval G r
  rw [h0, map_zero, det_apply, sum_eq_single p] at hdet
  · have hf : ∀ i, tutteEval G r (p i) i * tutteEval G r (p i) i = 1 := by
      intro i
      rw [hp, hentry, ite_eq_left (hinv i)]
      split_ifs <;> simp
    have hprod : (∏ i, tutteEval G r (p i) i) * ∏ i, tutteEval G r (p i) i = 1 := by
      rw [← prod_mul_distrib, prod_congr rfl fun i _ => hf i, prod_const_one]
    have hne : ∏ i, tutteEval G r (p i) i ≠ 0 := fun h => by
      rw [h, zero_mul] at hprod
      exact zero_ne_one hprod
    rcases Int.units_eq_one_or (Perm.sign p) with hs | hs <;> simp [hs, hne] at hdet
  · intro σ _ hσ
    obtain ⟨i, hi⟩ : ∃ i, τ (σ i) ≠ i := by
      by_contra! hall
      refine hσ (Equiv.ext fun i => ?_)
      have := congrArg τ (hall i)
      rw [hinv] at this
      exact this
    rw [prod_eq_zero (mem_univ i) (by rw [hentry, ite_eq_right hi]), smul_zero]
  · intro h
    exact absurd (mem_univ p) h

/-- **Tutte's theorem**: over a nontrivial commutative ring, the determinant of the Tutte matrix of
a simple graph is a nonzero polynomial exactly when the graph has a perfect matching. -/
theorem det_tutteMatrix_ne_zero_iff [Nontrivial R] :
    (tutteMatrix (R := R) G).det ≠ 0 ↔ ∃ M : G.Subgraph, M.IsPerfectMatching :=
  ⟨fun h => by_contra fun hG => h (det_tutteMatrix_eq_zero G hG),
    fun ⟨_, hM⟩ => det_tutteMatrix_ne_zero G hM⟩

/-- The determinant of the Tutte matrix has total degree at most `|V|`. -/
theorem totalDegree_det_tutteMatrix_le :
    (tutteMatrix (R := R) G).det.totalDegree ≤ Fintype.card V := by
  simpa using totalDegree_det_le _ 1 (totalDegree_tutteMatrix_le (R := R) G)

/-- **The randomized perfect-matching test**: for a simple graph with a perfect matching, over an
integral domain, the Tutte matrix at values drawn independently and uniformly from a finite set
`S` is singular with probability at most `|V| / |S|`. -/
theorem card_det_tutteEval_eq_zero_div_le [IsDomain R] [DecidableEq R] {M : G.Subgraph}
    (hM : M.IsPerfectMatching) (S : Finset R) :
    #{r ∈ Fintype.piFinset fun _ : Sym2 V => S | (tutteEval G r).det = 0} /
        (#S ^ Fintype.card (Sym2 V) : ℚ≥0) ≤ Fintype.card V / #S := by
  simp_rw [det_tutteEval]
  refine (schwartz_zippel_totalDegree_fintype (det_tutteMatrix_ne_zero G hM) S).trans ?_
  gcongr
  exact_mod_cast totalDegree_det_tutteMatrix_le G

/-- Values from any set of more than `|V|` elements of an integral domain detect a perfect
matching: some choice of them makes the Tutte matrix nonsingular. -/
theorem exists_det_tutteEval_ne_zero [IsDomain R] {M : G.Subgraph} (hM : M.IsPerfectMatching)
    {S : Finset R} (hS : Fintype.card V < #S) :
    ∃ r : Sym2 V → R, (∀ e, r e ∈ S) ∧ (tutteEval G r).det ≠ 0 := by
  classical
  by_contra! h
  have hb := card_det_tutteEval_eq_zero_div_le G hM S
  rw [filter_true_of_mem fun r hr => h r (Fintype.mem_piFinset.1 hr), Fintype.card_piFinset,
    prod_const, card_univ] at hb
  have hpos : (0 : ℚ≥0) < #S := by exact_mod_cast (Nat.zero_le _).trans_lt hS
  rw [Nat.cast_pow, div_self (pow_ne_zero _ hpos.ne'), le_div_iff₀ hpos, one_mul] at hb
  exact absurd hb (not_le.2 (by exact_mod_cast hS))

end Cslib.Algorithms.Matching
