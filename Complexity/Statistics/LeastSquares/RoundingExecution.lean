/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.Stability
public import Complexity.Foundations.LinearAlgebra.Matrix.RankOne
public import Cslib.Algorithms.Lean.TimeM
public import Complexity.Foundations.LinearAlgebra.Box
import all Complexity.Statistics.LeastSquares.Backbone
import Mathlib.Tactic

/-!
# Arithmetic implementation of monotone rounding

Explicit inverse computation and signed Sherman–Morrison updates for the rounding
algorithm of [XuGaoHu2027], Theorem 3.3, PDF pp. 6–7. The arithmetic definitions
are polymorphic in a field, and hence executable over the rationals. Their real
interpretation uses the existing inverse-matrix least-squares semantics.

Cramer's rule computes the initial coefficient without constructing a full inverse.
This is a separate linear-system solve and must be charged in addition to the LP
and the subsequent inverse computation. No cubic scalar-operation bound is claimed
for the determinant/adjugate implementation.

## Main definitions

* `VertexLP`, `sparsify`: standard external LP contract and constructed residual LP.
* `run`, `roundSparse`, `execute`: cached arithmetic rounding and initialization.
* `retained`: materialize the output's original-index subset.

## Main results

* `run_correct`, `roundSparse_correct`, `execute_correct`, `execute_retained`: semantics.
* `run_coordinates`, `run_rankChanges`, `execute_calls`: executed operation counts.
-/

public section

namespace Cslib.LeastSquares.RoundingExecution

open Matrix Algorithms.Lean

variable {K d : Type*} [Field K] [Fintype d] [DecidableEq d]

open Matrix.RankOne

variable {ι : Type*} [DecidableEq ι]

/-- The weights and cached normal-equation state returned by a rounding run.
Counts record the executed branches, not an a priori desired bound. -/
structure Result (K ι d : Type*) where
  /-- Final observation weights. -/
  weights : ι → K
  /-- Cached inverse of the final Gram matrix. -/
  inv : Matrix d d K
  /-- Cached final normal-equation response. -/
  response : d → K
  /-- Number of calls to the signed rank-one arithmetic kernel. -/
  rankChanges : ℕ
  /-- Number of observation weights processed. -/
  coordinates : ℕ

variable [LinearOrder K]

/-- Process a supplied list of fractional coordinates. A downdate removes the
current coordinate. If that endpoint improves the target, keep it; otherwise
restore this observation with weight one. Only the cached inverse is used.
All arithmetic is in `K`; in particular this definition executes over `ℚ`.
The correctness theorem requires distinct coordinates and a definite backbone. -/
@[expose] def run (x : ι → d → K) (y : ι → K) (e : d → K)
    (H : Matrix d d K) (r : d → K) (w : ι → K) : List ι → Result K ι d
  | [] => ⟨w, H, r, 0, 0⟩
  | i :: is =>
    let H₀ := change H (x i) (-w i)
    let r₀ := r - (w i * y i) • x i
    if e ⬝ᵥ (H₀ *ᵥ r₀) ≤ e ⬝ᵥ (H *ᵥ r) then
      let z := run x y e H₀ r₀ w is
      { z with
        weights := Function.update z.weights i 0
        rankChanges := z.rankChanges + 1
        coordinates := z.coordinates + 1 }
    else
      let H₁ := change H₀ (x i) 1
      let r₁ := r₀ + y i • x i
      let z := run x y e H₁ r₁ w is
      { z with
        weights := Function.update z.weights i 1
        rankChanges := z.rankChanges + 2
        coordinates := z.coordinates + 1 }

omit [DecidableEq d] in
/-- Termination and the exact number of processed coordinates follow from list
recursion, independently of arithmetic decisions and input feasibility. -/
theorem run_coordinates (x : ι → d → K) (y : ι → K) (e : d → K)
    (H : Matrix d d K) (r : d → K) (w : ι → K) (s : List ι) :
    (run x y e H r w s).coordinates = s.length := by
  induction s generalizing H r with
  | nil => rfl
  | cons i s ih => simp only [run]; split <;> simp only [ih, List.length_cons]

omit [DecidableEq d] in
/-- Each executed iteration makes one downdate and at most one restoration.
The bound is derived from the actual branch counters. -/
theorem run_rankChanges (x : ι → d → K) (y : ι → K) (e : d → K)
    (H : Matrix d d K) (r : d → K) (w : ι → K) (s : List ι) :
    (run x y e H r w s).rankChanges ≤ 2 * s.length := by
  induction s generalizing H r with
  | nil => simp [run]
  | cons i s ih =>
    simp only [run]
    split
    · have := ih (change H (x i) (-w i)) (r - (w i * y i) • x i)
      simp only [List.length_cons]; omega
    · have := ih (change (change H (x i) (-w i)) (x i) 1)
        (r - (w i * y i) • x i + y i • x i)
      simp only [List.length_cons]; omega

omit [DecidableEq d] in
/-- No observation outside the processing list is modified. -/
theorem run_outside (x : ι → d → K) (y : ι → K) (e : d → K)
    (H : Matrix d d K) (r : d → K) (w : ι → K) (s : List ι)
    (j : ι) (hj : j ∉ s) : (run x y e H r w s).weights j = w j := by
  induction s generalizing H r with
  | nil => rfl
  | cons i s ih =>
    have hji : j ≠ i := by intro h; exact hj (h ▸ List.mem_cons_self)
    have hjs : j ∉ s := fun h => hj (List.mem_cons_of_mem _ h)
    simp only [run]
    split <;> dsimp only <;> rw [Function.update_of_ne hji] <;> exact ih _ _ hjs

omit [DecidableEq d] in
/-- Every processed coordinate has an endpoint weight, even if the list happens
to contain repeats. Distinctness is needed for semantic rounding correctness. -/
theorem run_integral (x : ι → d → K) (y : ι → K) (e : d → K)
    (H : Matrix d d K) (r : d → K) (w : ι → K) (s : List ι)
    (j : ι) (hj : j ∈ s) :
    (run x y e H r w s).weights j = 0 ∨ (run x y e H r w s).weights j = 1 := by
  induction s generalizing H r with
  | nil => simp at hj
  | cons i s ih =>
    by_cases hji : j = i
    · subst j
      simp only [run]; split <;> simp
    · have hjs : j ∈ s := (List.mem_cons.mp hj).resolve_left hji
      simp only [run]
      split <;> dsimp only <;> simp only [Function.update_of_ne hji] <;> exact ih _ _ hjs

omit [Fintype d] [DecidableEq d] in
private theorem gram_update (G : Matrix d d ℝ) (s : Finset ι) {i : ι} (hi : i ∉ s)
    (x : ι → d → ℝ) (w : ι → ℝ) (b : ℝ) :
    weightedGram G (insert i s) x (Function.update w i b) =
      weightedGram (rankOneGram G (x i) b) s x w := by
  have hs : (∑ j ∈ s, Function.update w i b j • vecMulVec (x j) (x j)) =
      ∑ j ∈ s, w j • vecMulVec (x j) (x j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
  simp only [weightedGram, Finset.sum_insert hi, Function.update_self, hs, rankOneGram]
  abel

omit [Fintype d] [DecidableEq d] in
private theorem response_update (g : d → ℝ) (s : Finset ι) {i : ι} (hi : i ∉ s)
    (x : ι → d → ℝ) (y w : ι → ℝ) (b : ℝ) :
    weightedResponse g (insert i s) x y (Function.update w i b) =
      weightedResponse (g + (b * y i) • x i) s x y w := by
  have hs : (∑ j ∈ s, (Function.update w i b j * y j) • x j) =
      ∑ j ∈ s, (w j * y j) • x j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
  simp only [weightedResponse, Finset.sum_insert hi, Function.update_self, hs]
  abel

/-- With a positive definite fixed backbone, the arithmetic run maintains the
actual inverse and response, and cannot increase the specified linear target.
The list may contain arbitrary box weights; sparsity is only needed for the
dimension-dependent iteration bound. -/
theorem run_correct (x : ι → d → ℝ) (y w : ι → ℝ) (e : d → ℝ)
    (s : List ι) (hs : s.Nodup) (G : Matrix d d ℝ) (hG : G.PosDef) (g : d → ℝ)
    (hw : ∀ i ∈ s, w i ∈ Set.Icc (0 : ℝ) 1) :
    let z := run x y e (weightedGram G s.toFinset x w)⁻¹
      (weightedResponse g s.toFinset x y w) w s
    z.inv = (weightedGram G s.toFinset x z.weights)⁻¹ ∧
      z.response = weightedResponse g s.toFinset x y z.weights ∧
      e ⬝ᵥ weightedEstimate G g s.toFinset x y z.weights ≤
        e ⬝ᵥ weightedEstimate G g s.toFinset x y w := by
  induction s generalizing G g with
  | nil => simp [run, weightedGram, weightedResponse, weightedEstimate]
  | cons i s ih =>
    obtain ⟨his, hnodup⟩ := List.nodup_cons.mp hs
    have hi : i ∉ s.toFinset := by simpa using his
    have hws : ∀ j ∈ s, w j ∈ Set.Icc (0 : ℝ) 1 :=
      fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have hwi := hw i List.mem_cons_self
    let A := weightedGram G s.toFinset x w
    let r := weightedResponse g s.toFinset x y w
    have hA : A.PosDef := weightedGram_posDef hG _ x w (fun j hj => (hws j (by simpa using hj)).1)
    have hfull : (rankOneGram A (x i) (w i)).PosDef := rankOneGram_posDef hA _ hwi.1
    have hgram : weightedGram G (i :: s).toFinset x w = rankOneGram A (x i) (w i) := by
      simp [weightedGram, A, rankOneGram, Finset.sum_insert hi, add_comm, add_left_comm]
    have hresp : weightedResponse g (i :: s).toFinset x y w = r + (w i * y i) • x i := by
      simp [weightedResponse, r, Finset.sum_insert hi, add_comm, add_left_comm]
    have hzero : rankOneGram A (x i) (w i) + (-w i) • vecMulVec (x i) (x i) = A := by
      simp [rankOneGram]
    have hdown : change (rankOneGram A (x i) (w i))⁻¹ (x i) (-w i) = A⁻¹ := by
      rw [change_eq _ _ _ hfull.isUnit (hzero.symm ▸ hA.isUnit), hzero]
    have hresponse : r + (w i * y i) • x i - (w i * y i) • x i = r := by abel
    simp only [run, hgram, hresp, hdown, hresponse]
    split_ifs with hchoose
    · obtain ⟨hinv, hr, ht⟩ := ih hnodup G hG g hws
      dsimp only
      rw [List.toFinset_cons, gram_update G _ hi, response_update g _ hi]
      simp only [rankOneGram, zero_smul, add_zero, zero_mul] at *
      refine ⟨hinv, hr, ?_⟩
      have hfinal : weightedEstimate G g (insert i s.toFinset) x y
          (Function.update (run x y e A⁻¹ r w s).weights i 0) =
          weightedEstimate G g s.toFinset x y (run x y e A⁻¹ r w s).weights := by
        simp only [weightedEstimate, gram_update G _ hi, response_update g _ hi,
          rankOneGram, zero_smul, zero_mul, add_zero]
      rw [hfinal]
      apply ht.trans
      simpa only [weightedEstimate, ← List.toFinset_cons, hgram, hresp, A, r] using hchoose
    · have hup : change A⁻¹ (x i) 1 = (rankOneGram A (x i) 1)⁻¹ :=
        change_eq A (x i) 1 hA.isUnit (rankOneGram_posDef hA _ (by norm_num)).isUnit
      have hg : (rankOneGram G (x i) 1).PosDef := rankOneGram_posDef hG _ (by norm_num)
      have hnewGram : weightedGram (rankOneGram G (x i) 1) s.toFinset x w =
          rankOneGram A (x i) 1 := by
        simp only [weightedGram, rankOneGram, A]; abel
      have hnewResp : weightedResponse (g + y i • x i) s.toFinset x y w = r + y i • x i := by
        simp only [weightedResponse, r]; abel
      obtain ⟨hinv, hr, ht⟩ := ih hnodup (rankOneGram G (x i) 1) hg (g + y i • x i) hws
      rw [hnewGram, hnewResp] at hinv hr ht
      rw [hup]
      dsimp only
      rw [List.toFinset_cons, gram_update G _ hi, response_update g _ hi]
      simp only [one_mul]
      refine ⟨hinv, hr, ?_⟩
      have hend : e ⬝ᵥ rankOneEstimate A r (x i) (y i) 1 ≤
          e ⬝ᵥ rankOneEstimate A r (x i) (y i) (w i) := by
        obtain ⟨b, hb, hbtarget⟩ := exists_rankOneEstimate_endpoint hA r (x i) e (y i) hwi
        rcases hb with rfl | rfl
        · exact False.elim (hchoose (by simpa [rankOneEstimate, rankOneGram] using hbtarget))
        · exact hbtarget
      have hfinal : weightedEstimate G g (insert i s.toFinset) x y
          (Function.update (run x y e (rankOneGram A (x i) 1)⁻¹ (r + y i • x i) w s).weights i 1) =
          weightedEstimate (rankOneGram G (x i) 1) (g + y i • x i) s.toFinset x y
            (run x y e (rankOneGram A (x i) 1)⁻¹ (r + y i • x i) w s).weights := by
        simp only [weightedEstimate, gram_update G _ hi, response_update g _ hi, one_mul]
      rw [hfinal]
      apply ht.trans
      simpa only [weightedEstimate, hnewGram, hnewResp, rankOneEstimate, one_mul,
        ← List.toFinset_cons, hgram, hresp] using hend

/-- Enumerate fractional coordinates in original observation order, without a
noncomputable conversion from a finite set to a list. -/
@[expose] def fractionalList {n : ℕ} (w : Fin n → K) : List (Fin n) :=
  (List.finRange n).filter fun i => decide (0 < w i ∧ w i < 1)

/-- Initialize a single inverse of the sparse Gram matrix and execute rounding.
The only inverses inside `run` are signed rank-one arithmetic updates. -/
@[expose] def roundSparse {n : ℕ} (x : Fin n → d → K) (y w : Fin n → K) (e : d → K) :
    Result K (Fin n) d :=
  run x y e (inverse (∑ i, w i • vecMulVec (x i) (x i)))
    (∑ i, (w i * y i) • x i) w (fractionalList w)

private theorem fractionalList_finset {n : ℕ} (w : Fin n → ℝ) :
    (fractionalList w).toFinset = Finset.univ.filter (fun i => 0 < w i ∧ w i < 1) := by
  ext i
  simp [fractionalList]

/-- Sparse rounding computes an integral feasible estimate with strict loss below
the dimension, using at most `d` coordinate iterations and `2d` signed updates.
The inverse and response caches are also certified against the final weights. -/
theorem roundSparse_correct {n : ℕ} [Nonempty d] (x : Fin n → d → ℝ)
    (hgp : GeneralPosition x) (y w : Fin n → ℝ) (e : d → ℝ)
    (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1)
    (hsparse : (Finset.univ.filter fun i => 0 < w i ∧ w i < 1).card ≤ Fintype.card d)
    (hmass : 2 * (Fintype.card d : ℝ) ≤ ∑ i, w i) :
    let z := roundSparse x y w e
    (∀ i, z.weights i = 0 ∨ z.weights i = 1) ∧
      e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y z.weights ≤
        e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y w ∧
      (∑ i, w i) - (∑ i, z.weights i) < Fintype.card d ∧
      (weightedGram 0 Finset.univ x z.weights).PosDef ∧
      z.inv = (weightedGram 0 Finset.univ x z.weights)⁻¹ ∧
      z.response = weightedResponse 0 Finset.univ x y z.weights ∧
      z.coordinates ≤ Fintype.card d ∧ z.rankChanges ≤ 2 * Fintype.card d := by
  let J := fractionalList w
  let I := Finset.univ.filter fun i => w i = 1
  let G := ∑ i ∈ I, vecMulVec (x i) (x i)
  let g := ∑ i ∈ I, y i • x i
  have hJ : J.toFinset = Finset.univ.filter (fun i => 0 < w i ∧ w i < 1) :=
    fractionalList_finset w
  have hn : J.Nodup := (List.nodup_finRange n).filter _
  have hlen : J.length ≤ Fintype.card d := by
    rw [← List.toFinset_card_of_nodup hn, hJ]
    exact hsparse
  have hG : G.PosDef := hgp.sparse_backbone x Finset.univ w (fun i _ => hw i) hsparse hmass
  have hgram : weightedGram G J.toFinset x w = weightedGram 0 Finset.univ x w := by
    rw [hJ]
    simpa only [weightedGram, zero_add, G, I] using
      (sum_fractional_split Finset.univ w w (fun i => vecMulVec (x i) (x i))
        (fun i _ => hw i) (fun _ _ _ => rfl)).symm
  have hresp : weightedResponse g J.toFinset x y w = weightedResponse 0 Finset.univ x y w := by
    rw [hJ]
    simpa only [weightedResponse, zero_add, mul_smul, g, I] using
      (sum_fractional_split Finset.univ w w (fun i => y i • x i)
        (fun i _ => hw i) (fun _ _ _ => rfl)).symm
  have hinit : roundSparse x y w e = run x y e (weightedGram G J.toFinset x w)⁻¹
      (weightedResponse g J.toFinset x y w) w J := by
    rw [hgram, hresp]
    simp only [roundSparse, inverse_eq, weightedGram, weightedResponse, zero_add, J]
  let z := roundSparse x y w e
  have hout (i : Fin n) (hi : ¬ (0 < w i ∧ w i < 1)) : z.weights i = w i := by
    rw [show z = _ from hinit]
    apply run_outside
    simp [J, fractionalList, hi]
  have hu (i : Fin n) : z.weights i = 0 ∨ z.weights i = 1 := by
    by_cases hi : 0 < w i ∧ w i < 1
    · rw [show z = _ from hinit]
      exact run_integral _ _ _ _ _ _ _ i (by simp [J, fractionalList, hi])
    · rw [hout i hi]
      rcases eq_or_lt_of_le (hw i).1 with h0 | h0
      · exact Or.inl h0.symm
      · exact Or.inr (by by_contra h1; exact hi ⟨h0, lt_of_le_of_ne (hw i).2 h1⟩)
  obtain ⟨hinv, hr, ht⟩ := run_correct x y w e J hn G hG g (fun i _ => hw i)
  rw [← hinit] at hinv hr ht
  have hfinalGram : weightedGram G J.toFinset x z.weights =
      weightedGram 0 Finset.univ x z.weights := by
    rw [hJ]
    simpa only [weightedGram, zero_add, G, I] using
      (sum_fractional_split Finset.univ w z.weights (fun i => vecMulVec (x i) (x i))
        (fun i _ => hw i) (fun i _ hi => hout i hi)).symm
  have hfinalResp : weightedResponse g J.toFinset x y z.weights =
      weightedResponse 0 Finset.univ x y z.weights := by
    rw [hJ]
    simpa only [weightedResponse, zero_add, mul_smul, g, I] using
      (sum_fractional_split Finset.univ w z.weights (fun i => y i • x i)
        (fun i _ => hw i) (fun i _ hi => hout i hi)).symm
  dsimp only [z] at hfinalGram hfinalResp
  refine ⟨hu, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [weightedEstimate, hgram, hresp, hfinalGram, hfinalResp] using ht
  · have heq : (∑ i, w i) - (∑ i, z.weights i) =
        ∑ i ∈ J.toFinset, (w i - z.weights i) := by
      rw [← Finset.sum_sub_distrib]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      rw [hout i (by simpa [hJ] using hi), sub_self]
    rw [heq]
    have hd : (0 : ℝ) < Fintype.card d := Nat.cast_pos.mpr Fintype.card_pos
    by_cases hne : J.toFinset.Nonempty
    · have hlt : (∑ i ∈ J.toFinset, (w i - z.weights i)) < ∑ _i ∈ J.toFinset, (1 : ℝ) := by
        apply Finset.sum_lt_sum_of_nonempty hne
        intro i hi
        have hwi : w i < 1 := (Finset.mem_filter.mp (hJ ▸ hi)).2.2
        rcases hu i with h | h <;> rw [h] <;> linarith
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hlt
      exact hlt.trans_le (Nat.cast_le.mpr (hJ ▸ hsparse))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      exact hd
  · rw [← hfinalGram]
    exact weightedGram_posDef hG _ x z.weights (fun i _ => by
      rcases hu i with h | h <;> simp [h])
  · simpa only [hfinalGram] using hinv
  · simpa only [hfinalResp] using hr
  · rw [hinit, run_coordinates]
    exact hlen
  · rw [hinit]
    exact (run_rankChanges _ _ _ _ _ _ _).trans (Nat.mul_le_mul_left 2 hlen)

/-- Contract for an external box-constrained linear-programming solver, with a
vertex-returning optimum (simplex or crossover). The contract mentions only
linear equations, box membership, extremality and a linear objective. Sparsity,
least-squares preservation and rounding are derived by the caller. -/
@[expose] def VertexLP {n : ℕ}
    (lp : (Fin n → d → ℝ) → (d → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ (a : Fin n → d → ℝ) (b : d → ℝ),
    (∃ w : Fin n → ℝ, (∀ i, w i ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ i, w i • a i = b) →
    lp a b ∈ ({u : Fin n → ℝ | (∀ i, u i ∈ Set.Icc (0 : ℝ) 1) ∧
      ∑ i, u i • a i = b}).extremePoints ℝ ∧
      ∀ w : Fin n → ℝ, (∀ i, w i ∈ Set.Icc (0 : ℝ) 1) → (∑ i, w i • a i = b) →
        (∑ i, w i) ≤ ∑ i, lp a b i

/-- Construct the residual-normal-equation LP from the actual input weights.
The initial fit is computed by Cramer's rule, not supplied as an assumption. -/
@[expose] def sparsify {n : ℕ}
    (lp : (Fin n → d → K) → (d → K) → (Fin n → K))
    (x : Fin n → d → K) (y w : Fin n → K) : Fin n → K :=
  let b := solve (∑ i, w i • vecMulVec (x i) (x i)) (∑ i, (w i * y i) • x i)
  lp (fun i => (y i - x i ⬝ᵥ b) • x i) 0

/-- Execute one linear-system solve, one external vertex LP, one explicit inverse
initialization, and the signed-update rounding loop. The time components count
these three coarse operations in that order. Scalar arithmetic, comparison,
enumeration and memory costs are not represented by this coarse counter. In
particular it is not a Turing-time or a cubic inversion-time certificate. -/
@[expose] def execute {n : ℕ}
    (lp : (Fin n → d → K) → (d → K) → (Fin n → K))
    (x : Fin n → d → K) (y w : Fin n → K) (e : d → K) :
    TimeM (ℕ × ℕ × ℕ) (Result K (Fin n) d) := do
  TimeM.tick (1, 0, 0)
  let b := solve (∑ i, w i • vecMulVec (x i) (x i)) (∑ i, (w i * y i) • x i)
  TimeM.tick (0, 1, 0)
  let u := lp (fun i => (y i - x i ⬝ᵥ b) • x i) 0
  TimeM.tick (0, 0, 1)
  pure (roundSparse x y u e)

/-- The primitive-call counts follow by composing the executed initialization
stages. The signed-update count is supplied separately by the returned loop. -/
theorem execute_calls {n : ℕ}
    (lp : (Fin n → d → K) → (d → K) → (Fin n → K))
    (x : Fin n → d → K) (y w : Fin n → K) (e : d → K) :
    (execute lp x y w e).time = (1, 1, 1) := rfl

/-- A standard vertex LP suffices to sparsify the computed normal equations.
Neither sparse output nor preservation of the fit is part of the solver contract. -/
theorem sparsify_correct {n : ℕ}
    (lp : (Fin n → d → ℝ) → (d → ℝ) → (Fin n → ℝ)) (hlp : VertexLP lp)
    (x : Fin n → d → ℝ) (hgp : GeneralPosition x) (y w : Fin n → ℝ)
    (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1)
    (hmass : (Fintype.card d : ℝ) - 1 < ∑ i, w i) :
    let u := sparsify lp x y w
    (∀ i, u i ∈ Set.Icc (0 : ℝ) 1) ∧ (∑ i, w i) ≤ ∑ i, u i ∧
      (Finset.univ.filter fun i => 0 < u i ∧ u i < 1).card ≤ Fintype.card d ∧
      weightedEstimate 0 0 Finset.univ x y u = weightedEstimate 0 0 Finset.univ x y w := by
  let b := weightedEstimate 0 0 Finset.univ x y w
  let a := fun i => (y i - x i ⬝ᵥ b) • x i
  have hb : solve (∑ i, w i • vecMulVec (x i) (x i)) (∑ i, (w i * y i) • x i) = b := by
    simp only [solve_eq, b, weightedEstimate, weightedGram, weightedResponse, zero_add]
  have hn : ∑ i, w i • a i = 0 :=
    weightedEstimate_normal x y w (hgp.weightedGram_posDef x w hw hmass)
  obtain ⟨hext, hmax⟩ := hlp a 0 ⟨w, hw, hn⟩
  have hu := hext.1.1
  have hmu := hmax w hw hn
  have hG := hgp.weightedGram_posDef x (lp a 0) hu (hmass.trans_le hmu)
  have hid : sparsify lp x y w = lp a 0 := by simp only [sparsify, hb, a]
  rw [hid]
  refine ⟨hu, hmu, ?_, ?_⟩
  · have hi := linearIndependent_fractional_of_extreme a 0 (lp a 0) hext
    simpa only [Fintype.card_subtype, Finset.card_univ, Module.finrank_pi,
      Module.finrank_self, mul_one] using hi.fintype_card_le_finrank
  · apply hG.mulVec_injective
    rw [weightedEstimate, mulVec_mulVec,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hG.isUnit), one_mulVec]
    have heq : (∑ i, (lp a 0 i * y i) • x i) =
        ∑ i, lp a 0 i • ((x i ⬝ᵥ b) • x i) := by
      simpa only [a, sub_smul, smul_sub, mul_smul, Finset.sum_sub_distrib,
        sub_eq_zero] using hext.1.2
    simpa only [weightedResponse, weightedGram, zero_add, sum_mulVec,
      smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul] using heq

/-- Theorem 3.3's executed rounding endpoint relative to a standard external
vertex LP. Starting with arbitrary feasible weights of mass at least `2d`, the
computed weights are integral and feasible, lose strictly less than `d` mass,
and require at most `d` coordinate iterations and `2d` rank-one kernel calls.
The separately counted initial normal-equation solve is explicit. -/
theorem execute_correct {n : ℕ} [Nonempty d]
    (lp : (Fin n → d → ℝ) → (d → ℝ) → (Fin n → ℝ)) (hlp : VertexLP lp)
    (x : Fin n → d → ℝ) (hgp : GeneralPosition x) (y w : Fin n → ℝ) (e : d → ℝ) (θ : ℝ)
    (hw : Feasible x y e θ w) (hmass : 2 * (Fintype.card d : ℝ) ≤ ∑ i, w i) :
    let z := (execute lp x y w e).ret
    (∀ i, z.weights i = 0 ∨ z.weights i = 1) ∧ Feasible x y e θ z.weights ∧
      (∑ i, w i) - (∑ i, z.weights i) < Fintype.card d ∧
      z.inv = (weightedGram 0 Finset.univ x z.weights)⁻¹ ∧
      z.response = weightedResponse 0 Finset.univ x y z.weights ∧
      z.coordinates ≤ Fintype.card d ∧ z.rankChanges ≤ 2 * Fintype.card d := by
  obtain ⟨hu, hmu, hsparse, hfit⟩ := sparsify_correct lp hlp x hgp y w hw.1 (by
    have hd : (0 : ℝ) < Fintype.card d := Nat.cast_pos.mpr Fintype.card_pos
    linarith)
  obtain ⟨hz, ht, hloss, hG, hinv, hr, hc, hrc⟩ :=
    roundSparse_correct x hgp y (sparsify lp x y w) e hu hsparse (hmass.trans hmu)
  have hexe : (execute lp x y w e).ret = roundSparse x y (sparsify lp x y w) e := rfl
  rw [hexe]
  refine ⟨hz, ⟨?_, hG, ?_⟩, ?_, hinv, hr, hc, hrc⟩
  · intro i
    rcases hz i with h | h <;> simp [h]
  · rw [hfit] at ht
    exact ht.trans hw.2.2
  · linarith

/-- Materialize the retained subset from the computed endpoint weights. This
enumerates the original indices and tests each final weight for equality to one;
that traversal is separate from the coarse LP/solve/inverse call counter. -/
@[expose] def retained {n : ℕ} (z : Result K (Fin n) d) : Finset (Fin n) :=
  Finset.univ.filter fun i => z.weights i = 1

/-- The arithmetic endpoint supplies an actual retained subset, not only an
abstract existence witness. Its cardinality agrees with the retained mass. -/
theorem execute_retained {n : ℕ} [Nonempty d]
    (lp : (Fin n → d → ℝ) → (d → ℝ) → (Fin n → ℝ)) (hlp : VertexLP lp)
    (x : Fin n → d → ℝ) (hgp : GeneralPosition x) (y w : Fin n → ℝ) (e : d → ℝ) (θ : ℝ)
    (hw : Feasible x y e θ w) (hmass : 2 * (Fintype.card d : ℝ) ≤ ∑ i, w i) :
    let z := (execute lp x y w e).ret
    let S := retained z
    Feasible x y e θ (fun i => if i ∈ S then 1 else 0) ∧
      (n : ℝ) - S.card < (n : ℝ) - (∑ i, w i) + Fintype.card d := by
  obtain ⟨hu, hf, hloss, _⟩ := execute_correct lp hlp x hgp y w e θ hw hmass
  let z := (execute lp x y w e).ret
  have hind : (fun i => if i ∈ retained z then (1 : ℝ) else 0) = z.weights := by
    funext i
    rcases hu i with h | h <;> simp [retained, z, h]
  have hsum : (∑ i, z.weights i) = ((retained z).card : ℝ) := by
    rw [← hind]
    simp
  dsimp only
  rw [hind]
  refine ⟨hf, ?_⟩
  change (∑ i, w i) - (∑ i, z.weights i) < _ at hloss
  linarith

end Cslib.LeastSquares.RoundingExecution
