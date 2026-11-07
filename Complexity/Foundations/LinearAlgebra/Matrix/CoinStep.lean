/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Transition matrices of coin-driven maps

A map `next : α → Bool → α` moves a state to one of two successors, selected by a coin. On a finite
set `s` of states closed under `next`, its *count matrix* `Matrix.coinStepMatrix next s` has as
entry `(x, y)` the number of coins that move `x` to `y`. Its powers count coin strings
(`Matrix.coinStepMatrix_pow_mulVec`): `(N ^ t *ᵥ f) x` is the sum of `f` over the endpoints of
the `2 ^ t` coin strings of length `t` replayed from `x`. Halving the entries gives the stochastic
matrix of the fair-coin random walk.

Keeping only the rows of the *live* states gives `Matrix.liveCoinStepMatrix live next s`, which
counts coin strings along which every state before the last is live
(`Matrix.liveCoinStepMatrix_pow_mulVec`). When the other states are fixed by `next`, the walk
stops at the first state that is not live, and every coin string is counted by the time it stops
(`Matrix.coinStepMatrix_pow_mulVec_eq_sum`). When the live walks have bounded length, the live
matrix is nilpotent, and `1 - S` has the inverse `∑ i < n, S ^ i`
(`Matrix.inv_one_sub_eq_sum_pow`).

## Main definitions

* `Matrix.coinStepMatrix`: the count matrix of a coin-driven map on a finite set.
* `Matrix.liveCoinStepMatrix`: its rows at live states, zero rows elsewhere.

## Main results

* `Matrix.coinStepMatrix_pow_mulVec`: powers sum over coin strings.
* `Matrix.liveCoinStepMatrix_pow_mulVec`: powers of the live matrix sum over live coin strings.
* `Matrix.coinStepMatrix_pow_mulVec_eq_sum`: first-stop decomposition of the count matrix.
* `Matrix.liveCoinStepMatrix_pow_eq_zero`: bounded live walks make the live matrix nilpotent.
* `Matrix.inv_one_sub_eq_sum_pow`: the inverse of `1 - S` for nilpotent `S`.
-/

@[expose] public section

namespace Matrix

variable {α R : Type*} [DecidableEq α]

section Semiring

variable [CommSemiring R] (next : α → Bool → α) (s : Finset α)

/-- **The count matrix of a coin-driven map** on a finite set `s`: the entry at `(x, y)` is the
number of coins `b` with `next x b = y`. -/
def coinStepMatrix : Matrix s s R :=
  fun x y => ∑ b : Bool, if next x b = y then 1 else 0

variable (live : α → Prop) [DecidablePred live]

/-- **The live count matrix**: the rows of `Matrix.coinStepMatrix` at states satisfying `live`,
and zero rows at the other states. -/
def liveCoinStepMatrix : Matrix s s R :=
  fun x y => if live x then coinStepMatrix next s x y else 0

variable {next s live}

/-- A row of the count matrix, applied to a vector, sums the two coin successors. -/
theorem coinStepMatrix_mulVec (hs : ∀ x ∈ s, ∀ b, next x b ∈ s) (g : s → R) (x : s) :
    (coinStepMatrix next s *ᵥ g) x = ∑ b : Bool, g ⟨next x b, hs x x.2 b⟩ := by
  simp only [mulVec, dotProduct, coinStepMatrix, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single ⟨next x b, hs x x.2 b⟩]
  · simp
  · intro y _ hy
    simp only [show ¬ next x b = y from fun h => hy (Subtype.ext h.symm), ↓reduceIte]
  · simp

/-- A row of the live count matrix sums the two coin successors at a live state and vanishes
elsewhere. -/
theorem liveCoinStepMatrix_mulVec (hs : ∀ x ∈ s, ∀ b, next x b ∈ s) (g : s → R) (x : s) :
    (liveCoinStepMatrix next s live *ᵥ g) x =
      if live x then ∑ b : Bool, g ⟨next x b, hs x x.2 b⟩ else 0 := by
  rw [← coinStepMatrix_mulVec hs]
  simp only [mulVec, dotProduct, liveCoinStepMatrix]
  split_ifs <;> simp

/-- Sums over the coin strings of length `t + 1` split off the first coin. -/
private theorem sum_fin_succ_bool {M : Type*} [AddCommMonoid M] (t : ℕ)
    (g : (Fin (t + 1) → Bool) → M) :
    ∑ w : Fin (t + 1) → Bool, g w = ∑ b : Bool, ∑ w : Fin t → Bool, g (Fin.cons b w) := by
  rw [← Fintype.sum_prod_type', ← (Fin.consEquiv fun _ => Bool).sum_comp]
  rfl

/-- **Powers of the count matrix sum over coin strings**: `(N ^ t *ᵥ f) x` is the sum of `f` over
the states reached from `x` by the `2 ^ t` coin strings of length `t`. -/
theorem coinStepMatrix_pow_mulVec (hs : ∀ x ∈ s, ∀ b, next x b ∈ s) (f : α → R) (t : ℕ)
    (x : s) : (coinStepMatrix next s ^ t *ᵥ fun y : s => f y) x =
      ∑ w : Fin t → Bool, f ((List.ofFn w).foldl next x) := by
  induction t generalizing f x with
  | zero => simp
  | succ t ih =>
    have hfun : (coinStepMatrix next s ^ t *ᵥ fun y : s => f y) =
        fun y : s => ∑ w : Fin t → Bool, f ((List.ofFn w).foldl next y) := funext fun y => ih f y
    rw [pow_succ', ← mulVec_mulVec, hfun, coinStepMatrix_mulVec hs, sum_fin_succ_bool]
    simp [List.ofFn_succ]

/-- **Powers of the live count matrix sum over live coin strings**: `(S ^ t *ᵥ f) x` is the sum
of `f` over the states reached from `x` by those coin strings of length `t` along which every
state before the last is live. -/
theorem liveCoinStepMatrix_pow_mulVec (hs : ∀ x ∈ s, ∀ b, next x b ∈ s) (f : α → R) (t : ℕ)
    (x : s) : (liveCoinStepMatrix next s live ^ t *ᵥ fun y : s => f y) x =
      ∑ w : Fin t → Bool, if ∀ i : Fin t, live (((List.ofFn w).take i).foldl next x) then
        f ((List.ofFn w).foldl next x) else 0 := by
  classical
  induction t generalizing f x with
  | zero => simp
  | succ t ih =>
    have hfun : (liveCoinStepMatrix next s live ^ t *ᵥ fun y : s => f y) =
        fun y : s => ∑ w : Fin t → Bool, if ∀ i : Fin t,
          live (((List.ofFn w).take i).foldl next y) then f ((List.ofFn w).foldl next y) else 0 :=
      funext fun y => ih f y
    rw [pow_succ', ← mulVec_mulVec, hfun, liveCoinStepMatrix_mulVec hs, sum_fin_succ_bool]
    have hlive (b : Bool) (w : Fin t → Bool) :
        (∀ i : Fin (t + 1), live (((List.ofFn (Fin.cons b w : Fin (t + 1) → Bool)).take i).foldl
          next x)) ↔ live x ∧ ∀ i : Fin t, live (((List.ofFn w).take i).foldl next (next x b)) := by
      rw [Fin.forall_fin_succ]
      simp [List.ofFn_succ]
    split_ifs with hx
    · refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun w _ => ?_
      simp only [hlive, hx, true_and]
      simp [List.ofFn_succ]
    · refine (Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun w _ => ?_).symm
      rw [ite_eq_right_iff, hlive]
      exact fun h => absurd h.1 hx

/-- **First-stop decomposition.** If the states that are not live are fixed by `next`, and `f`
vanishes at live states, then counting the coin strings of length `T` by `f` at their endpoint
is the same as counting, for each `t ≤ T`, the live coin strings of length `t` by `f`, each
weighted by the `2 ^ (T - t)` continuations after the walk has stopped. -/
theorem coinStepMatrix_pow_mulVec_eq_sum (hs : ∀ x ∈ s, ∀ b, next x b ∈ s)
    (hfix : ∀ x, ¬ live x → ∀ b, next x b = x) {f : α → R} (hf : ∀ x, live x → f x = 0)
    (T : ℕ) (x : s) : (coinStepMatrix next s ^ T *ᵥ fun y : s => f y) x =
      ∑ t ∈ Finset.range (T + 1),
        2 ^ (T - t) * (liveCoinStepMatrix next s live ^ t *ᵥ fun y : s => f y) x := by
  induction T generalizing x with
  | zero => simp
  | succ T ih =>
    rw [pow_succ', ← mulVec_mulVec, coinStepMatrix_mulVec hs]
    by_cases hx : live x
    · rw [Finset.sum_range_succ', pow_zero, one_mulVec]
      simp only [hf x hx, mul_zero, add_zero]
      have hrow (t : ℕ) : (liveCoinStepMatrix next s live ^ (t + 1) *ᵥ fun y : s => f y) x =
          ∑ b : Bool, (liveCoinStepMatrix next s live ^ t *ᵥ fun y : s => f y)
            ⟨next x b, hs x x.2 b⟩ := by
        rw [pow_succ', ← mulVec_mulVec, liveCoinStepMatrix_mulVec hs]
        simp only [hx, ↓reduceIte]
      simp only [hrow, Finset.mul_sum, Nat.add_sub_add_right]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => ih ⟨next x b, hs x x.2 b⟩
    · have hnext (b : Bool) : (⟨next x b, hs x x.2 b⟩ : s) = x := Subtype.ext (hfix x hx b)
      have hzero (t : ℕ) :
          (liveCoinStepMatrix next s live ^ (t + 1) *ᵥ fun y : s => f y) x = 0 := by
        rw [pow_succ', ← mulVec_mulVec, liveCoinStepMatrix_mulVec hs]
        simp only [hx, ↓reduceIte]
      simp only [hnext]
      rw [Fintype.sum_bool, ih x, Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [hzero, mul_zero, Finset.sum_const_zero, zero_add, pow_zero, one_mulVec,
        Nat.sub_zero]
      ring

/-- **Bounded live walks make the live matrix nilpotent**: if along every coin string of length
`n` from a state of `s` some state before the last is not live, then `S ^ n = 0`. -/
theorem liveCoinStepMatrix_pow_eq_zero (hs : ∀ x ∈ s, ∀ b, next x b ∈ s) {n : ℕ}
    (h : ∀ x ∈ s, ∀ w : Fin n → Bool, ∃ i : Fin n,
      ¬ live (((List.ofFn w).take i).foldl next x)) :
    (liveCoinStepMatrix next s live : Matrix s s R) ^ n = 0 := by
  ext x y
  have hcol := liveCoinStepMatrix_pow_mulVec (R := R) (live := live) hs
    (fun z => if z = y then 1 else 0) n x
  have hvec : (fun z : s => if (z : α) = y then (1 : R) else 0) = Pi.single y 1 := by
    funext z
    simp only [Pi.single_apply, Subtype.ext_iff]
  rw [hvec, mulVec_single_one, Finset.sum_eq_zero fun w _ => ?_] at hcol
  · simpa using hcol
  · obtain ⟨i, hi⟩ := h x x.2 w
    exact ite_eq_right_iff.mpr fun hall => absurd (hall i) hi

end Semiring

/-- **Inverse of `1 - S` for nilpotent `S`**: if `S ^ n = 0`, then `1 - S` is invertible with
inverse the truncated geometric series `∑ i < n, S ^ i`. -/
theorem inv_one_sub_eq_sum_pow {ι : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {S : Matrix ι ι R} {n : ℕ} (h : S ^ n = 0) :
    (1 - S)⁻¹ = ∑ i ∈ Finset.range n, S ^ i :=
  inv_eq_right_inv (by rw [mul_neg_geom_sum, h, sub_zero])

end Matrix
