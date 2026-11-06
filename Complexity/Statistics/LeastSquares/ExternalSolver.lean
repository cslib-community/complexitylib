/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.EqualityTarget
public import Cslib.Algorithms.Lean.TimeM
import Mathlib.Tactic

/-!
# Integer brackets from an external fractional decision algorithm

[MoitraRohatgi2023], Definition 1.1, Theorem 1.2 and Appendix A, supplies an
external normal-equation equality-target threshold decision algorithm. Its real
number model is specified in the footnote to Theorem 4.1. It allows nonunique
OLS fits. The solver itself and Renegar's quantifier-elimination algorithm are
external assumptions here, not implemented or asserted by an axiom.

The contract below is at the normal-equation decision level: it does not assume
the local fractional optimum, its ceiling, any integral bracket, or a rounding
conclusion. `EqualityTarget` derives the nonsingular inequality-target bridge.
An executable bounded scan then computes the ceiling and the consecutive-integer
bracket in [XuGaoHu2027], Corollary 3.4(iii). It needs threshold decisions only;
it does not claim an algorithm returning an arbitrary exact real optimum.

The time hypothesis is in the external solver's exact-real arithmetic model,
with constants uniform in the number of observations for each fixed dimension.
There is no bit-complexity claim independent of input/output representation.
-/

public section

namespace Cslib.LeastSquares.ExternalSolver

open Matrix Algorithms.Lean

/-- Scan thresholds in increasing order, stopping after the first true answer.
If none of `0,...,cap` succeeds, return the sentinel `cap+1`. Each loop comparison
and result construction is charged one additional operation. -/
@[expose] def search (q : ℕ → TimeM ℕ Bool) : ℕ → TimeM ℕ ℕ
  | 0 => do
    let b ← q 0
    TimeM.tick 1
    pure (if b then 0 else 1)
  | cap + 1 => do
    let k ← search q cap
    TimeM.tick 1
    if k ≤ cap then pure k
    else
      let b ← q (cap + 1)
      pure (if b then cap + 1 else cap + 2)

/-- Correctness of the actual scan for any threshold oracle. -/
theorem search_correct (q : ℕ → TimeM ℕ Bool) (m cap : ℕ)
    (hq : ∀ k ≤ cap, (q k).ret = true ↔ m ≤ k) :
    (search q cap).ret = min m (cap + 1) := by
  induction cap with
  | zero =>
    simp only [search, TimeM.ret_bind, TimeM.ret_pure]
    split_ifs with h
    · have hm := (hq 0 (by omega)).mp h
      have hm0 : m = 0 := by omega
      simp [hm0]
    · have hm : ¬ m ≤ 0 := fun hh => h ((hq 0 (by omega)).mpr hh)
      omega
  | succ cap ih =>
    have hi := ih (fun k hk => hq k (by omega))
    have hb := hq (cap + 1) (by omega)
    simp only [search, TimeM.ret_bind, hi]
    split
    · simp only [TimeM.ret_pure]; omega
    · simp only [TimeM.ret_bind, TimeM.ret_pure]
      split <;> simp_all only [Bool.false_eq_true, false_iff, true_iff, not_le]
      all_goals omega

/-- The scan makes at most `cap+1` solver calls, with their supplied time bound.
The formula is proved from the early-stopping recursion. -/
theorem search_time (q : ℕ → TimeM ℕ Bool) (cap B : ℕ)
    (hq : ∀ k ≤ cap, (q k).time ≤ B) :
    (search q cap).time ≤ (cap + 1) * (B + 1) := by
  induction cap with
  | zero =>
    simp only [search, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
    have := hq 0 (by omega)
    omega
  | succ cap ih =>
    have hi := ih (fun k hk => hq k (by omega))
    have hb := hq (cap + 1) (by omega)
    simp only [search, TimeM.time_bind, TimeM.time_tick]
    split <;> simp only [TimeM.time_bind, TimeM.time_pure] <;> nlinarith

variable {n d : ℕ}

/-- Exact external decision contract. For the zero target in a specified
coordinate this is precisely the normal-equation formulation of the fractional
problem in Moitra–Rohatgi. Relabeling coordinates permits any specified `j`.
The cost of this solver remains an explicit external assumption. -/
@[expose] def NormalOracle (q : ℕ → TimeM ℕ Bool)
    (x : Fin n → Fin (d + 1) → ℝ) (y : Fin n → ℝ) (j : Fin (d + 1)) : Prop :=
  ∀ k : ℕ, (q k).ret = true ↔
    EqualityNormalDecision x y (Pi.single j 1) 0 k

/-- Compute the start of the integral bracket using an external equality-target
decision procedure. All queried thresholds have retained mass at least `d+1`;
singular solutions admitted by that procedure cannot cause a false answer. -/
theorem bracket_start (q : ℕ → TimeM ℕ Bool)
    (x : Fin n → Fin (d + 1) → ℝ) (hgp : GeneralPosition x) (y w : Fin n → ℝ)
    (j : Fin (d + 1)) (hq : NormalOracle q x y j)
    (hw : Feasible x y (Pi.single j 1) 0 w)
    (hmass : 2 * ((d + 1 : ℕ) : ℝ) ≤ ∑ i, w i)
    (hfull : 0 < (Pi.single j 1) ⬝ᵥ weightedEstimate 0 0 Finset.univ x y (fun _ => 1)) :
    (search q (n - (d + 1))).ret = ⌈fractionalStability x y (Pi.single j 1) 0⌉₊ := by
  have hsum : (∑ i, w i) ≤ n := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (g := fun _ => (1 : ℝ)) (fun i _ => (hw.1 i).2)
  have hdn : d + 1 ≤ n := by exact_mod_cast (show ((d + 1 : ℕ) : ℝ) ≤ n by linarith)
  have hmass' : (Fintype.card (Fin (d + 1)) : ℝ) - 1 < ∑ i, w i := by
    simp only [Fintype.card_fin]
    have : (0 : ℝ) < (d + 1 : ℕ) := by positivity
    linarith
  have hbound : ⌈fractionalStability x y (Pi.single j 1) 0⌉₊ ≤ n - (d + 1) := by
    apply Nat.ceil_le.mpr
    have hle := fractionalStability_le x y (Pi.single j 1) 0 w hw
    simp only [Fintype.card_fin, Nat.cast_sub hdn] at *
    linarith
  rw [search_correct q _ _ (fun k hk => ?_), Nat.min_eq_left (by omega :
    ⌈fractionalStability x y (Pi.single j 1) 0⌉₊ ≤ n - (d + 1) + 1)]
  rw [hq k, equalityNormalDecision_iff x hgp y (Pi.single j 1) 0 w hw hmass' hfull]
  · exact Nat.ceil_le.symm
  · have hcast : (k : ℝ) ≤ (n - (d + 1) : ℕ) := Nat.cast_le.mpr hk
    simpa only [Fintype.card_fin, Nat.cast_sub hdn] using hcast

/-- The returned integer and its next `d` successors contain integral stability.
This is a derived consequence of normal-equation decisions, not an oracle
contract for the desired interval. -/
theorem integral_bracket (q : ℕ → TimeM ℕ Bool)
    (x : Fin n → Fin (d + 1) → ℝ) (hgp : GeneralPosition x) (y w : Fin n → ℝ)
    (j : Fin (d + 1)) (hq : NormalOracle q x y j)
    (hw : Feasible x y (Pi.single j 1) 0 w)
    (hmass : 2 * ((d + 1 : ℕ) : ℝ) ≤ ∑ i, w i)
    (hfull : 0 < (Pi.single j 1) ⬝ᵥ weightedEstimate 0 0 Finset.univ x y (fun _ => 1)) :
    (search q (n - (d + 1))).ret ≤ integralStability x y (Pi.single j 1) 0 ∧
      integralStability x y (Pi.single j 1) 0 ≤ (search q (n - (d + 1))).ret + d := by
  rw [bracket_start q x hgp y w j hq hw hmass hfull]
  obtain ⟨hlo, hhi⟩ :=
    stability_ceiling_bounds x hgp y (Pi.single j 1) 0 w hw (by simpa using hmass)
  simp only [Fintype.card_fin] at hhi
  exact ⟨hlo, by omega⟩

/-- Composition preserves the advertised fixed-dimension polynomial exponent.
The external decision solver has cost at most `C*n^(c*(d+1)^3)`; the actual scan
has cost at most `2*(C+1)*n^((c+1)*(d+1)^3)`. Constants are uniform in `n`.
This is conditional on the cited external solver's real-arithmetic cost, and
does not certify that solver, exact-real output, or rational bit complexity. -/
theorem bracket_time (q : ℕ → TimeM ℕ Bool) (hn : 0 < n) (C c : ℕ)
    (hq : ∀ k ≤ n - (d + 1), (q k).time ≤ C * n ^ (c * (d + 1) ^ 3)) :
    (search q (n - (d + 1))).time ≤ 2 * (C + 1) * n ^ ((c + 1) * (d + 1) ^ 3) := by
  have ht := search_time q (n - (d + 1)) (C * n ^ (c * (d + 1) ^ 3)) hq
  have hp : 1 ≤ n ^ (c * (d + 1) ^ 3) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have he : c * (d + 1) ^ 3 + 1 ≤ (c + 1) * (d + 1) ^ 3 := by
    have : 1 ≤ (d + 1) ^ 3 := by
      have h : 0 < (d + 1) ^ 3 := by positivity
      omega
    nlinarith
  calc
    _ ≤ (n - (d + 1) + 1) * (C * n ^ (c * (d + 1) ^ 3) + 1) := ht
    _ ≤ (2 * n) * ((C + 1) * n ^ (c * (d + 1) ^ 3)) :=
      Nat.mul_le_mul (by omega) (by nlinarith)
    _ = 2 * (C + 1) * n ^ (c * (d + 1) ^ 3 + 1) := by rw [pow_succ]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn he)

end Cslib.LeastSquares.ExternalSolver
