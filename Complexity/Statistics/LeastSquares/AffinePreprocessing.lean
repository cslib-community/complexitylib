/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.AffineTarget
import Mathlib.Tactic

/-!
# Arithmetic execution of the affine-target adapter

The programs materialize every transformed row and response as lists, over any
field. Each scalar division, multiplication, subtraction or zero comparison
costs one; list termination and each output cons cost one. Vector reads,
finite-index views, binding, pairs and option construction are free, as in a
random-access exact-real arithmetic model. The counters follow the actual
loops and branches; no dense matrix multiplication is performed. The model
is not a native Lean runtime or a binary rational complexity certificate.

The supplied pivot can be found by `pivot`, which tests at most the dimension
many entries. `preprocess` then uses at most `n * (4 * D + 5) + 1` operations.
For positive `n,D`, the combined bound is `12 * n * D`. Real instantiation is
semantic because Lean reals are noncomputable; rational instantiation executes.

## Main definitions

* `pivot`: executed search for a nonzero target coordinate.
* `preprocess`: materialization of every transformed design row and response.
* `solve`: preprocessing followed by the external zero-coefficient decision scan.

## Main results

* `preprocess_real_ret`: agreement between the output table and the semantic change.
* `preprocessing_linear`: derived linear arithmetic preprocessing bound.
* `solve_correct`: the computed ceiling for an arbitrary affine target.
* `solve_integral_bracket`: the actual output's integral stability bracket.
* `solve_time`: the composed cost including preprocessing.
-/

public section

namespace Cslib.LeastSquares.AffineTarget

open Algorithms.Lean Matrix

variable {K : Type*} [Field K]

/-- Scalar real-arithmetic primitives, each charged once. -/
@[expose] def divide (a b : K) : TimeM ℕ K := ⟨a / b, 1⟩

/-- Scalar multiplication in the arithmetic model. -/
@[expose] def multiply (a b : K) : TimeM ℕ K := ⟨a * b, 1⟩

/-- Scalar subtraction in the arithmetic model. -/
@[expose] def subtract (a b : K) : TimeM ℕ K := ⟨a - b, 1⟩

/-- Scan coordinates for a nonzero target entry; no chosen pivot is assumed. -/
@[expose] def pivot [DecidableEq K] : {D : ℕ} → (Fin D → K) → TimeM ℕ (Option (Fin D))
  | 0, _ => do
    TimeM.tick 1
    pure none
  | D + 1, e => do
    TimeM.tick 1
    if e 0 ≠ 0 then pure (some 0)
    else
      let j ← pivot (fun i : Fin D => e i.succ)
      pure (j.map Fin.succ)

theorem pivot_time [DecidableEq K] {D : ℕ} (e : Fin D → K) : (pivot e).time ≤ D + 1 := by
  induction D with
  | zero => simp [pivot]
  | succ D ih =>
    simp only [pivot, TimeM.time_bind, TimeM.time_tick]
    split
    · simp only [TimeM.time_pure]; omega
    · simp only [TimeM.time_bind, TimeM.time_pure, add_zero]
      have := ih (fun i : Fin D => e i.succ)
      omega

theorem pivot_correct [DecidableEq K] {D : ℕ} (e : Fin D → K) :
    (∀ j, (pivot e).ret = some j → e j ≠ 0) ∧
      ((pivot e).ret = none ↔ ∀ j, e j = 0) := by
  induction D with
  | zero => simp [pivot]
  | succ D ih =>
    simp only [pivot, TimeM.ret_bind]
    split_ifs with h
    · simp only [TimeM.ret_pure]
      constructor
      · intro j hj; cases hj; exact h
      · simp only [reduceCtorEq, false_iff, not_forall]
        exact ⟨0, h⟩
    · simp only [TimeM.ret_bind, TimeM.ret_pure]
      obtain ⟨hgood, hnone⟩ := ih (fun i : Fin D => e i.succ)
      constructor
      · intro j hj
        obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hj
        exact hgood k hk
      · rw [Option.map_eq_none_iff, hnone]
        constructor
        · intro ht j; exact Fin.cases (not_ne_iff.mp h) ht j
        · intro ht j; exact ht j.succ

private def tabulate {α : Type*} : {N : ℕ} → (Fin N → TimeM ℕ α) → TimeM ℕ (List α)
  | 0, _ => do
    TimeM.tick 1
    pure []
  | N + 1, f => do
    let a ← f 0
    let as ← tabulate (fun i : Fin N => f i.succ)
    TimeM.tick 1
    pure (a :: as)

private theorem tabulate_ret {α : Type*} {N : ℕ} (f : Fin N → TimeM ℕ α) :
    (tabulate f).ret = List.ofFn (fun i => (f i).ret) := by
  induction N with
  | zero => simp [tabulate]
  | succ N ih => simp [tabulate, List.ofFn_succ, ih]

private theorem tabulate_time {α : Type*} {N : ℕ} (f : Fin N → TimeM ℕ α) (B : ℕ)
    (h : ∀ i, (f i).time ≤ B) : (tabulate f).time ≤ N * (B + 1) + 1 := by
  induction N with
  | zero => simp [tabulate]
  | succ N ih =>
    have ht := ih (fun i : Fin N => f i.succ) (fun i => h i.succ)
    have h0 := h 0
    simp only [tabulate, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
    nlinarith

/-- Materialize one transformed row and its response. The pivot quotient is
computed once, then reused in all coordinates and the response. -/
def preprocessRow {D : ℕ} (e : Fin D → K) (j : Fin D) (θ : K)
    (a : Fin D → K) (b : K) : TimeM ℕ (List K × K) := do
  let r ← divide (a j) (e j)
  let a' ← tabulate fun l : Fin D => do
    TimeM.tick 1
    if l = j then pure r
    else
      let t ← multiply (e l) r
      subtract (a l) t
  let t ← multiply θ r
  let b' ← subtract b t
  pure (a', b')

/-- Every output coordinate is the sparse affine design formula. -/
theorem preprocessRow_ret {D : ℕ} (e : Fin D → K) (j : Fin D) (θ : K)
    (a : Fin D → K) (b : K) :
    (preprocessRow e j θ a b).ret =
      (List.ofFn (fun l => if l = j then a j / e j else a l - e l * (a j / e j)),
        b - θ * (a j / e j)) := by
  simp only [preprocessRow, TimeM.ret_bind, divide, multiply, subtract, tabulate_ret,
    TimeM.ret_pure]
  congr 2
  funext l
  split <;> rfl

theorem preprocessRow_time {D : ℕ} (e : Fin D → K) (j : Fin D) (θ : K)
    (a : Fin D → K) (b : K) :
    (preprocessRow e j θ a b).time ≤ 4 * D + 4 := by
  have ht := tabulate_time (fun l : Fin D => do
    TimeM.tick 1
    if l = j then pure (a j / e j)
    else do
      let t ← multiply (e l) (a j / e j)
      subtract (a l) t) 3 (by intro l; split <;> simp [TimeM.time_bind, multiply, subtract])
  simp only [preprocessRow, TimeM.time_bind, divide, multiply, subtract, TimeM.time_pure]
  simp only [multiply, subtract] at ht
  omega

/-- Materialize the complete transformed dataset in original row order. -/
def preprocess {n D : ℕ} (e : Fin D → K) (j : Fin D) (θ : K)
    (x : Fin n → Fin D → K) (y : Fin n → K) : TimeM ℕ (List (List K × K)) :=
  tabulate (fun i => preprocessRow e j θ (x i) (y i))

theorem preprocess_ret {n D : ℕ} (e : Fin D → K) (j : Fin D) (θ : K)
    (x : Fin n → Fin D → K) (y : Fin n → K) :
    (preprocess e j θ x y).ret = List.ofFn (fun i =>
      (List.ofFn (fun l => if l = j then x i j / e j else x i l - e l * (x i j / e j)),
        y i - θ * (x i j / e j))) := by
  simp only [preprocess, tabulate_ret, preprocessRow_ret]

theorem preprocess_time {n D : ℕ} (e : Fin D → K) (j : Fin D) (θ : K)
    (x : Fin n → Fin D → K) (y : Fin n → K) :
    (preprocess e j θ x y).time ≤ n * (4 * D + 5) + 1 :=
  tabulate_time _ _ (fun i => preprocessRow_time e j θ (x i) (y i))

/-- Pivot selection plus actual materialization is linear in the input table size. -/
theorem preprocessing_linear [DecidableEq K] {n D : ℕ} (hn : 0 < n) (hD : 0 < D)
    (e : Fin D → K) (j : Fin D) (θ : K) (x : Fin n → Fin D → K) (y : Fin n → K) :
    (pivot e).time + (preprocess e j θ x y).time ≤ 12 * n * D := by
  have hp := pivot_time e
  have ht := preprocess_time e j θ x y
  have hnD : D ≤ n * D := Nat.le_mul_of_pos_left D hn
  have hDn : n ≤ n * D := Nat.le_mul_of_pos_right n hD
  nlinarith

/-- The executed real output is exactly the semantic change proved in `AffineTarget`. -/
theorem preprocess_real_ret {n D : ℕ} (e : Fin D → ℝ) (j : Fin D) (hj : e j ≠ 0)
    (θ : ℝ) (x : Fin n → Fin D → ℝ) (y : Fin n → ℝ) :
    (preprocess e j θ x y).ret =
      List.ofFn (fun i => (List.ofFn (row e j (x i)), response e j θ x y i)) := by
  rw [preprocess_ret]
  congr 1
  funext i
  congr 1
  apply congrArg List.ofFn
  funext l
  by_cases h : l = j
  · subst l
    simp [row, hj]
  · simp [row, h, mul_comm]

/-- Select a pivot, materialize the changed data, and run the external decision
scan on that actual output. The zero-vector branch returns `none`. -/
noncomputable def solve {n D : ℕ}
    (solver : Fin (D + 1) → List (List ℝ × ℝ) → ℕ → TimeM ℕ Bool)
    (e : Fin (D + 1) → ℝ) (θ : ℝ)
    (x : Fin n → Fin (D + 1) → ℝ) (y : Fin n → ℝ) : TimeM ℕ (Option ℕ) := do
  let j ← pivot e
  match j with
  | none => pure none
  | some j =>
    let data ← preprocess e j θ x y
    let k ← ExternalSolver.search (solver j data) (n - (D + 1))
    pure (some k)

/-- Correctness of preprocessing followed by the external zero-coefficient solver.
Only normal-equation decisions on the changed data are assumed of the solver. -/
theorem solve_correct {n D : ℕ}
    (solver : Fin (D + 1) → List (List ℝ × ℝ) → ℕ → TimeM ℕ Bool)
    (e : Fin (D + 1) → ℝ) (θ : ℝ)
    (x : Fin n → Fin (D + 1) → ℝ) (hgp : GeneralPosition x) (y w : Fin n → ℝ)
    (hs : ∀ j, e j ≠ 0 → ExternalSolver.NormalOracle
      (solver j (List.ofFn (fun i =>
        (List.ofFn (row e j (x i)), response e j θ x y i))))
      (fun i => row e j (x i)) (response e j θ x y) j)
    (hw : Feasible x y e θ w) (hmass : 2 * ((D + 1 : ℕ) : ℝ) ≤ ∑ i, w i)
    (hfull : θ < e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y (fun _ => 1)) :
    (solve solver e θ x y).ret = some ⌈fractionalStability x y e θ⌉₊ := by
  obtain ⟨j, hj⟩ := exists_pivot e θ x y w hw hfull
  have hp : (pivot e).ret ≠ none := by
    intro h
    exact hj ((pivot_correct e).2.mp h j)
  obtain ⟨j, hpj⟩ := Option.ne_none_iff_exists'.mp hp
  have hj := (pivot_correct e).1 j hpj
  simp only [solve, TimeM.ret_bind, hpj, preprocess_real_ret e j hj]
  rw [bracket_start _ x hgp y w e j hj θ (hs j hj) hw hmass hfull]
  rfl

/-- The complete executed adapter returns a dimension-many integral bracket. -/
theorem solve_integral_bracket {n D : ℕ}
    (solver : Fin (D + 1) → List (List ℝ × ℝ) → ℕ → TimeM ℕ Bool)
    (e : Fin (D + 1) → ℝ) (θ : ℝ)
    (x : Fin n → Fin (D + 1) → ℝ) (hgp : GeneralPosition x) (y w : Fin n → ℝ)
    (hs : ∀ j, e j ≠ 0 → ExternalSolver.NormalOracle
      (solver j (List.ofFn (fun i =>
        (List.ofFn (row e j (x i)), response e j θ x y i))))
      (fun i => row e j (x i)) (response e j θ x y) j)
    (hw : Feasible x y e θ w) (hmass : 2 * ((D + 1 : ℕ) : ℝ) ≤ ∑ i, w i)
    (hfull : θ < e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y (fun _ => 1)) :
    ∃ k, (solve solver e θ x y).ret = some k ∧ k ≤ integralStability x y e θ ∧
      integralStability x y e θ ≤ k + D := by
  refine ⟨_, solve_correct solver e θ x hgp y w hs hw hmass hfull, ?_⟩
  obtain ⟨hlo, hhi⟩ := stability_ceiling_bounds x hgp y e θ w hw (by simpa using hmass)
  simp only [Fintype.card_fin] at hhi
  exact ⟨hlo, by omega⟩

/-- Explicit end-to-end cost, including pivot search and table output. For fixed
`D`, preprocessing adds only linear cost to the external polynomial scan bound. -/
theorem solve_time {n D : ℕ} (hn : 0 < n)
    (solver : Fin (D + 1) → List (List ℝ × ℝ) → ℕ → TimeM ℕ Bool)
    (e : Fin (D + 1) → ℝ) (θ : ℝ)
    (x : Fin n → Fin (D + 1) → ℝ) (y : Fin n → ℝ) (C c : ℕ)
    (hs : ∀ j, ∀ k ≤ n - (D + 1),
      (solver j (preprocess e j θ x y).ret k).time ≤ C * n ^ (c * (D + 1) ^ 3)) :
    (solve solver e θ x y).time ≤
      12 * n * (D + 1) + 2 * (C + 1) * n ^ ((c + 1) * (D + 1) ^ 3) := by
  simp only [solve, TimeM.time_bind]
  split
  · simp only [TimeM.time_pure]
    have := pivot_time e
    have hmul : D + 1 ≤ n * (D + 1) := Nat.le_mul_of_pos_left _ hn
    have hpos : 0 < n * (D + 1) := by positivity
    rw [Nat.mul_assoc]
    omega
  · rename_i j _
    simp only [TimeM.time_bind, TimeM.time_pure, add_zero]
    have hp := preprocessing_linear hn (by omega : 0 < D + 1) e j θ x y
    have ht := ExternalSolver.bracket_time (solver j (preprocess e j θ x y).ret) hn C c (hs j)
    omega

end Cslib.LeastSquares.AffineTarget
