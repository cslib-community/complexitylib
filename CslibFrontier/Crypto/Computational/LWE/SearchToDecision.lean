/-
Copyright (c) 2026 Samuel Schlesinger, real-roots. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, real-roots
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Uniform
public import CslibFrontier.Crypto.Computational.LWE.PrimeModulus
public import CslibFrontier.Crypto.Game.Hybrid

public import Mathlib.Algebra.Field.ZMod
public import CslibFrontier.Languages.Probabilistic.Basic
public import CslibFrontier.Languages.Probabilistic.Repeat
public import CslibFrontier.Languages.Probabilistic.Concentration

/-!
# Search to Decision LWE

Regev's search-to-decision reduction for prime moduli.

## References

* [O. Regev, *On lattices, learning with errors, random linear codes, and cryptography*][Regev2009]
-/

public section

namespace Cslib.Crypto.PrimeLWE

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix NNReal

/-- Shift the `j`-th coordinate of the public matrix by adding a random vector `r` to the `j`-th
column of `A`, and adding `g * r` to the `0`-th column `b`. -/
def shiftCoordinate {n m q : ℕ} [Fact (Nat.Prime q)]
    (P : Matrix (Fin m) (Fin (n + 1)) (ZMod q))
    (j : Fin n) (g : ZMod q) (r : Fin m → ZMod q) :
    Matrix (Fin m) (Fin (n + 1)) (ZMod q) :=
  fun i => Fin.cons (P i 0 + g * r i) (fun c => if c = j then P i c.succ + r i else P i c.succ)

theorem shiftCoordinate_eq_LWE {n m q : ℕ} [Fact (Nat.Prime q)]
    (A : Matrix (Fin m) (Fin n) (ZMod q)) (s : Fin n → ZMod q) (e : Fin m → ZMod q)
    (j : Fin n) (g : ZMod q) (r : Fin m → ZMod q) :
    shiftCoordinate (publicMatrix A s e) j g r =
    publicMatrix (fun i c => if c = j then A i c + r i else A i c) s
      (fun i => e i + (g - s j) * r i) := by
  ext i c
  revert c
  refine Fin.cases ?_ ?_
  · simp only [shiftCoordinate, publicMatrix, Fin.cons_zero]
    have h1 : ((fun i c => if c = j then A i c + r i else A i c) *ᵥ s) i =
        (A *ᵥ s) i + r i * s j := by
      change (∑ c : Fin n, (if c = j then A i c + r i else A i c) * s c) =
        (∑ c : Fin n, A i c * s c) + r i * s j
      calc
        _ = ∑ c : Fin n, (A i c * s c + if c = j then r i * s c else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          split_ifs with hx
          · rw [hx, add_mul]
          · rw [add_zero]
        _ = (∑ c : Fin n, A i c * s c) + ∑ c : Fin n, if c = j then r i * s c else 0 := by
          rw [Finset.sum_add_distrib]
        _ = (∑ c : Fin n, A i c * s c) + r i * s j := by
          congr 1
          rw [Finset.sum_eq_single j]
          · simp
          · intro b _ hb
            simp [hb]
          · intro hj
            exfalso
            apply hj
            exact Finset.mem_univ j
    rw [h1]
    ring
  · intro c'
    simp only [shiftCoordinate, publicMatrix, Fin.cons_succ]

/-- Apply `shiftCoordinate` to the first `k` coordinates. -/
def shiftHybrid {n m q : ℕ} [Fact (Nat.Prime q)]
    (P : Matrix (Fin m) (Fin (n + 1)) (ZMod q))
    (g : Fin n → ZMod q) : (k : ℕ) → (hk : k ≤ n) → (Fin k → Fin m → ZMod q) →
    Matrix (Fin m) (Fin (n + 1)) (ZMod q)
  | 0, _, _ => P
  | k + 1, hk, R =>
    let hk' : k ≤ n := Nat.le_of_succ_le hk
    shiftCoordinate (shiftHybrid P g k hk' (fun j => R ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩))
      ⟨k, hk⟩ (g ⟨k, hk⟩) (R ⟨k, Nat.lt_succ_self k⟩)

/-- The `k`-th hybrid game: sample `P` from LWE, then shift the first `k` coordinates using `g`.
We pass the result to the distinguisher `W`. -/
noncomputable def hybridGame {n m q : ℕ} [Fact (Nat.Prime q)]
    (noise : PMF (ZMod q)) (g : Fin n → ZMod q)
    (W : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → Game) (k : ℕ) (hk : k ≤ n) : Game := do
  let P ← publicMatrixLaw n m q noise
  let R ← PMF.pi (fun _ : Fin k => PMF.uniformOfFintype (Fin m → ZMod q))
  W (shiftHybrid P g k hk R)

/-- For a fixed `r`, adding `r` to the `j`-th column is a bijection on matrices. -/
def shiftMatrixEquiv {n m q : ℕ} [Fact (Nat.Prime q)] (j : Fin n) (r : Fin m → ZMod q) :
    Matrix (Fin m) (Fin n) (ZMod q) ≃ Matrix (Fin m) (Fin n) (ZMod q) where
  toFun A i c := if c = j then A i c + r i else A i c
  invFun A i c := if c = j then A i c - r i else A i c
  left_inv A := by ext i c; dsimp; split_ifs <;> ring
  right_inv A := by ext i c; dsimp; split_ifs <;> ring

/-- For `g ≠ s j`, multiplying by `g - s j` and adding `e` is a bijection on `r`. -/
def shiftErrorEquiv {m q : ℕ} [Fact (Nat.Prime q)] (e : Fin m → ZMod q)
    (c : ZMod q) (hc : c ≠ 0) :
    (Fin m → ZMod q) ≃ (Fin m → ZMod q) where
  toFun r i := e i + c * r i
  invFun r' i := c⁻¹ * (r' i - e i)
  left_inv r := by
    ext i
    dsimp
    have h : c⁻¹ * c = 1 := by exact inv_mul_cancel₀ hc
    calc
      c⁻¹ * (e i + c * r i - e i) = c⁻¹ * (c * r i) := by rw [add_sub_cancel_left]
      _ = (c⁻¹ * c) * r i := by rw [← mul_assoc]
      _ = 1 * r i := by rw [h]
      _ = r i := by rw [one_mul]
  right_inv r' := by
    ext i
    dsimp
    have h : c * c⁻¹ = 1 := by exact mul_inv_cancel₀ hc
    calc
      e i + c * (c⁻¹ * (r' i - e i)) = e i + (c * c⁻¹) * (r' i - e i) := by rw [← mul_assoc]
      _ = e i + 1 * (r' i - e i) := by rw [h]
      _ = r' i := by ring

open Cslib Cslib.Probability Cslib.ProbComp

/-- The self-reduction for LWE Decision. -/
noncomputable def lweSelfReduceDistinguisher {n m q : ℕ} [Fact (Nat.Prime q)]
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (P : Matrix (Fin m) (Fin (n + 1)) (ZMod q)) (j : Fin n) (g : ZMod q) : ProbComp Bool := do
  let r ← ProbComp.uniform (Fin m → ZMod q)
  distinguisher (shiftCoordinate P j g r)

/-- Coordinate-wise search from decision. -/
noncomputable def lweSearchCoordinate {n m q : ℕ} [Fact (Nat.Prime q)]
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (invEps : ℕ) (P : Matrix (Fin m) (Fin (n + 1)) (ZMod q)) (j : Fin n) : ProbComp (ZMod q) := do
  let N := (n + 3) * (7 * invEps) ^ 2
  let cIdeal ← OracleComp.countTrue N (do
    let U ← ProbComp.uniform (Matrix (Fin m) (Fin (n + 1)) (ZMod q))
    distinguisher U)
  let counts ← List.mapM (fun (g : ZMod q) => do
    let cIn ← OracleComp.countTrue N (lweSelfReduceDistinguisher distinguisher P j g)
    return (g, cIn)) (List.finRange q)
  let best := counts.foldl (fun (best_g, best_diff) (g, cIn) =>
    let diff := if cIn ≥ cIdeal then cIn - cIdeal else cIdeal - cIn
    if diff > best_diff then (g, diff) else (best_g, best_diff)) (0, 0)
  return best.1

/-- Recursive helper to search all coordinates. -/
noncomputable def lweSearchDeciderAux {n m q : ℕ} [Fact (Nat.Prime q)]
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (invEps : ℕ) (P : Matrix (Fin m) (Fin (n + 1)) (ZMod q)) :
    (k : ℕ) → (hk : k ≤ n) → ProbComp (Fin k → ZMod q)
  | 0, _ => pure (fun _ => 0)
  | k + 1, hk => do
    let s ← lweSearchDeciderAux distinguisher invEps P k (Nat.le_of_succ_le hk)
    let g ← lweSearchCoordinate distinguisher invEps P ⟨k, hk⟩
    return fun j => (if h : j.val < k then s ⟨j.val, h⟩ else g : ZMod q)

/-- The full empirical distinguishing reduction. -/
noncomputable def lweSearchDecider {n m q : ℕ} [Fact (Nat.Prime q)]
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (invEps : ℕ) (P : Matrix (Fin m) (Fin (n + 1)) (ZMod q)) : ProbComp (Fin n → ZMod q) :=
  lweSearchDeciderAux distinguisher invEps P n (Nat.le_refl n)



theorem lweSelfReduce_real {n m q : ℕ} [Fact (Nat.Prime q)]
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (s : Fin n → ZMod q) (e : Fin m → ZMod q) (j : Fin n) (g : ZMod q) (hg : g = s j) :
    ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
      eval (lweSelfReduceDistinguisher distinguisher (publicMatrix A s e) j g)) =
    ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
      eval (distinguisher (publicMatrix A s e))) := by
  simp_rw [lweSelfReduceDistinguisher, eval_bind, eval_uniform, shiftCoordinate_eq_LWE]
  have hs1 (r : Fin m → ZMod q) :
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        eval (distinguisher
          (publicMatrix (fun i c => if c = j then A i c + r i else A i c) 
        s (fun i => e i + (g - s j) * r i))))
        =
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        eval (distinguisher (publicMatrix A s (fun i => e i + (g - s j) * r i)))) :=
    PMF.uniformOfFintype_bind_equiv (shiftMatrixEquiv j r)
      (fun A => eval (distinguisher (publicMatrix A s (fun i => e i + (g - s j) * r i))))
  have hs2 :
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        (PMF.uniformOfFintype (Fin m → ZMod q)).bind fun r =>
          eval (distinguisher
          (publicMatrix (fun i c => if c = j then A i c + r i else A i c) 
        s (fun i => e i + (g - s j) * r i))))
        =
      ((PMF.uniformOfFintype (Fin m → ZMod q)).bind fun r =>
        (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
          eval (distinguisher
          (publicMatrix (fun i c => if c = j then A i c + r i else A i c) 
        s (fun i => e i + (g - s j) * r i)))) :=
    PMF.bind_comm _ _ _
  rw [hs2]
  have hs3 :
      ((PMF.uniformOfFintype (Fin m → ZMod q)).bind fun r =>
        (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
          eval (distinguisher
          (publicMatrix (fun i c => if c = j then A i c + r i else A i c) 
        s (fun i => e i + (g - s j) * r i))))
        =
      ((PMF.uniformOfFintype (Fin m → ZMod q)).bind fun r =>
        (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
          eval (distinguisher (publicMatrix A s (fun i => e i + (g - s j) * r i)))) := by
    congr 1
    funext r
    exact hs1 r
  rw [hs3]
  have hs4 :
      ((PMF.uniformOfFintype (Fin m → ZMod q)).bind fun r =>
        (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
          eval (distinguisher (publicMatrix A s (fun i => e i + (g - s j) * r i)))) =
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        (PMF.uniformOfFintype (Fin m → ZMod q)).bind fun r =>
          eval (distinguisher (publicMatrix A s (fun i => e i + (g - s j) * r i)))) :=
    PMF.bind_comm _ _ _
  rw [hs4]
  have hg0 : g - s j = 0 := sub_eq_zero.mpr hg
  simp_rw [hg0, zero_mul, add_zero]
  have hs5 (A : Matrix (Fin m) (Fin n) (ZMod q)) :
      ((PMF.uniformOfFintype (Fin m → ZMod q)).bind fun _ =>
        eval (distinguisher (publicMatrix A s e))) =
      eval (distinguisher (publicMatrix A s e)) :=
    PMF.bind_const _ _
  have hs6 :
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        (PMF.uniformOfFintype (Fin m → ZMod q)).bind fun _ =>
          eval (distinguisher (publicMatrix A s e))) =
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        eval (distinguisher (publicMatrix A s e))) := by
    congr 1
    funext A
    exact hs5 A
  exact hs6

theorem lweSelfReduce_ideal {n m q : ℕ} [Fact (Nat.Prime q)]
    (distinguisher : Matrix (Fin m) (Fin (n + 1)) (ZMod q) → ProbComp Bool)
    (s : Fin n → ZMod q) (e : Fin m → ZMod q) (j : Fin n) (g : ZMod q) (hg : g ≠ s j) :
    ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
      eval (lweSelfReduceDistinguisher distinguisher (publicMatrix A s e) j g)) =
    ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
      (PMF.uniformOfFintype (Fin m → ZMod q)).bind fun v =>
        eval (distinguisher (publicMatrix A s v))) := by
  simp_rw [lweSelfReduceDistinguisher, eval_bind, eval_uniform, shiftCoordinate_eq_LWE]
  have hs1 (r : Fin m → ZMod q) :
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        eval (distinguisher
          (publicMatrix (fun i c => if c = j then A i c + r i else A i c) 
        s (fun i => e i + (g - s j) * r i))))
        =
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        eval (distinguisher (publicMatrix A s (fun i => e i + (g - s j) * r i)))) :=
    PMF.uniformOfFintype_bind_equiv (shiftMatrixEquiv j r)
      (fun A => eval (distinguisher (publicMatrix A s (fun i => e i + (g - s j) * r i))))
  have hs2 :
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        (PMF.uniformOfFintype (Fin m → ZMod q)).bind fun r =>
          eval (distinguisher
          (publicMatrix (fun i c => if c = j then A i c + r i else A i c) 
        s (fun i => e i + (g - s j) * r i))))
        =
      ((PMF.uniformOfFintype (Fin m → ZMod q)).bind fun r =>
        (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
          eval (distinguisher
          (publicMatrix (fun i c => if c = j then A i c + r i else A i c) 
        s (fun i => e i + (g - s j) * r i)))) :=
    PMF.bind_comm _ _ _
  rw [hs2]
  have hs3 :
      ((PMF.uniformOfFintype (Fin m → ZMod q)).bind fun r =>
        (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
          eval (distinguisher
          (publicMatrix (fun i c => if c = j then A i c + r i else A i c) 
        s (fun i => e i + (g - s j) * r i))))
        =
      ((PMF.uniformOfFintype (Fin m → ZMod q)).bind fun r =>
        (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
          eval (distinguisher (publicMatrix A s (fun i => e i + (g - s j) * r i)))) := by
    congr 1
    funext r
    exact hs1 r
  rw [hs3]
  have hs4 :
      ((PMF.uniformOfFintype (Fin m → ZMod q)).bind fun r =>
        (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
          eval (distinguisher (publicMatrix A s (fun i => e i + (g - s j) * r i)))) =
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        (PMF.uniformOfFintype (Fin m → ZMod q)).bind fun r =>
          eval (distinguisher (publicMatrix A s (fun i => e i + (g - s j) * r i)))) :=
    PMF.bind_comm _ _ _
  rw [hs4]
  have hs5 (A : Matrix (Fin m) (Fin n) (ZMod q)) :
      ((PMF.uniformOfFintype (Fin m → ZMod q)).bind fun r =>
        eval (distinguisher (publicMatrix A s (fun i => e i + (g - s j) * r i)))) =
      ((PMF.uniformOfFintype (Fin m → ZMod q)).bind fun v =>
        eval (distinguisher (publicMatrix A s v))) :=
    PMF.uniformOfFintype_bind_equiv (shiftErrorEquiv e (g - s j) (sub_ne_zero.mpr hg))
      (fun v => eval (distinguisher (publicMatrix A s v)))
  have hs6 :
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        (PMF.uniformOfFintype (Fin m → ZMod q)).bind fun r =>
          eval (distinguisher (publicMatrix A s (fun i => e i + (g - s j) * r i)))) =
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        (PMF.uniformOfFintype (Fin m → ZMod q)).bind fun v =>
          eval (distinguisher (publicMatrix A s v))) := by
    congr 1
    funext A
    exact hs5 A
  exact hs6

end Cslib.Crypto.PrimeLWE
