/-
Copyright (c) 2026 Samuel Schlesinger, real-roots. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, real-roots
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LWE.PrimeModulus
public import CslibFrontier.Crypto.Game.Hybrid

public import Mathlib.Algebra.Field.ZMod

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

end Cslib.Crypto.PrimeLWE
