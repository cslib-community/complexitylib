/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.Interpolation
public import Complexity.Foundations.Data.Code.LowDegreeExtension
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Counter evaluation of a packed gate extension

The grid is numbered by its base-`s` digits. A coordinate counter multiplies modular Lagrange
weights; an assignment counter sums the weighted table entries. Neither loop constructs a list
of assignments or a truth table. The caller supplies the table entry at one assignment index.

## Main definitions

* `Cslib.TreeEval.Ary.Packed.gridWeight`: the product of basis weights for one assignment.
* `Cslib.TreeEval.Ary.Packed.interpolateGrid`: sum the weighted entries using a counter.

## Main results

* `Cslib.TreeEval.Ary.Packed.cast_interpolateGrid`: agreement with the existing low-degree
  extension, including the empty coordinate tuple.

## References

* [R. Williams, *Simulating Time With Square-Root Space*][Williams2025], Appendix A,
  equation (6). This is an executable prime-field realization of that interpolation formula.

This file proves functional correctness and accumulator bounds. The table supplier is an
explicit parameter, without an assumed native resource bound. Its query implementation and the
native certificate for the complete loop remain separate obligations.
-/

@[expose] public section

namespace Cslib.TreeEval.Ary.Packed

open Reader

/-- One coordinate of the assignment index, in least-significant-first order. -/
def gridDigit (s k j : ℕ) : ℕ := k / s ^ j % s

/-- Multiply one coordinate's basis weight into the accumulator. -/
def gridWeightStep (p s : ℕ) (x : List ℕ) (st : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (st.1 + 1, st.2.1 / s, if p = 0 then 0 else
    mulMod p st.2.2 (basisWeight p s (st.2.1 % s) (x.getD st.1 0)))

/-- Weight one grid assignment by scanning coordinates with one product accumulator. -/
def gridWeight (p s n k : ℕ) (x : List ℕ) : ℕ :=
  ((gridWeightStep p s x)^[n] (0, k, 1 % p)).2.2

/-- The coordinate counter advances while the assignment is consumed one digit at a time.
Only division by `s` is computed at a step; no large power is materialized. -/
theorem gridWeightStep_counters (p s k : ℕ) (x : List ℕ) (n : ℕ) :
    ((gridWeightStep p s x)^[n] (0, k, 1 % p)).1 = n ∧
      ((gridWeightStep p s x)^[n] (0, k, 1 % p)).2.1 = k / s ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp [gridWeightStep, ih.1, ih.2, pow_succ, Nat.div_div_eq_div_mul]

/-- A positive modulus keeps every product accumulator reduced. -/
theorem gridWeight_lt {p : ℕ} (hp : 0 < p) (s n k : ℕ) (x : List ℕ) :
    gridWeight p s n k x < p := by
  cases n with
  | zero => exact Nat.mod_lt _ hp
  | succ n =>
    rw [gridWeight, Function.iterate_succ_apply']
    simp only [gridWeightStep, hp.ne', ↓reduceIte]
    exact Nat.mod_lt _ hp

/-- One assignment's contribution, with the table queried at its current index only. -/
def gridSumStep (p s n : ℕ) (table : ℕ → ℕ) (x : List ℕ) (st : ℕ × ℕ) : ℕ × ℕ :=
  (st.1 + 1, if p = 0 then 0 else
    addMod p st.2 (mulMod p (table st.1) (gridWeight p s n st.1 x)))

/-- Evaluate the interpolation by scanning all `s^n` assignments with one sum accumulator. -/
def interpolateGrid (p s n : ℕ) (table : ℕ → ℕ) (x : List ℕ) : ℕ :=
  ((gridSumStep p s n table x)^[s ^ n] (0, 0)).2

private theorem gridSumStep_counter (p s n : ℕ) (table : ℕ → ℕ) (x : List ℕ) (t : ℕ) :
    ((gridSumStep p s n table x)^[t] (0, 0)).1 = t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply']; simp [gridSumStep, ih]

/-- Every sum accumulator remains a reduced residue, independently of table entries. -/
theorem interpolateGrid_lt {p : ℕ} (hp : 0 < p) (s n : ℕ) (table : ℕ → ℕ) (x : List ℕ) :
    interpolateGrid p s n table x < p := by
  unfold interpolateGrid
  generalize s ^ n = t
  cases t with
  | zero => exact hp
  | succ t =>
    rw [Function.iterate_succ_apply']
    simp only [gridSumStep, hp.ne', ↓reduceIte]
    exact Nat.mod_lt _ hp

variable {p : ℕ} [Fact p.Prime]

private theorem cast_gridWeight_range {s : ℕ} (hs : 0 < s) (hsp : s ≤ p) (k : ℕ)
    (x : List ℕ) (n : ℕ) :
    ((gridWeight p s n k x : ℕ) : ZMod p) =
      ∏ j ∈ Finset.range n,
        (Lagrange.basis Finset.univ (fun a : Fin s => (a.val : ZMod p))
          ⟨gridDigit s k j, Nat.mod_lt _ hs⟩).eval (x.getD j 0 : ZMod p) := by
  simp only [gridDigit]
  induction n with
  | zero => simp [gridWeight]
  | succ n ih =>
    rw [gridWeight, Function.iterate_succ_apply']
    simp only [gridWeightStep, (gridWeightStep_counters p s k x n).1,
      (gridWeightStep_counters p s k x n).2, (Fact.out : p.Prime).ne_zero,
      ↓reduceIte, cast_mulMod, Finset.prod_range_succ]
    change ((gridWeight p s n k x : ℕ) : ZMod p) * _ = _
    rw [ih, cast_basisWeight hsp ⟨k / s ^ n % s, Nat.mod_lt _ hs⟩]

private theorem cast_gridSum_range (s n : ℕ) (table : ℕ → ℕ) (x : List ℕ) (t : ℕ) :
    (((gridSumStep p s n table x)^[t] (0, 0)).2 : ZMod p) =
      ∑ k ∈ Finset.range t, (table k : ZMod p) * (gridWeight p s n k x : ZMod p) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    simp only [gridSumStep, gridSumStep_counter, (Fact.out : p.Prime).ne_zero,
      ↓reduceIte, cast_addMod, cast_mulMod, Finset.sum_range_succ, ih]

/-- The streamed modular sum is exactly the finite-grid low-degree extension. The table is
indexed by Mathlib's existing base-`s` numbering of tuples; no additional gate model is used. -/
theorem cast_interpolateGrid {s n : ℕ} (hs : 0 < s) (hsp : s ≤ p)
    (h : Fin s ↪ ZMod p) (hh : ∀ a, h a = (a.val : ZMod p))
    (table : ℕ → ℕ) (x : List ℕ) :
    ((interpolateGrid p s n table x : ℕ) : ZMod p) =
      Code.lowDegreeExtension h
        (fun a : Fin n → Fin s => (table (finFunctionFinEquiv a) : ZMod p))
        (fun i => (x.getD i 0 : ZMod p)) := by
  rw [interpolateGrid, cast_gridSum_range, Finset.sum_range]
  have hemb : (fun a : Fin s => (a.val : ZMod p)) = h := funext fun a => (hh a).symm
  calc
    (∑ k : Fin (s ^ n), (table k : ZMod p) * (gridWeight p s n k x : ZMod p)) =
        ∑ a : Fin n → Fin s,
          (table (finFunctionFinEquiv a) : ZMod p) *
            (gridWeight p s n (finFunctionFinEquiv a) x : ZMod p) :=
      (Equiv.sum_comp finFunctionFinEquiv _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      rw [cast_gridWeight_range hs hsp, Finset.prod_range, hemb]
      apply Finset.prod_congr rfl
      intro i _
      have hdigit : (⟨gridDigit s (finFunctionFinEquiv a) i, Nat.mod_lt _ hs⟩ : Fin s) = a i := by
        apply Fin.ext
        exact (finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv a) i).symm.trans
          (congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply a) i))
      rw [hdigit]

end Cslib.TreeEval.Ary.Packed
