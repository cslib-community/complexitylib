/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ThreeSum.Convolution
public import Complexity.Computability.WordRAM.Signed.Arithmetic

/-!
# Memory layout of the Convolution-3SUM graph builder

The three matrices occupy disjoint row-major blocks following the input. This directly adapts
the memory invariant of Anthropic's `ConvFill.Args.filled` at
[`formal-math@16a5ce4`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21a/Convolution/Fill.lean).
Values use the native signed encoding; addresses are natural numbers.

## Main definitions

* `Fill.Args`: layout and values of one tripartite instance.
* `Fill.Args.filled`: the memory after writing a prefix of each matrix.

## Main results

* `Fill.Args.filled_succ`: one round consists of exactly three writes.
* `Fill.Args.input_filled`: matrix writes preserve the input.
* `Fill.Args.matrices_filled`: the completed memory contains the mathematical reduction.

## References

* [V. Vassilevska Williams and R. Williams, *Finding, minimizing, and counting weighted
  subgraphs*][VassilevskaWilliamsWilliams2013]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Fill

open Cslib.WordRAM.Signed (encode)
open Cslib.Algorithms.ThreeSum

/-- Input length, matrix side and instance number, input base and three matrix bases, input
values, and the filler. The bounds and disjointness assumptions belong to the execution theorem. -/
structure Args where
  /-- Input length. -/
  N : ℕ
  /-- Side length of each matrix. -/
  t : ℕ
  /-- Instance number. -/
  s : ℕ
  /-- Input base address. -/
  base : ℕ
  /-- AB matrix base address. -/
  ab : ℕ
  /-- BC matrix base address. -/
  bc : ℕ
  /-- AC matrix base address. -/
  ac : ℕ
  /-- Mathematical input values. -/
  values : ℕ → ℤ
  /-- Invalid-index filler. -/
  filler : ℤ

namespace Args

/-- The encoded AB weight in row-major cell `q`. -/
def valueAB (A : Args) (q : ℕ) : ℕ := encode (pick A.N A.values A.filler q)

/-- The encoded BC weight; a negative index is rejected before reading the input. -/
def valueBC (A : Args) (q : ℕ) : ℕ :=
  encode (pick A.N A.values A.filler ((q % A.t * A.t + A.s : ℕ) - ((q / A.t : ℕ) : ℤ)))

/-- The encoded AC weight; invalid entries retain the positive filler. -/
def valueAC (A : Args) (q : ℕ) : ℕ :=
  encode (-pick A.N A.values (-A.filler) ((q / A.t + q % A.t) * A.t + A.s : ℕ))

/-- The memory after writing the first `q` cells of all three matrices. -/
def filled (A : Args) (mem : ℕ → ℕ) (q : ℕ) : ℕ → ℕ := fun a =>
  if A.ab ≤ a ∧ a < A.ab + q then A.valueAB (a - A.ab)
  else if A.bc ≤ a ∧ a < A.bc + q then A.valueBC (a - A.bc)
  else if A.ac ≤ a ∧ a < A.ac + q then A.valueAC (a - A.ac)
  else mem a

/-- A zero-length prefix leaves all memory unchanged. -/
@[simp]
theorem filled_zero (A : Args) (mem : ℕ → ℕ) : A.filled mem 0 = mem := by
  funext a
  simp only [filled, Nat.add_zero]
  split_ifs <;> omega

/-- One round writes one cell of each matrix, in AB, BC, AC order. -/
theorem filled_succ (A : Args) (mem : ℕ → ℕ) {q : ℕ}
    (hbc : A.ab + A.t * A.t ≤ A.bc) (hac : A.bc + A.t * A.t ≤ A.ac)
    (hq : q < A.t * A.t) :
    A.filled mem (q + 1) =
      Function.update (Function.update (Function.update (A.filled mem q)
        (A.ab + q) (A.valueAB q)) (A.bc + q) (A.valueBC q)) (A.ac + q) (A.valueAC q) := by
  funext a
  by_cases hab : a = A.ab + q
  · subst a
    simp [filled, show A.ab ≠ A.ac by omega,
      show A.ab ≠ A.bc by omega]
  by_cases hbc' : a = A.bc + q
  · subst a
    simp [filled, show ¬(A.ab ≤ A.bc + q ∧ A.bc + q < A.ab + (q + 1)) by omega,
      show A.bc ≠ A.ac by omega]
  by_cases hac' : a = A.ac + q
  · subst a
    simp [filled, show ¬(A.ab ≤ A.ac + q ∧ A.ac + q < A.ab + (q + 1)) by omega,
      show ¬(A.bc ≤ A.ac + q ∧ A.ac + q < A.bc + (q + 1)) by omega]
  have habiff : (A.ab ≤ a ∧ a < A.ab + (q + 1)) ↔ (A.ab ≤ a ∧ a < A.ab + q) := by omega
  have hbciff : (A.bc ≤ a ∧ a < A.bc + (q + 1)) ↔ (A.bc ≤ a ∧ a < A.bc + q) := by omega
  have haciff : (A.ac ≤ a ∧ a < A.ac + (q + 1)) ↔ (A.ac ≤ a ∧ a < A.ac + q) := by omega
  simp only [filled, Function.update_of_ne hac', Function.update_of_ne hbc',
    Function.update_of_ne hab, habiff, hbciff, haciff]

/-- Cells outside the three written prefixes retain their old contents. -/
theorem outside_filled (A : Args) (mem : ℕ → ℕ) (q a : ℕ)
    (hab : ¬(A.ab ≤ a ∧ a < A.ab + q)) (hbc : ¬(A.bc ≤ a ∧ a < A.bc + q))
    (hac : ¬(A.ac ≤ a ∧ a < A.ac + q)) : A.filled mem q a = mem a := by
  simp [filled, hab, hbc, hac]

/-- Disjoint matrix prefixes preserve all input cells. -/
theorem input_filled (A : Args) (mem : ℕ → ℕ) (q : ℕ)
    (hinput : A.base + A.N ≤ A.ab) (hbc : A.ab ≤ A.bc) (hac : A.bc ≤ A.ac)
    {i : ℕ} (hi : i < A.N) : A.filled mem q (A.base + i) = mem (A.base + i) :=
  A.outside_filled mem q _ (by omega) (by omega) (by omega)

/-- The fully written blocks contain the three matrices of the mathematical reduction. -/
theorem matrices_filled (A : Args) (mem : ℕ → ℕ)
    (hbc : A.ab + A.t * A.t ≤ A.bc) (hac : A.bc + A.t * A.t ≤ A.ac)
    (a b c : Fin A.t) :
    A.filled mem (A.t * A.t) (A.ab + a.val * A.t + b.val) =
        encode (weightAB A.N A.values A.filler a b) ∧
    A.filled mem (A.t * A.t) (A.bc + b.val * A.t + c.val) =
        encode (weightBC A.N A.s A.values A.filler b c) ∧
    A.filled mem (A.t * A.t) (A.ac + a.val * A.t + c.val) =
        encode (weightAC A.N A.s A.values A.filler a c) := by
  have ht : 0 < A.t := Nat.pos_of_ne_zero (by intro h; have := a.isLt; omega)
  have hcell (i j : Fin A.t) : i.val * A.t + j.val < A.t * A.t := by
    have := Nat.mul_le_mul_right A.t (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    omega
  have hdiv (i j : Fin A.t) : (i.val * A.t + j.val) / A.t = i.val := by
    rw [Nat.mul_comm i.val A.t, Nat.mul_add_div ht, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  have hmod (i j : Fin A.t) : (i.val * A.t + j.val) % A.t = j.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  have hAB := hcell a b
  have hBC := hcell b c
  have hAC := hcell a c
  have vAB : A.valueAB (a.val * A.t + b.val) =
      encode (weightAB A.N A.values A.filler a b) := by
    rw [weightAB_eq_pick]
    rfl
  have vBC : A.valueBC (b.val * A.t + c.val) =
      encode (weightBC A.N A.s A.values A.filler b c) := by
    rw [weightBC_eq_pick]
    simp only [valueBC, hdiv, hmod]
  have vAC : A.valueAC (a.val * A.t + c.val) =
      encode (weightAC A.N A.s A.values A.filler a c) := by
    rw [weightAC_eq_pick]
    simp only [valueAC, hdiv, hmod]
  refine ⟨?_, ?_, ?_⟩
  · rw [show A.ab + a.val * A.t + b.val = A.ab + (a.val * A.t + b.val) by omega]
    simp [filled, hAB, vAB]
  · rw [show A.bc + b.val * A.t + c.val = A.bc + (b.val * A.t + c.val) by omega]
    simp [filled, show ¬(A.ab ≤ A.bc + (b.val * A.t + c.val) ∧
      A.bc + (b.val * A.t + c.val) < A.ab + A.t * A.t) by omega, hBC, vBC]
  · rw [show A.ac + a.val * A.t + c.val = A.ac + (a.val * A.t + c.val) by omega]
    simp [filled, show ¬(A.ab ≤ A.ac + (a.val * A.t + c.val) ∧
      A.ac + (a.val * A.t + c.val) < A.ab + A.t * A.t) by omega,
      show ¬(A.bc ≤ A.ac + (a.val * A.t + c.val) ∧
      A.ac + (a.val * A.t + c.val) < A.bc + A.t * A.t) by omega, hAC, vAC]

end Args
end Cslib.Algorithms.WordRAM.ThreeSum.Fill
