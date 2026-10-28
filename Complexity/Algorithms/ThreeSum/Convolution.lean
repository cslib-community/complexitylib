/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ExactTriangle.Defs
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Group.Abs

/-!
# Convolution-3SUM reduces to Exact Triangle

This directly adapts Anthropic's [pinned reduction](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/Theorem21a/Convolution.lean),
after the reduction cited there as [VassilevskaWilliamsWilliams2013, Theorem 4.3].
The theorem number is taken from that source. No machine, machine simulation, or subquadratic
time bound is asserted here.
The native graph-weight construction is developed separately.

An input has a solution when `x i + x j = x (i + j)` for some `i + j < N`; indices may repeat.
Indices start at zero: for nonempty input, `x 0 = 0` alone gives the solution `i = j = 0`.
This differs from ordinary 3SUM, which requires three distinct positions. For `N < t * t`,
construct `2 * t` tripartite instances with `t` vertices per part. Invalid indices receive
`2 * U + 1`, preventing them from creating zero triangles when input magnitudes are at most `U`.

## Main definitions

* `Convolution`: the one-array Convolution-3SUM predicate.
* `pick`: read a signed in-range index or use a filler.
* `weightAB`, `weightBC`, `weightAC`: the three matrices of instance `s`.

## Main results

* `convolution_iff`: correctness of the explicit reduction for `N < t * t`.
* `convolution_iff_sqrt`: the choice `t = Nat.sqrt N + 1`.
* `weights_abs_le`: all generated weights have magnitude at most `2 * U + 1`.

## References

* [V. Vassilevska Williams and R. Williams, *Finding, minimizing, and counting weighted
  subgraphs*][VassilevskaWilliamsWilliams2013]
-/

@[expose] public section

namespace Cslib.Algorithms.ThreeSum

open ExactTriangle (HasZeroTriangle)

/-- One-array Convolution-3SUM, allowing repeated indices. Only the first `N` entries matter. -/
def Convolution (N : ℕ) (x : ℕ → ℤ) : Prop :=
  ∃ i j, i + j < N ∧ x i + x j = x (i + j)

/-- A signed index selects an input entry exactly when it lies in `[0, N)`. -/
def pick (N : ℕ) (x : ℕ → ℤ) (fill z : ℤ) : ℤ :=
  if 0 ≤ z ∧ z < N then x z.toNat else fill

/-- A nonnegative index uses the usual natural-number bounds check. -/
theorem pick_nat (N : ℕ) (x : ℕ → ℤ) (fill : ℤ) (i : ℕ) :
    pick N x fill i = if i < N then x i else fill := by
  simp [pick]

/-- Signed subtraction rejects negative indices before converting them to naturals. -/
theorem pick_sub (N : ℕ) (x : ℕ → ℤ) (fill : ℤ) (a b : ℕ) :
    pick N x fill ((a : ℤ) - b) =
      if b ≤ a ∧ a - b < N then x (a - b) else fill := by
  by_cases h : b ≤ a
  · have he : (a : ℤ) - b = (a - b : ℕ) := by omega
    rw [he, pick_nat]
    simp [h]
  · have hn : ¬(0 ≤ (a : ℤ) - b ∧ (a : ℤ) - b < N) := by omega
    simp [pick, h]

/-- The edge `(a,b)` represents the input index `a*t+b`. -/
def weightAB {t : ℕ} (N : ℕ) (x : ℕ → ℤ) (fill : ℤ) (a b : Fin t) : ℤ :=
  if a.val * t + b.val < N then x (a.val * t + b.val) else fill

/-- The edge `(b,c)` represents the signed index `c*t+s-b`. -/
def weightBC {t : ℕ} (N s : ℕ) (x : ℕ → ℤ) (fill : ℤ) (b c : Fin t) : ℤ :=
  if b.val ≤ c.val * t + s ∧ c.val * t + s - b.val < N then
    x (c.val * t + s - b.val) else fill

/-- The edge `(a,c)` negates the entry at `(a+c)*t+s`, using positive filler if invalid. -/
def weightAC {t : ℕ} (N s : ℕ) (x : ℕ → ℤ) (fill : ℤ) (a c : Fin t) : ℤ :=
  if (a.val + c.val) * t + s < N then -x ((a.val + c.val) * t + s) else fill

/-- Matrix AB is implemented by a guarded signed-index read. -/
theorem weightAB_eq_pick {t : ℕ} (N : ℕ) (x : ℕ → ℤ) (fill : ℤ) (a b : Fin t) :
    weightAB N x fill a b = pick N x fill (a.val * t + b.val : ℕ) :=
  (pick_nat _ _ _ _).symm

/-- Matrix BC is implemented by a guarded signed-index read, with a possibly negative index. -/
theorem weightBC_eq_pick {t : ℕ} (N s : ℕ) (x : ℕ → ℤ) (fill : ℤ) (b c : Fin t) :
    weightBC N s x fill b c = pick N x fill ((c.val * t + s : ℕ) - (b.val : ℤ)) :=
  (pick_sub _ _ _ _ _).symm

/-- Matrix AC reads with negative filler before negating, retaining positive invalid weights. -/
theorem weightAC_eq_pick {t : ℕ} (N s : ℕ) (x : ℕ → ℤ) (fill : ℤ) (a c : Fin t) :
    weightAC N s x fill a c = -pick N x (-fill) ((a.val + c.val) * t + s : ℕ) := by
  rw [pick_nat]
  split_ifs <;> simp [weightAC, *]

/-- Every edge is either an input entry up to sign, or the filler. -/
theorem weights_abs_le {t N s : ℕ} {x : ℕ → ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hx : ∀ i < N, |x i| ≤ U) (a b c : Fin t) :
    |weightAB N x (2 * U + 1) a b| ≤ 2 * U + 1 ∧
    |weightBC N s x (2 * U + 1) b c| ≤ 2 * U + 1 ∧
    |weightAC N s x (2 * U + 1) a c| ≤ 2 * U + 1 := by
  have hf : |2 * U + 1| = 2 * U + 1 := abs_of_nonneg (by omega)
  refine ⟨?_, ?_, ?_⟩
  · unfold weightAB
    split_ifs with h
    · exact (hx _ h).trans (by omega)
    · exact hf.le
  · unfold weightBC
    split_ifs with h
    · exact (hx _ h.2).trans (by omega)
    · exact hf.le
  · unfold weightAC
    split_ifs with h
    · simpa only [abs_neg] using (hx _ h).trans (by omega : U ≤ 2 * U + 1)
    · exact hf.le

private theorem weights_neg_le {t N s : ℕ} {x : ℕ → ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hx : ∀ i < N, |x i| ≤ U) (a b c : Fin t) :
    -U ≤ weightAB N x (2 * U + 1) a b ∧
    -U ≤ weightBC N s x (2 * U + 1) b c ∧
    -U ≤ weightAC N s x (2 * U + 1) a c := by
  refine ⟨?_, ?_, ?_⟩
  · unfold weightAB
    split_ifs with h
    · exact (abs_le.mp (hx _ h)).1
    · omega
  · unfold weightBC
    split_ifs with h
    · exact (abs_le.mp (hx _ h.2)).1
    · omega
  · unfold weightAC
    split_ifs with h
    · exact neg_le_neg (abs_le.mp (hx _ h)).2
    · omega

/-- The explicit reduction is correct for every input size, including zero.
There are `2*t` instances and exactly `t` vertices in each of their three parts. -/
theorem convolution_iff {t N : ℕ} {x : ℕ → ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hNt : N < t * t) (hx : ∀ i < N, |x i| ≤ U) :
    Convolution N x ↔ ∃ s < 2 * t, HasZeroTriangle
      (weightAB (t := t) N x (2 * U + 1)) (weightBC N s x (2 * U + 1))
      (weightAC N s x (2 * U + 1)) := by
  constructor
  · rintro ⟨i, j, hij, h⟩
    have ht : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hit := Nat.mod_lt i ht
    have hjt := Nat.mod_lt j ht
    have hAB : i / t * t + i % t = i := Nat.div_add_mod' i t
    have hBC : j / t * t + (j % t + i % t) - i % t = j := by
      have := Nat.div_add_mod' j t
      omega
    have hAC : (i / t + j / t) * t + (j % t + i % t) = i + j := by
      rw [Nat.add_mul]
      omega
    refine ⟨j % t + i % t, by omega,
      ⟨i / t, Nat.div_lt_of_lt_mul (by omega : i < t * t)⟩, ⟨i % t, hit⟩,
      ⟨j / t, Nat.div_lt_of_lt_mul (by omega : j < t * t)⟩, ?_⟩
    dsimp only [weightAB, weightBC, weightAC]
    rw [ite_eq_left (by omega : i / t * t + i % t < N),
      ite_eq_left (show i % t ≤ j / t * t + (j % t + i % t) ∧
        j / t * t + (j % t + i % t) - i % t < N by omega),
      ite_eq_left (hAC.trans_lt hij), hAB, hBC, hAC, h]
    omega
  · rintro ⟨s, -, a, b, c, h⟩
    obtain ⟨hgeAB, hgeBC, hgeAC⟩ := weights_neg_le hU hx a b c (s := s)
    have hAB : a.val * t + b.val < N := by
      by_contra hout
      rw [weightAB, ite_eq_right hout] at h
      omega
    have hBC : b.val ≤ c.val * t + s ∧ c.val * t + s - b.val < N := by
      by_contra hout
      rw [weightBC, ite_eq_right hout] at h
      omega
    have hAC : (a.val + c.val) * t + s < N := by
      by_contra hout
      rw [weightAC, ite_eq_right hout] at h
      omega
    rw [weightAB, weightBC, weightAC, ite_eq_left hAB, ite_eq_left hBC, ite_eq_left hAC] at h
    have hsum : a.val * t + b.val + (c.val * t + s - b.val) = (a.val + c.val) * t + s := by
      rw [Nat.add_mul]
      omega
    exact ⟨a.val * t + b.val, c.val * t + s - b.val, hsum ▸ hAC, by
      rw [hsum]
      omega⟩

/-- Taking `t = ⌊√N⌋+1` gives `2*t` instances with `t` vertices per part. -/
theorem convolution_iff_sqrt {N : ℕ} {x : ℕ → ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hx : ∀ i < N, |x i| ≤ U) :
    Convolution N x ↔ ∃ s < 2 * (Nat.sqrt N + 1),
      HasZeroTriangle (weightAB (t := Nat.sqrt N + 1) N x (2 * U + 1))
        (weightBC N s x (2 * U + 1)) (weightAC N s x (2 * U + 1)) :=
  convolution_iff hU (Nat.lt_succ_sqrt N) hx

end Cslib.Algorithms.ThreeSum
