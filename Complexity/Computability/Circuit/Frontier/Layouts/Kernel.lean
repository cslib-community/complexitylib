/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Metric
import Complexity.Foundations.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.BigOperators.Field

/-!
# The truncated distance kernel

Fix a finite graph `G`, a ratio `q` and a radius `R`. The *kernel row* of a vertex `v`
(`Cslib.Circuits.Frontier.Gaussian.kernelRow`) is the vector `z ↦ q ^ dist(v, z)` of the Euclidean
space over the vertices, cut off to `0` outside the closed ball of radius `R` around `v`. Distances
are extended distances, so an unreachable vertex receives `0`. The row of `v` has entry
`q ^ 0 = 1` at `v`, so its norm is at least one, and the *unit kernel row*
(`Cslib.Circuits.Frontier.Gaussian.unitKernelRow`) divides it by its norm. These are the vectors
of the Gaussian layouts of the frontier method: a vertex is scored by the inner product of its
unit kernel row with a standard Gaussian vector.

**Correlation of adjacent rows.** For adjacent `u` and `v` the distances from `u` and from `v` to
any vertex differ by at most one. Where both rows are nonzero their entries `a, b` are equal or
differ by the factor `q`, and in either case `a b ≥ κ (a ^ 2 + b ^ 2) / 2` with
`κ = 2 q / (1 + q ^ 2) ≤ 1`. Where exactly one row is nonzero the vertex lies on a sphere of
radius `R` around `u` or `v`; in maximum degree `D ≥ 2` such a sphere has at most `D (D - 1) ^ R`
vertices, so these vertices cost at most `D ((D - 1) q ^ 2) ^ R` in total
(`Cslib.Circuits.Frontier.Gaussian.le_inner_kernelRow`). Dividing by the norms, for `q ≥ 0` the
unit rows of adjacent vertices have inner product at least `κ - D ((D - 1) q ^ 2) ^ R`
(`Cslib.Circuits.Frontier.Gaussian.le_inner_unitKernelRow`). No girth assumption is needed. As
`R` grows with `(D - 1) q ^ 2 < 1` the error vanishes, and as `q` increases to `1 / √(D - 1)`
the correlation `κ` tends to `2 √(D - 1) / D`.

## Main definitions

* `Cslib.Circuits.Frontier.Gaussian.kernelRow`: the truncated distance kernel row of a vertex.
* `Cslib.Circuits.Frontier.Gaussian.unitKernelRow`: the kernel row divided by its norm.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.norm_unitKernelRow`: unit kernel rows are unit vectors.
* `Cslib.Circuits.Frontier.Gaussian.unitKernelRow_eq_zero_of_lt`: the unit kernel row of `v`
  vanishes outside the closed ball of radius `R` around `v`.
* `Cslib.Circuits.Frontier.Gaussian.le_inner_kernelRow`,
  `Cslib.Circuits.Frontier.Gaussian.le_inner_unitKernelRow`: the correlation of adjacent rows.
-/

@[expose] public section

open Finset
open scoped RealInnerProductSpace

namespace Cslib.Circuits.Frontier.Gaussian

variable {V : Type*} (G : SimpleGraph V)

/-- The truncated distance kernel row of `v`: the vector `z ↦ q ^ dist(v, z)` of the Euclidean
space over the vertices, cut off to `0` where the extended distance from `v` exceeds `R`. -/
noncomputable def kernelRow (q : ℝ) (R : ℕ) (v : V) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 fun z => if G.edist v z ≤ R then q ^ G.dist v z else 0

/-- The unit kernel row of `v`: its kernel row divided by its norm. -/
noncomputable def unitKernelRow [Fintype V] (q : ℝ) (R : ℕ) (v : V) : EuclideanSpace ℝ V :=
  ‖kernelRow G q R v‖⁻¹ • kernelRow G q R v

variable {G}

theorem kernelRow_apply (q : ℝ) (R : ℕ) (v z : V) :
    kernelRow G q R v z = if G.edist v z ≤ R then q ^ G.dist v z else 0 :=
  rfl

/-- The kernel row of `v` takes the value `1` at `v`. -/
@[simp]
theorem kernelRow_self (q : ℝ) (R : ℕ) (v : V) : kernelRow G q R v v = 1 := by
  simp [kernelRow_apply]

/-- The kernel is nonnegative for a nonnegative ratio. -/
theorem kernelRow_nonneg {q : ℝ} (hq : 0 ≤ q) (R : ℕ) (v z : V) : 0 ≤ kernelRow G q R v z := by
  rw [kernelRow_apply]
  split_ifs <;> positivity

/-- The kernel is symmetric. -/
theorem kernelRow_comm (q : ℝ) (R : ℕ) (v z : V) : kernelRow G q R v z = kernelRow G q R z v := by
  simp only [kernelRow_apply, SimpleGraph.edist_comm (u := v), SimpleGraph.dist_comm (u := v)]

/-- The kernel row of `v` vanishes outside the closed ball of radius `R` around `v`. -/
private theorem kernelRow_eq_zero_of_lt {q : ℝ} {R : ℕ} {v z : V} (h : R < G.edist v z) :
    kernelRow G q R v z = 0 := by
  rw [kernelRow_apply, ite_eq_right (not_le.2 h)]

/-- Inside the closed ball of radius `R` around `v`, the kernel row of `v` is `q ^ dist(v, z)`. -/
theorem kernelRow_of_le {q : ℝ} {R : ℕ} {v z : V} (h : G.edist v z ≤ R) :
    kernelRow G q R v z = q ^ G.dist v z := by
  rw [kernelRow_apply, ite_eq_left h]

/-! ### Correlation of adjacent rows -/

/-- A bounded extended distance is the cast of the distance. -/
private theorem edist_eq_dist_of_le {v z : V} {n : ℕ} (h : G.edist v z ≤ n) :
    G.edist v z = G.dist v z :=
  (SimpleGraph.reachable_of_edist_ne_top
    (ne_top_of_le_ne_top (ENat.natCast_ne_top n) h)).coe_dist_eq_edist.symm

/-- `κ = 2 q / (1 + q ^ 2)` is at most one. -/
private theorem two_mul_div_one_add_sq_le_one (q : ℝ) : 2 * q / (1 + q ^ 2) ≤ 1 := by
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (q - 1)]

/-- Entries differing by the factor `q` meet the correlation bound with equality. -/
private theorem two_mul_div_mul_sq_add_sq (q x : ℝ) :
    2 * q / (1 + q ^ 2) * (x ^ 2 + (x * q) ^ 2) / 2 = x * (x * q) := by
  field_simp

/-- **Pointwise defect.** For adjacent `u` and `v`, the kernel entries at `z` fall short of `κ`
times their mean square only on the spheres of radius `R` around `u` and `v`. -/
private theorem kernelRow_defect_le {q : ℝ} (R : ℕ) {u v : V} (huv : G.Adj u v) (z : V) :
    2 * q / (1 + q ^ 2) * (kernelRow G q R u z ^ 2 + kernelRow G q R v z ^ 2) / 2 -
        kernelRow G q R u z * kernelRow G q R v z ≤
      (q ^ 2) ^ R / 2 *
        ((if G.edist u z = R then 1 else 0) + (if G.edist v z = R then 1 else 0)) := by
  wlog huvz : G.edist u z ≤ G.edist v z generalizing u v
  · linarith [this huv.symm (le_of_not_ge huvz)]
  have hκ := two_mul_div_one_add_sq_le_one q
  have hIv : (0 : ℝ) ≤ if G.edist v z = R then 1 else 0 := by split_ifs <;> norm_num
  have hRHS : 0 ≤ (q ^ 2) ^ R / 2 *
      ((if G.edist u z = R then 1 else 0) + (if G.edist v z = R then 1 else 0)) := by
    split_ifs <;> positivity
  have h := huv.symm.edist_le_edist_add_one z
  simp only [kernelRow_apply]
  by_cases hv : G.edist v z ≤ R
  · -- Both entries are nonzero: the distances are equal or differ by one.
    have hu := huvz.trans hv
    rw [ite_eq_left hu, ite_eq_left hv]
    refine le_trans ?_ hRHS
    rw [edist_eq_dist_of_le hu, edist_eq_dist_of_le hv] at huvz h
    have h1 : G.dist u z ≤ G.dist v z := by exact_mod_cast huvz
    have h2 : G.dist v z ≤ G.dist u z + 1 := by exact_mod_cast h
    rcases (by omega : G.dist v z = G.dist u z ∨ G.dist v z = G.dist u z + 1) with h | h
    · rw [h]
      nlinarith [mul_le_mul_of_nonneg_right hκ (sq_nonneg (q ^ G.dist u z))]
    · rw [h, pow_succ q (G.dist u z)]
      linarith [two_mul_div_mul_sq_add_sq q (q ^ G.dist u z)]
  rw [ite_eq_right hv]
  by_cases hu : G.edist u z ≤ R
  · -- Only the entry of `u` is nonzero, so `z` lies on the sphere of radius `R` around `u`.
    have hd := edist_eq_dist_of_le hu
    rw [hd] at h hu ⊢
    have hR : G.dist u z = R := by
      have hlt : R < G.dist u z + 1 := by exact_mod_cast (lt_of_not_ge hv).trans_le h
      have hle : G.dist u z ≤ R := by exact_mod_cast hu
      omega
    rw [hR, ite_eq_left le_rfl, ite_eq_left rfl, ← pow_mul, mul_comm R 2, pow_mul]
    have hP : 0 ≤ (q ^ 2) ^ R := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hκ hP, mul_nonneg hP hIv]
  · rw [ite_eq_right hu]
    simpa using hRHS

variable [Fintype V]

/-- Every kernel row has norm at least one, from its entry `1` at its own vertex. -/
private theorem one_le_norm_kernelRow (q : ℝ) (R : ℕ) (v : V) : 1 ≤ ‖kernelRow G q R v‖ := by
  have h : 1 ≤ ‖kernelRow G q R v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc (1 : ℝ) = kernelRow G q R v v ^ 2 := by rw [kernelRow_self, one_pow]
      _ ≤ ∑ z, kernelRow G q R v z ^ 2 :=
        single_le_sum (f := fun z => kernelRow G q R v z ^ 2) (fun z _ => sq_nonneg _)
          (mem_univ v)
  nlinarith [norm_nonneg (kernelRow G q R v)]

theorem unitKernelRow_apply (q : ℝ) (R : ℕ) (v z : V) :
    unitKernelRow G q R v z = ‖kernelRow G q R v‖⁻¹ * kernelRow G q R v z :=
  rfl

/-- Unit kernel rows are unit vectors. -/
@[simp]
theorem norm_unitKernelRow (q : ℝ) (R : ℕ) (v : V) : ‖unitKernelRow G q R v‖ = 1 := by
  have h := one_le_norm_kernelRow (G := G) q R v
  rw [unitKernelRow, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (by linarith)]

/-- The unit kernel row of `v` vanishes outside the closed ball of radius `R` around `v`. -/
theorem unitKernelRow_eq_zero_of_lt {q : ℝ} {R : ℕ} {v z : V} (h : R < G.edist v z) :
    unitKernelRow G q R v z = 0 := by
  rw [unitKernelRow_apply, kernelRow_eq_zero_of_lt h, mul_zero]

/-- The unit kernel is nonnegative for a nonnegative ratio. -/
theorem unitKernelRow_nonneg {q : ℝ} (hq : 0 ≤ q) (R : ℕ) (v z : V) :
    0 ≤ unitKernelRow G q R v z := by
  rw [unitKernelRow_apply]
  exact mul_nonneg (by positivity) (kernelRow_nonneg hq R v z)

variable [DecidableRel G.Adj]

/-- In maximum degree `D ≥ 2`, the sphere of radius `d` has at most `D (D - 1) ^ d` vertices. -/
private theorem card_edist_eq_le {D : ℕ} (hD : 2 ≤ D) (hdeg : ∀ v, G.degree v ≤ D) (u : V)
    (d : ℕ) : #{v | G.edist u v = d} ≤ D * (D - 1) ^ d := by
  cases d with
  | zero =>
    have h0 : ({v | G.edist u v = ((0 : ℕ) : ℕ∞)} : Finset V) = {u} := by
      ext v
      simp only [mem_filter, mem_univ, true_and, mem_singleton, Nat.cast_zero,
        SimpleGraph.edist_eq_zero_iff]
      exact eq_comm
    rw [h0, card_singleton, pow_zero, mul_one]
    omega
  | succ d =>
    have h := SimpleGraph.card_edist_eq_add_one_le hdeg u d
    rw [Nat.cast_add, Nat.cast_one]
    refine h.trans (Nat.mul_le_mul_left D ?_)
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ (by omega)

/-- **Correlation of adjacent kernel rows.** In a graph of maximum degree `D ≥ 2`, the kernel
rows of adjacent vertices have inner product at least `κ = 2 q / (1 + q ^ 2)` times the mean of
their squared norms, up to the error `D ((D - 1) q ^ 2) ^ R` of the truncation spheres. -/
theorem le_inner_kernelRow {D : ℕ} (hD : 2 ≤ D) (hdeg : ∀ v, G.degree v ≤ D) (q : ℝ) (R : ℕ)
    {u v : V} (huv : G.Adj u v) :
    2 * q / (1 + q ^ 2) * (‖kernelRow G q R u‖ ^ 2 + ‖kernelRow G q R v‖ ^ 2) / 2 -
        D * ((D - 1) * q ^ 2) ^ R ≤ ⟪kernelRow G q R u, kernelRow G q R v⟫ := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  have hsum : 2 * q / (1 + q ^ 2) *
        ((∑ z, kernelRow G q R u z ^ 2) + ∑ z, kernelRow G q R v z ^ 2) / 2 -
        ∑ z, kernelRow G q R v z * kernelRow G q R u z =
      ∑ z, (2 * q / (1 + q ^ 2) * (kernelRow G q R u z ^ 2 + kernelRow G q R v z ^ 2) / 2 -
        kernelRow G q R u z * kernelRow G q R v z) := by
    rw [sum_sub_distrib, ← sum_div, ← mul_sum, sum_add_distrib]
    simp only [mul_comm (kernelRow G q R v _)]
  have hle := sum_le_sum fun z (_ : z ∈ univ) => kernelRow_defect_le (q := q) R huv z
  have hcount : ∑ z, (q ^ 2) ^ R / 2 *
        ((if G.edist u z = R then (1 : ℝ) else 0) + (if G.edist v z = R then 1 else 0)) =
      (q ^ 2) ^ R / 2 * ((#{z | G.edist u z = R} : ℝ) + #{z | G.edist v z = R}) := by
    rw [← mul_sum, sum_add_distrib, sum_boole, sum_boole]
  have hD' : ((D - 1 : ℕ) : ℝ) = D - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hu : (#{z | G.edist u z = R} : ℝ) ≤ D * (D - 1) ^ R := by
    rw [← hD']
    exact_mod_cast card_edist_eq_le hD hdeg u R
  have hv : (#{z | G.edist v z = R} : ℝ) ≤ D * (D - 1) ^ R := by
    rw [← hD']
    exact_mod_cast card_edist_eq_le hD hdeg v R
  have hP : 0 ≤ (q ^ 2) ^ R := by positivity
  have hbound : (q ^ 2) ^ R / 2 * ((#{z | G.edist u z = R} : ℝ) + #{z | G.edist v z = R}) ≤
      D * ((D - 1) * q ^ 2) ^ R := by
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hu hv) hP]
  linarith

/-- **Correlation of adjacent unit kernel rows.** In a graph of maximum degree `D ≥ 2` and for a
nonnegative ratio `q`, the unit kernel rows of adjacent vertices have inner product at least
`2 q / (1 + q ^ 2) - D ((D - 1) q ^ 2) ^ R`. -/
theorem le_inner_unitKernelRow {D : ℕ} (hD : 2 ≤ D) (hdeg : ∀ v, G.degree v ≤ D) {q : ℝ}
    (hq : 0 ≤ q) (R : ℕ) {u v : V} (huv : G.Adj u v) :
    2 * q / (1 + q ^ 2) - D * ((D - 1) * q ^ 2) ^ R ≤
      ⟪unitKernelRow G q R u, unitKernelRow G q R v⟫ := by
  have hC := le_inner_kernelRow hD hdeg q R huv
  have hs := one_le_norm_kernelRow (G := G) q R u
  have ht := one_le_norm_kernelRow (G := G) q R v
  rw [unitKernelRow, unitKernelRow, real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
    ← mul_inv, inv_mul_eq_div]
  generalize ⟪kernelRow G q R u, kernelRow G q R v⟫ = C at hC ⊢
  generalize ‖kernelRow G q R u‖ = s at hs hC ⊢
  generalize ‖kernelRow G q R v‖ = t at ht hC ⊢
  have hκ : 0 ≤ 2 * q / (1 + q ^ 2) := by positivity
  have hD1 : (0 : ℝ) ≤ D - 1 := by
    have : (2 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  have he : 0 ≤ (D : ℝ) * ((D - 1) * q ^ 2) ^ R := by positivity
  have hamgm : 2 * (s * t) ≤ s ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (s - t)]
  have h1 : 1 ≤ s * t := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hamgm hκ, mul_le_mul_of_nonneg_left h1 he]

end Cslib.Circuits.Frontier.Gaussian
