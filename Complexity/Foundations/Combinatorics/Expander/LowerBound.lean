/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Basic

/-!
# A lower bound on the spectral expansion

A `D`-regular multigraph on `N ≥ 2` vertices has spectral expansion
`(N - D) / (D (N - 1)) ≤ λ(G) ^ 2` (`div_le_sq_spectralExpansion`). So no graph of degree below its
number of vertices has `λ(G) = 0` (`spectralExpansion_pos`), and `λ(G) ≥ 1 / √(2 D)` once
`N ≥ 2 D` (`one_div_sqrt_two_mul_le_spectralExpansion`): bounded-degree expanders cannot be
arbitrarily good. The bound is tight for `D = N`: the complete graph with a self-loop at every
vertex, whose walk operator maps every function to its expectation, has `λ = 0`
(`spectralExpansion_complete`).

The proof is the trace argument, phrased without spectral theory. Let `a v u` be the number of
edges from `v` to `u` and test the characterization of `λ(G)` on the functions
`f_u = δ_u - 1 / N` of expectation zero, which have `∑ v, f_u v ^ 2 = 1 - 1 / N`. Summing
`∑ v, (G.walk f_u) v ^ 2 ≤ λ ^ 2 (1 - 1 / N)` over `u` bounds `∑ v u, (a v u / D - 1 / N) ^ 2` by
`λ ^ 2 (N - 1)`, while `a v u ≤ a v u ^ 2` (edge multiplicities are natural numbers) and
`∑ u, a v u = D` bound it below by `N (1 / D - 1 / N)`. Compare the discussion of lower bounds on
the second eigenvalue in [Hoory, Linial and Wigderson, Section 5][HooryLinialWigderson2006].

## Main definitions

* `Cslib.RotationMap.complete`: the complete graph with a self-loop at every vertex.

## Main results

* `Cslib.RotationMap.div_le_sq_spectralExpansion`, `Cslib.RotationMap.sqrt_le_spectralExpansion`:
  `(N - D) / (D (N - 1)) ≤ λ(G) ^ 2`.
* `Cslib.RotationMap.spectralExpansion_pos`: `0 < λ(G)` when `D < N`.
* `Cslib.RotationMap.one_div_sqrt_two_mul_le_spectralExpansion`: `λ(G) ≥ 1 / √(2 D)` when
  `2 D ≤ N`.
* `Cslib.RotationMap.spectralExpansion_complete`: the complete graph with self-loops has
  `λ = 0`.

## References

* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

@[expose] public section

namespace Cslib

open Finset
open scoped BigOperators

namespace RotationMap

variable {V D : Type*}

/-! ### The complete graph with self-loops -/

/-- The complete graph on `V` with a self-loop at every vertex, as a `|V|`-regular multigraph: the
`u`-th edge at `v` leads to `u` and is the `v`-th edge there. -/
def complete (V : Type*) : RotationMap V V where
  rot := Prod.swap
  rot_involutive := Prod.swap_swap

/-- The rotation map of the complete graph swaps the vertex and the label. -/
@[simp]
theorem rot_complete (p : V × V) : (complete V).rot p = p.swap :=
  rfl

/-- The `u`-th neighbor of every vertex in the complete graph is `u`. -/
@[simp]
theorem neighbor_complete (v u : V) : (complete V).neighbor v u = u :=
  rfl

/-- The complete graph with self-loops has spectral expansion `0`: one step of its walk replaces a
function by its expectation. -/
theorem spectralExpansion_complete [Fintype V] :
    (complete V).spectralExpansion = 0 := by
  refine le_antisymm (spectralExpansion_le le_rfl fun f hf => ?_) (spectralExpansion_nonneg _)
  have h (v : V) : (complete V).walk f v = 0 := by
    rw [walk_apply]
    exact hf
  simp [h]

/-! ### The trace bound -/

variable [Fintype V] [Fintype D] [Nonempty D]

open Classical in
/-- Applying `expect_walk_sq_le_spectralExpansion_sq_mul` to the centered indicator
`f u v = (if v = u then 1 else 0) - 1 / |V|` bounds the column sum of centered normalized edge
counts by `λ(G)² (1 - 1 / |V|)`. -/
private theorem sum_edgeCount_div_sub_sq_le_spectralExpansion_sq_mul (G : RotationMap V D)
    (hV : 2 ≤ Fintype.card V) (u : V) :
    ∑ v, ((G.edgeCount v u : ℝ) / Fintype.card D - 1 / Fintype.card V) ^ 2 ≤
      G.spectralExpansion ^ 2 * (1 - 1 / Fintype.card V) := by
  set N : ℝ := (Fintype.card V : ℝ) with hN
  set d : ℝ := (Fintype.card D : ℝ) with hd
  have hN2 : (2 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hV
  have hNpos : (0 : ℝ) < N := by linarith
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.2 Fintype.card_pos
  -- the test function `δ_u - 1 / N`, of expectation zero
  set f : V → ℝ := fun v => (if v = u then 1 else 0) - 1 / N with hfdef
  have hf_exp : 𝔼 v, f v = 0 := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [hfdef, sum_sub_distrib, sum_ite_eq', mem_univ, ite_true, sum_const, card_univ,
      nsmul_eq_mul]
    rw [← hN]
    field_simp
    ring
  have hf_sq : ∑ v, f v ^ 2 = 1 - 1 / N := by
    have h (v : V) : f v ^ 2 = (if v = u then 1 - 2 / N else 0) + 1 / N ^ 2 := by
      simp only [hfdef]
      split_ifs <;> ring
    simp only [h, sum_add_distrib, sum_ite_eq', mem_univ, ite_true, sum_const, card_univ,
      nsmul_eq_mul]
    rw [← hN]
    field_simp
    ring
  have hwalk (v : V) : G.walk f v = (G.edgeCount v u : ℝ) / d - 1 / N := by
    rw [walk_apply, Fintype.expect_eq_sum_div_card]
    simp only [hfdef, edgeCount, sum_sub_distrib, sum_boole, sum_const, card_univ,
      nsmul_eq_mul]
    rw [← hd]
    field_simp
  have h := expect_walk_sq_le_spectralExpansion_sq_mul (G := G) hf_exp
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, hf_sq] at h
  simp only [hwalk] at h
  rw [← hN, div_le_iff₀ hNpos] at h
  calc ∑ v, ((G.edgeCount v u : ℝ) / d - 1 / N) ^ 2
      ≤ G.spectralExpansion ^ 2 * ((1 - 1 / N) / N) * N := h
    _ = G.spectralExpansion ^ 2 * (1 - 1 / N) := by field_simp

/-- **Trace bound.** A `D`-regular multigraph on `N ≥ 2` vertices has
`(N - D) / (D (N - 1)) ≤ λ(G) ^ 2`. -/
theorem div_le_sq_spectralExpansion (G : RotationMap V D) (hV : 2 ≤ Fintype.card V) :
    ((Fintype.card V : ℝ) - Fintype.card D) / ((Fintype.card D : ℝ) * ((Fintype.card V : ℝ) - 1))
      ≤ G.spectralExpansion ^ 2 := by
  classical
  set N : ℝ := (Fintype.card V : ℝ) with hN
  set d : ℝ := (Fintype.card D : ℝ) with hd
  have hN2 : (2 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hV
  have hNpos : (0 : ℝ) < N := by linarith
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.2 Fintype.card_pos
  set lam := G.spectralExpansion
  -- the number of edges from `v` to `u`
  set a : V → V → ℝ := fun v u => (G.edgeCount v u : ℝ) with hadef
  have ha_sum (v : V) : ∑ u, a v u = d := by
    simp only [hadef, ← Nat.cast_sum, G.sum_edgeCount, hd]
  have hrow (v : V) : 1 / d - 1 / N ≤ ∑ u, (a v u / d - 1 / N) ^ 2 := by
    calc 1 / d - 1 / N = ∑ u, (a v u / d ^ 2 - 2 * a v u / (d * N) + 1 / N ^ 2) := by
          rw [sum_add_distrib, sum_sub_distrib, ← sum_div, ← sum_div, ← mul_sum, ha_sum,
            sum_const, card_univ, nsmul_eq_mul, ← hN]
          field_simp
          ring
      _ ≤ ∑ u, (a v u / d - 1 / N) ^ 2 := by
          refine sum_le_sum fun u _ => ?_
          have h1 : a v u / d ^ 2 ≤ a v u ^ 2 / d ^ 2 :=
            div_le_div_of_nonneg_right
              (by simp only [hadef]; exact_mod_cast Nat.le_self_pow two_ne_zero _) (by positivity)
          linarith [show (a v u / d - 1 / N) ^ 2 =
            a v u ^ 2 / d ^ 2 - 2 * a v u / (d * N) + 1 / N ^ 2 by ring]
  have htot : (N - d) / d ≤ lam ^ 2 * (N - 1) := by
    calc (N - d) / d = N * (1 / d - 1 / N) := by field_simp
      _ = ∑ _v : V, (1 / d - 1 / N) := by simp only [sum_const, card_univ, nsmul_eq_mul, hN]
      _ ≤ ∑ v, ∑ u, (a v u / d - 1 / N) ^ 2 := sum_le_sum fun v _ => hrow v
      _ = ∑ u, ∑ v, (a v u / d - 1 / N) ^ 2 := sum_comm
      _ ≤ ∑ _u : V, lam ^ 2 * (1 - 1 / N) :=
          sum_le_sum fun u _ => G.sum_edgeCount_div_sub_sq_le_spectralExpansion_sq_mul hV u
      _ = N * (lam ^ 2 * (1 - 1 / N)) := by simp only [sum_const, card_univ, nsmul_eq_mul, hN]
      _ = lam ^ 2 * (N - 1) := by field_simp
  have hN1 : 0 < N - 1 := by linarith
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hdpos] at htot
  linarith

/-- **Trace bound**, square-root form: a `D`-regular multigraph on `N ≥ 2` vertices has
`√((N - D) / (D (N - 1))) ≤ λ(G)`. -/
theorem sqrt_le_spectralExpansion (G : RotationMap V D) (hV : 2 ≤ Fintype.card V) :
    Real.sqrt (((Fintype.card V : ℝ) - Fintype.card D) /
        ((Fintype.card D : ℝ) * ((Fintype.card V : ℝ) - 1))) ≤ G.spectralExpansion :=
  (Real.sqrt_le_sqrt (G.div_le_sq_spectralExpansion hV)).trans_eq
    (Real.sqrt_sq G.spectralExpansion_nonneg)

/-- A regular multigraph whose degree is below its number of vertices has positive spectral
expansion. -/
theorem spectralExpansion_pos (G : RotationMap V D) (hDV : Fintype.card D < Fintype.card V) :
    0 < G.spectralExpansion := by
  have hD : 1 ≤ Fintype.card D := Fintype.card_pos
  have hV : 2 ≤ Fintype.card V := by omega
  refine (Real.sqrt_pos.2 ?_).trans_le (G.sqrt_le_spectralExpansion hV)
  have h1 : (Fintype.card D : ℝ) < Fintype.card V := by exact_mod_cast hDV
  have h2 : (1 : ℝ) ≤ Fintype.card D := by exact_mod_cast hD
  apply div_pos <;> nlinarith

/-- A `D`-regular multigraph on at least `2 D` vertices has `1 / √(2 D) ≤ λ(G)`. -/
theorem one_div_sqrt_two_mul_le_spectralExpansion (G : RotationMap V D)
    (hDV : 2 * Fintype.card D ≤ Fintype.card V) :
    1 / Real.sqrt (2 * Fintype.card D) ≤ G.spectralExpansion := by
  have hD : 1 ≤ Fintype.card D := Fintype.card_pos
  refine le_trans ?_ (G.sqrt_le_spectralExpansion (by omega))
  rw [one_div, ← Real.sqrt_inv]
  apply Real.sqrt_le_sqrt
  have h1 : (2 * Fintype.card D : ℝ) ≤ Fintype.card V := by exact_mod_cast hDV
  have h2 : (1 : ℝ) ≤ Fintype.card D := by exact_mod_cast hD
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith

end RotationMap

end Cslib
