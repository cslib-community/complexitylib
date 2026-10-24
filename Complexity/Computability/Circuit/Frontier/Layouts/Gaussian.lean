/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.Cubic
public import Complexity.Computability.Circuit.Frontier.Layouts.Gaussian.Coefficient
public import Complexity.Computability.Circuit.Frontier.Layouts.Gaussian.Sample

/-!
# Gaussian layouts of cubic graphs

Every large loopless multigraph on `h` vertices in which every vertex has three edges, parallel
edges allowed, has a layout of width at most `(p + ξ) h`, for every `ξ > 0`, where

`p = (3 / (2π)) arccos ((1 + 2√2)/4) ≈ 0.14035`

is `Cslib.Circuits.Frontier.Gaussian.gaussianCoefficient`
(`Cslib.Circuits.Frontier.Gaussian.exists_width_le_gaussianCoefficient`). In particular `p` is a
cubic layout coefficient (`Cslib.Circuits.Frontier.Gaussian.cubicLayoutBound_gaussian`), and
through the cubic quotient of a subcubic multigraph, `2p ≈ 0.2807` is a layout coefficient for
maximum degree three (`Cslib.Circuits.Frontier.layoutBound_gaussian`).

**The random layout.** Give each vertex `v` its unit kernel row `x_v`
(`Cslib.Circuits.Frontier.Gaussian.unitKernelRow`): the normalized vector of distance weights
`q ^ dist(v, z)`, truncated at radius `R`. Give each edge `uv` the unit vector `y_uv` in the
direction of `x_u + x_v`. Draw a standard Gaussian vector `ω` and score each edge by `⟪y_e, ω⟫`.
List the vertices by the median of their three edge scores
(`Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_edgeScore`).

**One vertex.** A vertex straddles a threshold when two of its edge scores fall on opposite
sides. The three edge vectors at `v` have inner product at least `√((1 + ρ)/2)` with `x_v`, where
`ρ` bounds the inner products of adjacent rows; by Sheppard's bound [Sheppard1899] and the
concavity of `arccos` in a spherical cap, `v` straddles any fixed threshold with probability at
most `(3 / (2π)) arccos ((1 + 3ρ)/4)`
(`Cslib.Circuits.Frontier.Gaussian.measureReal_straddleEvent_le`).

**All thresholds at once.** Each event depends only on the coordinates of `ω` in a ball of
bounded radius, so each count of events has variance `O(h)` and is within `ε h` of its mean with
probability `1 - O(1/h)`. For large `h` one sample keeps the straddling counts at a grid of
thresholds, the window counts between them, and the tails near their means
(`Cslib.Circuits.Frontier.Gaussian.exists_good_sample`); the median layout of that sample has
width at most `(p_ρ + O(δ) + O(ε) + O(1/T ^ 2)) h`.

**The limit.** As `q` increases to `1/√2` and `R` grows, the adjacent correlation tends to
`2√2/3`, the neighbour correlation of Gaussian waves on the 3-regular tree, and
`(1 + 3 · 2√2/3)/4 = (1 + 2√2)/4`. No girth assumption is needed.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.exists_parameters`: parameters bringing the width per vertex
  within any `ξ > 0` of `gaussianCoefficient`.
* `Cslib.Circuits.Frontier.Gaussian.exists_width_le_gaussianCoefficient`: Gaussian layouts of
  loopless multigraphs whose vertices have three edges.
* `Cslib.Circuits.Frontier.Gaussian.cubicLayoutBound_gaussian`: the cubic layout bound with
  coefficient `gaussianCoefficient`.
* `Cslib.Circuits.Frontier.Gaussian.exists_ncard_edgeCut_le`: large cubic multigraphs have
  bisections, and more generally sets of any size, cut off by at most
  `(gaussianCoefficient + ξ) |V|` edges.
* `Cslib.Circuits.Frontier.layoutBound_gaussian`: the layout hypothesis for maximum degree three
  with coefficient `2 gaussianCoefficient`.

## References

* [W. F. Sheppard, *On the application of the theory of error to cases of normal distribution
  and normal correlation*][Sheppard1899]
-/

@[expose] public section

open Real

namespace Cslib.Circuits.Frontier.Gaussian

/-! ### Parameters -/

/-- **Decay rate and radius.** Every `ρ₀ < 2√2/3` admits a decay rate `q ≥ 0` and a radius `R`
with `ρ₀ ≤ 2 q / (1 + q ^ 2) - 3 (2 q ^ 2) ^ R`. -/
private theorem exists_decay_radius {ρ₀ : ℝ} (hρ₀ : ρ₀ < 2 * √2 / 3) :
    ∃ (q : ℝ) (R : ℕ), 0 ≤ q ∧ ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R := by
  have h3 : vertexCorrelation 3 = 2 * √2 / 3 := by norm_num [vertexCorrelation]
  obtain ⟨q, R, hq, hρ⟩ := exists_decay_radius_degree (by norm_num : 2 ≤ 3) (ρ := ρ₀)
    (by rw [h3]; exact hρ₀)
  refine ⟨q, R, hq, ?_⟩
  norm_num at hρ
  exact hρ

/-- **Parameters.** For every `ξ > 0`, some admissible parameters bring the width per vertex of
a good sample within `ξ` of `gaussianCoefficient`. -/
theorem exists_parameters {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ (q : ℝ) (R : ℕ) (ρ₀ T ε : ℝ) (M : ℕ), 0 ≤ q ∧ 1 / 8 ≤ ρ₀ ∧
      ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧ 0 < T ∧ 0 < ε ∧ 0 < M ∧
      cubicBound ρ₀ T ε M ≤ gaussianCoefficient + ξ := by
  set g : ℝ := 2 * √2 / 3 with hg
  have hsqrt_lo : (7 : ℝ) / 5 < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  -- A correlation bound `ρ₀ < g` with a nearly optimal straddling bound.
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    ((continuous_arccos.comp (by fun_prop : Continuous fun ρ : ℝ => (1 + 3 * ρ) / 4)
      ).continuousAt (x := g)) (π * ξ / 6) (by positivity)
  set ρ₀ := g - min η (1 / 4) / 2 with hρ₀
  have hmin : 0 < min η (1 / 4) := lt_min hη (by norm_num)
  have hρ₀g : ρ₀ < g := by
    rw [hρ₀]
    linarith
  have hρ₀low : 1 / 8 ≤ ρ₀ := by
    rw [hρ₀, hg]
    linarith [min_le_right η (1 / 4)]
  have hbound : straddleBound ρ₀ ≤ gaussianCoefficient + ξ / 4 := by
    have hdist : dist ρ₀ g < η := by
      rw [Real.dist_eq, hρ₀, abs_of_neg (by linarith)]
      linarith [min_le_left η (1 / 4)]
    have := hcont hdist
    simp only [Function.comp_apply, Real.dist_eq] at this
    have hle := (le_abs_self _).trans this.le
    rw [straddleBound, gaussianCoefficient_eq, ← hg, straddleBound]
    have hpi : 0 < π := pi_pos
    calc 3 / (2 * π) * arccos ((1 + 3 * ρ₀) / 4)
        ≤ 3 / (2 * π) * (arccos ((1 + 3 * g) / 4) + π * ξ / 6) := by
          gcongr
          linarith
      _ = 3 / (2 * π) * arccos ((1 + 3 * g) / 4) + ξ / 4 := by
          field_simp
          ring
  obtain ⟨q, R, hq0, hρ⟩ := exists_decay_radius hρ₀g
  -- The grid and the deviation slack.
  set ε := min (ξ / 12) (1 / 100) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by norm_num)
  set M : ℕ := ⌈720 / ξ⌉₊ + 1 with hM
  have hMpos : 0 < M := Nat.succ_pos _
  have hMR : 720 / ξ ≤ M := by
    rw [hM]
    push_cast
    linarith [Nat.le_ceil (720 / ξ)]
  refine ⟨q, R, ρ₀, 20, ε, M, hq0, hρ₀low, hρ, by norm_num, hεpos, hMpos, ?_⟩
  have hcoef := gaussianCoefficient_ge
  have hMpos' : (0 : ℝ) < M := by exact_mod_cast hMpos
  refine max_le ?_ ?_
  · have : ε ≤ 1 / 100 := min_le_right _ _
    linarith
  · have hεξ : ε ≤ ξ / 12 := min_le_left _ _
    have hsqrtpi : 2 ≤ √(2 * π) :=
      (le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [two_le_pi])
    have hgrid : 9 / 2 * (2 * 20 / M) / √(2 * π) ≤ ξ / 4 := by
      rw [div_le_iff₀ (by positivity)]
      calc 9 / 2 * (2 * 20 / (M : ℝ)) = 180 / M := by ring
        _ ≤ ξ / 2 := by
            rw [div_le_iff₀ hMpos']
            have := mul_le_mul_of_nonneg_left hMR hξ.le
            rw [mul_div_cancel₀ _ hξ.ne'] at this
            linarith
        _ ≤ ξ / 4 * √(2 * π) := by nlinarith
    linarith

/-! ### The layout bounds -/

/-- **Gaussian layouts of cubic multigraphs.** For every `ξ > 0`, every large enough loopless
multigraph in which every vertex has three edges, parallel edges allowed, has a layout of width at
most `(gaussianCoefficient + ξ) |V|`. -/
theorem exists_width_le_gaussianCoefficient {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (V E : Type*) [Finite V] [Finite E] (G : Multigraph V E), G.Loopless →
      (∀ v, (G.incidenceSet v).ncard = 3) → N₀ < Nat.card V →
        ∃ σ : Layout V, (G.width σ : ℝ) ≤ (gaussianCoefficient + ξ) * Nat.card V := by
  obtain ⟨q, R, ρ₀, T, ε, M, hq, hρ₀, hρ, hT, hε, hM, hbound⟩ := exists_parameters hξ
  refine ⟨⌈(3 * M + 3) * (vertexOverlap 3 R : ℝ) / ε ^ 2⌉₊, fun V E _ _ G hloop h3 hN => ?_⟩
  have large : (3 * M + 3) * (vertexOverlap 3 R : ℝ) / ε ^ 2 < Nat.card V :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast hN)
  obtain ⟨σ, hσ⟩ := exists_good_sample hloop h3 hq R (by linarith) hρ hT hε hM large
  refine ⟨σ, hσ.trans ?_⟩
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg _)

/-- **Gaussian layouts of cubic graphs.** For every `ξ > 0`, every large enough cubic graph on
`h` vertices has a layout of width at most `(gaussianCoefficient + ξ) h`, where
`gaussianCoefficient = (3 / (2π)) arccos ((1 + 2√2)/4)`. -/
theorem cubicLayoutBound_gaussian : CubicLayoutBound gaussianCoefficient := fun _ hξ =>
  (exists_width_le_gaussianCoefficient hξ).imp fun _ h V E _ _ G hloop _ h3 hN =>
    h V E G hloop h3 hN

/-- **Bisections of cubic multigraphs.** For every `ξ > 0`, every large enough loopless multigraph
whose vertices have three edges each, parallel edges allowed, has for every `k ≤ |V|` a set of `k`
vertices cut off by at most `(p + ξ) |V|` edges, where `p = (3/(2π)) arccos((1 + 2√2)/4)` is
`gaussianCoefficient`: take the first `k` vertices of a Gaussian layout. In particular its
bisection width is at most `(p + ξ) |V|`, with `p ≈ 0.1404`. -/
theorem exists_ncard_edgeCut_le {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (V E : Type*) [Finite V] [Finite E] (G : Multigraph V E), G.Loopless →
      (∀ v, (G.incidenceSet v).ncard = 3) → N₀ < Nat.card V → ∀ k ≤ Nat.card V,
        ∃ L : Set V, L.ncard = k ∧
          ((G.edgeCut L).ncard : ℝ) ≤ (gaussianCoefficient + ξ) * Nat.card V := by
  obtain ⟨N₀, hN₀⟩ := exists_width_le_gaussianCoefficient hξ
  refine ⟨N₀, fun V E _ _ G hloop h3 hN k hk => ?_⟩
  obtain ⟨σ, hσ⟩ := hN₀ V E G hloop h3 hN
  exact ⟨σ.initial k, σ.ncard_initial hk,
    (Nat.cast_le.mpr (G.ncard_frontier_le_width σ k)).trans hσ⟩

end Cslib.Circuits.Frontier.Gaussian

namespace Cslib.Circuits.Frontier

/-- **Gaussian layouts.** Connected, loopless multigraphs of maximum degree three have layouts of
width `(2p + o(1)) β₁ + o(|V|)`, where `β₁` is the cycle rank and
`p = (3 / (2π)) arccos ((1 + 2√2)/4)`, so `2p ≈ 0.2807`. -/
theorem layoutBound_gaussian : LayoutBound 3 (2 * Gaussian.gaussianCoefficient) :=
  LayoutBound.of_cubic Gaussian.gaussianCoefficient_pos.le Gaussian.cubicLayoutBound_gaussian

end Cslib.Circuits.Frontier
