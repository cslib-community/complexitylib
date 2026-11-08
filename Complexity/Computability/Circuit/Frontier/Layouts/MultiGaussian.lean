/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.MultiOrder
public import Complexity.Computability.Circuit.Frontier.Layouts.VertexGaussian

/-!
# Gaussian vertex layouts of multigraphs

Lay out a loopless multigraph `G` of maximum degree `d` by Gaussian vertex scores
(`Cslib.Circuits.Frontier.Gaussian.vertexScore`), sorting the vertices by score
(`Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_vertexScore`). The kernel rows are those
of the underlying simple graph, while the crossing events are indexed by the edges of `G`, so
parallel edges count with multiplicity.

Fix the grid `-T, -T + δ, ..., T` of `M` windows of width `δ = 2T / M`. Four families of counts
control the frontiers: the edges crossed at each grid threshold, the vertices scoring in each
window, and the vertices scoring in each tail. Each is a count of local events, which
concentrates by the second-moment bound, so for large `|V|` one sample keeps all of them within
`ε |V|` of their means (`Cslib.Circuits.Frontier.Gaussian.exists_multi_vertex_sample`). An edge is
crossed with probability at most `arccos ρ / π`, a vertex scores in a window with probability at
most `δ / √(2π)` and in a tail with probability at most `1 / T ^ 2`. As the parameters improve,
the width is at most `vertexCoefficient d · |E| + ξ |V|` for every `ξ > 0`
(`Cslib.Circuits.Frontier.Gaussian.exists_width_le_vertexCoefficient`).

## Main results

* `Cslib.Circuits.Frontier.Gaussian.exists_multi_vertex_sample`: a good sample.
* `Cslib.Circuits.Frontier.Gaussian.exists_width_le_vertexCoefficient`: Gaussian vertex layouts
  of large loopless multigraphs of maximum degree `d`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace Interval

namespace Cslib.Circuits.Frontier.Gaussian

variable {V E : Type*} {G : Multigraph V E} {q : ℝ}

/-- **A good sample.** Let `G` be a loopless multigraph of maximum degree `d ≥ 2`, and let `ρ`
be at most the truncated kernel bound `2 q / (1 + q ^ 2) - d ((d - 1) q ^ 2) ^ R`. If `G` has
more than `(M (d + 1) + 2) vertexOverlap d R / ε ^ 2` vertices, some sample of the Gaussian vertex
scores gives a layout of width at most
`(arccos ρ / π) |E| + |V| (d / T ^ 2 + d (2T / M) / √(2π) + (d + 1) ε)`. -/
theorem exists_multi_vertex_sample [Finite V] [Finite E] (hloop : G.Loopless) {d : ℕ}
    (hd : 2 ≤ d) (hdeg : G.MaxDegreeLE d) (hq : 0 ≤ q) (R : ℕ) {ρ : ℝ}
    (hρ : ρ ≤ 2 * q / (1 + q ^ 2) - d * ((d - 1) * q ^ 2) ^ R) {T ε : ℝ} (hT : 0 < T)
    (hε : 0 < ε) {M : ℕ} (hM : 0 < M)
    (large : (M * (d + 1) + 2) * (vertexOverlap d R : ℝ) / ε ^ 2 < Nat.card V) :
    ∃ σ : Layout V, (G.width σ : ℝ) ≤ arccos ρ / π * Nat.card E +
      Nat.card V * (d / T ^ 2 + d * (2 * T / M) / √(2 * π) + (d + 1) * ε) := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  set h : ℝ := ((Nat.card V : ℕ) : ℝ) with hh
  set m : ℝ := ((Nat.card E : ℕ) : ℝ) with hm
  set D : ℝ := ((vertexOverlap d R : ℕ) : ℝ)
  set δ : ℝ := 2 * T / M with hδ
  set c : ℝ := ε * h with hc
  set p : ℝ := arccos ρ / π with hp
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hhpos : 0 < h := lt_of_le_of_lt (by positivity) large
  have hcpos : 0 < c := by positivity
  have hδpos : 0 < δ := by positivity
  have hp0 : 0 ≤ p := div_nonneg (arccos_nonneg _) pi_pos.le
  have hmh : m ≤ d * h := by
    rw [hm, hh]
    exact_mod_cast G.card_le_mul_card hdeg
  have hcardV : (Fintype.card V : ℝ) = h := by rw [hh, Nat.card_eq_fintype_card]
  have hcardE : (Fintype.card E : ℝ) = m := by rw [hm, Nat.card_eq_fintype_card]
  have unit (v : V) : ‖unitKernelRow G.toSimpleGraph q R v‖ = 1 := norm_unitKernelRow q R v
  -- Each count deviates from its mean by `c` with probability `O(1 / h)`.
  have crossDev (t : ℝ) : P.real (deviation (crossingEvent G q R t) c) ≤ m * D / c ^ 2 := by
    have := measureReal_deviation_le (fun e => measurableSet_crossingEvent q R t e)
      (fun e => closedBall G.toSimpleGraph (G.src e) (R + 1))
      (fun e => dependsOn_crossingEvent q R t e)
      (fun e => card_not_disjoint_closedBall_src_le hdeg R e) hcpos
    rwa [hcardE] at this
  have vertexDev {f : ℝ → Prop} (hf : MeasurableSet {x | f x}) :
      P.real (deviation (vertexEvent G q R f) c) ≤ h * D / c ^ 2 := by
    have := measureReal_deviation_le (fun v => measurableSet_vertexEvent q R hf v)
      (fun v => closedBall G.toSimpleGraph v (R + 1)) (fun v => dependsOn_vertexEvent q R f v)
      (fun v => card_not_disjoint_closedBall_le hdeg (by omega) R v) hcpos
    rwa [hcardV] at this
  have hsmall : M * (m * D / c ^ 2 + h * D / c ^ 2) + h * D / c ^ 2 +
      h * D / c ^ 2 < 1 := by
    have hm' : m * D / c ^ 2 ≤ d * h * D / c ^ 2 := by gcongr
    have hcalc : (M * (d * h * D / c ^ 2 + h * D / c ^ 2) + h * D / c ^ 2 + h * D / c ^ 2) =
        (M * (d + 1) + 2) * D / ε ^ 2 / h := by
      rw [hc]
      field_simp
      ring
    have hlast : (M * (d + 1) + 2) * D / ε ^ 2 / h < 1 := (div_lt_one hhpos).mpr large
    nlinarith [mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg (α := ℝ) M)]
  obtain ⟨ω, hmid, hlow, hhigh⟩ := exists_sample_of_grid_bounds
    (fun i _ => crossDev (-T + i * δ))
    (fun i _ => vertexDev (f := fun x => -T + i * δ ≤ x ∧ x < -T + i * δ + δ)
      ((measurableSet_le measurable_const measurable_id).inter
        (measurableSet_lt measurable_id measurable_const)))
    (vertexDev (f := (· < -T)) (measurableSet_lt measurable_id measurable_const))
    (vertexDev (f := (T ≤ ·)) (measurableSet_le measurable_const measurable_id)) hsmall
  set score := vertexScore G q R ω
  set B := p * m + h * (d / T ^ 2 + d * δ / √(2 * π) + (d + 1) * ε)
  have vertexMean {f : ℝ → Prop} {b : ℝ} (hb : ∀ v, P.real (vertexEvent G q R f v) ≤ b) :
      ∑ v, P.real (vertexEvent G q R f v) ≤ h * b :=
    (Finset.sum_le_sum fun v _ => hb v).trans_eq
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardV])
  -- A tail count is below its mean plus `c`.
  have tail (f : ℝ → Prop) (hf : ∀ x, f x → T ≤ |x|)
      (hdev : ω ∉ deviation (vertexEvent G q R f) c) :
      d * ({v | ω ∈ vertexEvent G q R f v}.ncard : ℝ) ≤ B := by
    have hcount := ncard_lt_of_notMem_deviation hdev
    have hmean : ∑ v, P.real (vertexEvent G q R f v) ≤ h * (1 / T ^ 2) :=
      vertexMean fun v => (measureReal_mono (μ := P) fun ω' hω' => hf _ hω').trans
        (measureReal_le_abs_le (unit v) hT)
    have hbound : ({v | ω ∈ vertexEvent G q R f v}.ncard : ℝ) ≤ h / T ^ 2 + c := by grind
    have hmult := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg (α := ℝ) d)
    have hnonneg : 0 ≤ p * m + h * (d * δ / √(2 * π) + ε) := by positivity
    have hidentity : B = d * (h / T ^ 2 + c) + (p * m + h * (d * δ / √(2 * π) + ε)) := by
      simp only [B, hc]
      ring
    rw [hidentity]
    linarith
  -- The edges leaving a threshold set are those crossed at the threshold.
  have crossCount (t : ℝ) : (G.edgeCut {v | score v < t}).ncard =
      {e | ω ∈ crossingEvent G q R t e}.ncard := by
    congr 1
    ext e
    simp only [Multigraph.mem_edgeCut, crossingEvent, mem_ofPred_eq, mem_uIoc, ← not_lt]
    tauto
  have htop : -T + M * δ = T := by
    rw [hδ]
    field_simp
    ring
  obtain ⟨σ, hσ⟩ := G.exists_width_le_of_vertexScore hdeg score hδpos M (a := -T) (B := B)
    (tail (· < -T) (fun x hx => by rw [abs_of_neg (by linarith)]; linarith) hlow)
    (by
      rw [htop]
      exact tail (T ≤ ·) (fun x hx => hx.trans (le_abs_self x)) hhigh)
    (by
      intro i hi
      have hthr : -T + ((i : ℝ) + 1) * δ = -T + i * δ + δ := by ring
      rw [hthr]
      have hC := ncard_lt_of_notMem_deviation (hmid i hi).1
      have hW := ncard_lt_of_notMem_deviation (hmid i hi).2
      have hCm : ∑ e, P.real (crossingEvent G q R (-T + i * δ) e) ≤ m * p :=
        (Finset.sum_le_sum fun e _ => measureReal_crossingEvent_le hloop hd hdeg hq R hρ
          (-T + i * δ) e).trans_eq
            (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardE])
      have hWm := vertexMean (f := fun x => -T + i * δ ≤ x ∧ x < -T + i * δ + δ)
        (b := δ / √(2 * π)) fun v => measureReal_window_le (unit v) (-T + i * δ) hδpos.le
      have h1 : ((G.edgeCut {v | score v < -T + i * δ}).ncard : ℝ) ≤ m * p + c := by
        rw [crossCount]
        linarith
      have h2 : ({v | -T + i * δ ≤ score v ∧ score v < -T + i * δ + δ}.ncard : ℝ) ≤
          h * (δ / √(2 * π)) + c := by
        have : ({v | -T + i * δ ≤ score v ∧ score v < -T + i * δ + δ}.ncard : ℝ) <
            ∑ v, P.real (vertexEvent G q R (fun x => -T + i * δ ≤ x ∧ x < -T + i * δ + δ) v) +
              c := hW
        linarith
      have hmult := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) d)
      have hnonneg : 0 ≤ h * (d / T ^ 2) := by positivity
      have hidentity : B = (m * p + c) + d * (h * (δ / √(2 * π)) + c) + h * (d / T ^ 2) := by
        simp only [B, hc]
        ring
      rw [hidentity]
      linarith)
  exact ⟨σ, hσ⟩

/-- **Gaussian vertex layouts of multigraphs.** For every `ξ > 0`, every large enough loopless
multigraph of maximum degree `d ≥ 2` has a layout of width at most
`vertexCoefficient d · |E| + ξ |V|`, parallel edges counted with multiplicity. -/
theorem exists_width_le_vertexCoefficient {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (V E : Type*) [Finite V] [Finite E] (G : Multigraph V E), G.Loopless →
      G.MaxDegreeLE d → N₀ < Nat.card V →
        ∃ σ : Layout V, (G.width σ : ℝ) ≤ vertexCoefficient d * Nat.card E + ξ * Nat.card V := by
  set D : ℝ := (d : ℝ)
  have hD : 2 ≤ D := by
    simp only [D]
    exact_mod_cast hd
  set g := vertexCorrelation d
  have hg : 0 < g := vertexCorrelation_pos hd
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    (continuous_arccos.continuousAt (x := g)) (π * ξ / (4 * D)) (by positivity)
  set ρ := g - min η g / 2
  have hmin : 0 < min η g := lt_min hη hg
  have hρg : ρ < g := by
    simp only [ρ]
    linarith
  have hcoef : arccos ρ / π ≤ vertexCoefficient d + ξ / (4 * D) := by
    have hdist : dist ρ g < η := by
      rw [Real.dist_eq, show ρ - g = -(min η g / 2) by simp only [ρ]; ring, abs_neg,
        abs_of_pos (by positivity)]
      linarith [min_le_left η g]
    have H := (le_abs_self _).trans (hcont hdist).le
    rw [div_le_iff₀ pi_pos]
    have heq : (arccos g / π + ξ / (4 * D)) * π = arccos g + π * ξ / (4 * D) := by
      field_simp
    rw [vertexCoefficient, show vertexCorrelation d = g from rfl, heq]
    linarith
  obtain ⟨q, R, hq, hcorr⟩ := exists_decay_radius_degree hd hρg
  set T := 1 + 4 * D / ξ
  set ε := ξ / (4 * (D + 1))
  set M : ℕ := ⌈8 * D * T / ξ⌉₊ + 1
  have hT : 0 < T := by positivity
  have hε : 0 < ε := by positivity
  have hM : 0 < M := Nat.succ_pos _
  have hMR : 8 * D * T / ξ ≤ (M : ℝ) := by
    simp only [M]
    push_cast
    linarith [Nat.le_ceil (8 * D * T / ξ)]
  have htail : D / T ^ 2 ≤ ξ / 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos hT)]
    have hx : 0 ≤ 4 * D / ξ := by positivity
    have hsq : 4 * D / ξ ≤ T ^ 2 := by
      simp only [T]
      nlinarith [sq_nonneg (4 * D / ξ)]
    have H := mul_le_mul_of_nonneg_left hsq hξ.le
    rw [mul_div_cancel₀ _ hξ.ne'] at H
    linarith
  have hgrid : D * (2 * T / M) / √(2 * π) ≤ ξ / 4 := by
    have hsqrt : 1 ≤ √(2 * π) :=
      (le_sqrt (by norm_num) (by positivity)).mpr (by linarith [two_le_pi])
    have hfrac : D * (2 * T / M) ≤ ξ / 4 := by
      rw [← mul_div_assoc, div_le_iff₀ (by exact_mod_cast hM : (0 : ℝ) < M)]
      have H := (div_le_iff₀ hξ).mp hMR
      linarith
    exact (div_le_self (by positivity) hsqrt).trans hfrac
  have herr : D / T ^ 2 + D * (2 * T / M) / √(2 * π) + (D + 1) * ε ≤ 3 * ξ / 4 := by
    have heq : (D + 1) * ε = ξ / 4 := by
      simp only [ε]
      field_simp
    linarith
  refine ⟨⌈(M * (D + 1) + 2) * (vertexOverlap d R : ℝ) / ε ^ 2⌉₊,
    fun V E _ _ G hl hdeg large => ?_⟩
  have hlarge : (M * (D + 1) + 2) * (vertexOverlap d R : ℝ) / ε ^ 2 < Nat.card V :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast large)
  obtain ⟨σ, hσ⟩ := exists_multi_vertex_sample hl hd hdeg hq R hcorr hT hε hM hlarge
  refine ⟨σ, hσ.trans ?_⟩
  have hE : (Nat.card E : ℝ) ≤ D * Nat.card V := by
    simp only [D]
    exact_mod_cast G.card_le_mul_card hdeg
  have herror : ξ / (4 * D) * Nat.card E ≤ ξ / 4 * Nat.card V := by
    have h := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ ξ / (4 * D))
    convert h using 1
    field_simp
  have h1 := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) (Nat.card E))
  have h2 := mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg (α := ℝ) (Nat.card V))
  nlinarith

end Cslib.Circuits.Frontier.Gaussian
