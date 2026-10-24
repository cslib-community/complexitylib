/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.Gaussian.Straddle

/-!
# One sample controls every frontier of the median layout

Let `G` be a loopless multigraph on `h` vertices in which every vertex has three edges, so that
it has `3h/2` edges. Score its edges by a Gaussian sample and lay out its vertices by the medians
of their scores (`Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_edgeScore`), with the grid
`-T, -T + δ, ..., T` of `M` windows of width `δ = 2T / M`. Four families of counts control the
frontiers: the vertices straddling each grid threshold, the edges scoring in each window, and the
edges scoring in each tail.

Each count is a sum of indicators of local events, which concentrates by the second-moment bound
(`Cslib.Circuits.Frontier.Gaussian.measureReal_deviation_le`): it deviates from its mean by
`ε h` with probability `O(1 / (ε ^ 2 h))`. So for large `h` a union bound over the `2M + 2`
counts leaves a sample at which all of them are within `ε h` of their means
(`exists_concentrated_sample`). The means are at most `μ h` straddling vertices at each
threshold, `(3h/2) δ / √(2π)` edges in each window and `(3h/2) / T ^ 2` edges in each tail, so
the width is at most `h · cubicBoundOfMean μ T ε M`
(`Cslib.Circuits.Frontier.Gaussian.exists_good_sample_of_mean`), and with the straddling bound,
`h · cubicBound ρ₀ T ε M` (`Cslib.Circuits.Frontier.Gaussian.exists_good_sample`).

## Main definitions

* `Cslib.Circuits.Frontier.Gaussian.edgeScoreEvent`: an event about the score of one edge.
* `Cslib.Circuits.Frontier.Gaussian.cubicBound`,
  `Cslib.Circuits.Frontier.Gaussian.cubicBoundOfMean`: the width per vertex of the median layout
  of a good sample.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.exists_good_sample_of_mean`,
  `Cslib.Circuits.Frontier.Gaussian.exists_good_sample`: a good sample.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace Cslib.Circuits.Frontier.Gaussian

/-- The width per vertex of the median layout of a good sample, when the expected number of
vertices straddling any threshold is at most `μ` per vertex: the tails beyond `T`, the windows of
width `2T / M`, and deviations `ε` per vertex. -/
noncomputable def cubicBoundOfMean (μ T ε : ℝ) (M : ℕ) : ℝ :=
  max (9 / (2 * T ^ 2) + 3 * ε) (μ + 9 / 2 * (2 * T / M) / √(2 * π) + 4 * ε)

/-- The width per vertex of the median layout of a good sample, when adjacent kernel rows have
inner product at least `ρ₀`. -/
noncomputable def cubicBound (ρ₀ T ε : ℝ) (M : ℕ) : ℝ :=
  cubicBoundOfMean (straddleBound ρ₀) T ε M

variable {V E : Type*} [Fintype V] (G : Multigraph V E)

/-- The event that the score of `e` satisfies `p`. -/
def edgeScoreEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (e : E) : Set (V → ℝ) :=
  {ω | p (edgeScore G q R ω e)}

variable {G} {q : ℝ} {R : ℕ}

private theorem measurableSet_edgeScoreEvent (q : ℝ) (R : ℕ) {p : ℝ → Prop}
    (hp : MeasurableSet {x | p x}) (e : E) : MeasurableSet (edgeScoreEvent G q R p e) :=
  measurable_edgeScore q R e hp

/-- An event about the score of `e` depends only on the coordinates of the sample in the closed
ball of radius `R + 1` around the source of `e`. -/
private theorem dependsOn_edgeScoreEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (e : E) :
    DependsOn (· ∈ edgeScoreEvent G q R p e) (closedBall G.toSimpleGraph (G.src e) (R + 1)) := by
  intro ω ω' hω
  simp only [edgeScoreEvent, mem_ofPred_eq, edgeScore_congr (Or.inl rfl) hω]

/-- The handshake lemma for a loopless multigraph whose vertices have three edges:
`|E| = 3 |V| / 2`. -/
private theorem card_edges_eq [Fintype E] (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) :
    (Fintype.card E : ℝ) = 3 / 2 * Fintype.card V := by
  have hsum := G.sum_ncard_incidenceSet hloop
  simp only [h3, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have : ((Fintype.card V * 3 : ℕ) : ℝ) = ((2 * Nat.card E : ℕ) : ℝ) := by exact_mod_cast hsum
  rw [← Nat.card_eq_fintype_card (α := E)]
  push_cast at this
  linarith

/-- **Concentration.** For a large loopless multigraph whose vertices have three edges, some
sample keeps the four families of counts of the median layout within `ε |V|` of their means. -/
private theorem exists_concentrated_sample [Fintype E] (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (q : ℝ) (R : ℕ) (T : ℝ) {ε : ℝ} (hε : 0 < ε)
    (M : ℕ) (large : (3 * M + 3) * (vertexOverlap 3 R : ℝ) / ε ^ 2 < Fintype.card V) :
    ∃ ω, (∀ i < M,
        ω ∉ deviation (straddleEvent G q R (-T + i * (2 * T / M))) (ε * Fintype.card V) ∧
        ω ∉ deviation (edgeScoreEvent G q R fun x =>
          -T + i * (2 * T / M) ≤ x ∧ x < -T + i * (2 * T / M) + 2 * T / M)
          (ε * Fintype.card V)) ∧
      ω ∉ deviation (edgeScoreEvent G q R (· < -T)) (ε * Fintype.card V) ∧
      ω ∉ deviation (edgeScoreEvent G q R (T ≤ ·)) (ε * Fintype.card V) := by
  classical
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  set h : ℝ := (Fintype.card V : ℝ)
  set D : ℝ := ((vertexOverlap 3 R : ℕ) : ℝ)
  set c : ℝ := ε * h with hc
  have hhpos : 0 < h := lt_of_le_of_lt (by positivity) large
  have hcpos : 0 < c := by positivity
  have hdeg : G.MaxDegreeLE 3 := fun v => (h3 v).le
  have hE := card_edges_eq hloop h3
  -- Each count deviates from its mean by `c` with probability `O(1 / h)`.
  have devSt (t : ℝ) : P.real (deviation (straddleEvent G q R t) c) ≤ h * D / c ^ 2 :=
    measureReal_deviation_le (fun v => measurableSet_straddleEvent q R t v)
      (fun v => closedBall G.toSimpleGraph v (R + 1)) (fun v => dependsOn_straddleEvent q R t v)
      (fun v => card_not_disjoint_closedBall_le hdeg (by norm_num) R v) hcpos
  have devE {p : ℝ → Prop} (hp : MeasurableSet {x | p x}) :
      P.real (deviation (edgeScoreEvent G q R p) c) ≤ 3 / 2 * h * D / c ^ 2 := by
    have := measureReal_deviation_le (fun e => measurableSet_edgeScoreEvent q R hp e)
      (fun e => closedBall G.toSimpleGraph (G.src e) (R + 1))
      (fun e => dependsOn_edgeScoreEvent q R p e)
      (fun e => card_not_disjoint_closedBall_src_le hdeg R e) hcpos
    rwa [hE] at this
  set δ := 2 * T / M
  have hsmall : M * (h * D / c ^ 2 + 3 / 2 * h * D / c ^ 2) + 3 / 2 * h * D / c ^ 2 +
      3 / 2 * h * D / c ^ 2 < 1 := by
    have key : (M * (h * D / c ^ 2 + 3 / 2 * h * D / c ^ 2) + 3 / 2 * h * D / c ^ 2 +
        3 / 2 * h * D / c ^ 2) = (5 / 2 * M + 3) * D / ε ^ 2 / h := by
      rw [hc]
      field_simp
      ring
    rw [key, div_lt_one hhpos]
    calc (5 / 2 * (M : ℝ) + 3) * D / ε ^ 2 ≤ (3 * M + 3) * D / ε ^ 2 := by
          gcongr
          linarith
      _ < h := large
  exact exists_sample_of_grid_bounds (fun i _ => devSt _)
    (fun i _ => devE ((measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)))
    (devE (measurableSet_lt measurable_id measurable_const))
    (devE (measurableSet_le measurable_const measurable_id)) hsmall

/-- **A good sample, from the mean of the straddling counts.** Let `G` be a loopless multigraph
whose vertices have three edges, let adjacent kernel rows have inner product above `-1`, and let
every threshold be straddled by at most `μ |V|` vertices in expectation. If `G` has more than
`(3 M + 3) vertexOverlap 3 R / ε ^ 2` vertices, some Gaussian sample gives a median layout of
width at most `|V| · cubicBoundOfMean μ T ε M`. -/
theorem exists_good_sample_of_mean [Finite E] (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (hq : 0 ≤ q) (R : ℕ) {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    {M : ℕ} (hM : 0 < M) (large : (3 * M + 3) * (vertexOverlap 3 R : ℝ) / ε ^ 2 < Nat.card V)
    {μ : ℝ} (hmean : ∀ t, ∑ v, (Measure.pi fun _ : V => gaussianReal 0 1).real
      (straddleEvent G q R t v) ≤ Nat.card V * μ) :
    ∃ σ : Layout V, (G.width σ : ℝ) ≤ Nat.card V * cubicBoundOfMean μ T ε M := by
  classical
  have := Fintype.ofFinite E
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  set h : ℝ := ((Nat.card V : ℕ) : ℝ) with hh
  set δ : ℝ := 2 * T / M with hδ
  set c : ℝ := ε * h with hc
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hδpos : 0 < δ := by positivity
  have hhpos : 0 < h := lt_of_le_of_lt (by positivity) large
  have hdeg : G.MaxDegreeLE 3 := fun v => (h3 v).le
  have unit (e : E) : ‖edgeVector G q R e‖ = 1 := norm_edgeVector hloop hdeg hq hρ₀ hρ e
  have hE : (Fintype.card E : ℝ) = 3 / 2 * h := by
    rw [card_edges_eq hloop h3, hh, Nat.card_eq_fintype_card]
  obtain ⟨ω, hmid, hlow, hhigh⟩ := exists_concentrated_sample hloop h3 q R T hε M
    (by rwa [← Nat.card_eq_fintype_card])
  rw [← Nat.card_eq_fintype_card] at hmid hlow hhigh
  set B := h * cubicBoundOfMean μ T ε M
  have hB1 : h * (9 / (2 * T ^ 2) + 3 * ε) ≤ B :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hhpos.le
  have hB2 : h * (μ + 9 / 2 * δ / √(2 * π) + 4 * ε) ≤ B :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hhpos.le
  -- A tail count is below its mean plus `c`.
  have tail (p : ℝ → Prop) (hp : ∀ x, p x → T ≤ |x|)
      (hdev : ω ∉ deviation (edgeScoreEvent G q R p) c) :
      3 * ({e | ω ∈ edgeScoreEvent G q R p e}.ncard : ℝ) ≤ B := by
    have hcount := ncard_lt_of_notMem_deviation hdev
    have hmean : ∑ e, P.real (edgeScoreEvent G q R p e) ≤ 3 / 2 * h * (1 / T ^ 2) := by
      refine (Finset.sum_le_sum fun e _ => (measureReal_mono (μ := P) fun ω' hω' =>
        hp _ hω').trans (measureReal_le_abs_le (unit e) hT)).trans_eq ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hE]
    refine le_trans ?_ hB1
    have : 3 / 2 * h * (1 / T ^ 2) * 3 = h * (9 / (2 * T ^ 2)) := by
      field_simp
      ring
    nlinarith
  obtain ⟨σ, hσ⟩ := Multigraph.exists_width_le_of_edgeScore h3 (edgeScore G q R ω) hδpos M
    (a := -T) (B := B)
    (tail (· < -T) (fun x hx => by rw [abs_of_neg (by linarith)]; linarith) hlow) (by
      have hT' : -T + M * δ = T := by
        rw [hδ]
        field_simp
        ring
      rw [hT']
      exact tail (T ≤ ·) (fun x hx => hx.trans (le_abs_self x)) hhigh) (by
      intro i hi
      have hthr : -T + ((i : ℝ) + 1) * δ = -T + i * δ + δ := by ring
      rw [hthr]
      have hS := ncard_lt_of_notMem_deviation (hmid i hi).1
      have hW := ncard_lt_of_notMem_deviation (hmid i hi).2
      have hWmean : ∑ e, P.real (edgeScoreEvent G q R
          (fun x => -T + i * δ ≤ x ∧ x < -T + i * δ + δ) e) ≤ 3 / 2 * h * (δ / √(2 * π)) := by
        refine (Finset.sum_le_sum fun e _ =>
          measureReal_window_le (unit e) (-T + i * δ) hδpos.le).trans_eq ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hE]
      have hSmean := hmean (-T + i * δ)
      calc ({v | G.EdgeStraddles (edgeScore G q R ω) (-T + i * δ) v}.ncard : ℝ) +
            3 * {e | -T + i * δ ≤ edgeScore G q R ω e ∧
              edgeScore G q R ω e < -T + i * δ + δ}.ncard
          ≤ (h * μ + c) + 3 * (3 / 2 * h * (δ / √(2 * π)) + c) := by
            have h1 : ({v | G.EdgeStraddles (edgeScore G q R ω) (-T + i * δ) v}.ncard : ℝ) <
                ∑ v, P.real (straddleEvent G q R (-T + i * δ) v) + c := hS
            have h2 : ({e | -T + i * δ ≤ edgeScore G q R ω e ∧
                edgeScore G q R ω e < -T + i * δ + δ}.ncard : ℝ) <
                ∑ e, P.real (edgeScoreEvent G q R
                  (fun x => -T + i * δ ≤ x ∧ x < -T + i * δ + δ) e) + c := hW
            linarith
        _ = h * (μ + 9 / 2 * δ / √(2 * π) + 4 * ε) := by
            rw [hc]
            ring
        _ ≤ B := hB2)
  exact ⟨σ, hσ⟩

omit [Fintype V] in
/-- **A good sample.** Let `G` be a loopless multigraph whose vertices have three edges, and let
adjacent kernel rows have inner product at least `ρ₀ ≥ 0`. If `G` has more than
`(3 M + 3) vertexOverlap 3 R / ε ^ 2` vertices, some Gaussian sample gives a median layout of
width at most `|V| · cubicBound ρ₀ T ε M`. -/
theorem exists_good_sample [Finite V] [Finite E] (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (hq : 0 ≤ q) (R : ℕ) {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    {M : ℕ} (hM : 0 < M) (large : (3 * M + 3) * (vertexOverlap 3 R : ℝ) / ε ^ 2 < Nat.card V) :
    ∃ σ : Layout V, (G.width σ : ℝ) ≤ Nat.card V * cubicBound ρ₀ T ε M := by
  have := Fintype.ofFinite V
  refine exists_good_sample_of_mean hloop h3 hq R (by linarith) hρ hT hε hM large fun t => ?_
  refine (Finset.sum_le_sum fun v _ =>
    measureReal_straddleEvent_le hloop h3 hq hρ₀ hρ t v).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

end Cslib.Circuits.Frontier.Gaussian
