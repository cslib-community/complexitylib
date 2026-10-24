/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.Kernel
public import Complexity.Computability.Circuit.Frontier.Layouts.Support
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
import Complexity.Foundations.Combinatorics.SimpleGraph.Metric
import Complexity.Foundations.Probability.Gaussian.Multivariate
import Complexity.Foundations.Probability.Gaussian.Sheppard
import Complexity.Foundations.Probability.SecondMoment

/-!
# Shared estimates of the Gaussian layouts

The Gaussian layouts score the vertices, or the edges, of a multigraph `G` by inner products of
vectors built from the unit kernel rows of its underlying simple graph `H`
(`Cslib.Circuits.Frontier.Gaussian.unitKernelRow`) with a sample `ω` of independent standard
Gaussians, one per vertex. This file collects the estimates shared by the vertex scores and the
edge scores.

* **Locality.** The scores at a vertex `v` depend only on the coordinates of `ω` in the closed
  ball of radius `R + 1` around `v` (`closedBall`). In maximum degree `d` such a ball meets at
  most `vertexOverlap d R` of the balls around the vertices, and as many around the sources of
  the edges.
* **Concentration.** The number of local events that occur deviates from its mean by `c` with
  probability `O(|events| / c ^ 2)` (`measureReal_deviation_le`).
* **Projections.** The product of standard Gaussians on `V → ℝ` is carried to the standard
  Gaussian measure of `EuclideanSpace ℝ V`, so a unit projection lands in a window of width `δ`
  with probability at most `δ / √(2π)` (`measureReal_window_le`), beyond `T` with probability at
  most `1 / T ^ 2` (`measureReal_le_abs_le`), and two projections of equal norm are separated by
  a threshold with probability at most their angle over `π` (`measureReal_mem_uIoc_le`, Sheppard's
  bound [Sheppard1899]).
* **Correlations.** In maximum degree `d`, the unit kernel rows of adjacent vertices have inner
  product at least `2 q / (1 + q ^ 2) - d ((d - 1) q ^ 2) ^ R`, and every value below
  `2 √(d - 1) / d` (`vertexCorrelation`) is reached (`exists_decay_radius_degree`).

## Main definitions

* `Cslib.Circuits.Frontier.Gaussian.closedBall`: the closed ball of a simple graph.
* `Cslib.Circuits.Frontier.Gaussian.vertexOverlap`: the overlap bound of the balls.
* `Cslib.Circuits.Frontier.Gaussian.deviation`: the event that a count of events deviates from
  its mean.
* `Cslib.Circuits.Frontier.Gaussian.vertexCorrelation`: the limiting correlation of adjacent
  kernel rows in maximum degree `d`.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.closedBall_tgt_subset`: the ends of an edge are within
  distance one.
* `Cslib.Circuits.Frontier.Gaussian.card_not_disjoint_closedBall_le`,
  `Cslib.Circuits.Frontier.Gaussian.card_not_disjoint_closedBall_src_le`: overlapping balls.
* `Cslib.Circuits.Frontier.Gaussian.measureReal_deviation_le`: concentration of counts of local
  events.
* `Cslib.Circuits.Frontier.Gaussian.measureReal_window_le`,
  `Cslib.Circuits.Frontier.Gaussian.measureReal_le_abs_le`,
  `Cslib.Circuits.Frontier.Gaussian.measureReal_mem_uIoc_le`: windows, tails and crossings.
* `Cslib.Circuits.Frontier.Gaussian.le_inner_unitKernelRow_src_tgt`: the correlation of the rows
  at the ends of an edge.
* `Cslib.Circuits.Frontier.Gaussian.exists_decay_radius_degree`: every correlation below
  `vertexCorrelation d` is reached.

## References

* [W. F. Sheppard, *On the application of the theory of error to cases of normal distribution
  and normal correlation*][Sheppard1899]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace Interval

namespace Cslib.Circuits.Frontier.Gaussian

/-- The closed ball of radius `r` around `v` in a simple graph, for the extended distance. -/
def closedBall {V : Type*} (H : SimpleGraph V) (v : V) (r : ℕ) : Set V :=
  {z | H.edist v z ≤ r}

/-- The number of closed balls of radius `R + 1` that may meet a given one, around the vertices
or around the sources of the edges of a multigraph of maximum degree `d`. -/
def vertexOverlap (d R : ℕ) : ℕ :=
  d * (d + 1) ^ (2 * R + 2)

/-! ### Locality -/

section Locality

variable {V E : Type*} [Fintype V] {G : Multigraph V E}

omit [Fintype V] in
/-- Closed balls of radius `r` around `v` and `w` meet only when `w` is within `2 r` of `v`. -/
private theorem edist_le_of_not_disjoint {v w : V} {r : ℕ}
    (h : ¬Disjoint (closedBall G.toSimpleGraph v r) (closedBall G.toSimpleGraph w r)) :
    G.toSimpleGraph.edist v w ≤ ((2 * r : ℕ) : ℕ∞) := by
  obtain ⟨z, hvz, hwz⟩ := not_disjoint_iff.mp h
  calc G.toSimpleGraph.edist v w ≤ G.toSimpleGraph.edist v z + G.toSimpleGraph.edist z w :=
        SimpleGraph.edist_triangle
    _ = G.toSimpleGraph.edist v z + G.toSimpleGraph.edist w z := by
        rw [SimpleGraph.edist_comm (u := z)]
    _ ≤ r + r := add_le_add hvz hwz
    _ = ((2 * r : ℕ) : ℕ∞) := by push_cast; ring

omit [Fintype V] in
/-- The closed ball of radius `r` around the target of an edge lies in the closed ball of radius
`r + 1` around its source. -/
theorem closedBall_tgt_subset (e : E) (r : ℕ) :
    closedBall G.toSimpleGraph (G.tgt e) r ⊆ closedBall G.toSimpleGraph (G.src e) (r + 1) := by
  intro z (hz : G.toSimpleGraph.edist (G.tgt e) z ≤ r)
  have h : G.toSimpleGraph.edist (G.src e) z ≤ G.toSimpleGraph.edist (G.tgt e) z + 1 := by
    by_cases hst : G.src e = G.tgt e
    · rw [hst]
      exact le_self_add
    · exact SimpleGraph.Adj.edist_le_edist_add_one
        (Multigraph.toSimpleGraph_adj.mpr ⟨hst, e, rfl⟩) z
  change G.toSimpleGraph.edist (G.src e) z ≤ ((r + 1 : ℕ) : ℕ∞)
  push_cast
  exact h.trans (add_le_add_left hz 1)

variable [Finite E] {d : ℕ}

open Classical in
/-- In a multigraph of maximum degree `d ≥ 1`, a closed ball of radius `R + 1` meets at most
`vertexOverlap d R` of the closed balls of radius `R + 1` around the vertices. -/
theorem card_not_disjoint_closedBall_le (hdeg : G.MaxDegreeLE d) (hd : 1 ≤ d) (R : ℕ) (v : V) :
    (Finset.univ.filter fun w => ¬Disjoint (closedBall G.toSimpleGraph v (R + 1))
      (closedBall G.toSimpleGraph w (R + 1))).card ≤ vertexOverlap d R := by
  refine (Finset.card_le_card fun w hw => ?_).trans
    ((SimpleGraph.card_edist_le_le hdeg.degree_toSimpleGraph_le v (2 * (R + 1))).trans ?_)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,
      edist_le_of_not_disjoint (Finset.mem_filter.mp hw).2⟩
  · rw [vertexOverlap, show 2 * (R + 1) = 2 * R + 2 by ring]
    exact Nat.le_mul_of_pos_left _ hd

open Classical in
omit [Fintype V] in
/-- In a multigraph of maximum degree `d`, the closed ball of radius `R + 1` around the source of
an edge meets at most `vertexOverlap d R` of the closed balls of radius `R + 1` around the sources
of the edges. -/
theorem card_not_disjoint_closedBall_src_le [Finite V] [Fintype E] (hdeg : G.MaxDegreeLE d)
    (R : ℕ) (e : E) :
    (Finset.univ.filter fun l => ¬Disjoint (closedBall G.toSimpleGraph (G.src e) (R + 1))
      (closedBall G.toSimpleGraph (G.src l) (R + 1))).card ≤ vertexOverlap d R := by
  have := Fintype.ofFinite V
  refine (Finset.card_le_mul_card_image_of_maps_to (f := G.src)
    (t := Finset.univ.filter fun w =>
      G.toSimpleGraph.edist (G.src e) w ≤ ((2 * (R + 1) : ℕ) : ℕ∞))
    (fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      edist_le_of_not_disjoint (Finset.mem_filter.mp hl).2⟩) d fun w _ => ?_).trans ?_
  · rw [← ncard_coe_finset]
    exact (ncard_le_ncard fun l hl => Or.inl (Finset.mem_filter.mp hl).2).trans (hdeg w)
  · rw [vertexOverlap, show 2 * R + 2 = 2 * (R + 1) by ring]
    exact Nat.mul_le_mul_left d
      (SimpleGraph.card_edist_le_le hdeg.degree_toSimpleGraph_le (G.src e) (2 * (R + 1)))

end Locality

/-! ### Deviations of counts -/

section Deviations

variable {Ω κ : Type*} [Fintype κ]

/-- The number of events that occur is the sum of their indicators. -/
private theorem ncard_eq_sum_indicator (A : κ → Set Ω) (ω : Ω) :
    ({k | ω ∈ A k}.ncard : ℝ) = ∑ k, (A k).indicator (1 : Ω → ℝ) ω := by
  classical
  simp only [indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole, ← ncard_coe_finset, Finset.coe_filter_univ]

/-- Outside the event that the number of events that occur deviates from `m` by at least `c`,
this number is below `m + c`. -/
private theorem ncard_lt_of_not_le_abs {A : κ → Set Ω} {ω : Ω} {m c : ℝ}
    (h : ¬c ≤ |∑ k, (A k).indicator (1 : Ω → ℝ) ω - m|) : ({k | ω ∈ A k}.ncard : ℝ) < m + c := by
  rw [ncard_eq_sum_indicator]
  linarith [le_abs_self (∑ k, (A k).indicator (1 : Ω → ℝ) ω - m), not_le.mp h]

/-- Simultaneously avoid two families of grid events and both tail events when their
probability bounds sum to less than one. -/
theorem exists_sample_of_grid_bounds {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A B : ℕ → Set Ω} {C D : Set Ω} {a b c d : ℝ} {M : ℕ}
    (hA : ∀ i < M, P.real (A i) ≤ a) (hB : ∀ i < M, P.real (B i) ≤ b)
    (hC : P.real C ≤ c) (hD : P.real D ≤ d)
    (hsmall : M * (a + b) + c + d < 1) :
    ∃ ω, (∀ i < M, ω ∉ A i ∧ ω ∉ B i) ∧ ω ∉ C ∧ ω ∉ D := by
  let bad := ((⋃ i ∈ Finset.range M, A i ∪ B i) ∪ C) ∪ D
  have hbound : P.real bad ≤ M * (a + b) + c + d := by
    refine (measureReal_union_le _ _).trans (add_le_add ?_ hD)
    refine (measureReal_union_le _ _).trans (add_le_add ?_ hC)
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      Finset.sum_le_sum (fun i hi => (measureReal_union_le _ _).trans
        (add_le_add (hA i (Finset.mem_range.mp hi)) (hB i (Finset.mem_range.mp hi))))
  have hbad : ∃ ω, ω ∉ bad := by
    by_contra! hall
    have hlt := hbound.trans_lt hsmall
    rw [Set.eq_univ_of_forall hall, probReal_univ] at hlt
    exact lt_irrefl _ hlt
  simpa only [bad, mem_union, mem_iUnion, Finset.mem_range, not_or, not_exists,
    and_assoc] using hbad

variable {V : Type*} [Fintype V]

/-- The event that the number of the events `A k` that occur deviates from its mean under the
product of standard Gaussians by at least `c`. -/
def deviation (A : κ → Set (V → ℝ)) (c : ℝ) : Set (V → ℝ) :=
  {ω | c ≤ |∑ k, (A k).indicator (1 : (V → ℝ) → ℝ) ω -
    ∑ k, (Measure.pi fun _ : V => gaussianReal 0 1).real (A k)|}

/-- Outside the deviation event, the number of events that occur is below its mean plus `c`. -/
theorem ncard_lt_of_notMem_deviation {A : κ → Set (V → ℝ)} {c : ℝ} {ω : V → ℝ}
    (h : ω ∉ deviation A c) :
    ({k | ω ∈ A k}.ncard : ℝ) < ∑ k, (Measure.pi fun _ : V => gaussianReal 0 1).real (A k) + c :=
  ncard_lt_of_not_le_abs h

open Classical in
/-- **Concentration of local events.** Under the product of standard Gaussians, if each event
`A k` depends only on the coordinates in `S k`, and each `S k` meets at most `D` of the sets
`S l`, then the number of events that occur deviates from its mean by at least `c > 0` with
probability at most `|κ| D / c ^ 2`. -/
theorem measureReal_deviation_le {A : κ → Set (V → ℝ)} (hA : ∀ k, MeasurableSet (A k))
    (S : κ → Set V) (hAS : ∀ k, DependsOn (· ∈ A k) (S k)) {D : ℕ}
    (hD : ∀ k, (Finset.univ.filter fun l => ¬Disjoint (S k) (S l)).card ≤ D) {c : ℝ}
    (hc : 0 < c) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real (deviation A c) ≤
      Fintype.card κ * D / c ^ 2 := by
  have h := measureReal_pi_le_abs_sum_indicator_sub_le (μ := fun _ : V => gaussianReal 0 1)
    Finset.univ (fun k _ => hA k) S (fun k _ => hAS k) (fun k l => ¬Disjoint (S k) (S l))
    (fun _ _ _ _ h => not_not.mp h) (fun k _ => hD k) hc
  rwa [Finset.card_univ] at h

end Deviations

/-! ### Projections of the sample -/

section Projections

variable {V : Type*} [Fintype V]

/-- The product of standard Gaussians on `V → ℝ` carries an event about inner products to the
same event under the standard Gaussian measure of `EuclideanSpace ℝ V`. -/
private theorem measureReal_pi_eq {s : Set (EuclideanSpace ℝ V)} (hs : MeasurableSet s) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real {ω | WithLp.toLp 2 ω ∈ s} =
      (stdGaussian (EuclideanSpace ℝ V)).real s :=
  (measurePreserving_toLp_pi_gaussianReal V).measureReal_preimage hs.nullMeasurableSet

/-- **Window bound.** A unit projection of the sample lands in a window of width `δ ≥ 0` with
probability at most `δ / √(2π)`. -/
theorem measureReal_window_le {y : EuclideanSpace ℝ V} (hy : ‖y‖ = 1) (a : ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real
        {ω | a ≤ ⟪y, WithLp.toLp 2 ω⟫ ∧ ⟪y, WithLp.toLp 2 ω⟫ < a + δ} ≤ δ / √(2 * π) := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  refine (measureReal_pi_eq (s := {x | ⟪y, x⟫ ∈ Ico a (a + δ)})
    ((by fun_prop : Measurable fun x : EuclideanSpace ℝ V => ⟪y, x⟫) measurableSet_Ico)).trans_le
    ?_
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity)
    ((stdGaussian_inner_mem_le hy0 measurableSet_Ico).trans ?_)
  rw [hy, mul_one, Real.volume_Ico, add_sub_cancel_left, ← ENNReal.ofReal_mul (by positivity),
    inv_mul_eq_div]

/-- **Tail bound.** A unit projection of the sample has absolute value at least `T > 0` with
probability at most `1 / T ^ 2`. -/
theorem measureReal_le_abs_le {y : EuclideanSpace ℝ V} (hy : ‖y‖ = 1) {T : ℝ} (hT : 0 < T) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real {ω | T ≤ |⟪y, WithLp.toLp 2 ω⟫|} ≤
      1 / T ^ 2 := by
  refine (measureReal_pi_eq (s := {x | T ≤ |⟪y, x⟫|})
    (measurableSet_le measurable_const (by fun_prop))).trans_le ?_
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity)
    ((stdGaussian_le_abs_inner_le y hT).trans ?_)
  rw [hy, one_pow]

/-- **Sheppard's bound for the sample.** Two projections of the sample onto vectors of equal
norm are separated by a threshold with probability at most their angle over `π`. -/
theorem measureReal_mem_uIoc_le {y y' : EuclideanSpace ℝ V} (h : ‖y‖ = ‖y'‖) (t : ℝ) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real
        {ω | t ∈ Ι ⟪y, WithLp.toLp 2 ω⟫ ⟪y', WithLp.toLp 2 ω⟫} ≤
      InnerProductGeometry.angle y y' / π :=
  (measureReal_pi_eq (s := {x | t ∈ Ι ⟪y, x⟫ ⟪y', x⟫})
    (measurableSet_setOf_mem_uIoc (by fun_prop) (by fun_prop) t)).trans_le
    (measureReal_stdGaussian_mem_uIoc_le_angle h t)

/-- An inner product with a vector `y` depends only on the coordinates where `y` is nonzero. -/
theorem inner_toLp_congr {y : EuclideanSpace ℝ V} {S : Set V} (hy : ∀ z ∉ S, y z = 0)
    {ω ω' : V → ℝ} (h : ∀ z ∈ S, ω z = ω' z) :
    ⟪y, WithLp.toLp 2 ω⟫ = ⟪y, WithLp.toLp 2 ω'⟫ := by
  simp only [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : z ∈ S
  · simp [h z hz]
  · simp [hy z hz]

end Projections

/-! ### Correlations of adjacent rows -/

section Correlations

variable {V E : Type*} [Fintype V] {G : Multigraph V E}

/-- **Adjacent rows are correlated.** In a loopless multigraph of maximum degree `d ≥ 2`, the
unit kernel rows of the ends of an edge, in the underlying simple graph, have inner product at
least `2 q / (1 + q ^ 2) - d ((d - 1) q ^ 2) ^ R`. -/
theorem le_inner_unitKernelRow_src_tgt [Finite E] (hloop : G.Loopless) {d : ℕ} (hd : 2 ≤ d)
    (hdeg : G.MaxDegreeLE d) {q : ℝ} (hq : 0 ≤ q) (R : ℕ) (e : E) :
    2 * q / (1 + q ^ 2) - d * ((d - 1) * q ^ 2) ^ R ≤
      ⟪unitKernelRow G.toSimpleGraph q R (G.src e),
        unitKernelRow G.toSimpleGraph q R (G.tgt e)⟫ := by
  classical
  exact le_inner_unitKernelRow hd hdeg.degree_toSimpleGraph_le hq R
    (Multigraph.toSimpleGraph_adj.mpr ⟨hloop e, e, rfl⟩)

end Correlations

private theorem continuous_correlation : Continuous fun q : ℝ => 2 * q / (1 + q ^ 2) :=
  (continuous_const.mul continuous_id).div (continuous_const.add (continuous_pow 2))
    fun q => by positivity

/-- The limiting correlation `2 √(d - 1) / d` of the kernel rows of adjacent vertices in maximum
degree `d`: the neighbour correlation of Gaussian waves on the `d`-regular tree. -/
noncomputable def vertexCorrelation (d : ℕ) : ℝ :=
  2 * √(d - 1) / d

/-- The limiting adjacent correlation `vertexCorrelation d` is positive for `d ≥ 2`. -/
theorem vertexCorrelation_pos {d : ℕ} (hd : 2 ≤ d) : 0 < vertexCorrelation d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have : 0 < (d : ℝ) - 1 := by linarith
  unfold vertexCorrelation
  positivity

/-- **Decay rate and radius.** In maximum degree `d ≥ 2`, every correlation below
`vertexCorrelation d` is met by the truncated kernel bound for some decay rate `q ≥ 0` and some
radius `R`. -/
theorem exists_decay_radius_degree {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ}
    (hρ : ρ < vertexCorrelation d) :
    ∃ (q : ℝ) (R : ℕ), 0 ≤ q ∧ ρ ≤ 2 * q / (1 + q ^ 2) - d * ((d - 1) * q ^ 2) ^ R := by
  set D : ℝ := (d : ℝ)
  have hD : 2 ≤ D := by
    simp only [D]
    exact_mod_cast hd
  set g := vertexCorrelation d
  set q₀ := √(D - 1) / (D - 1)
  have hu : 0 < D - 1 := by linarith
  have hq₀ : 0 < q₀ := by positivity
  have hs : √(D - 1) ^ 2 = D - 1 := sq_sqrt hu.le
  have hsq : q₀ ^ 2 = 1 / (D - 1) := by
    simp only [q₀]
    rw [div_pow, hs]
    field_simp
  have hlim : 2 * q₀ / (1 + q₀ ^ 2) = g := by
    rw [hsq]
    have hD0 : D ≠ 0 := (by linarith : (0 : ℝ) < D).ne'
    have hu0 := hu.ne'
    change 2 * (√(D - 1) / (D - 1)) / (1 + 1 / (D - 1)) = 2 * √(D - 1) / D
    field_simp
    ring
  obtain ⟨δ, hδ, hκ⟩ := Metric.continuousAt_iff.mp continuous_correlation.continuousAt
    ((g - ρ) / 2) (by linarith)
  set q := q₀ - min δ q₀ / 2
  have hmin : 0 < min δ q₀ := lt_min hδ hq₀
  have hq0 : 0 ≤ q := by
    simp only [q]
    linarith [min_le_right δ q₀]
  have hqq : q < q₀ := by
    simp only [q]
    linarith
  have hκq : g - (g - ρ) / 2 < 2 * q / (1 + q ^ 2) := by
    have hdist : dist q q₀ < δ := by
      rw [Real.dist_eq, show q - q₀ = -(min δ q₀ / 2) by simp only [q]; ring, abs_neg,
        abs_of_pos (by positivity)]
      linarith [min_le_left δ q₀]
    have H := hκ hdist
    rw [Real.dist_eq, hlim] at H
    linarith [neg_abs_le (2 * q / (1 + q ^ 2) - g)]
  have hdecay : (D - 1) * q ^ 2 < 1 := by
    have hq2 : q ^ 2 < q₀ ^ 2 := by gcongr
    have hq2' := mul_lt_mul_of_pos_left hq2 hu
    rwa [hsq, mul_one_div_cancel hu.ne'] at hq2'
  obtain ⟨R, hR⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < (g - ρ) / (2 * D)) hdecay
  have hR' := mul_lt_mul_of_pos_left hR (by linarith : 0 < D)
  have hcancel : D * ((g - ρ) / (2 * D)) = (g - ρ) / 2 := by field_simp
  rw [hcancel] at hR'
  exact ⟨q, R, hq0, by linarith⟩

end Cslib.Circuits.Frontier.Gaussian
