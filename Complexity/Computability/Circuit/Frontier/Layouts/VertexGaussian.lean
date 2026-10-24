/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.Gaussian.Basic
import Complexity.Foundations.Geometry.Euclidean.Angle.Cap
import Complexity.Foundations.Probability.Gaussian.Sheppard

/-!
# Gaussian vertex scores

Let `G` be a loopless multigraph of maximum degree `d`, with underlying simple graph `H`. Give
each vertex `v` its unit kernel row `x_v` in `H`
(`Cslib.Circuits.Frontier.Gaussian.unitKernelRow`): the normalized vector of distance weights
`q ^ dist(v, z)`, truncated at radius `R`. Draw a sample `ω` of independent standard Gaussians,
one per vertex, and score each vertex by `⟪x_v, ω⟫`
(`Cslib.Circuits.Frontier.Gaussian.vertexScore`). Sorting the vertices by score gives the layouts
of the module `Complexity.Computability.Circuit.Frontier.Layouts.MultiGaussian`.

**One edge.** A threshold `t` *crosses* an edge when it separates the scores of its ends
(`Cslib.Circuits.Frontier.Gaussian.crossingEvent`). The rows of the ends have inner product at
least `ρ`, for any `ρ` below the truncated kernel bound `2 q / (1 + q ^ 2) - d ((d - 1) q ^ 2) ^ R`,
so by Sheppard's bound [Sheppard1899] the edge is crossed with probability at most `arccos ρ / π`
(`Cslib.Circuits.Frontier.Gaussian.measureReal_crossingEvent_le`).

**Locality.** A score depends only on the coordinates of `ω` in the closed ball of radius `R`
around its vertex, so the events about the score of `v`, and the crossing of an edge, depend only
on the closed ball of radius `R + 1` around `v`, or around the source of the edge.

**The limit.** As `q` increases to `1/√(d - 1)` and `R` grows, the adjacent correlation tends to
`2 √(d - 1) / d` (`Cslib.Circuits.Frontier.Gaussian.vertexCorrelation`), the neighbour
correlation of Gaussian waves on the `d`-regular tree. So the crossing probability of an edge
tends to `vertexCoefficient d = arccos (2 √(d - 1) / d) / π`.

## Main definitions

* `Cslib.Circuits.Frontier.Gaussian.vertexScore`: the Gaussian score of a vertex.
* `Cslib.Circuits.Frontier.Gaussian.vertexEvent`: an event about the score of a vertex.
* `Cslib.Circuits.Frontier.Gaussian.crossingEvent`: a threshold separates the scores of the ends
  of an edge.
* `Cslib.Circuits.Frontier.Gaussian.vertexCoefficient`: the limiting crossing probability
  `arccos (2 √(d - 1) / d) / π`.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.dependsOn_vertexEvent`,
  `Cslib.Circuits.Frontier.Gaussian.dependsOn_crossingEvent`: locality.
* `Cslib.Circuits.Frontier.Gaussian.measureReal_crossingEvent_le`: the crossing probability of
  an edge.

## References

* [W. F. Sheppard, *On the application of the theory of error to cases of normal distribution
  and normal correlation*][Sheppard1899]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace Interval

namespace Cslib.Circuits.Frontier.Gaussian

variable {V E : Type*} [Fintype V] (G : Multigraph V E)

/-- The Gaussian score `⟪x_v, ω⟫` of a vertex: the inner product of its unit kernel row, in the
underlying simple graph, with the sample. -/
noncomputable def vertexScore (q : ℝ) (R : ℕ) (ω : V → ℝ) (v : V) : ℝ :=
  ⟪unitKernelRow G.toSimpleGraph q R v, WithLp.toLp 2 ω⟫

/-- The event that the score of `v` satisfies `p`. -/
def vertexEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (v : V) : Set (V → ℝ) :=
  {ω | p (vertexScore G q R ω v)}

/-- The event that the threshold `t` separates the scores of the ends of an edge. -/
def crossingEvent (q : ℝ) (R : ℕ) (t : ℝ) (e : E) : Set (V → ℝ) :=
  {ω | t ∈ Ι (vertexScore G q R ω (G.src e)) (vertexScore G q R ω (G.tgt e))}

variable {G} {q : ℝ} {R : ℕ}

private theorem measurable_vertexScore (q : ℝ) (R : ℕ) (v : V) :
    Measurable fun ω => vertexScore G q R ω v := by
  unfold vertexScore
  fun_prop

theorem measurableSet_vertexEvent (q : ℝ) (R : ℕ) {p : ℝ → Prop}
    (hp : MeasurableSet {x | p x}) (v : V) : MeasurableSet (vertexEvent G q R p v) :=
  measurable_vertexScore q R v hp

theorem measurableSet_crossingEvent (q : ℝ) (R : ℕ) (t : ℝ) (e : E) :
    MeasurableSet (crossingEvent G q R t e) :=
  measurableSet_setOf_mem_uIoc (measurable_vertexScore q R _) (measurable_vertexScore q R _) t

/-- The score of `v` depends only on the coordinates of the sample in the closed ball of radius
`R` around `v`. -/
theorem vertexScore_congr {v : V} {ω ω' : V → ℝ}
    (h : ∀ z ∈ closedBall G.toSimpleGraph v R, ω z = ω' z) :
    vertexScore G q R ω v = vertexScore G q R ω' v :=
  inner_toLp_congr (fun _ hz => unitKernelRow_eq_zero_of_lt (lt_of_not_ge hz)) h

omit [Fintype V] in
/-- The closed ball of radius `R` lies in the closed ball of radius `R + 1`. -/
private theorem closedBall_subset_succ (v : V) (R : ℕ) :
    closedBall G.toSimpleGraph v R ⊆ closedBall G.toSimpleGraph v (R + 1) :=
  fun _ (hz : G.toSimpleGraph.edist v _ ≤ R) =>
    (show G.toSimpleGraph.edist v _ ≤ ((R + 1 : ℕ) : ℕ∞) from
      hz.trans (by exact_mod_cast Nat.le_succ R))

/-- **Locality.** An event about the score of `v` depends only on the coordinates of the sample
in the closed ball of radius `R + 1` around `v`. -/
theorem dependsOn_vertexEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (v : V) :
    DependsOn (· ∈ vertexEvent G q R p v) (closedBall G.toSimpleGraph v (R + 1)) := by
  intro ω ω' hω
  simp only [vertexEvent, mem_ofPred_eq]
  rw [vertexScore_congr fun z hz => hω z (closedBall_subset_succ v R hz)]

/-- **Locality.** Whether a threshold crosses an edge depends only on the coordinates of the
sample in the closed ball of radius `R + 1` around its source. -/
theorem dependsOn_crossingEvent (q : ℝ) (R : ℕ) (t : ℝ) (e : E) :
    DependsOn (· ∈ crossingEvent G q R t e) (closedBall G.toSimpleGraph (G.src e) (R + 1)) := by
  intro ω ω' hω
  simp only [crossingEvent, mem_ofPred_eq]
  rw [vertexScore_congr fun z hz => hω z (closedBall_subset_succ _ R hz),
    vertexScore_congr fun z hz => hω z (closedBall_tgt_subset e R hz)]

/-- **One edge.** In a loopless multigraph of maximum degree `d ≥ 2`, let `ρ` be at most the
truncated kernel bound `2 q / (1 + q ^ 2) - d ((d - 1) q ^ 2) ^ R`. A threshold crosses an edge
with probability at most `arccos ρ / π`. -/
theorem measureReal_crossingEvent_le [Finite E] (hloop : G.Loopless) {d : ℕ} (hd : 2 ≤ d)
    (hdeg : G.MaxDegreeLE d) (hq : 0 ≤ q) (R : ℕ) {ρ : ℝ}
    (hρ : ρ ≤ 2 * q / (1 + q ^ 2) - d * ((d - 1) * q ^ 2) ^ R) (t : ℝ) (e : E) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real (crossingEvent G q R t e) ≤ arccos ρ / π := by
  have hcorr := hρ.trans (le_inner_unitKernelRow_src_tgt hloop hd hdeg hq R e)
  have hu := norm_unitKernelRow (G := G.toSimpleGraph) q R (G.src e)
  have hv := norm_unitKernelRow (G := G.toSimpleGraph) q R (G.tgt e)
  refine (measureReal_mem_uIoc_le (hu.trans hv.symm) t).trans ?_
  rw [InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one hu hv]
  exact div_le_div_of_nonneg_right (arccos_le_arccos hcorr) pi_pos.le

/-- The limiting crossing probability of an edge under Gaussian vertex scores in maximum degree
`d`: `arccos (2 √(d - 1) / d) / π`. -/
noncomputable def vertexCoefficient (d : ℕ) : ℝ :=
  arccos (vertexCorrelation d) / π

end Cslib.Circuits.Frontier.Gaussian
