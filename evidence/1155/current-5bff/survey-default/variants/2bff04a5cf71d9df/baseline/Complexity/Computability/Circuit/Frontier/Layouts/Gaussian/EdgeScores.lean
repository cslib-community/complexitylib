/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.Gaussian.Basic
import Complexity.Foundations.Combinatorics.SimpleGraph.Metric

/-!
# Gaussian edge scores and their locality

Let `G` be a loopless multigraph of maximum degree three, with underlying simple graph `H`. Give
each edge `e` the unit vector `y_e` in the direction of `x_u + x_v`, where `x_u` and `x_v` are
the unit kernel rows of its ends in `H` (`Cslib.Circuits.Frontier.Gaussian.edgeVector`). Its
*score* at a sample `ω` is `⟪y_e, ω⟫` (`Cslib.Circuits.Frontier.Gaussian.edgeScore`).

If the rows of adjacent vertices have inner product `ρ`, the edge vector has inner product
`√((1 + ρ)/2)` with the row of either end: the sum of two unit vectors with inner product `ρ`
has norm `2 √((1 + ρ)/2)`. The edge vectors at a vertex `v` vanish outside the closed ball of
radius `R + 1` around `v`, so the scores of the edges at `v` depend only on the coordinates of the
sample in that ball (`Cslib.Circuits.Frontier.Gaussian.edgeScore_congr`).

## Main definitions

* `Cslib.Circuits.Frontier.Gaussian.edgeVector`: the unit vector of an edge.
* `Cslib.Circuits.Frontier.Gaussian.edgeScore`: the Gaussian score of an edge.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.norm_edgeVector`: edge vectors are unit vectors.
* `Cslib.Circuits.Frontier.Gaussian.le_inner_edgeVector`: the edge vectors at `v` are close to
  the row of `v`.
* `Cslib.Circuits.Frontier.Gaussian.edgeScore_congr`: locality of the scores.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace Cslib.Circuits.Frontier.Gaussian

/-! ### Normalized sums of unit vectors -/

section Normalize

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The sum of two unit vectors has norm `2 √((1 + ⟪a, b⟫)/2)`. -/
private theorem norm_add_eq {a b : F} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : -1 ≤ ⟪a, b⟫) :
    ‖a + b‖ = 2 * √((1 + ⟪a, b⟫) / 2) := by
  refine (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [norm_add_sq_real, ha, hb, mul_pow, sq_sqrt (by linarith)]
  ring

/-- The normalized sum of two unit vectors `a`, `b` has inner product `√((1 + ⟪a, b⟫)/2)` with
`b`. -/
private theorem inner_smul_add_right {a b : F} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : -1 < ⟪a, b⟫) : ⟪‖a + b‖⁻¹ • (a + b), b⟫ = √((1 + ⟪a, b⟫) / 2) := by
  have hs : 0 < √((1 + ⟪a, b⟫) / 2) := sqrt_pos.2 (by linarith)
  have hsq := sq_sqrt (show 0 ≤ (1 + ⟪a, b⟫) / 2 by linarith)
  rw [norm_add_eq ha hb hab.le, real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq,
    hb]
  field_simp
  linarith

/-- The normalized sum of two unit vectors `a`, `b` has inner product `√((1 + ⟪a, b⟫)/2)` with
`a`. -/
private theorem inner_smul_add_left {a b : F} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : -1 < ⟪a, b⟫) : ⟪‖a + b‖⁻¹ • (a + b), a⟫ = √((1 + ⟪a, b⟫) / 2) := by
  rw [add_comm a b, ← real_inner_comm a b]
  exact inner_smul_add_right hb ha (by rwa [real_inner_comm])

/-- The normalized sum of two unit vectors with inner product above `-1` is a unit vector. -/
private theorem norm_smul_add {a b : F} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : -1 < ⟪a, b⟫) :
    ‖‖a + b‖⁻¹ • (a + b)‖ = 1 := by
  have h : 0 < ‖a + b‖ := by
    rw [norm_add_eq ha hb hab.le]
    exact mul_pos two_pos (sqrt_pos.2 (by linarith))
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h.ne']

end Normalize

/-! ### Edge vectors and scores -/

variable {V E : Type*} [Fintype V] (G : Multigraph V E)

/-- The unit vector of an edge: the sum of the unit kernel rows of its ends, in the underlying
simple graph, divided by its norm. -/
noncomputable def edgeVector (q : ℝ) (R : ℕ) (e : E) : EuclideanSpace ℝ V :=
  ‖unitKernelRow G.toSimpleGraph q R (G.src e) + unitKernelRow G.toSimpleGraph q R (G.tgt e)‖⁻¹ •
    (unitKernelRow G.toSimpleGraph q R (G.src e) + unitKernelRow G.toSimpleGraph q R (G.tgt e))

/-- The Gaussian score of an edge at a sample `ω`: the inner product of its unit vector with
`ω`. -/
noncomputable def edgeScore (q : ℝ) (R : ℕ) (ω : V → ℝ) (e : E) : ℝ :=
  ⟪edgeVector G q R e, WithLp.toLp 2 ω⟫

variable {G}

/-- The Gaussian score `edgeScore G q R · e` is a measurable function of the sample. -/
theorem measurable_edgeScore (q : ℝ) (R : ℕ) (e : E) :
    Measurable fun ω => edgeScore G q R ω e := by
  unfold edgeScore
  fun_prop

variable {q : ℝ} {R : ℕ} {ρ₀ : ℝ}

/-- In maximum degree three, the rows of the ends of an edge have inner product at least
`2 q / (1 + q ^ 2) - 3 (2 q ^ 2) ^ R`. -/
private theorem le_inner_unitKernelRow_src_tgt_three [Finite E] (hloop : G.Loopless)
    (hdeg : G.MaxDegreeLE 3) (hq : 0 ≤ q) (R : ℕ) (e : E) :
    2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ≤
      ⟪unitKernelRow G.toSimpleGraph q R (G.src e),
        unitKernelRow G.toSimpleGraph q R (G.tgt e)⟫ := by
  have h := le_inner_unitKernelRow_src_tgt hloop (d := 3) (by norm_num) hdeg hq R e
  norm_num at h
  linarith

/-- **Edge vectors are unit vectors**, when adjacent rows have inner product at least
`ρ₀ > -1`. -/
theorem norm_edgeVector [Finite E] (hloop : G.Loopless) (hdeg : G.MaxDegreeLE 3) (hq : 0 ≤ q)
    (hρ₀ : -1 < ρ₀) (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (e : E) :
    ‖edgeVector G q R e‖ = 1 :=
  norm_smul_add (norm_unitKernelRow _ _ _) (norm_unitKernelRow _ _ _)
    (by linarith [le_inner_unitKernelRow_src_tgt_three hloop hdeg hq R e])

/-- **Edge vectors are close to the rows of their ends.** If adjacent rows have inner product at
least `ρ₀ ≥ 0`, an edge vector has inner product at least `√((1 + ρ₀)/2)` with the row of either
end. -/
theorem le_inner_edgeVector [Finite E] (hloop : G.Loopless) (hdeg : G.MaxDegreeLE 3)
    (hq : 0 ≤ q) (hρ₀ : 0 ≤ ρ₀) (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) {v : V}
    {e : E} (he : e ∈ G.incidenceSet v) :
    √((1 + ρ₀) / 2) ≤ ⟪edgeVector G q R e, unitKernelRow G.toSimpleGraph q R v⟫ := by
  have hcorr := hρ.trans (le_inner_unitKernelRow_src_tgt_three hloop hdeg hq R e)
  have hmono : √((1 + ρ₀) / 2) ≤ √((1 + ⟪unitKernelRow G.toSimpleGraph q R (G.src e),
      unitKernelRow G.toSimpleGraph q R (G.tgt e)⟫) / 2) := sqrt_le_sqrt (by linarith)
  rcases he with rfl | rfl
  · rwa [edgeVector, inner_smul_add_left (norm_unitKernelRow _ _ _)
      (norm_unitKernelRow _ _ _) (by linarith)]
  · rwa [edgeVector, inner_smul_add_right (norm_unitKernelRow _ _ _)
      (norm_unitKernelRow _ _ _) (by linarith)]

/-! ### Locality -/

/-- The edge vectors at `v` vanish outside the closed ball of radius `R + 1` around `v`. -/
theorem edgeVector_apply_eq_zero {v : V} {e : E} (he : e ∈ G.incidenceSet v) {z : V}
    (hz : z ∉ closedBall G.toSimpleGraph v (R + 1)) : edgeVector G q R e z = 0 := by
  have hz : ((R + 1 : ℕ) : ℕ∞) < G.toSimpleGraph.edist v z := lt_of_not_ge hz
  -- Both ends of `e` are `v` or neighbours of `v`.
  have hend (w : V) (hw : G.src e = w ∨ G.tgt e = w) :
      unitKernelRow G.toSimpleGraph q R w z = 0 := by
    refine unitKernelRow_eq_zero_of_lt (lt_of_not_ge fun hle => hz.not_ge ?_)
    have hvw : G.toSimpleGraph.edist v z ≤ G.toSimpleGraph.edist w z + 1 := by
      by_cases hvw : v = w
      · rw [hvw]
        exact le_self_add
      · refine SimpleGraph.Adj.edist_le_edist_add_one (Multigraph.toSimpleGraph_adj.mpr
          ⟨hvw, e, ?_⟩) z
        rcases he with hv | hv <;> rcases hw with hw | hw <;>
          simp_all [Multigraph.ends, Sym2.eq_swap]
    calc G.toSimpleGraph.edist v z ≤ G.toSimpleGraph.edist w z + 1 := hvw
      _ ≤ R + 1 := add_le_add_left hle 1
      _ = ((R + 1 : ℕ) : ℕ∞) := by push_cast; rfl
  simp [edgeVector, hend _ (Or.inl rfl), hend _ (Or.inr rfl)]

/-- **Locality.** The scores of the edges at `v` depend only on the coordinates of the sample in
the closed ball of radius `R + 1` around `v`. -/
theorem edgeScore_congr {v : V} {e : E} (he : e ∈ G.incidenceSet v) {ω ω' : V → ℝ}
    (h : ∀ z ∈ closedBall G.toSimpleGraph v (R + 1), ω z = ω' z) :
    edgeScore G q R ω e = edgeScore G q R ω' e :=
  inner_toLp_congr (fun _ hz => edgeVector_apply_eq_zero he hz) h

end Cslib.Circuits.Frontier.Gaussian
