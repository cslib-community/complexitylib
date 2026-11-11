/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Topology/MetricSpace/Brouwer.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.Sperner.Kuhn
public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Brouwer's fixed-point theorem on the cube

This file proves Brouwer's fixed-point theorem for the cube `[0, 1] ^ n`, with the sup metric of
`Fin n → ℝ`, from Sperner's lemma on the Kuhn-triangulated hypergrid
(`Cslib.Sperner.IsHypergridSperner.exists_isPanchromatic`), following the standard route described
by Yannakakis [Yannakakis2008] (Section 3): Sperner's lemma gives approximate fixed points, and
compactness gives an exact one.

For a map `f` of the cube into itself and `N > 0`, colour the grid point `p` (with `p ≤ N`) by
`j + 1` for the largest `j` such that `f` raises coordinate `j` at `x = p / N` (`x j < f x j`, or
`x j = f x j = 0`), and by `0` if there is none (`Cslib.Brouwer.coloring`). This colouring satisfies
the Sperner boundary condition `Cslib.Sperner.IsHypergridSperner` (`isHypergridSperner_coloring`);
it is generally not a valid colouring of Chen, Deng and Teng, whose boundary colours are fixed. A
panchromatic Kuhn simplex has a vertex where no coordinate is raised and, for each `k`, a vertex
where coordinate `k` is raised; its vertices are `1 / N`-close, so `f x - x` is small at each of
them (`exists_dist_le_of_forall_dist_le`).

Yannakakis sketches the argument on the unit simplex, with Scarf's labelling, and extracts a fixed
point from a convergent subsequence of weak approximations. Here the domain is the cube with the
Kuhn triangulation and the labelling above, and compactness enters instead through uniform
continuity and a minimizer of `dist (f x) x` on the cube.

## Main results

* `Cslib.Brouwer.exists_dist_le_of_lipschitzOnWith`: if `f` maps the cube into itself and is
  `K`-Lipschitz on it, then for every `N > 0` some grid point `x = p / N` satisfies
  `dist (f x) x ≤ (K + 1) / N`: a weak approximate fixed point in the sense of Yannakakis.
* `Cslib.Brouwer.exists_isFixedPt_cube`: **Brouwer's fixed-point theorem** for the cube.

The constant `(K + 1) / N` is our own bookkeeping of the standard argument; no novelty is claimed.
Arbitrary compact convex sets (by a retraction) are not treated here.

## References

* [M. Yannakakis, *Equilibria, fixed points, and complexity classes*][Yannakakis2008]
-/

public section

namespace Cslib.Brouwer

open Set Sperner Sperner.KuhnSimplex

variable {n : ℕ}

/-- The point `p / N` of the cube `[0, 1] ^ n`. -/
@[expose] noncomputable def gridPoint (N : ℕ) (p : Fin n → ℕ) : Fin n → ℝ := fun i => (p i : ℝ) / N

@[simp]
theorem gridPoint_apply (N : ℕ) (p : Fin n → ℕ) (i : Fin n) : gridPoint N p i = (p i : ℝ) / N :=
  rfl

theorem gridPoint_mem_Icc {N : ℕ} {p : Fin n → ℕ} (hp : ∀ i, p i ≤ N) :
    gridPoint N p ∈ Icc (0 : Fin n → ℝ) 1 := by
  refine ⟨fun i => by unfold gridPoint; positivity, fun i => ?_⟩
  exact div_le_one_of_le₀ (by exact_mod_cast hp i) (Nat.cast_nonneg N)

/-- The Sperner colouring of the hypergrid `[0, N] ^ n` induced by `f`: the grid point `p` has
colour `j + 1` for the largest `j` such that `f` raises coordinate `j` at `x = p / N`, that is
`x j < f x j`, or `x j = 0 = f x j`; and colour `0` if `f` raises no coordinate. -/
noncomputable def coloring (f : (Fin n → ℝ) → Fin n → ℝ) (N : ℕ) (p : Fin n → ℕ) : Fin (n + 1) :=
  open Classical in
  ({j | gridPoint N p j < f (gridPoint N p) j ∨
      (gridPoint N p j = 0 ∧ f (gridPoint N p) j = 0)} : Finset (Fin n)).sup Fin.succ

private theorem sup_succ_eq_zero {S : Finset (Fin n)} (h : S.sup Fin.succ = 0) : S = ∅ := by
  have h' : S.sup Fin.succ = ⊥ := h.trans bot_eq_zero.symm
  rw [Finset.sup_eq_bot_iff] at h'
  exact Finset.eq_empty_of_forall_notMem fun j hj =>
    Fin.succ_ne_zero j ((h' j hj).trans bot_eq_zero)

private theorem mem_of_sup_succ_eq {S : Finset (Fin n)} {k : Fin n}
    (h : S.sup Fin.succ = k.succ) : k ∈ S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact absurd h (by rw [Finset.sup_empty, bot_eq_zero]; exact (Fin.succ_ne_zero k).symm)
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup S hne Fin.succ
    rw [hjeq] at h
    exact Fin.succ_injective _ h ▸ hj

private theorem castSucc_lt_sup_succ {S : Finset (Fin n)} {j : Fin n} (hj : j ∈ S) :
    j.castSucc < S.sup Fin.succ :=
  Fin.castSucc_lt_succ.trans_le (Finset.le_sup hj)

/-- At a point of colour `0`, `f` lowers or fixes every coordinate. -/
theorem le_of_coloring_eq_zero {f : (Fin n → ℝ) → Fin n → ℝ} {N : ℕ} {p : Fin n → ℕ}
    (h : coloring f N p = 0) (j : Fin n) : f (gridPoint N p) j ≤ gridPoint N p j := by
  unfold coloring at h
  have hS := Finset.filter_eq_empty_iff.mp (sup_succ_eq_zero h) (Finset.mem_univ j)
  exact le_of_not_gt fun hlt => hS (.inl hlt)

/-- At a point of colour `k + 1`, `f` raises or fixes coordinate `k`. -/
theorem le_of_coloring_eq_succ {f : (Fin n → ℝ) → Fin n → ℝ} {N : ℕ} {p : Fin n → ℕ} {k : Fin n}
    (h : coloring f N p = k.succ) : gridPoint N p k ≤ f (gridPoint N p) k := by
  unfold coloring at h
  rcases (Finset.mem_filter.mp (mem_of_sup_succ_eq h)).2 with hlt | ⟨h0, h1⟩
  · exact hlt.le
  · rw [h0, h1]

/-- The colouring induced by a map of the cube into itself satisfies the Sperner boundary
condition. -/
theorem isHypergridSperner_coloring {f : (Fin n → ℝ) → Fin n → ℝ}
    (hf : MapsTo f (Icc 0 1) (Icc 0 1)) {N : ℕ} (hN : 0 < N) :
    IsHypergridSperner (fun _ => N) (coloring f N) := by
  intro p hp i
  have hx := hf (gridPoint_mem_Icc hp)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨fun h0 => ?_, fun hN' heq => ?_⟩
  · unfold coloring
    apply castSucc_lt_sup_succ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hg : gridPoint N p i = 0 := by simp [gridPoint, h0]
    rcases (hx.1 i).lt_or_eq with hlt | heq
    · exact .inl (hg ▸ hlt)
    · exact .inr ⟨hg, heq.symm⟩
  · unfold coloring at heq
    have hN'' : p i = N := hN'
    have hg : gridPoint N p i = 1 := by simp [gridPoint, hN'', hNr.ne']
    have h1 : f (gridPoint N p) i ≤ 1 := hx.2 i
    rcases (Finset.mem_filter.mp (mem_of_sup_succ_eq heq)).2 with hlt | ⟨h0, -⟩
    · rw [hg] at hlt
      linarith
    · rw [hg] at h0
      exact one_ne_zero h0

/-- **Approximate fixed points.** Let `f` map the cube `[0, 1] ^ n` into itself, and suppose that
any two points of the cube at distance at most `1 / N` have images at distance at most `η`. Then
some grid point `x = p / N` satisfies `dist (f x) x ≤ η + 1 / N`. -/
theorem exists_dist_le_of_forall_dist_le {f : (Fin n → ℝ) → Fin n → ℝ}
    (hf : MapsTo f (Icc 0 1) (Icc 0 1)) {N : ℕ} (hN : 0 < N) {η : ℝ}
    (hη : ∀ x ∈ Icc (0 : Fin n → ℝ) 1, ∀ y ∈ Icc (0 : Fin n → ℝ) 1, dist x y ≤ 1 / N →
      dist (f x) (f y) ≤ η) :
    ∃ p : Fin n → ℕ, (∀ i, p i ≤ N) ∧
      dist (f fun i => (p i : ℝ) / N) (fun i => (p i : ℝ) / N) ≤ η + 1 / N := by
  obtain ⟨s, hs, hpan⟩ := (isHypergridSperner_coloring hf hN).exists_isPanchromatic
  have hle : ∀ k i, s.vertex k i ≤ N := fun k i => vertex_le hs k i
  have hmem : ∀ k, gridPoint N (s.vertex k) ∈ Icc (0 : Fin n → ℝ) 1 :=
    fun k => gridPoint_mem_Icc (hle k)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hclose : ∀ k l i, |gridPoint N (s.vertex k) i - gridPoint N (s.vertex l) i| ≤ 1 / N := by
    intro k l i
    have h1 : (s.base i : ℝ) ≤ s.vertex k i := by exact_mod_cast base_le_vertex s k i
    have h2 : (s.vertex k i : ℝ) ≤ s.base i + 1 := by exact_mod_cast vertex_le_base_add_one s k i
    have h3 : (s.base i : ℝ) ≤ s.vertex l i := by exact_mod_cast base_le_vertex s l i
    have h4 : (s.vertex l i : ℝ) ≤ s.base i + 1 := by exact_mod_cast vertex_le_base_add_one s l i
    unfold gridPoint
    rw [div_sub_div_same, abs_div, abs_of_pos hNr, div_le_div_iff_of_pos_right hNr, abs_le]
    constructor <;> linarith
  have hdist : ∀ k l, dist (gridPoint N (s.vertex k)) (gridPoint N (s.vertex l)) ≤ 1 / N :=
    fun k l => (dist_pi_le_iff (by positivity)).mpr fun i => by
      rw [Real.dist_eq]; exact hclose k l i
  have hfη : ∀ k l, dist (f (gridPoint N (s.vertex k))) (f (gridPoint N (s.vertex l))) ≤ η :=
    fun k l => hη _ (hmem k) _ (hmem l) (hdist k l)
  have hη0 : 0 ≤ η := dist_nonneg.trans (hfη 0 0)
  obtain ⟨a, ha⟩ := hpan 0
  refine ⟨s.vertex 0, hle 0, (dist_pi_le_iff (add_nonneg hη0 (by positivity))).mpr fun k => ?_⟩
  obtain ⟨b, hb⟩ := hpan k.succ
  have hfa := le_of_coloring_eq_zero ha k
  have hfb := le_of_coloring_eq_succ hb
  have h0a := (dist_le_pi_dist _ _ k).trans (hfη 0 a)
  have h0b := (dist_le_pi_dist _ _ k).trans (hfη 0 b)
  have c0a := hclose 0 a k
  have c0b := hclose 0 b k
  rw [Real.dist_eq, abs_le] at h0a h0b
  rw [abs_le] at c0a c0b
  change |f (gridPoint N (s.vertex 0)) k - gridPoint N (s.vertex 0) k| ≤ η + 1 / N
  rw [abs_le]
  constructor <;> linarith

/-- **Weak approximate fixed points of Lipschitz maps.** If `f` maps the cube `[0, 1] ^ n` into
itself and is `K`-Lipschitz on it for the sup metric, then for every `N > 0` some grid point
`x = p / N` satisfies `dist (f x) x ≤ (K + 1) / N`. -/
theorem exists_dist_le_of_lipschitzOnWith {f : (Fin n → ℝ) → Fin n → ℝ}
    (hf : MapsTo f (Icc 0 1) (Icc 0 1)) {K : NNReal} (hK : LipschitzOnWith K f (Icc 0 1))
    {N : ℕ} (hN : 0 < N) :
    ∃ p : Fin n → ℕ, (∀ i, p i ≤ N) ∧
      dist (f fun i => (p i : ℝ) / N) (fun i => (p i : ℝ) / N) ≤ (K + 1) / N := by
  have h := exists_dist_le_of_forall_dist_le hf hN (η := K / N) fun x hx y hy hxy =>
    (hK.dist_le_mul x hx y hy).trans (by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hxy K.coe_nonneg)
  obtain ⟨p, hp, hd⟩ := h
  exact ⟨p, hp, hd.trans_eq (by ring)⟩

/-- **Brouwer's fixed-point theorem** for the cube `[0, 1] ^ n`: a continuous map of the cube into
itself has a fixed point. -/
theorem exists_isFixedPt_cube {f : (Fin n → ℝ) → Fin n → ℝ}
    (hf : MapsTo f (Icc 0 1) (Icc 0 1)) (hc : ContinuousOn f (Icc 0 1)) :
    ∃ x ∈ Icc (0 : Fin n → ℝ) 1, Function.IsFixedPt f x := by
  have hK : IsCompact (Icc (0 : Fin n → ℝ) 1) := isCompact_Icc
  have hne : (Icc (0 : Fin n → ℝ) 1).Nonempty := nonempty_Icc.mpr zero_le_one
  obtain ⟨x₀, hx₀, hmin⟩ :=
    hK.exists_isMinOn hne (continuous_dist.comp_continuousOn (hc.prodMk continuousOn_id))
  refine ⟨x₀, hx₀, dist_eq_zero.mp (le_antisymm ?_ dist_nonneg)⟩
  by_contra hpos
  set m := dist (f x₀) x₀ with hm
  have hm0 : 0 < m := lt_of_not_ge hpos
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff_le.mp
    (hK.uniformContinuousOn_of_continuous hc) (m / 4) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / δ) (4 / m))
  have hNpos : (0 : ℝ) < N := (lt_max_of_lt_left (by positivity : (0 : ℝ) < 1 / δ)).trans hN
  have hN1 : 1 / (N : ℝ) ≤ δ := by
    rw [one_div_le hNpos hδ]; exact (le_max_left _ _).trans hN.le
  have hN2 : 1 / (N : ℝ) < m / 4 := by
    rw [one_div_lt hNpos (by positivity), one_div_div]; exact (le_max_right _ _).trans_lt hN
  obtain ⟨p, hp, hd⟩ := exists_dist_le_of_forall_dist_le hf (Nat.cast_pos.mp hNpos)
    fun x hx y hy hxy => hδf x hx y hy (hxy.trans hN1)
  have hmp := isMinOn_iff.mp hmin _ (gridPoint_mem_Icc hp)
  change m ≤ dist (f (gridPoint N p)) (gridPoint N p) at hmp
  unfold gridPoint at hmp
  linarith

end Cslib.Brouwer
