/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.MarkovChain.PathCoupling
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Complexity.Foundations.Combinatorics.SimpleGraph.GreedyColoring
import Complexity.Foundations.Data.Hamming
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Expect
import Complexity.Probability.StatisticalDistance.ClosedForm
import Complexity.Probability.StatisticalDistance.OptimalCoupling

/-!
# Glauber dynamics for proper colorings

Glauber dynamics for `q`-colorings of a finite graph `G` with `n` vertices and maximum degree `Δ`
([LevinPeres2017], Sections 3.3.1 and 14.3): at each step a vertex `w` is chosen uniformly at
random and recolored with a color chosen uniformly from the colors absent from its neighbors
(`Cslib.Probability.MarkovChain.allowedColors`). As in [LevinPeres2017], Section 14.3, the chain
runs on all colorings `V → Fin q`, proper or not. It is reversible with respect to the uniform
distribution on proper colorings (`Cslib.Probability.MarkovChain.isReversible_glauberColoring`),
which is nonempty when `Δ < q` by greedy coloring.

**Rapid mixing** ([LevinPeres2017], Theorem 14.10). If `q > 2Δ` then
`t_mix(ε) ≤ ⌈((q - Δ) / (q - 2Δ)) n (log n - log ε)⌉`
(`Cslib.Probability.MarkovChain.mixingTime_glauberColoring_le`). The proof is path coupling for
the Hamming distance: two colorings differing at one vertex `v` are updated at the same uniformly
random vertex `w` with an optimal coupling of the two uniform color choices
(`Cslib.Probability.MarkovChain.exists_coupling_glauberColoring`). The colorings disagree after the
update with probability at most `1 / (q - Δ)` when `w` is a neighbor of `v`, never when `w = v`, and
stay at distance one otherwise, giving the contraction `1 - (1 - Δ / (q - Δ)) / n` of
[LevinPeres2017], (14.19).

## Main definitions

* `Cslib.Probability.MarkovChain.allowedColors`: the colors absent from the neighbors of a vertex.
* `Cslib.Probability.MarkovChain.IsProperColoring`,
  `Cslib.Probability.MarkovChain.properColorings`: proper colorings.
* `Cslib.Probability.MarkovChain.recolor`: the heat-bath update at one vertex.
* `Cslib.Probability.MarkovChain.glauberColoring`: Glauber dynamics for colorings.

## Main results

* `Cslib.Probability.MarkovChain.isReversible_glauberColoring`,
  `Cslib.Probability.MarkovChain.isStationary_glauberColoring`: the uniform distribution on proper
  colorings is reversible, hence stationary.
* `Cslib.Probability.MarkovChain.exists_coupling_glauberColoring`: the one-step contraction
  ([LevinPeres2017], (14.18) and (14.19)).
* `Cslib.Probability.MarkovChain.distToStationary_glauberColoring_le`,
  `Cslib.Probability.MarkovChain.mixingTime_glauberColoring_le`: [LevinPeres2017], Theorem 14.10.

## References

* [LevinPeres2017], Sections 3.3.1 and 14.3.
-/

public section

open scoped ENNReal Cslib.Probability.PMF

namespace Cslib.Probability.MarkovChain

open Cslib.Probability.PMF

variable {V : Type*} {q : ℕ}

/-! ### Proper colorings and allowed colors -/

section Proper

variable (G : SimpleGraph V)

/-- `x` is a proper coloring of `G`: adjacent vertices have different colors. -/
def IsProperColoring (x : V → Fin q) : Prop :=
  ∀ u v, G.Adj u v → x u ≠ x v

theorem isProperColoring_iff {x : V → Fin q} :
    IsProperColoring G x ↔ ∀ u v, G.Adj u v → x u ≠ x v :=
  Iff.rfl

/-- Proper colorings are the colorings of `G` in the sense of `SimpleGraph.Coloring`. -/
theorem isProperColoring_iff_exists_coloring {x : V → Fin q} :
    IsProperColoring G x ↔ ∃ C : G.Coloring (Fin q), ⇑C = x :=
  ⟨fun h => ⟨SimpleGraph.Coloring.mk x fun {u v} huv => h u v huv, rfl⟩,
    fun ⟨C, hC⟩ _ _ huv => hC ▸ C.valid huv⟩

end Proper

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The colors absent from the neighbors of `w` under the coloring `x` ([LevinPeres2017],
Section 3.3.1). -/
def allowedColors (x : V → Fin q) (w : V) : Finset (Fin q) :=
  Finset.univ \ (G.neighborFinset w).image x

theorem mem_allowedColors {x : V → Fin q} {w : V} {c : Fin q} :
    c ∈ allowedColors G x w ↔ ∀ u, G.Adj w u → x u ≠ c := by
  simp [allowedColors]

/-- At most `Δ` colors are excluded. -/
theorem card_allowedColors (x : V → Fin q) (w : V) :
    q - G.maxDegree ≤ (allowedColors G x w).card := by
  have h1 : ((G.neighborFinset w).image x).card ≤ G.maxDegree :=
    Finset.card_image_le.trans (G.degree_le_maxDegree w)
  have h2 := Finset.le_card_sdiff ((G.neighborFinset w).image x) Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at h2
  rw [allowedColors]
  omega

theorem allowedColors_nonempty (hq : G.maxDegree < q) (x : V → Fin q) (w : V) :
    (allowedColors G x w).Nonempty := by
  rw [← Finset.card_pos]
  have := card_allowedColors G x w
  omega

/-- The allowed colors at `w` depend only on the colors of the neighbors of `w`. -/
theorem allowedColors_congr {x y : V → Fin q} {w : V} (h : ∀ u, G.Adj w u → x u = y u) :
    allowedColors G x w = allowedColors G y w := by
  ext c
  simp only [mem_allowedColors]
  exact forall_congr' fun u => imp_congr_right fun hu => by rw [h u hu]

instance (x : V → Fin q) : Decidable (IsProperColoring G x) :=
  decidable_of_iff _ (isProperColoring_iff G).symm

theorem IsProperColoring.mem_allowedColors {G : SimpleGraph V} [DecidableRel G.Adj]
    {x : V → Fin q} (hx : IsProperColoring G x) (w : V) : x w ∈ allowedColors G x w :=
  (Cslib.Probability.MarkovChain.mem_allowedColors G).2 fun u hu => (hx w u hu).symm

variable [DecidableEq V]

/-- The proper `q`-colorings of `G`. -/
def properColorings (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) : Finset (V → Fin q) :=
  Finset.univ.filter fun x => IsProperColoring G x

theorem mem_properColorings {x : V → Fin q} : x ∈ properColorings G q ↔ IsProperColoring G x := by
  simp [properColorings]

/-- **Greedy coloring**: if `Δ < q`, proper `q`-colorings exist. -/
theorem properColorings_nonempty (hq : G.maxDegree < q) : (properColorings G q).Nonempty := by
  obtain ⟨C⟩ := G.colorable_of_maxDegree_lt hq
  exact ⟨C, (mem_properColorings G).2 fun u v huv => C.valid huv⟩

variable {G}

/-- Recoloring a vertex of a proper coloring with an allowed color gives a proper coloring. -/
theorem IsProperColoring.update_of_mem {x : V → Fin q} (hx : IsProperColoring G x) {w : V}
    {c : Fin q} (hc : c ∈ allowedColors G x w) : IsProperColoring G (Function.update x w c) := by
  rw [Cslib.Probability.MarkovChain.mem_allowedColors] at hc
  intro u v huv
  by_cases hu : u = w
  · subst hu
    rw [Function.update_self, Function.update_of_ne (G.ne_of_adj huv).symm]
    exact (hc v huv).symm
  · by_cases hv : v = w
    · subst hv
      rw [Function.update_self, Function.update_of_ne hu]
      exact hc u huv.symm
    · rw [Function.update_of_ne hu, Function.update_of_ne hv]
      exact hx u v huv

variable (G)

/-! ### Glauber dynamics -/

/-- The heat-bath update at `w`: recolor `w` with a uniformly random allowed color. If no color
is allowed, which cannot happen when `Δ < q` or when `x` is proper, the coloring is unchanged. -/
noncomputable def recolor (x : V → Fin q) (w : V) : PMF (V → Fin q) :=
  if h : (allowedColors G x w).Nonempty then
    (uniformOfFinset (allowedColors G x w) h).map (Function.update x w)
  else PMF.pure x

/-- **Glauber dynamics for colorings** ([LevinPeres2017], Sections 3.3.1 and 14.3): recolor a
uniformly random vertex with a uniformly random color absent from its neighbors. -/
noncomputable def glauberColoring [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) : MarkovChain (V → Fin q) where
  step x := (uniformOfFintype V).bind (recolor G x)

theorem glauberColoring_apply [Nonempty V] (x : V → Fin q) :
    glauberColoring G q x = (uniformOfFintype V).bind (recolor G x) := by
  rfl

/-- The heat-bath update moves to `y` with probability `1 / |A_w(x)|` if `y` agrees with `x` off
`w` and `y w` is allowed. -/
theorem recolor_apply {x : V → Fin q} {w : V} (h : (allowedColors G x w).Nonempty)
    (y : V → Fin q) : recolor G x w y =
      if Function.update x w (y w) = y ∧ y w ∈ allowedColors G x w then
        ((allowedColors G x w).card : ℝ≥0∞)⁻¹ else 0 := by
  rw [recolor, dite_eq_left h, PMF.map_apply, tsum_eq_single (y w)]
  · by_cases hy : Function.update x w (y w) = y
    · rw [ite_eq_left hy.symm, uniformOfFinset_apply]
      by_cases hm : y w ∈ allowedColors G x w
      · rw [ite_eq_left hm, ite_eq_left ⟨hy, hm⟩]
      · rw [ite_eq_right hm, ite_eq_right fun h => hm h.2]
    · rw [ite_eq_right (Ne.symm hy), ite_eq_right fun h => hy h.1]
  · intro c hc
    rw [ite_eq_right]
    intro hyc
    exact hc (by rw [hyc, Function.update_self])

private theorem recolor_eq_zero_of_not_proper {x y : V → Fin q} (hx : IsProperColoring G x)
    (hy : ¬IsProperColoring G y) (w : V) : recolor G x w y = 0 := by
  rw [recolor_apply G ⟨x w, hx.mem_allowedColors w⟩, ite_eq_right]
  rintro ⟨hupd, hmem⟩
  exact hy (hupd ▸ hx.update_of_mem hmem)

/-- Detailed balance for a single heat-bath update. -/
private theorem recolor_balance (hne : (properColorings G q).Nonempty) (x y : V → Fin q)
    (w : V) :
    uniformOfFinset (properColorings G q) hne x * recolor G x w y =
      uniformOfFinset (properColorings G q) hne y * recolor G y w x := by
  have hπ (z : V → Fin q) (hz : ¬IsProperColoring G z) :
      uniformOfFinset (properColorings G q) hne z = 0 := by
    rw [uniformOfFinset_apply, ite_eq_right fun h => hz ((mem_properColorings G).1 h)]
  by_cases hx : IsProperColoring G x <;> by_cases hy : IsProperColoring G y
  · rw [uniformOfFinset_apply, uniformOfFinset_apply,
      ite_eq_left ((mem_properColorings G).2 hx), ite_eq_left ((mem_properColorings G).2 hy)]
    congr 1
    rw [recolor_apply G ⟨x w, hx.mem_allowedColors w⟩,
      recolor_apply G ⟨y w, hy.mem_allowedColors w⟩]
    by_cases hxy : Function.update x w (y w) = y
    · have hyx : Function.update y w (x w) = x := by
        rw [← hxy, Function.update_idem, Function.update_eq_self]
      have hA : allowedColors G x w = allowedColors G y w :=
        allowedColors_congr G fun u hu => by
          rw [← hxy, Function.update_of_ne (G.ne_of_adj hu).symm]
      have hxA : x w ∈ allowedColors G y w := by
        rw [← hA]
        exact hx.mem_allowedColors w
      rw [hA, ite_eq_left ⟨hxy, hy.mem_allowedColors w⟩, ite_eq_left ⟨hyx, hxA⟩]
    · have hyx : Function.update y w (x w) ≠ x := fun h =>
        hxy (by rw [← h, Function.update_idem, Function.update_eq_self])
      rw [ite_eq_right fun h => hxy h.1, ite_eq_right fun h => hyx h.1]
  · rw [recolor_eq_zero_of_not_proper G hx hy, hπ y hy, mul_zero, zero_mul]
  · rw [recolor_eq_zero_of_not_proper G hy hx, hπ x hx, mul_zero, zero_mul]
  · rw [hπ x hx, hπ y hy, zero_mul, zero_mul]

/-- **Reversibility** ([LevinPeres2017], Sections 3.3.1 and 14.3): Glauber dynamics for colorings
is reversible with respect to the uniform distribution on proper colorings. -/
theorem isReversible_glauberColoring [Nonempty V] (hne : (properColorings G q).Nonempty) :
    (glauberColoring G q).IsReversible (uniformOfFinset (properColorings G q) hne) := by
  intro x y
  rw [glauberColoring_apply, glauberColoring_apply, PMF.bind_apply, PMF.bind_apply,
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun w => ?_
  rw [mul_left_comm, recolor_balance G hne x y w, mul_left_comm]

/-- The uniform distribution on proper colorings is stationary for Glauber dynamics. -/
theorem isStationary_glauberColoring [Nonempty V] (hne : (properColorings G q).Nonempty) :
    (glauberColoring G q).IsStationary (uniformOfFinset (properColorings G q) hne) :=
  (isReversible_glauberColoring G hne).isStationary

/-! ### Path coupling -/

omit [DecidableEq V] in
/-- Colorings agreeing off `v` have allowed-color sets at any vertex that differ by at most one
color on each side. -/
private theorem card_allowedColors_sdiff_le {x y : V → Fin q} {v : V}
    (hxy : ∀ u, u ≠ v → x u = y u) (w : V) :
    (allowedColors G y w \ allowedColors G x w).card ≤ 1 := by
  refine (Finset.card_le_card (t := {x v}) fun c hc => ?_).trans (Finset.card_singleton _).le
  rw [Finset.mem_sdiff, mem_allowedColors, mem_allowedColors] at hc
  obtain ⟨hy, hx⟩ := hc
  push Not at hx
  obtain ⟨u, hu, hxu⟩ := hx
  rw [Finset.mem_singleton]
  by_cases huv : u = v
  · rw [← hxu, huv]
  · exact absurd (by rw [← hxy u huv, hxu]) (hy u hu)

omit [DecidableEq V] in
/-- `1 - Δ / (q - Δ) = (q - 2Δ) / (q - Δ)`. -/
private theorem one_sub_div_eq (hq : 2 * G.maxDegree < q) :
    1 - (G.maxDegree : ℝ) / ((q - G.maxDegree : ℕ) : ℝ) =
      ((q - 2 * G.maxDegree : ℕ) : ℝ) / ((q - G.maxDegree : ℕ) : ℝ) := by
  have hD : ((q - G.maxDegree : ℕ) : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    omega
  rw [eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD, one_mul,
    Nat.cast_sub (by omega : G.maxDegree ≤ q), Nat.cast_sub (by omega : 2 * G.maxDegree ≤ q)]
  push_cast
  ring

omit [DecidableEq V] in
/-- The uniform allowed-color distributions at `w` for colorings agreeing off `v` are at
statistical distance at most `1 / (q - Δ)` if `w` is a neighbor of `v`, and coincide
otherwise. -/
private theorem dist_allowedColors_le (hq : G.maxDegree < q) {x y : V → Fin q} {v : V}
    (hxy : ∀ u, u ≠ v → x u = y u) (w : V) :
    dist (uniformOfFinset (allowedColors G x w) (allowedColors_nonempty G hq x w))
        (uniformOfFinset (allowedColors G y w) (allowedColors_nonempty G hq y w)) ≤
      if G.Adj v w then 1 / ((q - G.maxDegree : ℕ) : ℝ) else 0 := by
  split_ifs with hvw
  · refine (dist_uniformOfFinset_le _ _ (by omega) (card_allowedColors G x w)
      (card_allowedColors G y w) (card_allowedColors_sdiff_le G hxy w)
      (card_allowedColors_sdiff_le G (fun u hu => (hxy u hu).symm) w)).trans_eq ?_
    rw [Nat.cast_one]
  · have hA : allowedColors G x w = allowedColors G y w :=
      allowedColors_congr G fun u hu => hxy u fun h => hvw (h ▸ hu.symm)
    have : uniformOfFinset (allowedColors G x w) (allowedColors_nonempty G hq x w) =
        uniformOfFinset (allowedColors G y w) (allowedColors_nonempty G hq y w) := by
      congr 1
    rw [this, dist_self]

/-- **One-step contraction for colorings** ([LevinPeres2017], (14.18) and (14.19)): if `Δ < q`,
two colorings at Hamming distance one admit a coupling of one Glauber step under which the
expected Hamming distance is at most `1 - (1 - Δ / (q - Δ)) / n`. -/
theorem exists_coupling_glauberColoring [Nonempty V] (hq : G.maxDegree < q) {x y : V → Fin q}
    (hxy : hammingDist x y = 1) :
    ∃ ω : PMF ((V → Fin q) × (V → Fin q)),
      ω.map Prod.fst = glauberColoring G q x ∧ ω.map Prod.snd = glauberColoring G q y ∧
      ∑ p, (ω p).toReal * (hammingDist p.1 p.2 : ℝ) ≤
        (1 - (1 - G.maxDegree / ((q - G.maxDegree : ℕ) : ℝ)) / Fintype.card V) *
          (hammingDist x y : ℝ) := by
  classical
  obtain ⟨v, -, hv⟩ := hammingDist_eq_one_iff.1 hxy
  have γspec (w : V) := exists_coupling_toReal_eq_dist
    (uniformOfFinset (allowedColors G x w) (allowedColors_nonempty G hq x w))
    (uniformOfFinset (allowedColors G y w) (allowedColors_nonempty G hq y w))
  choose γ hγ1 hγ2 hγ3 using γspec
  have hrec (z : V → Fin q) (w : V) : recolor G z w =
      (uniformOfFinset (allowedColors G z w) (allowedColors_nonempty G hq z w)).map
        (Function.update z w) := by
    rw [recolor, dite_eq_left (allowedColors_nonempty G hq z w)]
  refine ⟨(uniformOfFintype V).bind fun w =>
    (γ w).map fun c => (Function.update x w c.1, Function.update y w c.2), ?_, ?_, ?_⟩
  · rw [PMF.map_bind, glauberColoring_apply]
    congr 1
    funext w
    rw [PMF.map_comp, hrec, ← hγ1 w, PMF.map_comp]
    rfl
  · rw [PMF.map_bind, glauberColoring_apply]
    congr 1
    funext w
    rw [PMF.map_comp, hrec, ← hγ2 w, PMF.map_comp]
    rfl
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 Fintype.card_pos
  have hD : (0 : ℝ) < ((q - G.maxDegree : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
  -- the expected distance after updating `w`
  have hw (w : V) : ∑ c, ((γ w) c).toReal *
      (hammingDist (Function.update x w c.1) (Function.update y w c.2) : ℝ) ≤
      (1 - if x w ≠ y w then 1 else 0) +
        if G.Adj v w then 1 / ((q - G.maxDegree : ℕ) : ℝ) else 0 := by
    have hupd (c : Fin q × Fin q) :
        (hammingDist (Function.update x w c.1) (Function.update y w c.2) : ℝ) =
          (1 - if x w ≠ y w then 1 else 0) + 1 * if c.1 ≠ c.2 then 1 else 0 := by
      have := hammingDist_update_update x y w c.1 c.2
      rw [hxy] at this
      have h' : ((hammingDist (Function.update x w c.1) (Function.update y w c.2) : ℕ) : ℝ) +
          ((if x w ≠ y w then 1 else 0 : ℕ) : ℝ) =
            1 + ((if c.1 ≠ c.2 then 1 else 0 : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at h'
      linarith
    simp only [hupd]
    rw [sum_affine (γ w) _ 1, one_mul]
    have hev : ∑ c, ((γ w) c).toReal * (if c.1 ≠ c.2 then (1 : ℝ) else 0) =
        ((γ w).toOuterMeasure {c | c.1 ≠ c.2}).toReal := by
      rw [toOuterMeasure_apply_toReal]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : c.1 ≠ c.2 <;> simp [hc]
    rw [hev, hγ3 w]
    exact add_le_add le_rfl (dist_allowedColors_le G hq hv w)
  have h1 : ∑ w : V, (if x w ≠ y w then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_boole]
    have h := hxy
    rw [hammingDist] at h
    exact_mod_cast h
  have h2 : ∑ w : V, (if G.Adj v w then 1 / ((q - G.maxDegree : ℕ) : ℝ) else 0) =
      G.degree v * (1 / ((q - G.maxDegree : ℕ) : ℝ)) := by
    rw [← Finset.sum_filter, ← SimpleGraph.neighborFinset_eq_filter, Finset.sum_const,
      SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  rw [hxy, Nat.cast_one, mul_one, sum_bind_mul]
  simp only [sum_map_mul]
  calc ∑ w, ((uniformOfFintype V) w).toReal * ∑ c, ((γ w) c).toReal *
        (hammingDist (Function.update x w c.1) (Function.update y w c.2) : ℝ)
      ≤ ∑ w, ((uniformOfFintype V) w).toReal *
          ((1 - if x w ≠ y w then 1 else 0) +
            if G.Adj v w then 1 / ((q - G.maxDegree : ℕ) : ℝ) else 0) :=
        Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hw w) ENNReal.toReal_nonneg
    _ = (Fintype.card V : ℝ)⁻¹ *
          (Fintype.card V - 1 + G.degree v * (1 / ((q - G.maxDegree : ℕ) : ℝ))) := by
        simp only [uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    _ ≤ (Fintype.card V : ℝ)⁻¹ *
          (Fintype.card V - 1 + G.maxDegree * (1 / ((q - G.maxDegree : ℕ) : ℝ))) := by
        have hdeg : (G.degree v : ℝ) ≤ G.maxDegree := by
          exact_mod_cast G.degree_le_maxDegree v
        refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (inv_nonneg.2 hn.le)
        exact mul_le_mul_of_nonneg_right hdeg (div_nonneg zero_le_one hD.le)
    _ = 1 - (1 - G.maxDegree / ((q - G.maxDegree : ℕ) : ℝ)) / Fintype.card V := by
        field_simp
        ring

/-- **Path coupling bound for colorings** ([LevinPeres2017], proof of Theorem 14.10): if
`2Δ < q` then `d(t) ≤ (1 - c / n) ^ t n` with `c = (q - 2Δ) / (q - Δ)`. -/
theorem distToStationary_glauberColoring_le [Nonempty V] (hq : 2 * G.maxDegree < q)
    (hne : (properColorings G q).Nonempty) (t : ℕ) :
    (glauberColoring G q).distToStationary (uniformOfFinset (properColorings G q) hne) t ≤
      (1 - ((q - 2 * G.maxDegree : ℕ) : ℝ) / ((q - G.maxDegree : ℕ) : ℝ) /
        Fintype.card V) ^ t * Fintype.card V := by
  have hq' : G.maxDegree < q := by omega
  have hn : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hD : (0 : ℝ) < ((q - G.maxDegree : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
  have hc1 : ((q - 2 * G.maxDegree : ℕ) : ℝ) / ((q - G.maxDegree : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hD]
    exact_mod_cast (by omega : q - 2 * G.maxDegree ≤ q - G.maxDegree)
  have hκ : 0 ≤ 1 - ((q - 2 * G.maxDegree : ℕ) : ℝ) / ((q - G.maxDegree : ℕ) : ℝ) /
      Fintype.card V := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  refine (isStationary_glauberColoring G hne).distToStationary_le_of_pathCoupling
    (isPathMetric_hammingDist (β := fun _ : V => Fin q)) hκ (fun x y hxy => ?_)
    (fun x y => by exact_mod_cast hammingDist_le_card_fintype) t
  rw [← one_sub_div_eq G hq]
  exact exists_coupling_glauberColoring G hq' hxy

/-- **Rapid mixing of Glauber dynamics for colorings** ([LevinPeres2017], Theorem 14.10): for a
graph with `n` vertices and maximum degree `Δ`, if `q > 2Δ` then
`t_mix(ε) ≤ ⌈((q - Δ) / (q - 2Δ)) n (log n - log ε)⌉`. -/
theorem mixingTime_glauberColoring_le [Nonempty V] (hq : 2 * G.maxDegree < q)
    (hne : (properColorings G q).Nonempty) {ε : ℝ} (hε : 0 < ε) :
    (glauberColoring G q).mixingTime (uniformOfFinset (properColorings G q) hne) ε ≤
      (⌈((q - G.maxDegree : ℕ) : ℝ) / ((q - 2 * G.maxDegree : ℕ) : ℝ) * Fintype.card V *
        (Real.log (Fintype.card V) - Real.log ε)⌉₊ : ℕ) := by
  have hq' : G.maxDegree < q := by omega
  have hn : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hD : (0 : ℝ) < ((q - G.maxDegree : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
  have hE : (0 : ℝ) < ((q - 2 * G.maxDegree : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
  have hc1 : ((q - 2 * G.maxDegree : ℕ) : ℝ) / ((q - G.maxDegree : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hD]
    exact_mod_cast (by omega : q - 2 * G.maxDegree ≤ q - G.maxDegree)
  set α := ((q - 2 * G.maxDegree : ℕ) : ℝ) / ((q - G.maxDegree : ℕ) : ℝ) / Fintype.card V
    with hα_def
  have hα : 0 < α := by positivity
  have hα1 : α ≤ 1 := by
    rw [hα_def, div_le_one (by linarith)]
    linarith
  have h := (isStationary_glauberColoring G hne).mixingTime_le_of_pathCoupling
    (isPathMetric_hammingDist (β := fun _ : V => Fin q)) (κ := 1 - α)
    (D := (Fintype.card V : ℝ)) (by linarith) hα
    (by linarith [Real.add_one_le_exp (-α)])
    (fun x y hxy => by
      rw [hα_def, ← one_sub_div_eq G hq]
      exact exists_coupling_glauberColoring G hq' hxy)
    (by linarith) (fun x y => by exact_mod_cast hammingDist_le_card_fintype) hε
  have heq : ((q - G.maxDegree : ℕ) : ℝ) / ((q - 2 * G.maxDegree : ℕ) : ℝ) * Fintype.card V *
      (Real.log (Fintype.card V) - Real.log ε) =
        (Real.log (Fintype.card V) - Real.log ε) / α := by
    rw [hα_def]
    field_simp
  rw [heq]
  exact h

end Cslib.Probability.MarkovChain
