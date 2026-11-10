/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.ProperColoring
public import CslibFrontier.Probability.MarkovChain.PathCoupling
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.StatisticalDistance.ClosedForm
import CslibFrontier.Probability.StatisticalDistance.OptimalCoupling

/-!
# Glauber dynamics for proper colorings

Glauber dynamics for `q`-colorings of a finite graph `G` with `n` vertices and maximum degree `Δ`
([LevinPeres2017], Sections 3.3.1 and 14.3): at each step a vertex `w` is chosen uniformly at
random and recolored with a color chosen uniformly from the colors absent from its neighbors
(`SimpleGraph.allowedColors`). As in [LevinPeres2017], Section 14.3, the chain runs on all
colorings `V → Fin q`, proper or not. It is reversible with respect to the uniform distribution on
proper colorings (`Cslib.Probability.MarkovChain.isReversible_glauberColoring`), which is nonempty
when `Δ < q` by greedy coloring.

**Rapid mixing** ([LevinPeres2017], Theorem 14.10). If `q > 2Δ` then
`t_mix(ε) ≤ ⌈((q - Δ) / (q - 2Δ)) n (log n - log ε)⌉`
(`Cslib.Probability.MarkovChain.mixingTime_glauberColoring_le`). The proof is path coupling for
the Hamming distance: two colorings differing at one vertex `v` are updated at the same uniformly
random vertex `w` with an optimal coupling of the two uniform color choices
(`Cslib.Probability.MarkovChain.exists_coupling_glauberColoringOn`). The colorings disagree after
the update with probability at most `1 / (q - Δ)` when `w` is a neighbor of `v`, never when
`w = v`, and stay at distance one otherwise, giving the contraction `1 - (1 - Δ / (q - Δ)) / n` of
[LevinPeres2017], (14.19).

**Frozen boundary.** The approximate counting algorithm of [LevinPeres2017], Section 14.4.2, runs
the same dynamics with only the vertices of a set `U` updated
(`Cslib.Probability.MarkovChain.glauberColoringOn`; `glauberColoring` is the case `U = univ`).
The uniform distribution on the proper colorings agreeing with a coloring `b` off `U`
(`SimpleGraph.frozenColorings`) is reversible. The chain started at a coloring
that agrees with `b` off `U` stays among such colorings, so path coupling on that closed set
(`Cslib.Probability.MarkovChain.IsStationary.dist_le_of_pathCoupling_on`) gives the bound
`(1 - c / |U|) ^ t |U|` on the distance to stationarity, `c = (q - 2Δ) / (q - Δ)`. In particular
`t ≥ ((q - Δ) / (q - 2Δ)) n (log n - log δ)` steps suffice for distance `δ` whenever `|U| ≤ n`
(`Cslib.Probability.MarkovChain.dist_glauberColoringOn_frozen_le_of_le`), the form of
[LevinPeres2017], (14.23). The chain does not mix on all of `V → Fin q`, since colorings that
differ off `U` never meet, so the bound is stated for starting colorings that agree with `b`
off `U`.

## Main definitions

* `Cslib.Probability.MarkovChain.recolor`: the heat-bath update at one vertex.
* `Cslib.Probability.MarkovChain.glauberColoringOn`: Glauber dynamics updating the vertices
  of `U`.
* `Cslib.Probability.MarkovChain.glauberColoring`: Glauber dynamics for colorings.

## Main results

* `Cslib.Probability.MarkovChain.isReversible_glauberColoring`,
  `Cslib.Probability.MarkovChain.isStationary_glauberColoring`: the uniform distribution on proper
  colorings is reversible, hence stationary.
* `Cslib.Probability.MarkovChain.isReversible_glauberColoringOn_frozen`,
  `Cslib.Probability.MarkovChain.isStationary_recolor_frozen`: the same for the frozen-boundary
  chain and for a single heat-bath update at a vertex of `U`.
* `Cslib.Probability.MarkovChain.exists_coupling_glauberColoringOn`,
  `Cslib.Probability.MarkovChain.exists_coupling_glauberColoring`: the one-step contraction
  ([LevinPeres2017], (14.18) and (14.19)).
* `Cslib.Probability.MarkovChain.distToStationary_glauberColoring_le`,
  `Cslib.Probability.MarkovChain.mixingTime_glauberColoring_le`: [LevinPeres2017], Theorem 14.10.
* `Cslib.Probability.MarkovChain.dist_glauberColoringOn_frozen_le`,
  `Cslib.Probability.MarkovChain.dist_glauberColoringOn_frozen_le_of_le`: the frozen-boundary
  form used in [LevinPeres2017], proof of Theorem 14.14.

## References

* [LevinPeres2017], Sections 3.3.1, 14.3 and 14.4.2.
-/

public section

open scoped ENNReal Cslib.Probability.PMF

namespace Cslib.Probability.MarkovChain

open Cslib.Probability.PMF SimpleGraph

variable {V : Type*} {q : ℕ} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Glauber dynamics -/

/-- The heat-bath update at `w`: recolor `w` with a uniformly random allowed color. If no color
is allowed, which cannot happen when `Δ < q` or when `x` is proper, the coloring is unchanged. -/
noncomputable def recolor (x : V → Fin q) (w : V) : PMF (V → Fin q) :=
  if h : (G.allowedColors x w).Nonempty then
    (uniformOfFinset (G.allowedColors x w) h).map (Function.update x w)
  else PMF.pure x

theorem recolor_of_nonempty {x : V → Fin q} {w : V} (h : (G.allowedColors x w).Nonempty) :
    recolor G x w = (uniformOfFinset (G.allowedColors x w) h).map (Function.update x w) := by
  rw [recolor, dite_eq_left h]

/-- **Glauber dynamics updating the vertices of `U`** ([LevinPeres2017], proof of Theorem 14.14):
recolor a uniformly random vertex of `U` with a uniformly random color absent from its neighbors.
The colors off `U` are frozen. -/
noncomputable def glauberColoringOn (q : ℕ) (U : Finset V) (hU : U.Nonempty) :
    MarkovChain (V → Fin q) where
  step x := (uniformOfFinset U hU).bind (recolor G x)

theorem glauberColoringOn_apply {U : Finset V} (hU : U.Nonempty) (x : V → Fin q) :
    glauberColoringOn G q U hU x = (uniformOfFinset U hU).bind (recolor G x) := by
  rfl

/-- **Glauber dynamics for colorings** ([LevinPeres2017], Sections 3.3.1 and 14.3): recolor a
uniformly random vertex with a uniformly random color absent from its neighbors. -/
noncomputable def glauberColoring [Nonempty V] (q : ℕ) : MarkovChain (V → Fin q) :=
  glauberColoringOn G q Finset.univ Finset.univ_nonempty

theorem glauberColoring_eq_glauberColoringOn [Nonempty V] :
    glauberColoring G q = glauberColoringOn G q Finset.univ Finset.univ_nonempty := by
  rfl

theorem glauberColoring_apply [Nonempty V] (x : V → Fin q) :
    glauberColoring G q x = (uniformOfFintype V).bind (recolor G x) := by
  rfl

/-- The heat-bath update moves to `y` with probability `1 / |A_w(x)|` if `y` agrees with `x` off
`w` and `y w` is allowed. -/
theorem recolor_apply {x : V → Fin q} {w : V} (h : (G.allowedColors x w).Nonempty)
    (y : V → Fin q) : recolor G x w y =
      if Function.update x w (y w) = y ∧ y w ∈ G.allowedColors x w then
        ((G.allowedColors x w).card : ℝ≥0∞)⁻¹ else 0 := by
  rw [recolor_of_nonempty G h, PMF.map_apply, tsum_eq_single (y w)]
  · by_cases hy : Function.update x w (y w) = y
    · rw [ite_eq_left hy.symm, uniformOfFinset_apply]
      by_cases hm : y w ∈ G.allowedColors x w
      · rw [ite_eq_left hm, ite_eq_left ⟨hy, hm⟩]
      · rw [ite_eq_right hm, ite_eq_right fun h => hm h.2]
    · rw [ite_eq_right (Ne.symm hy), ite_eq_right fun h => hy h.1]
  · intro c hc
    rw [ite_eq_right]
    intro hyc
    exact hc (by rw [hyc, Function.update_self])

/-- The heat-bath update at `w` changes only the color of `w`. -/
theorem eq_of_mem_support_recolor {x y : V → Fin q} {w : V} (hy : y ∈ (recolor G x w).support)
    {u : V} (hu : u ≠ w) : y u = x u := by
  unfold recolor at hy
  split_ifs at hy with h
  · obtain ⟨c, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
    exact Function.update_of_ne hu _ _
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hy
    rw [hy]

/-! ### Stationarity -/

/-- Detailed balance for a single heat-bath update at `w`, for the uniform distribution on a set
`T` of proper colorings closed under recoloring `w` with an allowed color. -/
private theorem recolor_balance {T : Finset (V → Fin q)} (hT : T.Nonempty)
    (hTp : ∀ x ∈ T, G.IsProperColoring x) {w : V}
    (hTw : ∀ x ∈ T, ∀ c ∈ G.allowedColors x w, Function.update x w c ∈ T) (x y : V → Fin q) :
    uniformOfFinset T hT x * recolor G x w y = uniformOfFinset T hT y * recolor G y w x := by
  have hπ (z : V → Fin q) (hz : z ∉ T) : uniformOfFinset T hT z = 0 := by
    rw [uniformOfFinset_apply, ite_eq_right fun h => hz h]
  have hzero {x y : V → Fin q} (hx : x ∈ T) (hy : y ∉ T) : recolor G x w y = 0 := by
    rw [recolor_apply G ⟨x w, (hTp x hx).mem_allowedColors w⟩, ite_eq_right]
    rintro ⟨hupd, hmem⟩
    exact hy (hupd ▸ hTw x hx _ hmem)
  by_cases hx : x ∈ T <;> by_cases hy : y ∈ T
  · rw [uniformOfFinset_apply, uniformOfFinset_apply, ite_eq_left hx, ite_eq_left hy]
    congr 1
    rw [recolor_apply G ⟨x w, (hTp x hx).mem_allowedColors w⟩,
      recolor_apply G ⟨y w, (hTp y hy).mem_allowedColors w⟩]
    by_cases hxy : Function.update x w (y w) = y
    · have hyx : Function.update y w (x w) = x := by
        rw [← hxy, Function.update_idem, Function.update_eq_self]
      have hA : G.allowedColors x w = G.allowedColors y w :=
        G.allowedColors_congr fun u hu => by
          rw [← hxy, Function.update_of_ne (G.ne_of_adj hu).symm]
      have hxA : x w ∈ G.allowedColors y w := by
        rw [← hA]
        exact (hTp x hx).mem_allowedColors w
      rw [hA, ite_eq_left ⟨hxy, (hTp y hy).mem_allowedColors w⟩, ite_eq_left ⟨hyx, hxA⟩]
    · have hyx : Function.update y w (x w) ≠ x := fun h =>
        hxy (by rw [← h, Function.update_idem, Function.update_eq_self])
      rw [ite_eq_right fun h => hxy h.1, ite_eq_right fun h => hyx h.1]
  · rw [hzero hx hy, hπ y hy, mul_zero, zero_mul]
  · rw [hzero hy hx, hπ x hx, mul_zero, zero_mul]
  · rw [hπ x hx, hπ y hy, zero_mul, zero_mul]

/-- Proper colorings are closed under recoloring a vertex with an allowed color. -/
private theorem properColorings_closed {w : V} :
    ∀ x ∈ G.properColorings q, ∀ c ∈ G.allowedColors x w,
      Function.update x w c ∈ G.properColorings q := fun _ hx _ hc =>
  (mem_properColorings G).2 (((mem_properColorings G).1 hx).update_of_mem hc)

/-- Colorings frozen off `U` are closed under recoloring a vertex of `U` with an allowed
color. -/
private theorem frozenColorings_closed {U : Finset V} {b : V → Fin q} {w : V} (hw : w ∈ U) :
    ∀ x ∈ frozenColorings G q U b, ∀ c ∈ G.allowedColors x w,
      Function.update x w c ∈ frozenColorings G q U b := by
  intro x hx c hc
  obtain ⟨hxp, hxb⟩ := mem_frozenColorings.1 hx
  refine mem_frozenColorings.2 ⟨hxp.update_of_mem hc, fun u hu => ?_⟩
  rw [Function.update_of_ne (show u ≠ w from fun h => hu (h ▸ hw))]
  exact hxb u hu

/-- Reversibility of `glauberColoringOn` for the uniform distribution on a set of proper
colorings closed under recoloring the vertices of `U`. -/
private theorem isReversible_glauberColoringOn_of_closed {U : Finset V} (hU : U.Nonempty)
    {T : Finset (V → Fin q)} (hT : T.Nonempty) (hTp : ∀ x ∈ T, G.IsProperColoring x)
    (hTw : ∀ w ∈ U, ∀ x ∈ T, ∀ c ∈ G.allowedColors x w, Function.update x w c ∈ T) :
    (glauberColoringOn G q U hU).IsReversible (uniformOfFinset T hT) := by
  intro x y
  rw [glauberColoringOn_apply, glauberColoringOn_apply, PMF.bind_apply, PMF.bind_apply,
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun w => ?_
  by_cases hw : w ∈ U
  · rw [mul_left_comm, recolor_balance G hT hTp (hTw w hw) x y, mul_left_comm]
  · have h0 : uniformOfFinset U hU w = 0 := by
      rw [uniformOfFinset_apply, ite_eq_right fun h => hw h]
    simp only [h0, zero_mul, mul_zero]

/-- **Reversibility** ([LevinPeres2017], Sections 3.3.1 and 14.3): Glauber dynamics for colorings
is reversible with respect to the uniform distribution on proper colorings. -/
theorem isReversible_glauberColoring [Nonempty V] (hne : (G.properColorings q).Nonempty) :
    (glauberColoring G q).IsReversible (uniformOfFinset (G.properColorings q) hne) :=
  isReversible_glauberColoringOn_of_closed G _ hne (fun _ hx => (mem_properColorings G).1 hx)
    fun _ _ => properColorings_closed G

/-- The uniform distribution on proper colorings is stationary for Glauber dynamics. -/
theorem isStationary_glauberColoring [Nonempty V] (hne : (G.properColorings q).Nonempty) :
    (glauberColoring G q).IsStationary (uniformOfFinset (G.properColorings q) hne) :=
  (isReversible_glauberColoring G hne).isStationary

/-- **Reversibility with a frozen boundary** ([LevinPeres2017], proof of Theorem 14.14): the
uniform distribution on the proper colorings agreeing with `b` off `U` is reversible for the
dynamics updating the vertices of `U`. -/
theorem isReversible_glauberColoringOn_frozen {U : Finset V} (hU : U.Nonempty) {b : V → Fin q}
    (hne : (frozenColorings G q U b).Nonempty) :
    (glauberColoringOn G q U hU).IsReversible (uniformOfFinset (frozenColorings G q U b) hne) :=
  isReversible_glauberColoringOn_of_closed G hU hne
    (fun _ hx => (mem_frozenColorings.1 hx).1) fun _ hw => frozenColorings_closed G hw

theorem isStationary_glauberColoringOn_frozen {U : Finset V} (hU : U.Nonempty) {b : V → Fin q}
    (hne : (frozenColorings G q U b).Nonempty) :
    (glauberColoringOn G q U hU).IsStationary (uniformOfFinset (frozenColorings G q U b) hne) :=
  (isReversible_glauberColoringOn_frozen G hU hne).isStationary

/-- A single heat-bath update at a vertex `w ∈ U` preserves the uniform distribution on the
colorings frozen off `U`. -/
theorem isStationary_recolor_frozen {U : Finset V} {b : V → Fin q}
    (hne : (frozenColorings G q U b).Nonempty) {w : V} (hw : w ∈ U) :
    (⟨fun x => recolor G x w⟩ : MarkovChain (V → Fin q)).IsStationary
      (uniformOfFinset (frozenColorings G q U b) hne) :=
  IsReversible.isStationary fun x y =>
    recolor_balance G hne (fun _ hx => (mem_frozenColorings.1 hx).1)
      (frozenColorings_closed G hw) x y

/-! ### Path coupling -/

omit [DecidableEq V] in
/-- Colorings agreeing off `v` have allowed-color sets at any vertex that differ by at most one
color on each side. -/
private theorem card_allowedColors_sdiff_le {x y : V → Fin q} {v : V}
    (hxy : ∀ u, u ≠ v → x u = y u) (w : V) :
    (G.allowedColors y w \ G.allowedColors x w).card ≤ 1 := by
  refine (Finset.card_le_card (t := {x v}) fun c hc => ?_).trans (Finset.card_singleton _).le
  rw [Finset.mem_sdiff, mem_allowedColors, mem_allowedColors] at hc
  obtain ⟨hy, hx⟩ := hc
  push Not at hx
  obtain ⟨u, hu, hxu⟩ := hx
  rw [Finset.mem_singleton]
  by_cases huv : u = v
  · rw [← hxu, huv]
  · exact absurd (by rw [← hxy u huv, hxu]) (hy u hu)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- `1 - Δ / (q - Δ) = (q - 2Δ) / (q - Δ)`. -/
private theorem one_sub_div_eq [Fintype V] [DecidableRel G.Adj] (hq : 2 * G.maxDegree < q) :
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
    dist (uniformOfFinset (G.allowedColors x w) (G.allowedColors_nonempty hq x w))
        (uniformOfFinset (G.allowedColors y w) (G.allowedColors_nonempty hq y w)) ≤
      if G.Adj v w then 1 / ((q - G.maxDegree : ℕ) : ℝ) else 0 := by
  split_ifs with hvw
  · refine (dist_uniformOfFinset_le _ _ (by omega) (G.sub_maxDegree_le_card_allowedColors x w)
      (G.sub_maxDegree_le_card_allowedColors y w) (card_allowedColors_sdiff_le G hxy w)
      (card_allowedColors_sdiff_le G (fun u hu => (hxy u hu).symm) w)).trans_eq ?_
    rw [Nat.cast_one]
  · have hA : G.allowedColors x w = G.allowedColors y w :=
      G.allowedColors_congr fun u hu => hxy u fun h => hvw (h ▸ hu.symm)
    have : uniformOfFinset (G.allowedColors x w) (G.allowedColors_nonempty hq x w) =
        uniformOfFinset (G.allowedColors y w) (G.allowedColors_nonempty hq y w) := by
      congr 1
    rw [this, dist_self]

/-- **One-step contraction with a frozen boundary** ([LevinPeres2017], (14.18) and (14.19)): if
`Δ < q`, two colorings at Hamming distance one that agree off `U` admit a coupling of one step of
the dynamics updating `U` under which the expected Hamming distance is at most
`1 - (1 - Δ / (q - Δ)) / |U|`. -/
theorem exists_coupling_glauberColoringOn (hq : G.maxDegree < q) {U : Finset V}
    (hU : U.Nonempty) {x y : V → Fin q} (hxy : hammingDist x y = 1)
    (hU' : ∀ u ∉ U, x u = y u) :
    ∃ ω : PMF ((V → Fin q) × (V → Fin q)),
      ω.map Prod.fst = glauberColoringOn G q U hU x ∧
      ω.map Prod.snd = glauberColoringOn G q U hU y ∧
      ∑ p, (ω p).toReal * (hammingDist p.1 p.2 : ℝ) ≤
        (1 - (1 - G.maxDegree / ((q - G.maxDegree : ℕ) : ℝ)) / U.card) *
          (hammingDist x y : ℝ) := by
  classical
  obtain ⟨v, hvne, hv⟩ := hammingDist_eq_one_iff.1 hxy
  have hvU : v ∈ U := by
    by_contra h
    exact hvne (hU' v h)
  have γspec (w : V) := exists_coupling_toReal_eq_dist
    (uniformOfFinset (G.allowedColors x w) (G.allowedColors_nonempty hq x w))
    (uniformOfFinset (G.allowedColors y w) (G.allowedColors_nonempty hq y w))
  choose γ hγ1 hγ2 hγ3 using γspec
  refine ⟨(uniformOfFinset U hU).bind fun w =>
    (γ w).map fun c => (Function.update x w c.1, Function.update y w c.2), ?_, ?_, ?_⟩
  · rw [PMF.map_bind, glauberColoringOn_apply]
    congr 1
    funext w
    rw [PMF.map_comp, recolor_of_nonempty G (G.allowedColors_nonempty hq x w), ← hγ1 w,
      PMF.map_comp]
    rfl
  · rw [PMF.map_bind, glauberColoringOn_apply]
    congr 1
    funext w
    rw [PMF.map_comp, recolor_of_nonempty G (G.allowedColors_nonempty hq y w), ← hγ2 w,
      PMF.map_comp]
    rfl
  have hn : (0 : ℝ) < U.card := Nat.cast_pos.2 hU.card_pos
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
  have h1 : ∑ w ∈ U, (if x w ≠ y w then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single v (fun w _ hwv => ite_eq_right (not_not.2 (hv w hwv)))
      (fun h => absurd hvU h), ite_eq_left hvne]
  have h2 : ∑ w ∈ U, (if G.Adj v w then 1 / ((q - G.maxDegree : ℕ) : ℝ) else 0) ≤
      G.maxDegree * (1 / ((q - G.maxDegree : ℕ) : ℝ)) := by
    calc ∑ w ∈ U, (if G.Adj v w then 1 / ((q - G.maxDegree : ℕ) : ℝ) else 0)
        ≤ ∑ w, (if G.Adj v w then 1 / ((q - G.maxDegree : ℕ) : ℝ) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
            fun _ _ _ => by split_ifs <;> positivity
      _ = G.degree v * (1 / ((q - G.maxDegree : ℕ) : ℝ)) := by
          rw [← Finset.sum_filter, ← SimpleGraph.neighborFinset_eq_filter, Finset.sum_const,
            SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
      _ ≤ G.maxDegree * (1 / ((q - G.maxDegree : ℕ) : ℝ)) := by
          have hdeg : (G.degree v : ℝ) ≤ G.maxDegree := by
            exact_mod_cast G.degree_le_maxDegree v
          exact mul_le_mul_of_nonneg_right hdeg (div_nonneg zero_le_one hD.le)
  have hunif (w : V) : ((uniformOfFinset U hU) w).toReal =
      if w ∈ U then (U.card : ℝ)⁻¹ else 0 := by
    rw [uniformOfFinset_apply]
    split_ifs <;> simp
  rw [hxy, Nat.cast_one, mul_one, sum_bind_mul]
  simp only [sum_map_mul]
  calc ∑ w, ((uniformOfFinset U hU) w).toReal * ∑ c, ((γ w) c).toReal *
        (hammingDist (Function.update x w c.1) (Function.update y w c.2) : ℝ)
      ≤ ∑ w, ((uniformOfFinset U hU) w).toReal *
          ((1 - if x w ≠ y w then 1 else 0) +
            if G.Adj v w then 1 / ((q - G.maxDegree : ℕ) : ℝ) else 0) :=
        Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hw w) ENNReal.toReal_nonneg
    _ = (U.card : ℝ)⁻¹ * ∑ w ∈ U, ((1 - if x w ≠ y w then 1 else 0) +
            if G.Adj v w then 1 / ((q - G.maxDegree : ℕ) : ℝ) else 0) := by
        simp only [hunif, ite_mul, zero_mul]
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.mul_sum]
    _ ≤ (U.card : ℝ)⁻¹ *
          (U.card - 1 + G.maxDegree * (1 / ((q - G.maxDegree : ℕ) : ℝ))) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, Finset.sum_const, nsmul_eq_mul,
          mul_one]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl h2) (inv_nonneg.2 hn.le)
    _ = 1 - (1 - G.maxDegree / ((q - G.maxDegree : ℕ) : ℝ)) / U.card := by
        field_simp
        ring

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
  have h := exists_coupling_glauberColoringOn G hq Finset.univ_nonempty hxy
    fun u hu => absurd (Finset.mem_univ u) hu
  rwa [Finset.card_univ] at h

/-- **Path coupling bound for colorings** ([LevinPeres2017], proof of Theorem 14.10): if
`2Δ < q` then `d(t) ≤ (1 - c / n) ^ t n` with `c = (q - 2Δ) / (q - Δ)`. -/
theorem distToStationary_glauberColoring_le [Nonempty V] (hq : 2 * G.maxDegree < q)
    (hne : (G.properColorings q).Nonempty) (t : ℕ) :
    (glauberColoring G q).distToStationary (uniformOfFinset (G.properColorings q) hne) t ≤
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
    (hne : (G.properColorings q).Nonempty) {ε : ℝ} (hε : 0 < ε) :
    (glauberColoring G q).mixingTime (uniformOfFinset (G.properColorings q) hne) ε ≤
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

/-! ### Mixing with a frozen boundary -/

/-- **Path coupling bound with a frozen boundary** ([LevinPeres2017], proof of Theorem 14.14): if
`2Δ < q`, then from any coloring `x` that agrees with `b` off `U`, `t` steps of the dynamics
updating `U` are within `(1 - c / |U|) ^ t |U|` of the uniform distribution on the proper
colorings agreeing with `b` off `U`, where `c = (q - 2Δ) / (q - Δ)`. -/
theorem dist_glauberColoringOn_frozen_le (hq : 2 * G.maxDegree < q) {U : Finset V}
    (hU : U.Nonempty) {b : V → Fin q} (hne : (frozenColorings G q U b).Nonempty) (t : ℕ)
    {x : V → Fin q} (hx : ∀ u ∉ U, x u = b u) :
    dist ((glauberColoringOn G q U hU ^ t) x) (uniformOfFinset (frozenColorings G q U b) hne) ≤
      (1 - ((q - 2 * G.maxDegree : ℕ) : ℝ) / ((q - G.maxDegree : ℕ) : ℝ) / U.card) ^ t *
        U.card := by
  have hq' : G.maxDegree < q := by omega
  have hn : (1 : ℝ) ≤ U.card := by exact_mod_cast hU.card_pos
  have hD : (0 : ℝ) < ((q - G.maxDegree : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
  have hc1 : ((q - 2 * G.maxDegree : ℕ) : ℝ) / ((q - G.maxDegree : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hD]
    exact_mod_cast (by omega : q - 2 * G.maxDegree ≤ q - G.maxDegree)
  have hκ : 0 ≤ 1 - ((q - 2 * G.maxDegree : ℕ) : ℝ) / ((q - G.maxDegree : ℕ) : ℝ) /
      U.card := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  set C : Set (V → Fin q) := {z | ∀ u ∉ U, z u = b u} with hC
  refine (isStationary_glauberColoringOn_frozen G hU hne).dist_le_of_pathCoupling_on
    (C := C) ?_ (isPathMetricOn_hammingDist ?_) ?_ hκ ?_ (D := (U.card : ℝ)) ?_ t hx
  · intro z hz
    exact (mem_frozenColorings.1 ((mem_support_uniformOfFinset_iff hne z).1 hz)).2
  · intro z hz z' hz' i u hu
    by_cases hui : u = i
    · subst hui
      rw [Function.update_self]
      exact hz' u hu
    · rw [Function.update_of_ne hui]
      exact hz u hu
  · intro z hz z' hz' u hu
    rw [glauberColoringOn_apply] at hz'
    obtain ⟨w, hw, hz'w⟩ := (PMF.mem_support_bind_iff _ _ _).1 hz'
    have hwU : w ∈ U := (mem_support_uniformOfFinset_iff hU w).1 hw
    rw [eq_of_mem_support_recolor G hz'w (show u ≠ w from fun h => hu (h ▸ hwU))]
    exact hz u hu
  · intro z hz z' hz' hzz'
    rw [← one_sub_div_eq G hq]
    exact exists_coupling_glauberColoringOn G hq' hU hzz'
      fun u hu => (hz u hu).trans (hz' u hu).symm
  · intro z hz z' hz'
    have hsub : (Finset.univ.filter fun u => z u ≠ z' u) ⊆ U := by
      intro u hu
      by_contra h
      exact (Finset.mem_filter.1 hu).2 ((hz u h).trans (hz' u h).symm)
    exact_mod_cast Finset.card_le_card hsub

/-- **Frozen-boundary sampling time** ([LevinPeres2017], (14.23)): if `2Δ < q`, `|U| ≤ n` and
`t ≥ ((q - Δ) / (q - 2Δ)) n (log n - log δ)`, then from any coloring that agrees with `b` off `U`,
`t` steps of the dynamics updating `U` are within `δ` of the uniform distribution on the proper
colorings agreeing with `b` off `U`. -/
theorem dist_glauberColoringOn_frozen_le_of_le (hq : 2 * G.maxDegree < q) {U : Finset V}
    (hU : U.Nonempty) {b : V → Fin q} (hne : (frozenColorings G q U b).Nonempty) {n : ℕ}
    (hn : U.card ≤ n) {δ : ℝ} (hδ : 0 < δ) {t : ℕ}
    (ht : ((q - G.maxDegree : ℕ) : ℝ) / ((q - 2 * G.maxDegree : ℕ) : ℝ) * n *
      (Real.log n - Real.log δ) ≤ t)
    {x : V → Fin q} (hx : ∀ u ∉ U, x u = b u) :
    dist ((glauberColoringOn G q U hU ^ t) x) (uniformOfFinset (frozenColorings G q U b) hne) ≤
      δ := by
  refine (dist_glauberColoringOn_frozen_le G hq hU hne t hx).trans ?_
  have hD : (0 : ℝ) < ((q - G.maxDegree : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
  have hE : (0 : ℝ) < ((q - 2 * G.maxDegree : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
  set c := ((q - 2 * G.maxDegree : ℕ) : ℝ) / ((q - G.maxDegree : ℕ) : ℝ) with hc_def
  have hc : 0 < c := div_pos hE hD
  have hk : (0 : ℝ) < U.card := Nat.cast_pos.2 hU.card_pos
  have hkn : (U.card : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := hk.trans_le hkn
  have hc1 : c ≤ 1 := by
    rw [hc_def, div_le_one hD]
    exact_mod_cast (by omega : q - 2 * G.maxDegree ≤ q - G.maxDegree)
  have hck : c / U.card ≤ 1 := by
    rw [div_le_one hk]
    exact hc1.trans (by exact_mod_cast hU.card_pos)
  have ht' : n * (Real.log n - Real.log δ) ≤ c * t := by
    have h1 : ((q - G.maxDegree : ℕ) : ℝ) / ((q - 2 * G.maxDegree : ℕ) : ℝ) = c⁻¹ := by
      rw [hc_def, inv_div]
    rw [h1] at ht
    have := mul_le_mul_of_nonneg_left ht hc.le
    calc n * (Real.log n - Real.log δ) = c * (c⁻¹ * n * (Real.log n - Real.log δ)) := by
          field_simp
      _ ≤ c * t := this
  calc (1 - c / U.card) ^ t * U.card
      ≤ Real.exp (-(c / U.card)) ^ t * U.card :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-(c / U.card))]) t)
          hk.le
    _ = Real.exp (-(c * t / U.card)) * U.card := by
        rw [← Real.exp_nat_mul]
        ring_nf
    _ ≤ Real.exp (-(c * t / n)) * n := by
        refine mul_le_mul (Real.exp_le_exp.2 ?_) hkn hk.le (Real.exp_pos _).le
        rw [neg_le_neg_iff]
        exact div_le_div_of_nonneg_left (by positivity) hk hkn
    _ ≤ Real.exp (-(Real.log n - Real.log δ)) * n := by
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hn0.le
        rw [neg_le_neg_iff, le_div_iff₀ hn0]
        linarith
    _ = δ := by
        rw [neg_sub, Real.exp_sub, Real.exp_log hδ, Real.exp_log hn0]
        field_simp

end Cslib.Probability.MarkovChain
