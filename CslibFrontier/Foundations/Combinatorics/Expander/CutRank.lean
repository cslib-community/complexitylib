/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Mixing
public import CslibFrontier.Foundations.Combinatorics.Expander.SimpleGraph
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.CutRank

/-!
# Spectral expansion and cut rank

The sharp mixing lemma gives Tanner's neighborhood estimate
[Hoory, Linial, and Wigderson, Theorem 4.15][HooryLinialWigderson2006]: for a simple regular
rotation map with normalized spectral expansion `μ`, a set of `s` vertices in an `n`-vertex graph
has at least `s * n / (s + μ² * (n - s))` neighbors. A row basis of the cut matrix covers every
exterior neighbor. Combining these facts gives, over every field,

`(1 - μ²) * s * (n - s) ≤ d * cutRank(S) * (s + μ² * (n - s))`.

Both statements are expressed without division. Thus the estimates include empty sets, and
the cut-rank statement does not require choosing an induced matching. The graph is supplied
as a simple rotation map; this module does not construct a near-Ramanujan family.

## Main results

* `Cslib.RotationMap.IsSimple.card_mul_card_le_card_neighbors_mul`: Tanner's neighborhood
  estimate from the sharp mixing lemma.
* `Cslib.RotationMap.IsSimple.mul_card_mul_card_compl_le_cutRank_mul`: the resulting
  quantitative cut-rank estimate over every field.
* `Cslib.RotationMap.IsSimple.card_le_fortyOne_mul_cutRank`: a simple degree-seven graph with
  normalized spectral expansion at most `7 / 10` has cut rank at least `n / 41` across every
  cut whose two sides have at least `n / 3` vertices.

## References

* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
* [C. Lee, J. Lee, and S. Oum, *Rank-width of random graphs*][LeeLeeOum2012]
-/

public section

namespace Cslib.RotationMap

open Finset Matrix
open scoped BigOperators

private theorem tanner_of_mixing {s t n d μ : ℝ} (hs : 0 < s) (ht : 0 ≤ t)
    (hn : 0 < n) (hsn : s ≤ n) (htn : t ≤ n) (hd : 0 < d)
    (hmix : |d * s - d * s * t / n| ≤
      μ * d * Real.sqrt (s * (n - s) * t * (n - t)) / n) :
    s * n ≤ t * (s + μ ^ 2 * (n - s)) := by
  by_cases htn' : t < n
  · have hns : 0 ≤ n - s := sub_nonneg.mpr hsn
    have hnt : 0 < n - t := sub_pos.mpr htn'
    have hpos : 0 < s * (n - t) := mul_pos hs hnt
    have hleft : d * s - d * s * t / n = d * s * (n - t) / n := by
      field_simp [ne_of_gt hn]
    rw [hleft, abs_of_nonneg (by positivity)] at hmix
    have hmul := (div_le_div_iff_of_pos_right hn).mp hmix
    have hbound : s * (n - t) ≤ μ * Real.sqrt (s * (n - s) * t * (n - t)) := by
      have hscaled : d * (s * (n - t)) ≤
          d * (μ * Real.sqrt (s * (n - s) * t * (n - t))) := by
        convert hmul using 1 <;> ring
      exact le_of_mul_le_mul_left hscaled hd
    have hsqrt : Real.sqrt (s * (n - s) * t * (n - t)) ^ 2 =
        s * (n - s) * t * (n - t) := Real.sq_sqrt (by positivity)
    have hsq := pow_le_pow_left₀ hpos.le hbound 2
    simp only [mul_pow, hsqrt] at hsq
    have hfactor : (s * (n - t)) * (s * (n - t)) ≤
        (s * (n - t)) * (μ ^ 2 * t * (n - s)) := by
      convert hsq using 1 <;> ring
    have hcancel := le_of_mul_le_mul_left hfactor hpos
    nlinarith only [hcancel]
  · have htEq : t = n := le_antisymm htn (le_of_not_gt htn')
    rw [htEq]
    have hnonneg : 0 ≤ n * (μ ^ 2 * (n - s)) :=
      mul_nonneg hn.le (mul_nonneg (sq_nonneg μ) (sub_nonneg.mpr hsn))
    nlinarith only [hnonneg]

variable {V D K : Type*} [Fintype V] [Fintype D] [Nonempty D] [DecidableEq V]
  {G : RotationMap V D}

/-- **Tanner's neighborhood estimate**, in division-free form
[Hoory, Linial, and Wigderson, Theorem 4.15][HooryLinialWigderson2006]. The normalized spectral
bound controls the full neighborhood of every vertex set, including neighbors inside the set. -/
theorem IsSimple.card_mul_card_le_card_neighbors_mul (hG : G.IsSimple) (S : Finset V) :
    (#S : ℝ) * Fintype.card V ≤
      #(S.biUnion (fun v ↦ G.toSimpleGraph.neighborFinset v)) *
        (#S + G.spectralExpansion ^ 2 * (Fintype.card V - #S)) := by
  classical
  by_cases hS : S = ∅
  · simp [hS]
  have hSne : S.Nonempty := nonempty_iff_ne_empty.mpr hS
  have : Nonempty V := ⟨hSne.choose⟩
  let T := S.biUnion (fun v ↦ G.toSimpleGraph.neighborFinset v)
  have hinter : G.interedges S T = S ×ˢ univ := by
    ext p
    simp only [mem_interedges, mem_product, mem_univ, and_true]
    constructor
    · exact And.left
    · intro hp
      refine ⟨hp, mem_biUnion.mpr ⟨p.1, hp, ?_⟩⟩
      exact (G.toSimpleGraph.mem_neighborFinset _ _).mpr
        (hG.toSimpleGraph_adj_iff.mpr ⟨p.2, rfl⟩)
  have hmix := G.abs_card_interedges_sub_le S T
  simp only [hinter, card_product, card_univ, Nat.cast_mul, card_compl,
    Nat.cast_sub (card_le_univ S), Nat.cast_sub (card_le_univ T)] at hmix
  have hmix' : |(Fintype.card D : ℝ) * #S - Fintype.card D * #S * #T / Fintype.card V| ≤
      G.spectralExpansion * Fintype.card D *
        Real.sqrt ((#S : ℝ) * (Fintype.card V - #S) * #T * (Fintype.card V - #T)) /
          Fintype.card V := by
    simpa only [mul_comm (#S : ℝ) (Fintype.card D : ℝ)] using hmix
  exact tanner_of_mixing (Nat.cast_pos.mpr (card_pos.mpr hSne)) (Nat.cast_nonneg _)
    (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_le.mpr (card_le_univ S))
    (Nat.cast_le.mpr (card_le_univ T)) (Nat.cast_pos.mpr Fintype.card_pos) hmix'

/-- Spectral neighborhood expansion gives a cut-rank lower bound over every field. Writing
`s = |S|`, `n = |V|`, `d = |D|`, and `μ = G.spectralExpansion`, this is
`(1 - μ²) s (n - s) ≤ d * cutRank(S) * (s + μ² (n - s))`. -/
theorem IsSimple.mul_card_mul_card_compl_le_cutRank_mul [Field K] (hG : G.IsSimple)
    (S : Finset V) :
    (1 - G.spectralExpansion ^ 2) * (#S : ℝ) * (Fintype.card V - #S) ≤
      Fintype.card D * ((G.toSimpleGraph.adjMatrix K).cutRank (↑S : Set V) : ℝ) *
        (#S + G.spectralExpansion ^ 2 * (Fintype.card V - #S)) := by
  have hneighbor := hG.card_mul_card_le_card_neighbors_mul S
  have hcover := G.toSimpleGraph.card_neighbors_le_card_add_cutRank_mul (K := K) S
    (Fintype.card D) (fun v _ ↦ (hG.isRegularOfDegree v).le)
  have hcover' : (#(S.biUnion (fun v ↦ G.toSimpleGraph.neighborFinset v)) : ℝ) ≤
      #S + ((G.toSimpleGraph.adjMatrix K).cutRank (↑S : Set V) : ℝ) * Fintype.card D := by
    exact_mod_cast hcover
  have hnonneg : 0 ≤ (#S : ℝ) + G.spectralExpansion ^ 2 * (Fintype.card V - #S) :=
    add_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (Nat.cast_le.mpr (card_le_univ S))))
  have hcombined := hneighbor.trans (mul_le_mul_of_nonneg_right hcover' hnonneg)
  calc
    (1 - G.spectralExpansion ^ 2) * (#S : ℝ) * (Fintype.card V - #S) =
        (#S : ℝ) * Fintype.card V -
          #S * (#S + G.spectralExpansion ^ 2 * (Fintype.card V - #S)) := by ring
    _ ≤ (#S + ((G.toSimpleGraph.adjMatrix K).cutRank (↑S : Set V) : ℝ) * Fintype.card D) *
          (#S + G.spectralExpansion ^ 2 * (Fintype.card V - #S)) -
            #S * (#S + G.spectralExpansion ^ 2 * (Fintype.card V - #S)) :=
      sub_le_sub_right hcombined _
    _ = _ := by ring

private theorem balanced_cut_rank_bound {n s r : ℝ} (hn : 0 ≤ n) (hr : 0 ≤ r)
    (hlo : n ≤ 3 * s) (hhi : 2 * s ≤ n)
    (hbound : (51 / 100 : ℝ) * s * (n - s) ≤
      7 * r * (s + (49 / 100 : ℝ) * (n - s))) : n ≤ 41 * r := by
  by_cases hn0 : n = 0
  · rw [hn0]
    positivity
  have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm hn0)
  have hspos : 0 < s := by linarith
  have hns : 0 ≤ n - s := by linarith
  have hden : 0 < 7 * (s + (49 / 100 : ℝ) * (n - s)) := by positivity
  have hprod : 0 ≤ (3 * s - n) * (n - 2 * s) :=
    mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  have hprod' : 0 ≤ n * (n - 2 * s) := mul_nonneg hn (sub_nonneg.mpr hhi)
  have hpoly : n * (7 * (s + (49 / 100 : ℝ) * (n - s))) ≤
      41 * ((51 / 100 : ℝ) * s * (n - s)) := by
    nlinarith only [hprod, hprod', sq_nonneg n]
  have h := hpoly.trans (mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 41))
  have hscaled : (7 * (s + (49 / 100 : ℝ) * (n - s))) * n ≤
      (7 * (s + (49 / 100 : ℝ) * (n - s))) * (41 * r) := by
    convert h using 1 <;> ring
  exact le_of_mul_le_mul_left hscaled hden

/-- Every balanced cut of a simple degree-seven graph with normalized spectral expansion at most
`7 / 10` has adjacency cut rank at least `n / 41`, over every field. Both sides of the cut must
contain at least `n / 3` vertices. The theorem assumes the graph and its spectral certificate;
it does not assert the existence or explicit construction of such a graph. -/
theorem IsSimple.card_le_fortyOne_mul_cutRank [Field K] (hG : G.IsSimple)
    (hD : Fintype.card D = 7) (hμ : G.spectralExpansion ≤ 7 / 10) (S : Finset V)
    (hlo : Fintype.card V ≤ 3 * #S) (hhi : 3 * #S ≤ 2 * Fintype.card V) :
    Fintype.card V ≤ 41 * (G.toSimpleGraph.adjMatrix K).cutRank (↑S : Set V) := by
  have hσ : G.spectralExpansion ^ 2 ≤ (49 / 100 : ℝ) := by
    calc
      G.spectralExpansion ^ 2 ≤ (7 / 10 : ℝ) ^ 2 :=
        pow_le_pow_left₀ G.spectralExpansion_nonneg hμ 2
      _ = _ := by norm_num
  have hsmall (T : Finset V) (hTlo : Fintype.card V ≤ 3 * #T)
      (hThi : 2 * #T ≤ Fintype.card V) :
      Fintype.card V ≤ 41 * (G.toSimpleGraph.adjMatrix K).cutRank (↑T : Set V) := by
    have hbase := hG.mul_card_mul_card_compl_le_cutRank_mul (K := K) T
    simp only [hD, Nat.cast_ofNat] at hbase
    have hs : (0 : ℝ) ≤ #T := Nat.cast_nonneg _
    have hns : (0 : ℝ) ≤ Fintype.card V - #T :=
      sub_nonneg.mpr (Nat.cast_le.mpr (card_le_univ T))
    have hr : (0 : ℝ) ≤ (G.toSimpleGraph.adjMatrix K).cutRank (↑T : Set V) :=
      Nat.cast_nonneg _
    have hleft : (51 / 100 : ℝ) * (#T : ℝ) * (Fintype.card V - #T) ≤
        (1 - G.spectralExpansion ^ 2) * (#T : ℝ) * (Fintype.card V - #T) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : (51 / 100 : ℝ) ≤
          1 - G.spectralExpansion ^ 2) hs) hns
    have hright : 7 * ((G.toSimpleGraph.adjMatrix K).cutRank (↑T : Set V) : ℝ) *
        (#T + G.spectralExpansion ^ 2 * (Fintype.card V - #T)) ≤
      7 * ((G.toSimpleGraph.adjMatrix K).cutRank (↑T : Set V) : ℝ) *
        (#T + (49 / 100 : ℝ) * (Fintype.card V - #T)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hσ hns))
        (mul_nonneg (by norm_num) hr)
    have h := balanced_cut_rank_bound (Nat.cast_nonneg _) hr
      (by exact_mod_cast hTlo) (by exact_mod_cast hThi) (hleft.trans (hbase.trans hright))
    exact_mod_cast h
  by_cases hhalf : 2 * #S ≤ Fintype.card V
  · exact hsmall S hlo hhalf
  · have hc := card_compl_add_card S
    have h := hsmall Sᶜ (by omega) (by omega)
    rwa [coe_compl, (G.toSimpleGraph.isSymm_adjMatrix (α := K)).cutRank_compl] at h

end Cslib.RotationMap
