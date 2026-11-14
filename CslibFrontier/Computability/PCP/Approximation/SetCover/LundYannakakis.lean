/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PCP.Approximation.LabelCover.SmallSoundness
public import CslibFrontier.Computability.PCP.Approximation.SetCover.ApproxReduction
public import CslibFrontier.Computability.PCP.Approximation.SetCover.PartitionGadget
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryPair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.EraseDupsBy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Pairing

/-!
# Lund–Yannakakis / Feige hardness of approximating Set Cover

The Lund–Yannakakis / Feige reduction from Label Cover (`GapLabelCover`) to weighted and unweighted
Set Cover (`GapWeightedSetCover`, `GapSetCover`) ([LundYannakakis1994]; [Feige1998]).

For an encoded Label Cover instance `g : Graph (β → γ)` with `m = g.edges.length` edges and a
partition gadget `G : PartitionGadget γ`, every edge `e = (u, v, π)` receives `deg_L(u) * deg_R(v)`
copies of `G`'s universe in the unweighted reduction `toSetCoverOf` (and a single copy with vertex
weights `deg_L(u)`, `deg_R(v)` in the weighted reduction `toWeightedSetCoverOf`), neutralizing
non-uniform degrees in `g`.

* **Completeness**: a satisfying labelling `(ℓ, r)` selects one label per vertex copy on each side,
  forming a cover of cost `2 * m`.
* **Soundness**: for unweighted covers `C`, picking for each vertex `u` (resp. `v`) its copy
  `r₁*(u)` (resp. `r₂*(v)`) of minimum list size yields candidate sets `L u`, `R v` satisfying
  `∑ e, (|L e.src| + |R e.dst|) ≤ |C|`. When `G.Separates t`, Markov's inequality and averaging a
  random selection from `L u × R v` (`exists_labelling_of_list_sets`) yield a deterministic
  labelling satisfying at least `(1 - 2 * ρ / t) * (4 / t ^ 2)` of the edges whenever a cover of
  cost at most `ρ * (2 * m)` exists.

Instantiating `G` with `boolCubeGadget γ` and composing with `exists_GapLabelCover_npHard` proves
**Milestone 1**: `GapSetCover c` and `GapWeightedSetCover c` are `NP`-hard for every `c > 1`
(`GapSetCover_npHard`, `GapWeightedSetCover_npHard`), ruling out polynomial-time constant-factor
approximation algorithms for unweighted and weighted Set Cover unless `P = NP`.

Instantiating `G` with `exists_small_partitionGadget` gives per-instance `c * Real.log n` gap
theorems (`exists_weightedSetCover_log_gap`, `exists_setCover_log_gap`) for any
`0 < c < 1 / (4 * log 2)` and any `t ≥ logGapThreshold c p g.edges.length |γ|` (an explicit
threshold growing like `O(p * log m + log log |γ|)`), conditional on the Label Cover instance
having soundness `≤ 1 / t ^ 2`. Obtaining unconditional complexity-theoretic hardness from this
conditional reduction requires ingredients beyond the constant-round `exists_GapLabelCover_npHard`
base: super-constant parallel repetition uses a quasi-polynomial reduction and therefore yields
hardness against polynomial-time algorithms only under the stronger assumption
`NP ⊈ DTIME(n^{O(log log n)})` rather than `P ≠ NP` alone, whereas `P ≠ NP` hardness requires a
polynomial-time low-soundness Label Cover theorem (such as Dinur–Steurer for `(1 - ε) ln n`).

## Main definitions

* `Cslib.Complexity.SetCoverReduction.toWeightedSetCoverOf`,
  `Cslib.Complexity.SetCoverReduction.toSetCoverOf`: computable weighted and unweighted reductions
  from Label Cover parameterized by explicit label lists and a `PartitionGadget`.
* `Cslib.Complexity.logGapThreshold`: explicit `O(p * log m + log log |γ|)` threshold above
  which the `c * ln n` gap arithmetic holds.

## Main results

* `Cslib.Complexity.polyTimeReducible_GapLabelCover_GapWeightedSetCover`,
  `Cslib.Complexity.polyTimeReducible_GapLabelCover_GapSetCover`: gap-preserving polynomial-time
  reductions from `GapLabelCover`.
* `Cslib.Complexity.GapSetCover_npHard`, `Cslib.Complexity.GapWeightedSetCover_npHard`,
  `Cslib.Complexity.P_eq_NP_of_setCover_approx_const`,
  `Cslib.Complexity.P_eq_NP_of_weightedSetCover_approx_const`: constant-factor NP-hardness for
  every constant.
* `Cslib.Complexity.exists_weightedSetCover_log_gap`,
  `Cslib.Complexity.exists_setCover_log_gap`: per-instance `c * ln n` gap for any `t` above
  `logGapThreshold`, conditional on `1 / t ^ 2` Label Cover soundness.

## References

Primary texts uninspected (bibliographic metadata checked via search records only; locators
unverified and no numbered paper theorems are claimed). The parameterized constructions
`toWeightedSetCoverOf` and `toSetCoverOf` (explicit label lists, `PartitionGadget`, and
`deg_L(u) * deg_R(v)` edge duplication) and the explicit constant threshold `c < 1 / (4 * log 2)`
in `exists_weightedSetCover_log_gap` / `exists_setCover_log_gap` are this library's formalization.

* [C. Lund, M. Yannakakis, *On the hardness of approximating minimization
  problems*][LundYannakakis1994]
* [U. Feige, *A threshold of ln n for approximating set cover*][Feige1998]
-/

public section

namespace Cslib.Complexity

open Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM ComputableInPolyTime

/-! ### Core Label-Cover label extraction lemma -/

section LabelExtraction

private theorem card_pi_update_eq {U : Type*} [Fintype U] [DecidableEq U]
    {T : U → Type*} [∀ u, Fintype (T u)] [∀ u, DecidableEq (T u)] (u₀ : U) (y₀ : T u₀) :
    Fintype.card {f : ∀ u, T u // f u₀ = y₀} * Fintype.card (T u₀) =
      Fintype.card (∀ u, T u) := by
  classical
  let φ : {f : ∀ u, T u // f u₀ = y₀} × T u₀ ≃ ∀ u, T u :=
    { toFun := fun p => Function.update p.1.1 u₀ p.2
      invFun := fun g => (⟨Function.update g u₀ y₀, Function.update_self _ _ _⟩, g u₀)
      left_inv := fun ⟨⟨f, hf⟩, y⟩ => by
        apply Prod.ext
        · apply Subtype.ext
          funext u
          by_cases hu : u = u₀
          · subst hu
            simp [hf]
          · simp [hu]
        · simp
      right_inv := fun g => by
        funext u
        by_cases hu : u = u₀
        · subst hu
          simp
        · simp [hu] }
  rw [← Fintype.card_prod, Fintype.card_congr φ]

/-- **Core Lund–Yannakakis label-extraction lemma**: given candidate label sets `L u : Finset β`
and `R v : Finset γ` such that every edge `(u, v)` with `|L u| + |R v| ≤ t` has a matching pair
`(a, b) ∈ L u × R v` and `∑ e, (|L e.src| + |R e.dst|) ≤ ρ * (2 * m)`, some deterministic
labelling satisfies at least `(1 - 2 * ρ / t) * (4 / t ^ 2)` of the edges of `g`. -/
theorem exists_labelling_of_list_sets {β γ : Type} [DecidableEq γ] [Nonempty β] [Nonempty γ]
    (g : Graph (β → γ)) (L : ℕ → Finset β) (R : ℕ → Finset γ) {t : ℕ} (ht : 0 < t)
    {ρ : ℝ} (hm : 0 < g.edges.length)
    (hmatch : ∀ i : Fin g.edges.length,
      (L (g.edges[i].src)).card + (R (g.edges[i].dst)).card ≤ t →
        ∃ a ∈ L (g.edges[i].src), ∃ b ∈ R (g.edges[i].dst), (g.edges[i].constraint) a = b)
    (hsum : ∑ i : Fin g.edges.length,
      (((L (g.edges[i].src)).card + (R (g.edges[i].dst)).card : ℕ) : ℝ) ≤
        ρ * (2 * g.edges.length)) :
    (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) ≤ 1 - (g.toGraph projectionEval).unsatVal := by
  classical
  let m := g.edges.length
  let a₀ : β := Classical.arbitrary β
  let b₀ : γ := Classical.arbitrary γ
  let goodEdges : Finset (Fin m) := Finset.univ.filter fun i =>
    (L (g.edges[i].src)).card + (R (g.edges[i].dst)).card ≤ t
  let badEdges : Finset (Fin m) := Finset.univ \ goodEdges
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hbad_bound : (badEdges.card : ℝ) * t ≤ ρ * (2 * m) := by
    calc (badEdges.card : ℝ) * t
        = ∑ _i ∈ badEdges, (t : ℝ) := by simp
      _ ≤ ∑ i ∈ badEdges,
          (((L (g.edges[i].src)).card + (R (g.edges[i].dst)).card : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hnot : ¬ (L (g.edges[i].src)).card + (R (g.edges[i].dst)).card ≤ t := by
            simpa [goodEdges, badEdges] using hi
          exact_mod_cast (le_of_lt (Nat.lt_of_not_le hnot))
      _ ≤ ∑ i : Fin m,
          (((L (g.edges[i].src)).card + (R (g.edges[i].dst)).card : ℕ) : ℝ) :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.cast_nonneg _
      _ ≤ ρ * (2 * m) := hsum
  have hgood_card : (1 - 2 * ρ / t) * m ≤ (goodEdges.card : ℝ) := by
    have hsplit : goodEdges.card + badEdges.card = m := by
      rw [add_comm]
      have hsub : goodEdges ⊆ Finset.univ := Finset.subset_univ _
      simpa [badEdges] using Finset.card_sdiff_add_card_eq_card hsub
    have hcast : (goodEdges.card : ℝ) + badEdges.card = m := by exact_mod_cast hsplit
    have hdiv : (badEdges.card : ℝ) ≤ (2 * ρ / t) * m := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ht0]
      linarith
    linarith
  let VL : Finset ℕ := (g.edges.map Edge.src).toFinset
  let VR : Finset ℕ := (g.edges.map Edge.dst).toFinset
  let L' (u : ℕ) : Finset β := if (L u).Nonempty then L u else {a₀}
  let R' (v : ℕ) : Finset γ := if (R v).Nonempty then R v else {b₀}
  have hL'_ne : ∀ u, (L' u).Nonempty := fun u => by
    dsimp only [L']
    split_ifs with h
    · exact h
    · exact ⟨a₀, Finset.mem_singleton_self _⟩
  have hR'_ne : ∀ v, (R' v).Nonempty := fun v => by
    dsimp only [R']
    split_ifs with h
    · exact h
    · exact ⟨b₀, Finset.mem_singleton_self _⟩
  let ChoiceL := ∀ u : VL, L' u.1
  let ChoiceR := ∀ v : VR, R' v.1
  let Choice := ChoiceL × ChoiceR
  have : Nonempty ChoiceL := ⟨fun u => ⟨(hL'_ne u.1).choose, (hL'_ne u.1).choose_spec⟩⟩
  have : Nonempty ChoiceR := ⟨fun v => ⟨(hR'_ne v.1).choose, (hR'_ne v.1).choose_spec⟩⟩
  have : Nonempty Choice := inferInstance
  let σ_of (c : Choice) (x : ℕ) : β × γ :=
    (if hx : x ∈ VL then (c.1 ⟨x, hx⟩).1 else a₀,
      if hy : x ∈ VR then (c.2 ⟨x, hy⟩).1 else b₀)
  let hitSet (i : Fin m) : Finset Choice :=
    Finset.univ.filter fun c => (g.toGraph projectionEval).Satisfies (σ_of c) i
  have hhit_edge : ∀ i ∈ goodEdges,
      (4 / (t : ℝ) ^ 2) * Fintype.card Choice ≤ (hitSet i).card := by
    intro i hi
    have hle : (L (g.edges[i].src)).card + (R (g.edges[i].dst)).card ≤ t :=
      (Finset.mem_filter.1 hi).2
    obtain ⟨a_star, haL, b_star, hbR, heq⟩ := hmatch i hle
    have hLne : (L (g.edges[i].src)).Nonempty := ⟨a_star, haL⟩
    have hRne : (R (g.edges[i].dst)).Nonempty := ⟨b_star, hbR⟩
    have haL' : a_star ∈ L' (g.edges[i].src) := by
      dsimp only [L']
      split_ifs
      exact haL
    have hbR' : b_star ∈ R' (g.edges[i].dst) := by
      dsimp only [R']
      split_ifs
      exact hbR
    have huVL : g.edges[i].src ∈ VL :=
      List.mem_toFinset.2 (List.mem_map.2 ⟨g.edges[i], List.getElem_mem _, rfl⟩)
    have hvVR : g.edges[i].dst ∈ VR :=
      List.mem_toFinset.2 (List.mem_map.2 ⟨g.edges[i], List.getElem_mem _, rfl⟩)
    let u₀ : VL := ⟨g.edges[i].src, huVL⟩
    let v₀ : VR := ⟨g.edges[i].dst, hvVR⟩
    let yL₀ : L' u₀.1 := ⟨a_star, haL'⟩
    let yR₀ : R' v₀.1 := ⟨b_star, hbR'⟩
    have hcardL := card_pi_update_eq (T := fun u : VL => L' u.1) u₀ yL₀
    have hcardR := card_pi_update_eq (T := fun v : VR => R' v.1) v₀ yR₀
    let hitPair :=
      {fL : ChoiceL // fL u₀ = yL₀} × {fR : ChoiceR // fR v₀ = yR₀}
    have hcard_mul : Fintype.card hitPair * ((L' u₀.1).card * (R' v₀.1).card) =
        Fintype.card Choice := by
      simp only [hitPair, Fintype.card_prod, Choice]
      calc (Fintype.card {fL : ChoiceL // fL u₀ = yL₀} *
              Fintype.card {fR : ChoiceR // fR v₀ = yR₀}) *
            ((L' u₀.1).card * (R' v₀.1).card)
          = (Fintype.card {fL : ChoiceL // fL u₀ = yL₀} * (L' u₀.1).card) *
              (Fintype.card {fR : ChoiceR // fR v₀ = yR₀} * (R' v₀.1).card) := by ring
        _ = Fintype.card ChoiceL * Fintype.card ChoiceR := by
            rw [← Fintype.card_coe (L' u₀.1), ← Fintype.card_coe (R' v₀.1), hcardL, hcardR]
    have hsub_hit : Fintype.card hitPair ≤ (hitSet i).card := by
      let emb : hitPair ↪ Choice :=
        ⟨fun p => (p.1.1, p.2.1), fun p q hpq =>
          Prod.ext (Subtype.ext (Prod.ext_iff.1 hpq).1) (Subtype.ext (Prod.ext_iff.1 hpq).2)⟩
      calc Fintype.card hitPair
          = (Finset.univ.map emb).card := (Finset.card_map emb).symm
        _ ≤ (hitSet i).card := Finset.card_le_card fun c hc => by
            obtain ⟨⟨⟨fL, hfL⟩, ⟨fR, hfR⟩⟩, -, rfl⟩ := Finset.mem_map.1 hc
            refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
            rw [satisfies_toGraph_projectionEval_iff, List.get_eq_getElem]
            have hfL' : (fL u₀).1 = a_star := congrArg Subtype.val hfL
            have hfR' : (fR v₀).1 = b_star := congrArg Subtype.val hfR
            have hemb : emb (⟨fL, hfL⟩, ⟨fR, hfR⟩) = (fL, fR) := rfl
            dsimp only [σ_of]
            rw [hemb]
            have h1 : (if hx : g.edges[↑i].src ∈ VL then
                (fL ⟨g.edges[↑i].src, hx⟩).1 else a₀) = a_star := by
              split_ifs with hx
              · exact hfL'
              · exact absurd (by simpa [Fin.getElem_fin] using huVL) hx
            have h2 : (if hy : g.edges[↑i].dst ∈ VR then
                (fR ⟨g.edges[↑i].dst, hy⟩).1 else b₀) = b_star := by
              split_ifs with hy
              · exact hfR'
              · exact absurd (by simpa [Fin.getElem_fin] using hvVR) hy
            change g.edges[↑i].constraint
                (if hx : g.edges[↑i].src ∈ VL then (fL ⟨g.edges[↑i].src, hx⟩).1 else a₀) =
              if hy : g.edges[↑i].dst ∈ VR then (fR ⟨g.edges[↑i].dst, hy⟩).1 else b₀
            rw [h1, h2]
            exact heq
    have hprod_le : 4 * ((L' u₀.1).card * (R' v₀.1).card) ≤ t ^ 2 := by
      have hLcard : (L' u₀.1).card = (L u₀.1).card := by
        dsimp only [L', u₀]
        split_ifs
        rfl
      have hRcard : (R' v₀.1).card = (R v₀.1).card := by
        dsimp only [R', v₀]
        split_ifs
        rfl
      have hsum_le : (L' u₀.1).card + (R' v₀.1).card ≤ t := by
        rw [hLcard, hRcard]
        exact hle
      rw [← mul_assoc]
      exact (_root_.four_mul_le_sq_add _ _).trans (Nat.pow_le_pow_left hsum_le 2)
    have hnat_mul : 4 * Fintype.card Choice ≤ t ^ 2 * (hitSet i).card := by
      calc 4 * Fintype.card Choice
          = 4 * (Fintype.card hitPair * ((L' u₀.1).card * (R' v₀.1).card)) := by rw [hcard_mul]
        _ = (4 * ((L' u₀.1).card * (R' v₀.1).card)) * Fintype.card hitPair := by ring
        _ ≤ t ^ 2 * (hitSet i).card := Nat.mul_le_mul hprod_le hsub_hit
    have hreal_mul : (4 : ℝ) * Fintype.card Choice ≤ (t : ℝ) ^ 2 * (hitSet i).card := by
      exact_mod_cast hnat_mul
    rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos ht0)]
    linarith
  have hsum_sat : ∑ c : Choice,
      ((Finset.univ.filter fun i : Fin m =>
        (g.toGraph projectionEval).Satisfies (σ_of c) i).card : ℝ)
      = ∑ i : Fin m, ((hitSet i).card : ℝ) := by
    have hnat : ∑ c : Choice,
        (Finset.univ.filter fun i : Fin m => (g.toGraph projectionEval).Satisfies (σ_of c) i).card
        = ∑ i : Fin m, (hitSet i).card := by
      simp only [hitSet, Finset.card_filter]
      exact Finset.sum_comm
    exact_mod_cast hnat
  have htotal : (goodEdges.card : ℝ) * ((4 / (t : ℝ) ^ 2) * Fintype.card Choice) ≤
      ∑ c : Choice,
        ((Finset.univ.filter fun i : Fin m =>
          (g.toGraph projectionEval).Satisfies (σ_of c) i).card : ℝ) := by
    calc (goodEdges.card : ℝ) * ((4 / (t : ℝ) ^ 2) * Fintype.card Choice)
        = ∑ _i ∈ goodEdges, (4 / (t : ℝ) ^ 2) * Fintype.card Choice := by simp
      _ ≤ ∑ i ∈ goodEdges, ((hitSet i).card : ℝ) := Finset.sum_le_sum hhit_edge
      _ ≤ ∑ i : Fin m, ((hitSet i).card : ℝ) :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.cast_nonneg _
      _ = _ := hsum_sat.symm
  have ⟨c_star, hc_star⟩ : ∃ c : Choice, (goodEdges.card : ℝ) * (4 / (t : ℝ) ^ 2) ≤
      ((Finset.univ.filter fun i : Fin m =>
        (g.toGraph projectionEval).Satisfies (σ_of c) i).card : ℝ) := by
    by_contra hlt
    push Not at hlt
    have hsum_lt : ∑ c : Choice,
        ((Finset.univ.filter fun i : Fin m =>
          (g.toGraph projectionEval).Satisfies (σ_of c) i).card : ℝ) <
        ∑ _c : Choice, ((goodEdges.card : ℝ) * (4 / (t : ℝ) ^ 2)) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun c _ => hlt c
    have hcard_mul : ∑ _c : Choice, ((goodEdges.card : ℝ) * (4 / (t : ℝ) ^ 2)) =
        (goodEdges.card : ℝ) * ((4 / (t : ℝ) ^ 2) * Fintype.card Choice) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    linarith
  have hunsat_le : (g.toGraph projectionEval).unsatVal ≤
      (g.toGraph projectionEval).unsatFrac (σ_of c_star) :=
    ConstraintGraph.unsatVal_le _ _
  have hfrac : (goodEdges.card : ℝ) * (4 / (t : ℝ) ^ 2) ≤
      (1 - (g.toGraph projectionEval).unsatFrac (σ_of c_star)) * m := by
    rw [ConstraintGraph.unsatFrac, Fintype.card_fin]
    have hcompl :
        ((g.toGraph projectionEval).unsatEdges (σ_of c_star)).card +
        (Finset.univ.filter fun i : Fin m =>
          (g.toGraph projectionEval).Satisfies (σ_of c_star) i).card = m := by
      have hdisj : Disjoint ((g.toGraph projectionEval).unsatEdges (σ_of c_star))
          (Finset.univ.filter fun i : Fin m =>
            (g.toGraph projectionEval).Satisfies (σ_of c_star) i) := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        rw [ConstraintGraph.mem_unsatEdges] at hi1
        exact hi1 (Finset.mem_filter.1 hi2).2
      have hunion : ((g.toGraph projectionEval).unsatEdges (σ_of c_star)) ∪
          (Finset.univ.filter fun i : Fin m =>
            (g.toGraph projectionEval).Satisfies (σ_of c_star) i) = Finset.univ := by
        ext i
        simp only [Finset.mem_union, ConstraintGraph.mem_unsatEdges, Finset.mem_filter,
          Finset.mem_univ, true_and, iff_true]
        exact (em _).symm
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_fin]
    have hcompl_cast :
        (((g.toGraph projectionEval).unsatEdges (σ_of c_star)).card : ℝ) +
        ((Finset.univ.filter fun i : Fin m =>
          (g.toGraph projectionEval).Satisfies (σ_of c_star) i).card : ℝ) = m := by
      exact_mod_cast hcompl
    have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm0
    have hsub : (1 - (((g.toGraph projectionEval).unsatEdges (σ_of c_star)).card : ℝ) / m) * m =
        ((Finset.univ.filter fun i : Fin m =>
          (g.toGraph projectionEval).Satisfies (σ_of c_star) i).card : ℝ) := by
      field_simp [hm_ne]
      linarith
    rw [hsub]
    exact hc_star
  have hmain : (1 - 2 * ρ / t) * m * (4 / (t : ℝ) ^ 2) ≤
      (1 - (g.toGraph projectionEval).unsatVal) * m := by
    calc (1 - 2 * ρ / t) * m * (4 / (t : ℝ) ^ 2)
        ≤ (goodEdges.card : ℝ) * (4 / (t : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hgood_card (by positivity)
      _ ≤ (1 - (g.toGraph projectionEval).unsatFrac (σ_of c_star)) * m := hfrac
      _ ≤ (1 - (g.toGraph projectionEval).unsatVal) * m :=
            mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hmain' : (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) * m ≤
      (1 - (g.toGraph projectionEval).unsatVal) * m := by
    linarith [show (1 - 2 * ρ / t) * m * (4 / (t : ℝ) ^ 2) =
      (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) * m by ring]
  exact le_of_mul_le_mul_right hmain' hm0

end LabelExtraction

/-! ### Reductions to Weighted and Unweighted Set Cover -/

namespace SetCoverReduction

section Combinatorial

variable {β γ : Type}

/-- Deduplicated list of left endpoints appearing in `g.edges`. -/
@[expose] def leftVertices (g : Graph (β → γ)) : List ℕ :=
  (g.edges.map Edge.src).eraseDupsBy fun a b => decide (a = b)

/-- Deduplicated list of right endpoints appearing in `g.edges`. -/
@[expose] def rightVertices (g : Graph (β → γ)) : List ℕ :=
  (g.edges.map Edge.dst).eraseDupsBy fun a b => decide (a = b)

/-- Left degree of vertex `u` in `g.edges`. -/
@[expose] def degL (g : Graph (β → γ)) (u : ℕ) : ℕ :=
  g.edges.countP fun d => decide (d.src = u)

/-- Right degree of vertex `v` in `g.edges`. -/
@[expose] def degR (g : Graph (β → γ)) (v : ℕ) : ℕ :=
  g.edges.countP fun d => decide (d.dst = v)

private theorem nodup_leftVertices (g : Graph (β → γ)) : (leftVertices g).Nodup :=
  List.nodup_eraseDupsBy_eq _

private theorem nodup_rightVertices (g : Graph (β → γ)) : (rightVertices g).Nodup :=
  List.nodup_eraseDupsBy_eq _

private theorem mem_leftVertices {g : Graph (β → γ)} {u : ℕ} :
    u ∈ leftVertices g ↔ ∃ d ∈ g.edges, d.src = u := by
  simp only [leftVertices, List.mem_eraseDupsBy_eq, List.mem_map]

private theorem mem_rightVertices {g : Graph (β → γ)} {v : ℕ} :
    v ∈ rightVertices g ↔ ∃ d ∈ g.edges, d.dst = v := by
  simp only [rightVertices, List.mem_eraseDupsBy_eq, List.mem_map]

private theorem degL_pos_of_mem {g : Graph (β → γ)} {u : ℕ} (hu : u ∈ leftVertices g) :
    0 < degL g u := by
  obtain ⟨d, hd, rfl⟩ := mem_leftVertices.1 hu
  exact List.countP_pos_iff.2 ⟨d, hd, decide_eq_true rfl⟩

private theorem degR_pos_of_mem {g : Graph (β → γ)} {v : ℕ} (hv : v ∈ rightVertices g) :
    0 < degR g v := by
  obtain ⟨d, hd, rfl⟩ := mem_rightVertices.1 hv
  exact List.countP_pos_iff.2 ⟨d, hd, decide_eq_true rfl⟩

private theorem degL_le_length (g : Graph (β → γ)) (u : ℕ) : degL g u ≤ g.edges.length :=
  List.countP_le_length

private theorem degR_le_length (g : Graph (β → γ)) (v : ℕ) : degR g v ≤ g.edges.length :=
  List.countP_le_length

private theorem sum_map_eq_sum_countP_mul {α : Type*} (l : List α) (proj : α → ℕ)
    (S : Finset ℕ) (hS : ∀ x ∈ l, proj x ∈ S) (f : ℕ → ℕ) :
    (l.map fun x => f (proj x)).sum =
      ∑ u ∈ S, l.countP (fun x => decide (proj x = u)) * f u := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    rw [ih (fun y hy => hS y (List.mem_cons_of_mem x hy))]
    have hsum : ∑ u ∈ S,
        (xs.countP (fun y => decide (proj y = u)) +
          if decide (proj x = u) = true then 1 else 0) * f u =
        (∑ u ∈ S, xs.countP (fun y => decide (proj y = u)) * f u) +
          ∑ u ∈ S, (if decide (proj x = u) = true then 1 else 0) * f u := by
      simp only [add_mul, Finset.sum_add_distrib]
    rw [hsum]
    have hx : proj x ∈ S := hS x List.mem_cons_self
    have hsingle : ∑ u ∈ S, (if decide (proj x = u) = true then 1 else 0) * f u = f (proj x) := by
      simp [hx]
    omega

private theorem sum_degL_eq_length (g : Graph (β → γ)) :
    ∑ u ∈ (leftVertices g).toFinset, degL g u = g.edges.length := by
  have h := sum_map_eq_sum_countP_mul g.edges Edge.src (leftVertices g).toFinset
    (fun d hd => List.mem_toFinset.2 (mem_leftVertices.2 ⟨d, hd, rfl⟩)) (fun _ => 1)
  simpa [degL] using h.symm

private theorem sum_degR_eq_length (g : Graph (β → γ)) :
    ∑ v ∈ (rightVertices g).toFinset, degR g v = g.edges.length := by
  have h := sum_map_eq_sum_countP_mul g.edges Edge.dst (rightVertices g).toFinset
    (fun d hd => List.mem_toFinset.2 (mem_rightVertices.2 ⟨d, hd, rfl⟩)) (fun _ => 1)
  simpa [degR] using h.symm

private theorem sum_over_edges_degL (g : Graph (β → γ)) (f : ℕ → ℕ) :
    ∑ i : Fin g.edges.length, f g.edges[i].src =
      ∑ u ∈ (leftVertices g).toFinset, degL g u * f u := by
  have h := sum_map_eq_sum_countP_mul g.edges Edge.src (leftVertices g).toFinset
    (fun d hd => List.mem_toFinset.2 (mem_leftVertices.2 ⟨d, hd, rfl⟩)) f
  simp only [degL]
  rw [← h, ← List.sum_ofFn (n := g.edges.length)
    (f := fun i : Fin g.edges.length => f g.edges[i].src)]
  congr 1
  ext1 i
  by_cases hi : i < g.edges.length <;> simp [hi]

private theorem sum_over_edges_degR (g : Graph (β → γ)) (f : ℕ → ℕ) :
    ∑ i : Fin g.edges.length, f g.edges[i].dst =
      ∑ v ∈ (rightVertices g).toFinset, degR g v * f v := by
  have h := sum_map_eq_sum_countP_mul g.edges Edge.dst (rightVertices g).toFinset
    (fun d hd => List.mem_toFinset.2 (mem_rightVertices.2 ⟨d, hd, rfl⟩)) f
  simp only [degR]
  rw [← h, ← List.sum_ofFn (n := g.edges.length)
    (f := fun i : Fin g.edges.length => f g.edges[i].dst)]
  congr 1
  ext1 i
  by_cases hi : i < g.edges.length <;> simp [hi]

private theorem nodup_flatMap_range {α : Type*} {l : List ℕ} (hl : l.Nodup) (n : ℕ → ℕ)
    {s : ℕ → ℕ → List α} (hs : ∀ u r, (s u r).Nodup)
    (hdisj : ∀ u₁ r₁ u₂ r₂ x, x ∈ s u₁ r₁ → x ∈ s u₂ r₂ → u₁ = u₂ ∧ r₁ = r₂) :
    (l.flatMap fun u => (List.range (n u)).flatMap fun r => s u r).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun u _ => ?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun r _ => hs u r, ?_⟩
    exact (List.nodup_iff_pairwise_ne.1 List.nodup_range).imp fun hne x hx1 hx2 =>
      hne (hdisj _ _ _ _ x hx1 hx2).2
  · refine hl.imp ?_
    intro u₁ u₂ hne x hx1 hx2
    obtain ⟨r₁, -, hx1'⟩ := List.mem_flatMap.1 hx1
    obtain ⟨r₂, -, hx2'⟩ := List.mem_flatMap.1 hx2
    exact hne (hdisj _ _ _ _ x hx1' hx2').1

/-! #### Weighted reduction -/

/-- Ground elements for the weighted Set Cover reduction: pairs `Nat.pair e x` for edge index
`e < g.edges.length` and gadget element `x < G.size`. -/
@[expose] def weightedGround {γ : Type} (G : PartitionGadget γ) (g : Graph (β → γ)) : List ℕ :=
  (List.range g.edges.length).flatMap fun e =>
    (List.range G.size).map (Nat.pair e)

/-- Left candidate sets `(u, a)` in the weighted reduction, weighted by `degL g u`. -/
@[expose] def weightedLeftSet (fallback : γ) (G : PartitionGadget γ) (g : Graph (β → γ))
    (u : ℕ) (a : β) : WeightedSet :=
  ⟨(List.range g.edges.length).flatMap fun e =>
      let d := g.edges.getD e ⟨0, 0, fun _ => fallback⟩
      if d.src = u then
        ((List.range G.size).filter fun x => !G.mem x (d.constraint a)).map (Nat.pair e)
      else [],
    degL g u⟩

/-- Right candidate sets `(v, b)` in the weighted reduction, weighted by `degR g v`. -/
@[expose] def weightedRightSet (fallback : γ) (G : PartitionGadget γ) (g : Graph (β → γ))
    (v : ℕ) (b : γ) : WeightedSet :=
  ⟨(List.range g.edges.length).flatMap fun e =>
      let d := g.edges.getD e ⟨0, 0, fun _ => fallback⟩
      if d.dst = v then
        ((List.range G.size).filter fun x => G.mem x b).map (Nat.pair e)
      else [],
    degR g v⟩

/-- Left item list `(u, a)` for the weighted reduction. -/
@[expose] def weightedLeftItems (bs : List β) (g : Graph (β → γ)) : List (ℕ × β) :=
  (leftVertices g).flatMap fun u => bs.map fun a => (u, a)

/-- Right item list `(v, b)` for the weighted reduction. -/
@[expose] def weightedRightItems (gs : List γ) (g : Graph (β → γ)) : List (ℕ × γ) :=
  (rightVertices g).flatMap fun v => gs.map fun b => (v, b)

/-- Weighted set system constructed by the Lund–Yannakakis / Feige reduction. -/
@[expose] def weightedSetSystemOf (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) (g : Graph (β → γ)) : WeightedSetSystem :=
  ⟨weightedGround G g,
    (weightedLeftItems bs g).map (fun p => weightedLeftSet fallback G g p.1 p.2) ++
      (weightedRightItems gs g).map (fun p => weightedRightSet fallback G g p.1 p.2)⟩

/-- Computable weighted Set Cover reduction from Label Cover parameterized by explicit label lists
`bs`, `gs`, a fallback label `fallback : γ`, and a partition gadget `G`. -/
@[expose] def toWeightedSetCoverOf (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) (g : Graph (β → γ)) : WeightedSetSystem × ℕ :=
  (weightedSetSystemOf bs gs fallback G g, 2 * g.edges.length)

theorem weightedSetSystemOf_ground_length {bs : List β} {gs : List γ} {fallback : γ}
    {G : PartitionGadget γ} {g : Graph (β → γ)} :
    (weightedSetSystemOf bs gs fallback G g).ground.length = g.edges.length * G.size := by
  simp [weightedSetSystemOf, weightedGround, List.length_flatMap, List.map_const',
    List.sum_replicate]

private theorem mem_weightedGround {G : PartitionGadget γ} {g : Graph (β → γ)} {z : ℕ} :
    z ∈ weightedGround G g ↔
      ∃ e < g.edges.length, ∃ x < G.size, Nat.pair e x = z := by
  simp only [weightedGround, List.mem_flatMap, List.mem_map, List.mem_range]

private theorem mem_weightedLeftSet {fallback : γ} {G : PartitionGadget γ} {g : Graph (β → γ)}
    {u : ℕ} {a : β} {e x : ℕ} (he : e < g.edges.length) (hx : x < G.size) :
    Nat.pair e x ∈ (weightedLeftSet fallback G g u a).elements ↔
      g.edges[e].src = u ∧ G.mem x (g.edges[e].constraint a) = false := by
  simp only [weightedLeftSet, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨e', he', hz⟩
    rw [List.getD_eq_getElem _ _ he'] at hz
    split_ifs at hz with hsrc
    · simp only [List.mem_map, List.mem_filter, List.mem_range, Bool.not_eq_true'] at hz
      obtain ⟨x', ⟨_, hx'⟩, hpair⟩ := hz
      obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 hpair
      exact ⟨hsrc, hx'⟩
    · simp at hz
  · rintro ⟨hsrc, hmem⟩
    refine ⟨e, he, ?_⟩
    rw [List.getD_eq_getElem _ _ he]
    simp only [hsrc, ↓reduceIte, List.mem_map, List.mem_filter, List.mem_range, Bool.not_eq_true']
    exact ⟨x, ⟨hx, hmem⟩, rfl⟩

private theorem mem_weightedRightSet {fallback : γ} {G : PartitionGadget γ} {g : Graph (β → γ)}
    {v : ℕ} {b : γ} {e x : ℕ} (he : e < g.edges.length) (hx : x < G.size) :
    Nat.pair e x ∈ (weightedRightSet fallback G g v b).elements ↔
      g.edges[e].dst = v ∧ G.mem x b = true := by
  simp only [weightedRightSet, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨e', he', hz⟩
    rw [List.getD_eq_getElem _ _ he'] at hz
    split_ifs at hz with hdst
    · simp only [List.mem_map, List.mem_filter, List.mem_range] at hz
      obtain ⟨x', ⟨_, hx'⟩, hpair⟩ := hz
      obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 hpair
      exact ⟨hdst, hx'⟩
    · simp at hz
  · rintro ⟨hdst, hmem⟩
    refine ⟨e, he, ?_⟩
    rw [List.getD_eq_getElem _ _ he]
    simp only [hdst, ↓reduceIte, List.mem_map, List.mem_filter, List.mem_range]
    exact ⟨x, ⟨hx, hmem⟩, rfl⟩

private theorem weightedSetSystemOf_sets_length (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) (g : Graph (β → γ)) :
    (weightedSetSystemOf bs gs fallback G g).sets.length =
      (weightedLeftItems bs g).length + (weightedRightItems gs g).length := by
  simp [weightedSetSystemOf]

private theorem weightedSet_getElem_left {bs : List β} {gs : List γ} {fallback : γ}
    {G : PartitionGadget γ} {g : Graph (β → γ)}
    {i : Fin (weightedSetSystemOf bs gs fallback G g).sets.length}
    (hi : (i : ℕ) < (weightedLeftItems bs g).length) :
    (weightedSetSystemOf bs gs fallback G g).sets[i] =
      weightedLeftSet fallback G g ((weightedLeftItems bs g)[(i : ℕ)]'hi).1
        ((weightedLeftItems bs g)[(i : ℕ)]'hi).2 := by
  change ((weightedLeftItems bs g).map (fun p => weightedLeftSet fallback G g p.1 p.2) ++
      (weightedRightItems gs g).map (fun p => weightedRightSet fallback G g p.1 p.2))[(i : ℕ)] = _
  rw [List.getElem_append_left (by simp [hi]), List.getElem_map]

private theorem weightedSet_getElem_right {bs : List β} {gs : List γ} {fallback : γ}
    {G : PartitionGadget γ} {g : Graph (β → γ)}
    {i : Fin (weightedSetSystemOf bs gs fallback G g).sets.length}
    (hi : (weightedLeftItems bs g).length ≤ (i : ℕ))
    (hk : (i : ℕ) - (weightedLeftItems bs g).length < (weightedRightItems gs g).length) :
    (weightedSetSystemOf bs gs fallback G g).sets[i] =
      weightedRightSet fallback G g
        ((weightedRightItems gs g)[(i : ℕ) - (weightedLeftItems bs g).length]'hk).1
        ((weightedRightItems gs g)[(i : ℕ) - (weightedLeftItems bs g).length]'hk).2 := by
  have hge : ((weightedLeftItems bs g).map
      (fun p => weightedLeftSet fallback G g p.1 p.2)).length ≤ (i : ℕ) := by
    simp [hi]
  change ((weightedLeftItems bs g).map (fun p => weightedLeftSet fallback G g p.1 p.2) ++
      (weightedRightItems gs g).map (fun p => weightedRightSet fallback G g p.1 p.2))[(i : ℕ)] = _
  rw [List.getElem_append_right hge]
  simp only [List.length_map, List.getElem_map]

theorem weightedSetSystemOf_coverable [Nonempty β] {bs : List β} {gs : List γ} {fallback : γ}
    (hbs_all : ∀ a, a ∈ bs) (hgs_all : ∀ b, b ∈ gs)
    (G : PartitionGadget γ) (g : Graph (β → γ)) :
    (weightedSetSystemOf bs gs fallback G g).Coverable := by
  refine ⟨Finset.univ, fun z hz => ?_⟩
  obtain ⟨e, he, x, hx, rfl⟩ := mem_weightedGround.1 hz
  let a₀ : β := Classical.arbitrary β
  let b := g.edges[e].constraint a₀
  have hu : g.edges[e].src ∈ leftVertices g :=
    mem_leftVertices.2 ⟨g.edges[e], List.getElem_mem he, rfl⟩
  have hv : g.edges[e].dst ∈ rightVertices g :=
    mem_rightVertices.2 ⟨g.edges[e], List.getElem_mem he, rfl⟩
  cases hbit : G.mem x b
  · have hmemL : (g.edges[e].src, a₀) ∈ weightedLeftItems bs g :=
      List.mem_flatMap.2 ⟨g.edges[e].src, hu, List.mem_map.2 ⟨a₀, hbs_all a₀, rfl⟩⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.1 hmemL
    let i : Fin (weightedSetSystemOf bs gs fallback G g).sets.length :=
      ⟨k, by rw [weightedSetSystemOf_sets_length]; exact Nat.lt_add_right _ hk⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [weightedSet_getElem_left hk]
    simp only [i, hget]
    exact (mem_weightedLeftSet he hx).2 ⟨rfl, hbit⟩
  · have hmemR : (g.edges[e].dst, b) ∈ weightedRightItems gs g :=
      List.mem_flatMap.2 ⟨g.edges[e].dst, hv, List.mem_map.2 ⟨b, hgs_all b, rfl⟩⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.1 hmemR
    let i : Fin (weightedSetSystemOf bs gs fallback G g).sets.length :=
      ⟨(weightedLeftItems bs g).length + k, by rw [weightedSetSystemOf_sets_length]; omega⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [weightedSet_getElem_right (i := i) (Nat.le_add_right _ _)
      (by simpa [i, Nat.add_sub_cancel_left] using hk)]
    simp only [i, Nat.add_sub_cancel_left, hget]
    exact (mem_weightedRightSet he hx).2 ⟨rfl, hbit⟩

theorem weightedSetSystemOf_complete [DecidableEq γ] [Nonempty β] [Nonempty γ]
    {bs : List β} {gs : List γ} {fallback : γ}
    (hbs_all : ∀ a, a ∈ bs) (hgs_all : ∀ b, b ∈ gs)
    (G : PartitionGadget γ) (g : Graph (β → γ))
    (hsat : 1 ≤ 1 - (g.toGraph projectionEval).unsatVal) :
    (weightedSetSystemOf bs gs fallback G g).optCoverWeight ≤ 2 * g.edges.length := by
  classical
  have hunsat0 : (g.toGraph projectionEval).unsatVal = 0 :=
    le_antisymm (by linarith) (ConstraintGraph.unsatVal_nonneg _)
  have hSat : (g.toGraph projectionEval).Satisfiable :=
    (ConstraintGraph.unsatVal_eq_zero_iff _).1 hunsat0
  obtain ⟨ℓ, r, hsat_edge⟩ := (satisfiable_toGraph_projectionEval_iff g).1 hSat
  let W := weightedSetSystemOf bs gs fallback G g
  have hmemL : ∀ u : ↥(leftVertices g).toFinset,
      ∃ k, ∃ hk : k < (weightedLeftItems bs g).length,
        (weightedLeftItems bs g)[k]'hk = (u.1, ℓ u.1) := by
    intro u
    have hmem : (u.1, ℓ u.1) ∈ weightedLeftItems bs g :=
      List.mem_flatMap.2 ⟨u.1, List.mem_toFinset.1 u.2, List.mem_map.2 ⟨ℓ u.1, hbs_all _, rfl⟩⟩
    exact List.mem_iff_getElem.1 hmem
  have hmemR : ∀ v : ↥(rightVertices g).toFinset,
      ∃ k, ∃ hk : k < (weightedRightItems gs g).length,
        (weightedRightItems gs g)[k]'hk = (v.1, r v.1) := by
    intro v
    have hmem : (v.1, r v.1) ∈ weightedRightItems gs g :=
      List.mem_flatMap.2 ⟨v.1, List.mem_toFinset.1 v.2, List.mem_map.2 ⟨r v.1, hgs_all _, rfl⟩⟩
    exact List.mem_iff_getElem.1 hmem
  let leftChoice (u : ↥(leftVertices g).toFinset) : Fin W.sets.length :=
    ⟨(hmemL u).choose, by
      rw [weightedSetSystemOf_sets_length]
      exact Nat.lt_add_right _ (hmemL u).choose_spec.1⟩
  let rightChoice (v : ↥(rightVertices g).toFinset) : Fin W.sets.length :=
    ⟨(weightedLeftItems bs g).length + (hmemR v).choose, by
      rw [weightedSetSystemOf_sets_length]
      exact Nat.add_lt_add_left (hmemR v).choose_spec.1 _⟩
  let C_L : Finset (Fin W.sets.length) := (leftVertices g).toFinset.attach.image leftChoice
  let C_R : Finset (Fin W.sets.length) := (rightVertices g).toFinset.attach.image rightChoice
  have hC : W.IsCover (C_L ∪ C_R) := by
    intro z hz
    obtain ⟨e, he, x, hx, rfl⟩ := mem_weightedGround.1 hz
    let d := g.edges[e]
    have hd : d ∈ g.edges := List.getElem_mem he
    have hcon := hsat_edge d hd
    cases hbit : G.mem x (d.constraint (ℓ d.src))
    · let u : ↥(leftVertices g).toFinset :=
        ⟨d.src, List.mem_toFinset.2 (mem_leftVertices.2 ⟨d, hd, rfl⟩)⟩
      refine ⟨leftChoice u, Finset.mem_union_left _ (Finset.mem_image.2 ⟨u,
        Finset.mem_attach _ u, rfl⟩), ?_⟩
      have hk := (hmemL u).choose_spec.1
      have hget := (hmemL u).choose_spec.2
      dsimp only [W]
      change Nat.pair e x ∈ (weightedSetSystemOf bs gs fallback G g).sets[leftChoice u].elements
      rw [weightedSet_getElem_left (i := leftChoice u) hk]
      simp only [leftChoice] at *
      rw [hget]
      exact (mem_weightedLeftSet he hx).2 ⟨rfl, hbit⟩
    · let v : ↥(rightVertices g).toFinset :=
        ⟨d.dst, List.mem_toFinset.2 (mem_rightVertices.2 ⟨d, hd, rfl⟩)⟩
      refine ⟨rightChoice v, Finset.mem_union_right _ (Finset.mem_image.2 ⟨v,
        Finset.mem_attach _ v, rfl⟩), ?_⟩
      have hk := (hmemR v).choose_spec.1
      have hget := (hmemR v).choose_spec.2
      dsimp only [W]
      change Nat.pair e x ∈ (weightedSetSystemOf bs gs fallback G g).sets[rightChoice v].elements
      rw [weightedSet_getElem_right (i := rightChoice v) (Nat.le_add_right _ _)
        (by simpa [rightChoice, Nat.add_sub_cancel_left] using hk)]
      simp only [rightChoice, Nat.add_sub_cancel_left] at *
      rw [hget]
      exact (mem_weightedRightSet he hx).2 ⟨rfl, hcon ▸ hbit⟩
  have hinjL : ∀ u₁ ∈ (leftVertices g).toFinset.attach, ∀ u₂ ∈ (leftVertices g).toFinset.attach,
      leftChoice u₁ = leftChoice u₂ → u₁ = u₂ := by
    intro u₁ _ u₂ _ heq
    have hk : (hmemL u₁).choose = (hmemL u₂).choose := congrArg Fin.val heq
    have hp : (u₁.1, ℓ u₁.1) = (u₂.1, ℓ u₂.1) := by
      rw [← (hmemL u₁).choose_spec.2, ← (hmemL u₂).choose_spec.2]
      simp only [hk]
    exact Subtype.ext (Prod.ext_iff.1 hp).1
  have hinjR : ∀ v₁ ∈ (rightVertices g).toFinset.attach, ∀ v₂ ∈ (rightVertices g).toFinset.attach,
      rightChoice v₁ = rightChoice v₂ → v₁ = v₂ := by
    intro v₁ _ v₂ _ heq
    have hk : (hmemR v₁).choose = (hmemR v₂).choose := by
      have := congrArg Fin.val heq
      dsimp only [rightChoice] at this
      omega
    have hp : (v₁.1, r v₁.1) = (v₂.1, r v₂.1) := by
      rw [← (hmemR v₁).choose_spec.2, ← (hmemR v₂).choose_spec.2]
      simp only [hk]
    exact Subtype.ext (Prod.ext_iff.1 hp).1
  have hwtL : W.coverWeight C_L = g.edges.length := by
    rw [WeightedSetSystem.coverWeight, Finset.sum_image hinjL]
    have hcongr : ∑ u ∈ (leftVertices g).toFinset.attach, W.sets[leftChoice u].weight =
        ∑ u ∈ (leftVertices g).toFinset.attach, degL g u.1 := by
      refine Finset.sum_congr rfl fun u _ => ?_
      dsimp only [W]
      change (weightedSetSystemOf bs gs fallback G g).sets[leftChoice u].weight = degL g u.1
      rw [weightedSet_getElem_left (i := leftChoice u) (hmemL u).choose_spec.1]
      simp only [leftChoice]
      rw [(hmemL u).choose_spec.2]
      rfl
    rw [hcongr, Finset.sum_attach (leftVertices g).toFinset (fun u => degL g u)]
    exact sum_degL_eq_length g
  have hwtR : W.coverWeight C_R = g.edges.length := by
    rw [WeightedSetSystem.coverWeight, Finset.sum_image hinjR]
    have hcongr : ∑ v ∈ (rightVertices g).toFinset.attach, W.sets[rightChoice v].weight =
        ∑ v ∈ (rightVertices g).toFinset.attach, degR g v.1 := by
      refine Finset.sum_congr rfl fun v _ => ?_
      dsimp only [W]
      change (weightedSetSystemOf bs gs fallback G g).sets[rightChoice v].weight = degR g v.1
      rw [weightedSet_getElem_right (i := rightChoice v) (Nat.le_add_right _ _)
        (by simpa [rightChoice, Nat.add_sub_cancel_left] using (hmemR v).choose_spec.1)]
      simp only [rightChoice, Nat.add_sub_cancel_left]
      rw [(hmemR v).choose_spec.2]
      rfl
    rw [hcongr, Finset.sum_attach (rightVertices g).toFinset (fun v => degR g v)]
    exact sum_degR_eq_length g
  have hwt_union : W.coverWeight (C_L ∪ C_R) ≤ W.coverWeight C_L + W.coverWeight C_R := by
    have h := Finset.sum_union_inter (s₁ := C_L) (s₂ := C_R)
      (f := fun i : Fin W.sets.length => W.sets[i].weight)
    change W.coverWeight (C_L ∪ C_R) + W.coverWeight (C_L ∩ C_R) =
      W.coverWeight C_L + W.coverWeight C_R at h
    omega
  refine (WeightedSetSystem.optCoverWeight_le hC).trans ?_
  omega

private theorem weighted_sum_deg_mul_cand_le {α : Type} [DecidableEq α]
    (W : WeightedSetSystem) (V : Finset ℕ) (deg : ℕ → ℕ)
    (S : Finset (Fin W.sets.length)) (item : Fin W.sets.length → ℕ × α)
    (cand : ℕ → Finset α)
    (hcand : ∀ v, cand v = (S.filter fun i => (item i).1 = v).image fun i => (item i).2)
    (hmem : ∀ i ∈ S, (item i).1 ∈ V)
    (hwt : ∀ i ∈ S, W.sets[i].weight = deg (item i).1) :
    ∑ v ∈ V, deg v * (cand v).card ≤ ∑ i ∈ S, W.sets[i].weight := by
  calc ∑ v ∈ V, deg v * (cand v).card
      ≤ ∑ v ∈ V, deg v * (S.filter fun i => (item i).1 = v).card := by
          refine Finset.sum_le_sum fun v _ => Nat.mul_le_mul_left _ ?_
          rw [hcand v]
          exact Finset.card_image_le
    _ = ∑ v ∈ V, ∑ i ∈ S.filter (fun i => (item i).1 = v), W.sets[i].weight := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.card_eq_sum_ones, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          obtain ⟨hiS, hfv⟩ := Finset.mem_filter.1 hi
          rw [mul_one, hwt i hiS, hfv]
    _ = ∑ i ∈ S, W.sets[i].weight :=
          Finset.sum_fiberwise_of_maps_to hmem (fun i => W.sets[i].weight)

private theorem sum_cand_card_le_of_deg_bounds {β γ : Type}
    (g : Graph (β → γ)) (L : ℕ → Finset β) (R : ℕ → Finset γ) {totL totR tot : ℕ} {ρ : ℝ}
    (hsumL : ∑ u ∈ (leftVertices g).toFinset, degL g u * (L u).card ≤ totL)
    (hsumR : ∑ v ∈ (rightVertices g).toFinset, degR g v * (R v).card ≤ totR)
    (hpart : totL + totR = tot) (htot : (tot : ℝ) ≤ ρ * (2 * g.edges.length)) :
    ∑ i : Fin g.edges.length,
      (((L g.edges[i].src).card + (R g.edges[i].dst).card : ℕ) : ℝ) ≤
        ρ * (2 * g.edges.length) := by
  have hsum_nat : ∑ i : Fin g.edges.length, ((L g.edges[i].src).card + (R g.edges[i].dst).card) ≤
      tot := by
    rw [Finset.sum_add_distrib, sum_over_edges_degL g (fun u => (L u).card),
      sum_over_edges_degR g (fun v => (R v).card)]
    omega
  have hcast : (∑ i : Fin g.edges.length,
      (((L g.edges[i].src).card + (R g.edges[i].dst).card : ℕ) : ℝ)) ≤ tot := by
    exact_mod_cast hsum_nat
  exact hcast.trans htot

theorem weightedSetSystemOf_sound_of_isCover [DecidableEq γ] [Nonempty β] [Nonempty γ]
    {bs : List β} {gs : List γ} {fallback : γ} {G : PartitionGadget γ} {t : ℕ} (ht : 0 < t)
    (hsep : G.Separates t) {g : Graph (β → γ)} (hm : 0 < g.edges.length) {ρ : ℝ}
    {C : Finset (Fin (weightedSetSystemOf bs gs fallback G g).sets.length)}
    (hC : (weightedSetSystemOf bs gs fallback G g).IsCover C)
    (hwt : ((weightedSetSystemOf bs gs fallback G g).coverWeight C : ℝ) ≤
      ρ * (2 * g.edges.length)) :
    (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) ≤ 1 - (g.toGraph projectionEval).unsatVal := by
  classical
  let W := weightedSetSystemOf bs gs fallback G g
  let nL := (weightedLeftItems bs g).length
  let a₀ : β := Classical.arbitrary β
  let b₀ : γ := Classical.arbitrary γ
  have hlen_lt : ∀ i : Fin W.sets.length, nL ≤ (i : ℕ) →
      (i : ℕ) - nL < (weightedRightItems gs g).length := fun i hi => by
    have h := lt_of_lt_of_eq i.isLt (weightedSetSystemOf_sets_length bs gs fallback G g)
    omega
  let leftItem (i : Fin W.sets.length) : ℕ × β :=
    if hi : (i : ℕ) < nL then (weightedLeftItems bs g)[(i : ℕ)]'hi else (0, a₀)
  let rightItem (i : Fin W.sets.length) : ℕ × γ :=
    if hi : nL ≤ (i : ℕ) then (weightedRightItems gs g)[(i : ℕ) - nL]'(hlen_lt i hi) else (0, b₀)
  let C_L := C.filter fun i : Fin W.sets.length => (i : ℕ) < nL
  let C_R := C.filter fun i : Fin W.sets.length => nL ≤ (i : ℕ)
  let L (u : ℕ) : Finset β := (C_L.filter fun i => (leftItem i).1 = u).image fun i => (leftItem i).2
  let R (v : ℕ) : Finset γ :=
    (C_R.filter fun i => (rightItem i).1 = v).image fun i => (rightItem i).2
  have hleftItem_mem : ∀ i ∈ C_L, (leftItem i).1 ∈ (leftVertices g).toFinset := by
    intro i hi
    have hiL : (i : ℕ) < nL := (Finset.mem_filter.1 hi).2
    have hmem : leftItem i ∈ weightedLeftItems bs g := by
      simp only [leftItem, hiL, ↓reduceDIte]
      exact List.getElem_mem hiL
    obtain ⟨u, hu, heq⟩ := List.mem_flatMap.1 hmem
    obtain ⟨a, -, hpair⟩ := List.mem_map.1 heq
    have hu' : (leftItem i).1 = u := (congrArg Prod.fst hpair).symm
    simpa [List.mem_toFinset, hu'] using hu
  have hrightItem_mem : ∀ i ∈ C_R, (rightItem i).1 ∈ (rightVertices g).toFinset := by
    intro i hi
    have hiR : nL ≤ (i : ℕ) := (Finset.mem_filter.1 hi).2
    have hmem : rightItem i ∈ weightedRightItems gs g := by
      simp only [rightItem, hiR, ↓reduceDIte]
      exact List.getElem_mem (hlen_lt i hiR)
    obtain ⟨v, hv, heq⟩ := List.mem_flatMap.1 hmem
    obtain ⟨b, -, hpair⟩ := List.mem_map.1 heq
    have hv' : (rightItem i).1 = v := (congrArg Prod.fst hpair).symm
    simpa [List.mem_toFinset, hv'] using hv
  have hsumL_le : ∑ u ∈ (leftVertices g).toFinset, degL g u * (L u).card ≤
      ∑ i ∈ C_L, W.sets[i].weight := by
    refine weighted_sum_deg_mul_cand_le W (leftVertices g).toFinset (degL g) C_L leftItem L
      (fun _ => rfl) hleftItem_mem fun i hi => ?_
    have hiL : (i : ℕ) < nL := (Finset.mem_filter.1 hi).2
    dsimp only [W]
    rw [weightedSet_getElem_left (i := i) hiL]
    simp only [leftItem, hiL, ↓reduceDIte]
    rfl
  have hsumR_le : ∑ v ∈ (rightVertices g).toFinset, degR g v * (R v).card ≤
      ∑ i ∈ C_R, W.sets[i].weight := by
    refine weighted_sum_deg_mul_cand_le W (rightVertices g).toFinset (degR g) C_R rightItem R
      (fun _ => rfl) hrightItem_mem fun i hi => ?_
    have hiR : nL ≤ (i : ℕ) := (Finset.mem_filter.1 hi).2
    dsimp only [W]
    rw [weightedSet_getElem_right (i := i) hiR (hlen_lt i hiR)]
    simp only [rightItem, hiR, ↓reduceDIte]
    rfl
  have hpart : (∑ i ∈ C_L, W.sets[i].weight) + (∑ i ∈ C_R, W.sets[i].weight) = W.coverWeight C := by
    have := Finset.sum_filter_add_sum_filter_not C (fun i : Fin W.sets.length => (i : ℕ) < nL)
      (fun i => W.sets[i].weight)
    simpa [C_L, C_R, not_lt, WeightedSetSystem.coverWeight] using this
  have hsum : ∑ i : Fin g.edges.length,
      (((L g.edges[i].src).card + (R g.edges[i].dst).card : ℕ) : ℝ) ≤
        ρ * (2 * g.edges.length) :=
    sum_cand_card_le_of_deg_bounds g L R hsumL_le hsumR_le hpart hwt
  have hmatch : ∀ i : Fin g.edges.length,
      (L g.edges[i].src).card + (R g.edges[i].dst).card ≤ t →
        ∃ a ∈ L g.edges[i].src, ∃ b ∈ R g.edges[i].dst, g.edges[i].constraint a = b := by
    intro i hle
    refine G.exists_eq_of_covers hsep g.edges[i].constraint _ _ hle fun x hx => ?_
    have hz : Nat.pair i.1 x ∈ W.ground :=
      mem_weightedGround.2 ⟨i.1, i.isLt, x, hx, rfl⟩
    obtain ⟨j, hjC, hjz⟩ := hC (Nat.pair i.1 x) hz
    by_cases hjL : (j : ℕ) < nL
    · left
      have hjCL : j ∈ C_L := Finset.mem_filter.2 ⟨hjC, hjL⟩
      have hjz' : Nat.pair i.1 x ∈
          (weightedLeftSet fallback G g (leftItem j).1 (leftItem j).2).elements := by
        change Nat.pair i.1 x ∈ (weightedSetSystemOf bs gs fallback G g).sets[j].elements at hjz
        rw [weightedSet_getElem_left (i := j) hjL] at hjz
        simpa [leftItem, hjL] using hjz
      obtain ⟨hsrc, hmem⟩ := (mem_weightedLeftSet i.isLt hx).1 hjz'
      refine ⟨(leftItem j).2, Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨hjCL, hsrc.symm⟩, rfl⟩,
        hmem⟩
    · right
      have hjR : nL ≤ (j : ℕ) := Nat.le_of_not_lt hjL
      have hjCR : j ∈ C_R := Finset.mem_filter.2 ⟨hjC, hjR⟩
      have hjz' : Nat.pair i.1 x ∈
          (weightedRightSet fallback G g (rightItem j).1 (rightItem j).2).elements := by
        change Nat.pair i.1 x ∈ (weightedSetSystemOf bs gs fallback G g).sets[j].elements at hjz
        rw [weightedSet_getElem_right (i := j) hjR (hlen_lt j hjR)] at hjz
        simpa [rightItem, hjR] using hjz
      obtain ⟨hdst, hmem⟩ := (mem_weightedRightSet i.isLt hx).1 hjz'
      refine ⟨(rightItem j).2, Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨hjCR, hdst.symm⟩, rfl⟩,
        hmem⟩
  exact exists_labelling_of_list_sets g L R ht hm hmatch hsum

theorem weightedSetSystemOf_sound [DecidableEq γ] [Nonempty β] [Nonempty γ]
    {bs : List β} {gs : List γ} {fallback : γ} (hbs_all : ∀ a, a ∈ bs) (hgs_all : ∀ b, b ∈ gs)
    {G : PartitionGadget γ} {t : ℕ} (ht : 0 < t) (hsep : G.Separates t)
    {g : Graph (β → γ)} (hm : 0 < g.edges.length) {ρ : ℝ}
    (hwt : ((weightedSetSystemOf bs gs fallback G g).optCoverWeight : ℝ) ≤
      ρ * (2 * g.edges.length)) :
    (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) ≤ 1 - (g.toGraph projectionEval).unsatVal := by
  obtain ⟨C, hC, hCwt⟩ := WeightedSetSystem.exists_isCover_optCoverWeight
    (weightedSetSystemOf_coverable hbs_all hgs_all G g)
  rw [← hCwt] at hwt
  exact weightedSetSystemOf_sound_of_isCover ht hsep hm hC hwt

/-! #### Unweighted reduction -/

/-- Ground elements for the unweighted Set Cover reduction: quadruples
`(e, x, r₁, r₂)` encoded as `Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂)` for each edge `e`,
gadget element `x < G.size`, left copy `r₁ < degL g e.src`, and right copy `r₂ < degR g e.dst`. -/
@[expose] def unweightedGround (fallback : γ) (G : PartitionGadget γ) (g : Graph (β → γ)) :
    List ℕ :=
  (List.range g.edges.length).flatMap fun e =>
    let d := g.edges.getD e ⟨0, 0, fun _ => fallback⟩
    (List.range G.size).flatMap fun x =>
      (List.range (degL g d.src)).flatMap fun r₁ =>
        (List.range (degR g d.dst)).map fun r₂ =>
          Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂)

/-- Left candidate sets `(u, r₁, a)` in the unweighted reduction. -/
@[expose] def unweightedLeftSet (fallback : γ) (G : PartitionGadget γ) (g : Graph (β → γ))
    (u r₁ : ℕ) (a : β) : List ℕ :=
  (List.range g.edges.length).flatMap fun e =>
    let d := g.edges.getD e ⟨0, 0, fun _ => fallback⟩
    if d.src = u then
      ((List.range G.size).filter fun x => !G.mem x (d.constraint a)).flatMap fun x =>
        (List.range (degR g d.dst)).map fun r₂ =>
          Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂)
    else []

/-- Right candidate sets `(v, r₂, b)` in the unweighted reduction. -/
@[expose] def unweightedRightSet (fallback : γ) (G : PartitionGadget γ) (g : Graph (β → γ))
    (v r₂ : ℕ) (b : γ) : List ℕ :=
  (List.range g.edges.length).flatMap fun e =>
    let d := g.edges.getD e ⟨0, 0, fun _ => fallback⟩
    if d.dst = v then
      ((List.range G.size).filter fun x => G.mem x b).flatMap fun x =>
        (List.range (degL g d.src)).map fun r₁ =>
          Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂)
    else []

/-- Left item list `(u, r₁, a)` for the unweighted reduction. -/
@[expose] def unweightedLeftItems (bs : List β) (g : Graph (β → γ)) : List (ℕ × ℕ × β) :=
  (leftVertices g).flatMap fun u =>
    (List.range (degL g u)).flatMap fun r₁ =>
      bs.map fun a => (u, r₁, a)

/-- Right item list `(v, r₂, b)` for the unweighted reduction. -/
@[expose] def unweightedRightItems (gs : List γ) (g : Graph (β → γ)) : List (ℕ × ℕ × γ) :=
  (rightVertices g).flatMap fun v =>
    (List.range (degR g v)).flatMap fun r₂ =>
      gs.map fun b => (v, r₂, b)

/-- Unweighted set system constructed by the Lund–Yannakakis / Feige reduction. -/
@[expose] def setSystemOf (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) (g : Graph (β → γ)) : SetSystem :=
  ⟨unweightedGround fallback G g,
    (unweightedLeftItems bs g).map
        (fun (u, r₁, a) => unweightedLeftSet fallback G g u r₁ a) ++
      (unweightedRightItems gs g).map
        (fun (v, r₂, b) => unweightedRightSet fallback G g v r₂ b)⟩

/-- Computable unweighted Set Cover reduction from Label Cover parameterized by explicit label
lists `bs`, `gs`, a fallback label `fallback : γ`, and a partition gadget `G`. -/
@[expose] def toSetCoverOf (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) (g : Graph (β → γ)) : SetSystem × ℕ :=
  (setSystemOf bs gs fallback G g, 2 * g.edges.length)

private theorem mem_unweightedGround {fallback : γ} {G : PartitionGadget γ}
    {g : Graph (β → γ)} {z : ℕ} :
    z ∈ unweightedGround fallback G g ↔
      ∃ e < g.edges.length, ∃ x < G.size,
        ∃ r₁ < degL g (g.edges.getD e ⟨0, 0, fun _ => fallback⟩).src,
          ∃ r₂ < degR g (g.edges.getD e ⟨0, 0, fun _ => fallback⟩).dst,
            Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂) = z := by
  simp only [unweightedGround, List.mem_flatMap, List.mem_map, List.mem_range]

private theorem mem_unweightedLeftSet {fallback : γ} {G : PartitionGadget γ} {g : Graph (β → γ)}
    {u r₁' : ℕ} {a : β} {e x r₁ r₂ : ℕ} (he : e < g.edges.length) (hx : x < G.size)
    (hr₂ : r₂ < degR g g.edges[e].dst) :
    Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂) ∈ unweightedLeftSet fallback G g u r₁' a ↔
      g.edges[e].src = u ∧ r₁ = r₁' ∧ G.mem x (g.edges[e].constraint a) = false := by
  simp only [unweightedLeftSet, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨e', he', hz⟩
    rw [List.getD_eq_getElem _ _ he'] at hz
    split_ifs at hz with hsrc
    · simp only [List.mem_flatMap, List.mem_filter, List.mem_range, Bool.not_eq_true',
        List.mem_map] at hz
      obtain ⟨x', ⟨_, hx'⟩, r₂', _, hpair⟩ := hz
      obtain ⟨hp1, hp2⟩ := Nat.pair_eq_pair.1 hpair
      obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 hp1
      obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 hp2
      exact ⟨hsrc, rfl, hx'⟩
    · simp at hz
  · rintro ⟨hsrc, rfl, hmem⟩
    refine ⟨e, he, ?_⟩
    rw [List.getD_eq_getElem _ _ he]
    simp only [hsrc, ↓reduceIte, List.mem_flatMap, List.mem_filter, List.mem_range,
      Bool.not_eq_true', List.mem_map]
    exact ⟨x, ⟨hx, hmem⟩, r₂, hr₂, rfl⟩

private theorem mem_unweightedRightSet {fallback : γ} {G : PartitionGadget γ} {g : Graph (β → γ)}
    {v r₂' : ℕ} {b : γ} {e x r₁ r₂ : ℕ} (he : e < g.edges.length) (hx : x < G.size)
    (hr₁ : r₁ < degL g g.edges[e].src) :
    Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂) ∈ unweightedRightSet fallback G g v r₂' b ↔
      g.edges[e].dst = v ∧ r₂ = r₂' ∧ G.mem x b = true := by
  simp only [unweightedRightSet, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨e', he', hz⟩
    rw [List.getD_eq_getElem _ _ he'] at hz
    split_ifs at hz with hdst
    · simp only [List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map] at hz
      obtain ⟨x', ⟨_, hx'⟩, r₁', _, hpair⟩ := hz
      obtain ⟨hp1, hp2⟩ := Nat.pair_eq_pair.1 hpair
      obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 hp1
      obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 hp2
      exact ⟨hdst, rfl, hx'⟩
    · simp at hz
  · rintro ⟨hdst, rfl, hmem⟩
    refine ⟨e, he, ?_⟩
    rw [List.getD_eq_getElem _ _ he]
    simp only [hdst, ↓reduceIte, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map]
    exact ⟨x, ⟨hx, hmem⟩, r₁, hr₁, rfl⟩

private theorem setSystemOf_sets_length (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) (g : Graph (β → γ)) :
    (setSystemOf bs gs fallback G g).sets.length =
      (unweightedLeftItems bs g).length + (unweightedRightItems gs g).length := by
  simp [setSystemOf]

private theorem setSystem_getElem_left {bs : List β} {gs : List γ} {fallback : γ}
    {G : PartitionGadget γ} {g : Graph (β → γ)}
    {i : Fin (setSystemOf bs gs fallback G g).sets.length}
    (hi : (i : ℕ) < (unweightedLeftItems bs g).length) :
    (setSystemOf bs gs fallback G g).sets[i] =
      unweightedLeftSet fallback G g ((unweightedLeftItems bs g)[(i : ℕ)]'hi).1
        ((unweightedLeftItems bs g)[(i : ℕ)]'hi).2.1
        ((unweightedLeftItems bs g)[(i : ℕ)]'hi).2.2 := by
  change ((unweightedLeftItems bs g).map
        (fun (u, r₁, a) => unweightedLeftSet fallback G g u r₁ a) ++
      (unweightedRightItems gs g).map
        (fun (v, r₂, b) => unweightedRightSet fallback G g v r₂ b))[(i : ℕ)] = _
  rw [List.getElem_append_left (by simp [hi])]
  simp only [List.getElem_map]

private theorem setSystem_getElem_right {bs : List β} {gs : List γ} {fallback : γ}
    {G : PartitionGadget γ} {g : Graph (β → γ)}
    {i : Fin (setSystemOf bs gs fallback G g).sets.length}
    (hi : (unweightedLeftItems bs g).length ≤ (i : ℕ))
    (hk : (i : ℕ) - (unweightedLeftItems bs g).length < (unweightedRightItems gs g).length) :
    (setSystemOf bs gs fallback G g).sets[i] =
      unweightedRightSet fallback G g
        ((unweightedRightItems gs g)[(i : ℕ) - (unweightedLeftItems bs g).length]'hk).1
        ((unweightedRightItems gs g)[(i : ℕ) - (unweightedLeftItems bs g).length]'hk).2.1
        ((unweightedRightItems gs g)[(i : ℕ) - (unweightedLeftItems bs g).length]'hk).2.2 := by
  have hge : ((unweightedLeftItems bs g).map
      (fun (u, r₁, a) => unweightedLeftSet fallback G g u r₁ a)).length ≤ (i : ℕ) := by
    simp [hi]
  change ((unweightedLeftItems bs g).map
        (fun (u, r₁, a) => unweightedLeftSet fallback G g u r₁ a) ++
      (unweightedRightItems gs g).map
        (fun (v, r₂, b) => unweightedRightSet fallback G g v r₂ b))[(i : ℕ)] = _
  rw [List.getElem_append_right hge]
  simp only [List.length_map, List.getElem_map]

theorem setSystemOf_ground_length_le {bs : List β} {gs : List γ} {fallback : γ}
    {G : PartitionGadget γ} {g : Graph (β → γ)} :
    (setSystemOf bs gs fallback G g).ground.length ≤ g.edges.length ^ 3 * G.size := by
  simp only [setSystemOf, unweightedGround, List.length_flatMap, List.length_map,
    List.length_range]
  have hinner : ∀ e ∈ List.range g.edges.length,
      (List.map (fun x =>
          (List.map (fun r₁ => degR g (g.edges.getD e ⟨0, 0, fun _ => fallback⟩).dst)
            (List.range (degL g (g.edges.getD e ⟨0, 0, fun _ => fallback⟩).src))).sum)
        (List.range G.size)).sum ≤ g.edges.length ^ 2 * G.size := by
    intro e _
    simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
    calc G.size *
          (degL g (g.edges.getD e ⟨0, 0, fun _ => fallback⟩).src *
            degR g (g.edges.getD e ⟨0, 0, fun _ => fallback⟩).dst)
        ≤ G.size * (g.edges.length * g.edges.length) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul (degL_le_length _ _) (degR_le_length _ _))
      _ = g.edges.length ^ 2 * G.size := by ring
  calc ((List.range g.edges.length).map _).sum
      ≤ ((List.range g.edges.length).map fun _ => g.edges.length ^ 2 * G.size).sum :=
          List.sum_le_sum hinner
    _ = g.edges.length ^ 3 * G.size := by
          simp [List.map_const', List.sum_replicate]
          ring

theorem setSystemOf_ground_length_pos {bs : List β} {gs : List γ} {fallback : γ}
    {G : PartitionGadget γ} {g : Graph (β → γ)}
    (hm : 0 < g.edges.length) (hG : 0 < G.size) :
    0 < (setSystemOf bs gs fallback G g).ground.length := by
  have hr₁ : 0 < degL g g.edges[0].src :=
    degL_pos_of_mem (mem_leftVertices.2 ⟨g.edges[0], List.getElem_mem hm, rfl⟩)
  have hr₂ : 0 < degR g g.edges[0].dst :=
    degR_pos_of_mem (mem_rightVertices.2 ⟨g.edges[0], List.getElem_mem hm, rfl⟩)
  have hmem : Nat.pair (Nat.pair 0 0) (Nat.pair 0 0) ∈
      (setSystemOf bs gs fallback G g).ground := by
    refine mem_unweightedGround.2 ⟨0, hm, 0, hG, 0, ?_, 0, ?_, rfl⟩
    · rwa [List.getD_eq_getElem _ _ hm]
    · rwa [List.getD_eq_getElem _ _ hm]
  exact List.length_pos_of_mem hmem

theorem setSystemOf_ground_length_ge {bs : List β} {gs : List γ} {fallback : γ}
    {G : PartitionGadget γ} {g : Graph (β → γ)} (hm : 0 < g.edges.length) :
    G.size ≤ (setSystemOf bs gs fallback G g).ground.length := by
  have hr₁ : 0 < degL g g.edges[0].src :=
    degL_pos_of_mem (mem_leftVertices.2 ⟨g.edges[0], List.getElem_mem hm, rfl⟩)
  have hr₂ : 0 < degR g g.edges[0].dst :=
    degR_pos_of_mem (mem_rightVertices.2 ⟨g.edges[0], List.getElem_mem hm, rfl⟩)
  let f : Fin G.size → ℕ := fun x => Nat.pair (Nat.pair 0 x.1) (Nat.pair 0 0)
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 := (Nat.pair_eq_pair.1 hxy).1
    exact Fin.ext (Nat.pair_eq_pair.1 h1).2
  have hsub : Finset.univ.image f ⊆ (setSystemOf bs gs fallback G g).ground.toFinset := by
    intro z hz
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hz
    refine List.mem_toFinset.2 (mem_unweightedGround.2 ⟨0, hm, x.1, x.isLt, 0, ?_, 0, ?_, rfl⟩)
    · rwa [List.getD_eq_getElem _ _ hm]
    · rwa [List.getD_eq_getElem _ _ hm]
  calc G.size
      = (Finset.univ : Finset (Fin G.size)).card := (Fintype.card_fin _).symm
    _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (setSystemOf bs gs fallback G g).ground.toFinset.card := Finset.card_le_card hsub
    _ ≤ (setSystemOf bs gs fallback G g).ground.length := List.toFinset_card_le _

theorem setSystemOf_coverable [Nonempty β] {bs : List β} {gs : List γ} {fallback : γ}
    (hbs_all : ∀ a, a ∈ bs) (hgs_all : ∀ b, b ∈ gs)
    (G : PartitionGadget γ) (g : Graph (β → γ)) :
    (setSystemOf bs gs fallback G g).Coverable := by
  refine ⟨Finset.univ, fun z hz => ?_⟩
  obtain ⟨e, he, x, hx, r₁, hr₁, r₂, hr₂, rfl⟩ := mem_unweightedGround.1 hz
  rw [List.getD_eq_getElem _ _ he] at hr₁ hr₂
  let a₀ : β := Classical.arbitrary β
  let b := g.edges[e].constraint a₀
  have hu : g.edges[e].src ∈ leftVertices g :=
    mem_leftVertices.2 ⟨g.edges[e], List.getElem_mem he, rfl⟩
  have hv : g.edges[e].dst ∈ rightVertices g :=
    mem_rightVertices.2 ⟨g.edges[e], List.getElem_mem he, rfl⟩
  cases hbit : G.mem x b
  · have hmemL : (g.edges[e].src, r₁, a₀) ∈ unweightedLeftItems bs g :=
      List.mem_flatMap.2 ⟨g.edges[e].src, hu,
        List.mem_flatMap.2 ⟨r₁, List.mem_range.2 hr₁, List.mem_map.2 ⟨a₀, hbs_all a₀, rfl⟩⟩⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.1 hmemL
    let i : Fin (setSystemOf bs gs fallback G g).sets.length :=
      ⟨k, by rw [setSystemOf_sets_length]; exact Nat.lt_add_right _ hk⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    change Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂) ∈ (setSystemOf bs gs fallback G g).sets[i]
    rw [setSystem_getElem_left hk]
    simp only [i, hget]
    exact (mem_unweightedLeftSet he hx hr₂).2 ⟨rfl, rfl, hbit⟩
  · have hmemR : (g.edges[e].dst, r₂, b) ∈ unweightedRightItems gs g :=
      List.mem_flatMap.2 ⟨g.edges[e].dst, hv,
        List.mem_flatMap.2 ⟨r₂, List.mem_range.2 hr₂, List.mem_map.2 ⟨b, hgs_all b, rfl⟩⟩⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.1 hmemR
    let i : Fin (setSystemOf bs gs fallback G g).sets.length :=
      ⟨(unweightedLeftItems bs g).length + k, by rw [setSystemOf_sets_length]; omega⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    change Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂) ∈ (setSystemOf bs gs fallback G g).sets[i]
    rw [setSystem_getElem_right (i := i) (Nat.le_add_right _ _)
      (by simpa [i, Nat.add_sub_cancel_left] using hk)]
    simp only [i, Nat.add_sub_cancel_left, hget]
    exact (mem_unweightedRightSet he hx hr₁).2 ⟨rfl, rfl, hbit⟩

theorem setSystemOf_complete [DecidableEq γ] [Nonempty β] [Nonempty γ]
    {bs : List β} {gs : List γ} {fallback : γ}
    (hbs_all : ∀ a, a ∈ bs) (hgs_all : ∀ b, b ∈ gs)
    (G : PartitionGadget γ) (g : Graph (β → γ))
    (hsat : 1 ≤ 1 - (g.toGraph projectionEval).unsatVal) :
    (setSystemOf bs gs fallback G g).optCoverSize ≤ 2 * g.edges.length := by
  classical
  have hunsat0 : (g.toGraph projectionEval).unsatVal = 0 :=
    le_antisymm (by linarith) (ConstraintGraph.unsatVal_nonneg _)
  have hSat : (g.toGraph projectionEval).Satisfiable :=
    (ConstraintGraph.unsatVal_eq_zero_iff _).1 hunsat0
  obtain ⟨ℓ, r, hsat_edge⟩ := (satisfiable_toGraph_projectionEval_iff g).1 hSat
  let S := setSystemOf bs gs fallback G g
  have hmemL : ∀ (u : ↥(leftVertices g).toFinset) (r₁ : ↥(Finset.range (degL g u.1))),
      ∃ k, ∃ hk : k < (unweightedLeftItems bs g).length,
        (unweightedLeftItems bs g)[k]'hk = (u.1, r₁.1, ℓ u.1) := by
    intro u r₁
    have hmem : (u.1, r₁.1, ℓ u.1) ∈ unweightedLeftItems bs g :=
      List.mem_flatMap.2 ⟨u.1, List.mem_toFinset.1 u.2,
        List.mem_flatMap.2 ⟨r₁.1, List.mem_range.2 (Finset.mem_range.1 r₁.2),
          List.mem_map.2 ⟨ℓ u.1, hbs_all _, rfl⟩⟩⟩
    exact List.mem_iff_getElem.1 hmem
  have hmemR : ∀ (v : ↥(rightVertices g).toFinset) (r₂ : ↥(Finset.range (degR g v.1))),
      ∃ k, ∃ hk : k < (unweightedRightItems gs g).length,
        (unweightedRightItems gs g)[k]'hk = (v.1, r₂.1, r v.1) := by
    intro v r₂
    have hmem : (v.1, r₂.1, r v.1) ∈ unweightedRightItems gs g :=
      List.mem_flatMap.2 ⟨v.1, List.mem_toFinset.1 v.2,
        List.mem_flatMap.2 ⟨r₂.1, List.mem_range.2 (Finset.mem_range.1 r₂.2),
          List.mem_map.2 ⟨r v.1, hgs_all _, rfl⟩⟩⟩
    exact List.mem_iff_getElem.1 hmem
  let leftChoice (u : ↥(leftVertices g).toFinset) (r₁ : ↥(Finset.range (degL g u.1))) :
      Fin S.sets.length :=
    ⟨(hmemL u r₁).choose, by
      rw [setSystemOf_sets_length]
      exact Nat.lt_add_right _ (hmemL u r₁).choose_spec.1⟩
  let rightChoice (v : ↥(rightVertices g).toFinset) (r₂ : ↥(Finset.range (degR g v.1))) :
      Fin S.sets.length :=
    ⟨(unweightedLeftItems bs g).length + (hmemR v r₂).choose, by
      rw [setSystemOf_sets_length]
      exact Nat.add_lt_add_left (hmemR v r₂).choose_spec.1 _⟩
  let C_L : Finset (Fin S.sets.length) :=
    (leftVertices g).toFinset.attach.biUnion fun u =>
      (Finset.range (degL g u.1)).attach.image fun r₁ => leftChoice u r₁
  let C_R : Finset (Fin S.sets.length) :=
    (rightVertices g).toFinset.attach.biUnion fun v =>
      (Finset.range (degR g v.1)).attach.image fun r₂ => rightChoice v r₂
  have hC : S.IsCover (C_L ∪ C_R) := by
    intro z hz
    obtain ⟨e, he, x, hx, r₁, hr₁, r₂, hr₂, rfl⟩ := mem_unweightedGround.1 hz
    rw [List.getD_eq_getElem _ _ he] at hr₁ hr₂
    let d := g.edges[e]
    have hd : d ∈ g.edges := List.getElem_mem he
    have hcon := hsat_edge d hd
    cases hbit : G.mem x (d.constraint (ℓ d.src))
    · let u : ↥(leftVertices g).toFinset :=
        ⟨d.src, List.mem_toFinset.2 (mem_leftVertices.2 ⟨d, hd, rfl⟩)⟩
      let r₁' : ↥(Finset.range (degL g u.1)) := ⟨r₁, Finset.mem_range.2 hr₁⟩
      refine ⟨leftChoice u r₁', Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨u,
        Finset.mem_attach _ u, Finset.mem_image.2 ⟨r₁', Finset.mem_attach _ r₁', rfl⟩⟩), ?_⟩
      dsimp only [S]
      change Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂) ∈
        (setSystemOf bs gs fallback G g).sets[leftChoice u r₁']
      rw [setSystem_getElem_left (i := leftChoice u r₁') (hmemL u r₁').choose_spec.1]
      simp only [leftChoice]
      rw [(hmemL u r₁').choose_spec.2]
      exact (mem_unweightedLeftSet he hx hr₂).2 ⟨rfl, rfl, hbit⟩
    · let v : ↥(rightVertices g).toFinset :=
        ⟨d.dst, List.mem_toFinset.2 (mem_rightVertices.2 ⟨d, hd, rfl⟩)⟩
      let r₂' : ↥(Finset.range (degR g v.1)) := ⟨r₂, Finset.mem_range.2 hr₂⟩
      refine ⟨rightChoice v r₂', Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨v,
        Finset.mem_attach _ v, Finset.mem_image.2 ⟨r₂', Finset.mem_attach _ r₂', rfl⟩⟩), ?_⟩
      dsimp only [S]
      change Nat.pair (Nat.pair e x) (Nat.pair r₁ r₂) ∈
        (setSystemOf bs gs fallback G g).sets[rightChoice v r₂']
      rw [setSystem_getElem_right (i := rightChoice v r₂') (Nat.le_add_right _ _)
        (by simpa [rightChoice, Nat.add_sub_cancel_left] using (hmemR v r₂').choose_spec.1)]
      simp only [rightChoice, Nat.add_sub_cancel_left]
      rw [(hmemR v r₂').choose_spec.2]
      exact (mem_unweightedRightSet he hx hr₁).2 ⟨rfl, rfl, hcon ▸ hbit⟩
  have hcardL : C_L.card ≤ g.edges.length := by
    calc C_L.card
        ≤ ∑ u ∈ (leftVertices g).toFinset.attach,
            ((Finset.range (degL g u.1)).attach.image fun r₁ => leftChoice u r₁).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ u ∈ (leftVertices g).toFinset.attach, (Finset.range (degL g u.1)).attach.card :=
            Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ = ∑ u ∈ (leftVertices g).toFinset.attach, degL g u.1 := by
            simp only [Finset.card_attach, Finset.card_range]
      _ = ∑ u ∈ (leftVertices g).toFinset, degL g u :=
            Finset.sum_attach (leftVertices g).toFinset (fun u => degL g u)
      _ = g.edges.length := sum_degL_eq_length g
  have hcardR : C_R.card ≤ g.edges.length := by
    calc C_R.card
        ≤ ∑ v ∈ (rightVertices g).toFinset.attach,
            ((Finset.range (degR g v.1)).attach.image fun r₂ => rightChoice v r₂).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ v ∈ (rightVertices g).toFinset.attach, (Finset.range (degR g v.1)).attach.card :=
            Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ = ∑ v ∈ (rightVertices g).toFinset.attach, degR g v.1 := by
            simp only [Finset.card_attach, Finset.card_range]
      _ = ∑ v ∈ (rightVertices g).toFinset, degR g v :=
            Finset.sum_attach (rightVertices g).toFinset (fun v => degR g v)
      _ = g.edges.length := sum_degR_eq_length g
  have hcard : (C_L ∪ C_R).card ≤ 2 * g.edges.length := by
    calc (C_L ∪ C_R).card
        ≤ C_L.card + C_R.card := Finset.card_union_le _ _
      _ ≤ 2 * g.edges.length := by omega
  exact (SetSystem.optCoverSize_le hC).trans hcard

private theorem sum_deg_mul_cand_le_card {ι α : Type} [DecidableEq α]
    (V : Finset ℕ) (deg : ℕ → ℕ) (Cand : ℕ → Finset α)
    (Rep : ℕ → ℕ → Finset α) (Sub : Finset ι) (item : ι → ℕ × ℕ × α)
    (hrep : ∀ v ∈ V, ∀ r ∈ Finset.range (deg v), (Cand v).card ≤ (Rep v r).card)
    (himg : ∀ v r, Rep v r =
      (Sub.filter fun i => (item i).1 = v ∧ (item i).2.1 = r).image fun i => (item i).2.2)
    (hitem : ∀ i ∈ Sub, (item i).1 ∈ V ∧ (item i).2.1 ∈ Finset.range (deg (item i).1)) :
    ∑ v ∈ V, deg v * (Cand v).card ≤ Sub.card := by
  calc ∑ v ∈ V, deg v * (Cand v).card
      = ∑ v ∈ V, ∑ _r ∈ Finset.range (deg v), (Cand v).card := by
          refine Finset.sum_congr rfl fun v _ => ?_
          simp [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ ∑ v ∈ V, ∑ r ∈ Finset.range (deg v), (Rep v r).card :=
          Finset.sum_le_sum fun v hv => Finset.sum_le_sum fun r hr => hrep v hv r hr
    _ ≤ ∑ v ∈ V, ∑ r ∈ Finset.range (deg v),
          (Sub.filter fun i => (item i).1 = v ∧ (item i).2.1 = r).card := by
          refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun r _ => ?_
          rw [himg v r]
          exact Finset.card_image_le
    _ = ∑ v ∈ V, (Sub.filter fun i => (item i).1 = v).card := by
          refine Finset.sum_congr rfl fun v _ => ?_
          have hfib : ∀ r ∈ Finset.range (deg v),
              (Sub.filter fun i => (item i).1 = v ∧ (item i).2.1 = r).card =
                ((Sub.filter fun i => (item i).1 = v).filter
                  fun i => (item i).2.1 = r).card := fun r _ => by
              congr 1; ext i; simp [Finset.mem_filter, and_assoc]
          rw [Finset.sum_congr rfl hfib, Finset.sum_card_fiberwise_eq_card_filter]
          congr 1
          refine Finset.filter_eq_self.2 fun i hi => ?_
          obtain ⟨hiS, hfv⟩ := Finset.mem_filter.1 hi
          have hp := (hitem i hiS).2
          rwa [hfv] at hp
    _ = Sub.card := by
          rw [Finset.sum_card_fiberwise_eq_card_filter]
          congr 1
          exact Finset.filter_eq_self.2 fun i hi => (hitem i hi).1

theorem setSystemOf_sound_of_isCover [DecidableEq γ] [Nonempty β] [Nonempty γ]
    {bs : List β} {gs : List γ} {fallback : γ} {G : PartitionGadget γ} {t : ℕ} (ht : 0 < t)
    (hsep : G.Separates t) {g : Graph (β → γ)} (hm : 0 < g.edges.length) {ρ : ℝ}
    {C : Finset (Fin (setSystemOf bs gs fallback G g).sets.length)}
    (hC : (setSystemOf bs gs fallback G g).IsCover C)
    (hcard : (C.card : ℝ) ≤ ρ * (2 * g.edges.length)) :
    (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) ≤ 1 - (g.toGraph projectionEval).unsatVal := by
  classical
  let nL := (unweightedLeftItems bs g).length
  let a₀ : β := Classical.arbitrary β
  let b₀ : γ := Classical.arbitrary γ
  have hlen_lt : ∀ i : Fin (setSystemOf bs gs fallback G g).sets.length, nL ≤ (i : ℕ) →
      (i : ℕ) - nL < (unweightedRightItems gs g).length := fun i hi => by
    have h := lt_of_lt_of_eq i.isLt (setSystemOf_sets_length bs gs fallback G g)
    omega
  let leftItem (i : Fin (setSystemOf bs gs fallback G g).sets.length) : ℕ × ℕ × β :=
    if hi : (i : ℕ) < nL then (unweightedLeftItems bs g)[(i : ℕ)]'hi else (0, 0, a₀)
  let rightItem (i : Fin (setSystemOf bs gs fallback G g).sets.length) : ℕ × ℕ × γ :=
    if hi : nL ≤ (i : ℕ) then (unweightedRightItems gs g)[(i : ℕ) - nL]'(hlen_lt i hi)
    else (0, 0, b₀)
  let C_L := C.filter fun i : Fin (setSystemOf bs gs fallback G g).sets.length => (i : ℕ) < nL
  let C_R := C.filter fun i : Fin (setSystemOf bs gs fallback G g).sets.length => nL ≤ (i : ℕ)
  let L_rep (u r₁ : ℕ) : Finset β :=
    (C_L.filter fun i => (leftItem i).1 = u ∧ (leftItem i).2.1 = r₁).image
      fun i => (leftItem i).2.2
  let R_rep (v r₂ : ℕ) : Finset γ :=
    (C_R.filter fun i => (rightItem i).1 = v ∧ (rightItem i).2.1 = r₂).image
      fun i => (rightItem i).2.2
  have hminL : ∀ u ∈ leftVertices g, ∃ r₁ ∈ Finset.range (degL g u),
      ∀ r₁' ∈ Finset.range (degL g u), (L_rep u r₁).card ≤ (L_rep u r₁').card := fun u hu =>
    Finset.exists_min_image _ (fun r₁ => (L_rep u r₁).card)
      ⟨0, Finset.mem_range.2 (degL_pos_of_mem hu)⟩
  have hminR : ∀ v ∈ rightVertices g, ∃ r₂ ∈ Finset.range (degR g v),
      ∀ r₂' ∈ Finset.range (degR g v), (R_rep v r₂).card ≤ (R_rep v r₂').card := fun v hv =>
    Finset.exists_min_image _ (fun r₂ => (R_rep v r₂).card)
      ⟨0, Finset.mem_range.2 (degR_pos_of_mem hv)⟩
  let r₁Star (u : ℕ) : ℕ := if hu : u ∈ leftVertices g then (hminL u hu).choose else 0
  let r₂Star (v : ℕ) : ℕ := if hv : v ∈ rightVertices g then (hminR v hv).choose else 0
  let L (u : ℕ) : Finset β := L_rep u (r₁Star u)
  let R (v : ℕ) : Finset γ := R_rep v (r₂Star v)
  have hleftItem_prop : ∀ i ∈ C_L,
      (leftItem i).1 ∈ (leftVertices g).toFinset ∧
        (leftItem i).2.1 ∈ Finset.range (degL g (leftItem i).1) := by
    intro i hi
    have hiL : (i : ℕ) < nL := (Finset.mem_filter.1 hi).2
    have hmem : leftItem i ∈ unweightedLeftItems bs g := by
      simp only [leftItem, hiL, ↓reduceDIte]
      exact List.getElem_mem hiL
    obtain ⟨u, hu, heq⟩ := List.mem_flatMap.1 hmem
    obtain ⟨r₁, hr₁, heq2⟩ := List.mem_flatMap.1 heq
    obtain ⟨a, -, hpair⟩ := List.mem_map.1 heq2
    have hu' : (leftItem i).1 = u := (congrArg Prod.fst hpair).symm
    have hr₁' : (leftItem i).2.1 = r₁ := (congrArg (fun p => p.2.1) hpair).symm
    refine ⟨by simpa [List.mem_toFinset, hu'] using hu, ?_⟩
    simpa [hu', hr₁'] using List.mem_range.1 hr₁
  have hrightItem_prop : ∀ i ∈ C_R,
      (rightItem i).1 ∈ (rightVertices g).toFinset ∧
        (rightItem i).2.1 ∈ Finset.range (degR g (rightItem i).1) := by
    intro i hi
    have hiR : nL ≤ (i : ℕ) := (Finset.mem_filter.1 hi).2
    have hmem : rightItem i ∈ unweightedRightItems gs g := by
      simp only [rightItem, hiR, ↓reduceDIte]
      exact List.getElem_mem (hlen_lt i hiR)
    obtain ⟨v, hv, heq⟩ := List.mem_flatMap.1 hmem
    obtain ⟨r₂, hr₂, heq2⟩ := List.mem_flatMap.1 heq
    obtain ⟨b, -, hpair⟩ := List.mem_map.1 heq2
    have hv' : (rightItem i).1 = v := (congrArg Prod.fst hpair).symm
    have hr₂' : (rightItem i).2.1 = r₂ := (congrArg (fun p => p.2.1) hpair).symm
    refine ⟨by simpa [List.mem_toFinset, hv'] using hv, ?_⟩
    simpa [hv', hr₂'] using List.mem_range.1 hr₂
  have hsumL_le : ∑ u ∈ (leftVertices g).toFinset, degL g u * (L u).card ≤ C_L.card :=
    sum_deg_mul_cand_le_card (leftVertices g).toFinset (degL g) L L_rep C_L leftItem
      (fun u hu r₁ hr₁ => by
        have hu' : u ∈ leftVertices g := List.mem_toFinset.1 hu
        simp only [L, r₁Star, hu', ↓reduceDIte]
        exact (hminL u hu').choose_spec.2 r₁ hr₁)
      (fun _ _ => rfl) hleftItem_prop
  have hsumR_le : ∑ v ∈ (rightVertices g).toFinset, degR g v * (R v).card ≤ C_R.card :=
    sum_deg_mul_cand_le_card (rightVertices g).toFinset (degR g) R R_rep C_R rightItem
      (fun v hv r₂ hr₂ => by
        have hv' : v ∈ rightVertices g := List.mem_toFinset.1 hv
        simp only [R, r₂Star, hv', ↓reduceDIte]
        exact (hminR v hv').choose_spec.2 r₂ hr₂)
      (fun _ _ => rfl) hrightItem_prop
  have hpart : C_L.card + C_R.card = C.card := by
    have h := Finset.sum_filter_add_sum_filter_not C
      (fun i : Fin (setSystemOf bs gs fallback G g).sets.length => (i : ℕ) < nL) (fun _ => 1)
    simpa [C_L, C_R, not_lt] using h
  have hsum : ∑ i : Fin g.edges.length,
      (((L g.edges[i].src).card + (R g.edges[i].dst).card : ℕ) : ℝ) ≤
        ρ * (2 * g.edges.length) :=
    sum_cand_card_le_of_deg_bounds g L R hsumL_le hsumR_le hpart hcard
  have hmatch : ∀ i : Fin g.edges.length,
      (L g.edges[i].src).card + (R g.edges[i].dst).card ≤ t →
        ∃ a ∈ L g.edges[i].src, ∃ b ∈ R g.edges[i].dst, g.edges[i].constraint a = b := by
    intro i hle
    have hu : g.edges[i].src ∈ leftVertices g :=
      mem_leftVertices.2 ⟨g.edges[i], List.getElem_mem i.isLt, rfl⟩
    have hv : g.edges[i].dst ∈ rightVertices g :=
      mem_rightVertices.2 ⟨g.edges[i], List.getElem_mem i.isLt, rfl⟩
    have hr₁ : r₁Star g.edges[i].src < degL g g.edges[i].src := by
      simp only [r₁Star, hu, ↓reduceDIte]
      exact Finset.mem_range.1 (hminL g.edges[i].src hu).choose_spec.1
    have hr₂ : r₂Star g.edges[i].dst < degR g g.edges[i].dst := by
      simp only [r₂Star, hv, ↓reduceDIte]
      exact Finset.mem_range.1 (hminR g.edges[i].dst hv).choose_spec.1
    refine G.exists_eq_of_covers hsep g.edges[i].constraint _ _ hle fun x hx => ?_
    let r₁ := r₁Star g.edges[i].src
    let r₂ := r₂Star g.edges[i].dst
    have hz : Nat.pair (Nat.pair i.1 x) (Nat.pair r₁ r₂) ∈
        (setSystemOf bs gs fallback G g).ground := by
      refine mem_unweightedGround.2 ⟨i.1, i.isLt, x, hx, r₁, ?_, r₂, ?_, rfl⟩
      · rwa [List.getD_eq_getElem _ _ i.isLt]
      · rwa [List.getD_eq_getElem _ _ i.isLt]
    obtain ⟨j, hjC, hjz⟩ := hC (Nat.pair (Nat.pair i.1 x) (Nat.pair r₁ r₂)) hz
    by_cases hjL : (j : ℕ) < nL
    · left
      have hjCL : j ∈ C_L := Finset.mem_filter.2 ⟨hjC, hjL⟩
      have hjz' : Nat.pair (Nat.pair i.1 x) (Nat.pair r₁ r₂) ∈
          unweightedLeftSet fallback G g (leftItem j).1 (leftItem j).2.1 (leftItem j).2.2 := by
        change Nat.pair (Nat.pair i.1 x) (Nat.pair r₁ r₂) ∈
          (setSystemOf bs gs fallback G g).sets[j] at hjz
        rw [setSystem_getElem_left (i := j) hjL] at hjz
        simpa [leftItem, hjL] using hjz
      obtain ⟨hsrc, hr1eq, hmem⟩ := (mem_unweightedLeftSet i.isLt hx hr₂).1 hjz'
      refine ⟨(leftItem j).2.2,
        Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨hjCL, hsrc.symm, hr1eq.symm⟩, rfl⟩, hmem⟩
    · right
      have hjR : nL ≤ (j : ℕ) := Nat.le_of_not_lt hjL
      have hjCR : j ∈ C_R := Finset.mem_filter.2 ⟨hjC, hjR⟩
      have hjz' : Nat.pair (Nat.pair i.1 x) (Nat.pair r₁ r₂) ∈
          unweightedRightSet fallback G g (rightItem j).1 (rightItem j).2.1 (rightItem j).2.2 := by
        change Nat.pair (Nat.pair i.1 x) (Nat.pair r₁ r₂) ∈
          (setSystemOf bs gs fallback G g).sets[j] at hjz
        rw [setSystem_getElem_right (i := j) hjR (hlen_lt j hjR)] at hjz
        simpa [rightItem, hjR] using hjz
      obtain ⟨hdst, hr2eq, hmem⟩ := (mem_unweightedRightSet i.isLt hx hr₁).1 hjz'
      refine ⟨(rightItem j).2.2,
        Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨hjCR, hdst.symm, hr2eq.symm⟩, rfl⟩, hmem⟩
  exact exists_labelling_of_list_sets g L R ht hm hmatch hsum

theorem setSystemOf_sound [DecidableEq γ] [Nonempty β] [Nonempty γ]
    {bs : List β} {gs : List γ} {fallback : γ} (hbs_all : ∀ a, a ∈ bs) (hgs_all : ∀ b, b ∈ gs)
    {G : PartitionGadget γ} {t : ℕ} (ht : 0 < t) (hsep : G.Separates t)
    {g : Graph (β → γ)} (hm : 0 < g.edges.length) {ρ : ℝ}
    (hcard : ((setSystemOf bs gs fallback G g).optCoverSize : ℝ) ≤ ρ * (2 * g.edges.length)) :
    (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) ≤ 1 - (g.toGraph projectionEval).unsatVal := by
  obtain ⟨C, hC, hCcard⟩ := SetSystem.exists_isCover_optCoverSize
    (setSystemOf_coverable hbs_all hgs_all G g)
  rw [← hCcard] at hcard
  exact setSystemOf_sound_of_isCover ht hsep hm hC hcard

end Combinatorial

/-! ### Polynomial-time certificates -/

section PolyTime

private theorem unaryToNat {α : Type} {enc : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f enc encUnary) : ComputableInPolyTime f enc encNat :=
  (of_tidy ComputableTidilyInPolyTime.unary_to_binary).comp hf

private theorem computableInPolyTime_leftVertices {β γ : Type} (encC : (β → γ) ↪ List Bool) :
    ComputableInPolyTime (leftVertices (β := β) (γ := γ))
      (Graph.encoding encC) (encList encUnary) := by
  have hmap : ComputableInPolyTime (fun g : Graph (β → γ) => g.edges.map Edge.src)
      (Graph.encoding encC) (encList encUnary) :=
    (ComputableInPolyTime.map (Edge.isPolyTime_src id')).comp
      (Graph.isPolyTime_edges id')
  exact eraseDupsByWithInput hmap (decide_eq' (fst _ _).snd' (snd _ _))

private theorem computableInPolyTime_rightVertices {β γ : Type} (encC : (β → γ) ↪ List Bool) :
    ComputableInPolyTime (rightVertices (β := β) (γ := γ))
      (Graph.encoding encC) (encList encUnary) := by
  have hmap : ComputableInPolyTime (fun g : Graph (β → γ) => g.edges.map Edge.dst)
      (Graph.encoding encC) (encList encUnary) :=
    (ComputableInPolyTime.map (Edge.isPolyTime_dst id')).comp
      (Graph.isPolyTime_edges id')
  exact eraseDupsByWithInput hmap (decide_eq' (fst _ _).snd' (snd _ _))

private theorem computableInPolyTime_countEndpoint {β γ : Type}
    (encC : (β → γ) ↪ List Bool) {proj : Edge (β → γ) → ℕ}
    (hproj : ComputableInPolyTime (fun q : (Graph (β → γ) × ℕ) × Edge (β → γ) => proj q.2)
      (encPair (encPair (Graph.encoding encC) encUnary) (Edge.encoding encC)) encUnary) :
    ComputableInPolyTime
      (fun p : Graph (β → γ) × ℕ => p.1.edges.countP fun d => decide (proj d = p.2))
      (encPair (Graph.encoding encC) encUnary) encUnary :=
  countPWithInput (Graph.isPolyTime_edges (fst _ _)) (hproj.decide_eq' ((snd _ _).comp (fst _ _)))

private theorem computableInPolyTime_degL {β γ : Type} (encC : (β → γ) ↪ List Bool) :
    ComputableInPolyTime (fun p : Graph (β → γ) × ℕ => degL p.1 p.2)
      (encPair (Graph.encoding encC) encUnary) encUnary := by
  unfold degL
  exact computableInPolyTime_countEndpoint encC (Edge.isPolyTime_src (snd _ _))

private theorem computableInPolyTime_degR {β γ : Type} (encC : (β → γ) ↪ List Bool) :
    ComputableInPolyTime (fun p : Graph (β → γ) × ℕ => degR p.1 p.2)
      (encPair (Graph.encoding encC) encUnary) encUnary := by
  unfold degR
  exact computableInPolyTime_countEndpoint encC (Edge.isPolyTime_dst (snd _ _))

private theorem computableInPolyTime_weightedGround {β γ : Type} (encC : (β → γ) ↪ List Bool)
    (G : PartitionGadget γ) :
    ComputableInPolyTime (weightedGround (β := β) G) (Graph.encoding encC) (encList encNat) := by
  unfold weightedGround
  refine flatMapWithInput (unary_range' (length_list _ |>.comp (Graph.isPolyTime_edges id'))) ?_
  refine mapWithInput (const (encOut := encList encNat) (List.range G.size)) ?_
  exact binary_pair' (unaryToNat ((snd _ _).comp (fst _ _))) (snd _ _)

private theorem computableInPolyTime_weightedLeftSet {β γ : Type} [Finite β] [Finite γ]
    (encC : (β → γ) ↪ List Bool) (fallback : γ) (G : PartitionGadget γ) (a : β) :
    ComputableInPolyTime (fun p : Graph (β → γ) × ℕ => weightedLeftSet fallback G p.1 p.2 a)
      (encPair (Graph.encoding encC) encUnary) encWeightedSet := by
  unfold weightedLeftSet
  refine computableInPolyTime_weightedSetMk ?_
    (unaryToNat (computableInPolyTime_degL encC))
  refine flatMapWithInput (unary_range' (length_list _ |>.comp
    (Graph.isPolyTime_edges (fst _ _)))) ?_
  have hedge : ComputableInPolyTime
      (fun q : (Graph (β → γ) × ℕ) × ℕ => q.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩)
      (encPair (encPair (Graph.encoding encC) encUnary) encUnary) (Edge.encoding encC) :=
    (listGetD (encA := Edge.encoding encC) ⟨0, 0, fun _ => fallback⟩).comp
      ((Graph.isPolyTime_edges ((fst _ _).comp (fst _ _))).prod (snd _ _))
  have hcond : ComputableInPolyTime
      (fun q : (Graph (β → γ) × ℕ) × ℕ =>
        decide ((q.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩).src = q.1.2))
      (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encBool :=
    (Edge.isPolyTime_src hedge).decide_eq' ((snd _ _).comp (fst _ _))
  have hxs : ComputableInPolyTime
      (fun q : (Graph (β → γ) × ℕ) × ℕ =>
        (List.range G.size).filter fun x =>
          !G.mem x ((q.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩).constraint a))
      (encPair (encPair (Graph.encoding encC) encUnary) encUnary) (encList encNat) :=
    (of_finite (encIn := encC) (encOut := encList encNat)
      (fun c : β → γ => (List.range G.size).filter fun x => !G.mem x (c a))).comp
      (Edge.isPolyTime_constraint hedge)
  have hbranch : ComputableInPolyTime
      (fun q : (Graph (β → γ) × ℕ) × ℕ =>
        ((List.range G.size).filter fun x =>
          !G.mem x ((q.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩).constraint a)).map
            (Nat.pair q.2))
      (encPair (encPair (Graph.encoding encC) encUnary) encUnary) (encList encNat) := by
    refine mapWithInput hxs ?_
    exact binary_pair' (unaryToNat ((snd _ _).comp (fst _ _))) (snd _ _)
  simpa only [decide_eq_true_eq] using ite' hcond hbranch (const [])

private theorem computableInPolyTime_weightedRightSet {β γ : Type}
    (encC : (β → γ) ↪ List Bool) (fallback : γ) (G : PartitionGadget γ) (b : γ) :
    ComputableInPolyTime (fun p : Graph (β → γ) × ℕ => weightedRightSet fallback G p.1 p.2 b)
      (encPair (Graph.encoding encC) encUnary) encWeightedSet := by
  unfold weightedRightSet
  refine computableInPolyTime_weightedSetMk ?_
    (unaryToNat (computableInPolyTime_degR encC))
  refine flatMapWithInput (unary_range' (length_list _ |>.comp
    (Graph.isPolyTime_edges (fst _ _)))) ?_
  have hedge : ComputableInPolyTime
      (fun q : (Graph (β → γ) × ℕ) × ℕ => q.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩)
      (encPair (encPair (Graph.encoding encC) encUnary) encUnary) (Edge.encoding encC) :=
    (listGetD (encA := Edge.encoding encC) ⟨0, 0, fun _ => fallback⟩).comp
      ((Graph.isPolyTime_edges ((fst _ _).comp (fst _ _))).prod (snd _ _))
  have hcond : ComputableInPolyTime
      (fun q : (Graph (β → γ) × ℕ) × ℕ =>
        decide ((q.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩).dst = q.1.2))
      (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encBool :=
    (Edge.isPolyTime_dst hedge).decide_eq' ((snd _ _).comp (fst _ _))
  have hbranch : ComputableInPolyTime
      (fun q : (Graph (β → γ) × ℕ) × ℕ =>
        ((List.range G.size).filter fun x => G.mem x b).map (Nat.pair q.2))
      (encPair (encPair (Graph.encoding encC) encUnary) encUnary) (encList encNat) := by
    refine mapWithInput (const (encOut := encList encNat)
      ((List.range G.size).filter fun x => G.mem x b)) ?_
    exact binary_pair' (unaryToNat ((snd _ _).comp (fst _ _))) (snd _ _)
  simpa only [decide_eq_true_eq] using ite' hcond hbranch (const [])

theorem computableInPolyTime_toWeightedSetCoverOf {β γ : Type} [Finite β] [Finite γ]
    (encC : (β → γ) ↪ List Bool) (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) :
    ComputableInPolyTime (toWeightedSetCoverOf bs gs fallback G)
      (Graph.encoding encC) encWeightedSetCover := by
  have hL : ComputableInPolyTime
      (fun g : Graph (β → γ) =>
        (weightedLeftItems bs g).map fun p => weightedLeftSet fallback G g p.1 p.2)
      (Graph.encoding encC) (encList encWeightedSet) := by
    have heq : (fun g : Graph (β → γ) =>
          (weightedLeftItems bs g).map fun p => weightedLeftSet fallback G g p.1 p.2) =
        fun g => (leftVertices g).flatMap fun u =>
          bs.map fun a => weightedLeftSet fallback G g u a := by
      funext g
      simp [weightedLeftItems, List.map_flatMap, List.map_map, Function.comp_def]
    rw [heq]
    exact flatMapWithInput (computableInPolyTime_leftVertices encC)
      (mapConst bs fun a _ => computableInPolyTime_weightedLeftSet encC fallback G a)
  have hR : ComputableInPolyTime
      (fun g : Graph (β → γ) =>
        (weightedRightItems gs g).map fun p => weightedRightSet fallback G g p.1 p.2)
      (Graph.encoding encC) (encList encWeightedSet) := by
    have heq : (fun g : Graph (β → γ) =>
          (weightedRightItems gs g).map fun p => weightedRightSet fallback G g p.1 p.2) =
        fun g => (rightVertices g).flatMap fun v =>
          gs.map fun b => weightedRightSet fallback G g v b := by
      funext g
      simp [weightedRightItems, List.map_flatMap, List.map_map, Function.comp_def]
    rw [heq]
    exact flatMapWithInput (computableInPolyTime_rightVertices encC)
      (mapConst gs fun b _ => computableInPolyTime_weightedRightSet encC fallback G b)
  have hW : ComputableInPolyTime (weightedSetSystemOf bs gs fallback G)
      (Graph.encoding encC) encWeightedSetSystem :=
    computableInPolyTime_weightedSetSystemMk (computableInPolyTime_weightedGround encC G)
      (listAppend' hL hR)
  have hm : ComputableInPolyTime (fun g : Graph (β → γ) => 2 * g.edges.length)
      (Graph.encoding encC) encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_mul' (const 2).tidy
      (unaryToNat ((length_list _).comp (Graph.isPolyTime_edges id'))).tidy)
  exact hW.prod hm

private theorem computableInPolyTime_unweightedGround {β γ : Type}
    (encC : (β → γ) ↪ List Bool) (fallback : γ) (G : PartitionGadget γ) :
    ComputableInPolyTime (unweightedGround (β := β) fallback G)
      (Graph.encoding encC) (encList encNat) := by
  unfold unweightedGround
  refine flatMapWithInput (unary_range' (length_list _ |>.comp (Graph.isPolyTime_edges id'))) ?_
  refine flatMapWithInput (const (encOut := encList encNat) (List.range G.size)) ?_
  have hedge : ComputableInPolyTime
      (fun q : (Graph (β → γ) × ℕ) × ℕ =>
        q.1.1.edges.getD q.1.2 ⟨0, 0, fun _ => fallback⟩)
      (encPair (encPair (Graph.encoding encC) encUnary) encNat) (Edge.encoding encC) :=
    (listGetD (encA := Edge.encoding encC) ⟨0, 0, fun _ => fallback⟩).comp
      ((Graph.isPolyTime_edges ((fst _ _).comp (fst _ _))).prod ((snd _ _).comp (fst _ _)))
  have hr1List : ComputableInPolyTime
      (fun q : (Graph (β → γ) × ℕ) × ℕ =>
        List.range (degL q.1.1 (q.1.1.edges.getD q.1.2 ⟨0, 0, fun _ => fallback⟩).src))
      (encPair (encPair (Graph.encoding encC) encUnary) encNat) (encList encUnary) :=
    unary_range' ((computableInPolyTime_degL encC).comp
      (((fst _ _).comp (fst _ _)).prod (Edge.isPolyTime_src hedge)))
  refine flatMapWithInput hr1List ?_
  have hedge2 : ComputableInPolyTime
      (fun q : ((Graph (β → γ) × ℕ) × ℕ) × ℕ =>
        q.1.1.1.edges.getD q.1.1.2 ⟨0, 0, fun _ => fallback⟩)
      (encPair (encPair (encPair (Graph.encoding encC) encUnary) encNat) encUnary)
      (Edge.encoding encC) :=
    hedge.comp (fst _ _)
  have hr2List : ComputableInPolyTime
      (fun q : ((Graph (β → γ) × ℕ) × ℕ) × ℕ =>
        List.range (degR q.1.1.1 (q.1.1.1.edges.getD q.1.1.2 ⟨0, 0, fun _ => fallback⟩).dst))
      (encPair (encPair (encPair (Graph.encoding encC) encUnary) encNat) encUnary)
      (encList encUnary) :=
    unary_range' ((computableInPolyTime_degR encC).comp
      (((fst _ _).comp ((fst _ _).comp (fst _ _))).prod (Edge.isPolyTime_dst hedge2)))
  refine mapWithInput hr2List ?_
  have he : ComputableInPolyTime
      (fun q : (((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.2)
      (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encNat) encUnary)
        encUnary) encNat :=
    unaryToNat ((snd _ _).comp ((fst _ _).comp ((fst _ _).comp (fst _ _))))
  have hx : ComputableInPolyTime
      (fun q : (((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.2)
      (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encNat) encUnary)
        encUnary) encNat :=
    (snd _ _).comp ((fst _ _).comp (fst _ _))
  have hr1 : ComputableInPolyTime
      (fun q : (((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.2)
      (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encNat) encUnary)
        encUnary) encNat :=
    unaryToNat ((snd _ _).comp (fst _ _))
  have hr2 : ComputableInPolyTime
      (fun q : (((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ => q.2)
      (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encNat) encUnary)
        encUnary) encNat :=
    unaryToNat (snd _ _)
  exact binary_pair' (binary_pair' he hx) (binary_pair' hr1 hr2)

private theorem computableInPolyTime_unweightedLeftSet {β γ : Type} [Finite β] [Finite γ]
    (encC : (β → γ) ↪ List Bool) (fallback : γ) (G : PartitionGadget γ) (a : β) :
    ComputableInPolyTime
      (fun q : (Graph (β → γ) × ℕ) × ℕ => unweightedLeftSet fallback G q.1.1 q.1.2 q.2 a)
      (encPair (encPair (Graph.encoding encC) encUnary) encUnary) (encList encNat) := by
  unfold unweightedLeftSet
  refine flatMapWithInput (unary_range' (length_list _ |>.comp
    (Graph.isPolyTime_edges ((fst _ _).comp (fst _ _))))) ?_
  have hedge : ComputableInPolyTime
      (fun q : ((Graph (β → γ) × ℕ) × ℕ) × ℕ =>
        q.1.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩)
      (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encUnary)
      (Edge.encoding encC) :=
    (listGetD (encA := Edge.encoding encC) ⟨0, 0, fun _ => fallback⟩).comp
      ((Graph.isPolyTime_edges ((fst _ _).comp ((fst _ _).comp (fst _ _)))).prod (snd _ _))
  have hcond : ComputableInPolyTime
      (fun q : ((Graph (β → γ) × ℕ) × ℕ) × ℕ =>
        decide ((q.1.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩).src = q.1.1.2))
      (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encUnary) encBool :=
    (Edge.isPolyTime_src hedge).decide_eq' ((snd _ _).comp ((fst _ _).comp (fst _ _)))
  have hxs : ComputableInPolyTime
      (fun q : ((Graph (β → γ) × ℕ) × ℕ) × ℕ =>
        (List.range G.size).filter fun x =>
          !G.mem x ((q.1.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩).constraint a))
      (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encUnary)
      (encList encNat) :=
    (of_finite (encIn := encC) (encOut := encList encNat)
      (fun c : β → γ => (List.range G.size).filter fun x => !G.mem x (c a))).comp
      (Edge.isPolyTime_constraint hedge)
  have hbranch : ComputableInPolyTime
      (fun q : ((Graph (β → γ) × ℕ) × ℕ) × ℕ =>
        ((List.range G.size).filter fun x =>
          !G.mem x ((q.1.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩).constraint a)).flatMap
            fun x => (List.range (degR q.1.1.1
              (q.1.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩).dst)).map fun r₂ =>
                Nat.pair (Nat.pair q.2 x) (Nat.pair q.1.2 r₂))
      (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encUnary)
      (encList encNat) := by
    refine flatMapWithInput hxs ?_
    have hedge2 : ComputableInPolyTime
        (fun q : (((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ =>
          q.1.1.1.1.edges.getD q.1.2 ⟨0, 0, fun _ => fallback⟩)
        (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encUnary)
          encNat) (Edge.encoding encC) :=
      hedge.comp (fst _ _)
    have hr2List : ComputableInPolyTime
        (fun q : (((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ =>
          List.range (degR q.1.1.1.1
            (q.1.1.1.1.edges.getD q.1.2 ⟨0, 0, fun _ => fallback⟩).dst))
        (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encUnary)
          encNat) (encList encUnary) :=
      unary_range' ((computableInPolyTime_degR encC).comp
        (((fst _ _).comp ((fst _ _).comp ((fst _ _).comp (fst _ _)))).prod
          (Edge.isPolyTime_dst hedge2)))
    refine mapWithInput hr2List ?_
    have he : ComputableInPolyTime
        (fun q : ((((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.2)
        (encPair (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary)
          encUnary) encNat) encUnary) encNat :=
      unaryToNat ((snd _ _).comp ((fst _ _).comp (fst _ _)))
    have hx : ComputableInPolyTime
        (fun q : ((((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.2)
        (encPair (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary)
          encUnary) encNat) encUnary) encNat :=
      (snd _ _).comp (fst _ _)
    have hr1 : ComputableInPolyTime
        (fun q : ((((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.2)
        (encPair (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary)
          encUnary) encNat) encUnary) encNat :=
      unaryToNat ((snd _ _).comp ((fst _ _).comp ((fst _ _).comp (fst _ _))))
    have hr2 : ComputableInPolyTime
        (fun q : ((((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.2)
        (encPair (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary)
          encUnary) encNat) encUnary) encNat :=
      unaryToNat (snd _ _)
    exact binary_pair' (binary_pair' he hx) (binary_pair' hr1 hr2)
  simpa only [decide_eq_true_eq] using ite' hcond hbranch (const [])

private theorem computableInPolyTime_unweightedRightSet {β γ : Type}
    (encC : (β → γ) ↪ List Bool) (fallback : γ) (G : PartitionGadget γ) (b : γ) :
    ComputableInPolyTime
      (fun q : (Graph (β → γ) × ℕ) × ℕ => unweightedRightSet fallback G q.1.1 q.1.2 q.2 b)
      (encPair (encPair (Graph.encoding encC) encUnary) encUnary) (encList encNat) := by
  unfold unweightedRightSet
  refine flatMapWithInput (unary_range' (length_list _ |>.comp
    (Graph.isPolyTime_edges ((fst _ _).comp (fst _ _))))) ?_
  have hedge : ComputableInPolyTime
      (fun q : ((Graph (β → γ) × ℕ) × ℕ) × ℕ =>
        q.1.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩)
      (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encUnary)
      (Edge.encoding encC) :=
    (listGetD (encA := Edge.encoding encC) ⟨0, 0, fun _ => fallback⟩).comp
      ((Graph.isPolyTime_edges ((fst _ _).comp ((fst _ _).comp (fst _ _)))).prod (snd _ _))
  have hcond : ComputableInPolyTime
      (fun q : ((Graph (β → γ) × ℕ) × ℕ) × ℕ =>
        decide ((q.1.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩).dst = q.1.1.2))
      (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encUnary) encBool :=
    (Edge.isPolyTime_dst hedge).decide_eq' ((snd _ _).comp ((fst _ _).comp (fst _ _)))
  have hbranch : ComputableInPolyTime
      (fun q : ((Graph (β → γ) × ℕ) × ℕ) × ℕ =>
        ((List.range G.size).filter fun x => G.mem x b).flatMap fun x =>
          (List.range (degL q.1.1.1
            (q.1.1.1.edges.getD q.2 ⟨0, 0, fun _ => fallback⟩).src)).map fun r₁ =>
              Nat.pair (Nat.pair q.2 x) (Nat.pair r₁ q.1.2))
      (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encUnary)
      (encList encNat) := by
    refine flatMapWithInput (const (encOut := encList encNat)
      ((List.range G.size).filter fun x => G.mem x b)) ?_
    have hedge2 : ComputableInPolyTime
        (fun q : (((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ =>
          q.1.1.1.1.edges.getD q.1.2 ⟨0, 0, fun _ => fallback⟩)
        (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encUnary)
          encNat) (Edge.encoding encC) :=
      hedge.comp (fst _ _)
    have hr1List : ComputableInPolyTime
        (fun q : (((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ =>
          List.range (degL q.1.1.1.1
            (q.1.1.1.1.edges.getD q.1.2 ⟨0, 0, fun _ => fallback⟩).src))
        (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary) encUnary)
          encNat) (encList encUnary) :=
      unary_range' ((computableInPolyTime_degL encC).comp
        (((fst _ _).comp ((fst _ _).comp ((fst _ _).comp (fst _ _)))).prod
          (Edge.isPolyTime_src hedge2)))
    refine mapWithInput hr1List ?_
    have he : ComputableInPolyTime
        (fun q : ((((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.2)
        (encPair (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary)
          encUnary) encNat) encUnary) encNat :=
      unaryToNat ((snd _ _).comp ((fst _ _).comp (fst _ _)))
    have hx : ComputableInPolyTime
        (fun q : ((((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.2)
        (encPair (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary)
          encUnary) encNat) encUnary) encNat :=
      (snd _ _).comp (fst _ _)
    have hr1 : ComputableInPolyTime
        (fun q : ((((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.2)
        (encPair (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary)
          encUnary) encNat) encUnary) encNat :=
      unaryToNat (snd _ _)
    have hr2 : ComputableInPolyTime
        (fun q : ((((Graph (β → γ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.2)
        (encPair (encPair (encPair (encPair (encPair (Graph.encoding encC) encUnary) encUnary)
          encUnary) encNat) encUnary) encNat :=
      unaryToNat ((snd _ _).comp ((fst _ _).comp ((fst _ _).comp (fst _ _))))
    exact binary_pair' (binary_pair' he hx) (binary_pair' hr1 hr2)
  simpa only [decide_eq_true_eq] using ite' hcond hbranch (const [])

theorem computableInPolyTime_toSetCoverOf {β γ : Type} [Finite β] [Finite γ]
    (encC : (β → γ) ↪ List Bool) (bs : List β) (gs : List γ) (fallback : γ)
    (G : PartitionGadget γ) :
    ComputableInPolyTime (toSetCoverOf bs gs fallback G)
      (Graph.encoding encC) encSetCover := by
  have hL : ComputableInPolyTime
      (fun g : Graph (β → γ) =>
        (unweightedLeftItems bs g).map
          fun (u, r₁, a) => unweightedLeftSet fallback G g u r₁ a)
      (Graph.encoding encC) encNatSetList := by
    have heq : (fun g : Graph (β → γ) =>
          (unweightedLeftItems bs g).map
            fun (u, r₁, a) => unweightedLeftSet fallback G g u r₁ a) =
        fun g => (leftVertices g).flatMap fun u =>
          (List.range (degL g u)).flatMap fun r₁ =>
            bs.map fun a => unweightedLeftSet fallback G g u r₁ a := by
      funext g
      simp [unweightedLeftItems, List.map_flatMap, List.map_map, Function.comp_def]
    rw [heq]
    refine flatMapWithInput (computableInPolyTime_leftVertices encC) ?_
    refine flatMapWithInput (unary_range' (computableInPolyTime_degL encC)) ?_
    exact mapConst bs fun a _ => computableInPolyTime_unweightedLeftSet encC fallback G a
  have hR : ComputableInPolyTime
      (fun g : Graph (β → γ) =>
        (unweightedRightItems gs g).map
          fun (v, r₂, b) => unweightedRightSet fallback G g v r₂ b)
      (Graph.encoding encC) encNatSetList := by
    have heq : (fun g : Graph (β → γ) =>
          (unweightedRightItems gs g).map
            fun (v, r₂, b) => unweightedRightSet fallback G g v r₂ b) =
        fun g => (rightVertices g).flatMap fun v =>
          (List.range (degR g v)).flatMap fun r₂ =>
            gs.map fun b => unweightedRightSet fallback G g v r₂ b := by
      funext g
      simp [unweightedRightItems, List.map_flatMap, List.map_map, Function.comp_def]
    rw [heq]
    refine flatMapWithInput (computableInPolyTime_rightVertices encC) ?_
    refine flatMapWithInput (unary_range' (computableInPolyTime_degR encC)) ?_
    exact mapConst gs fun b _ => computableInPolyTime_unweightedRightSet encC fallback G b
  have hS : ComputableInPolyTime (setSystemOf bs gs fallback G)
      (Graph.encoding encC) encSetSystem :=
    computableInPolyTime_setSystemMk (computableInPolyTime_unweightedGround encC fallback G)
      (listAppend' hL hR)
  have hm : ComputableInPolyTime (fun g : Graph (β → γ) => 2 * g.edges.length)
      (Graph.encoding encC) encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_mul' (const 2).tidy
      (unaryToNat ((length_list _).comp (Graph.isPolyTime_edges id'))).tidy)
  exact hS.prod hm

end PolyTime

end SetCoverReduction

/-! ### Hardness endpoints: Milestone 1 and `c ln n` gap -/

section Hardness

open SetCoverReduction

private theorem edges_length_pos_of_no_gapLabelCover {β γ : Type} [DecidableEq γ] [Nonempty β]
    [Nonempty γ] {s : ℝ} {g : Graph (β → γ)} (hg : g ∈ (GapLabelCover β γ 1 s).no) :
    0 < g.edges.length := by
  rw [GapLabelCover, PromiseProblem.mem_no_gapMax] at hg
  by_contra h
  have hm0 : g.edges.length = 0 := Nat.eq_zero_of_not_pos h
  have hsat : (g.toGraph projectionEval).Satisfiable := by
    refine ⟨fun _ => (Classical.arbitrary β, Classical.arbitrary γ), fun i => ?_⟩
    exact False.elim (Nat.not_lt_zero i.1 (hm0 ▸ i.isLt))
  have hunsat : (g.toGraph projectionEval).unsatVal = 0 :=
    (ConstraintGraph.unsatVal_eq_zero_iff _).2 hsat
  linarith

/-- **Gap-preserving polynomial-time reduction from `GapLabelCover` to `GapWeightedSetCover`**. -/
theorem polyTimeReducible_GapLabelCover_GapWeightedSetCover
    {β γ : Type} [Finite β] [Nonempty β] [Finite γ] [DecidableEq γ] [Nonempty γ]
    (encC : (β → γ) ↪ List Bool) {G : PartitionGadget γ} {t : ℕ} (ht : 0 < t)
    (hsep : G.Separates t) {r s : ℝ} (hr : 1 < r)
    (hs : s < (1 - 2 * r / t) * (4 / (t : ℝ) ^ 2)) :
    PromiseProblem.PolyTimeReducible (Graph.encoding encC) encWeightedSetCover
      (GapLabelCover β γ 1 s) (GapWeightedSetCover r) := by
  classical
  let _ := Fintype.ofFinite β
  let _ := Fintype.ofFinite γ
  let bs : List β := Finset.univ.toList
  let gs : List γ := Finset.univ.toList
  have hbs : ∀ a : β, a ∈ bs := fun a => Finset.mem_toList.2 (Finset.mem_univ a)
  have hgs : ∀ b : γ, b ∈ gs := fun b => Finset.mem_toList.2 (Finset.mem_univ b)
  refine ⟨toWeightedSetCoverOf bs gs (Classical.arbitrary γ) G,
    computableInPolyTime_toWeightedSetCoverOf encC bs gs _ G, fun g hg => ?_, fun g hg => ?_⟩
  · rw [GapLabelCover, PromiseProblem.mem_yes_gapMax] at hg
    rw [GapWeightedSetCover, mem_yes_GapWeightedSetCoverFn]
    exact ⟨weightedSetSystemOf_coverable hbs hgs G g,
      weightedSetSystemOf_complete hbs hgs G g hg⟩
  · have hm : 0 < g.edges.length := edges_length_pos_of_no_gapLabelCover hg
    rw [GapLabelCover, PromiseProblem.mem_no_gapMax] at hg
    rw [GapWeightedSetCover, mem_no_GapWeightedSetCoverFn]
    refine ⟨weightedSetSystemOf_coverable hbs hgs G g, ?_, ?_⟩
    · by_contra hlt
      push Not at hlt
      dsimp only [toWeightedSetCoverOf] at hlt
      push_cast at hlt
      have hsound := weightedSetSystemOf_sound hbs hgs ht hsep hm (ρ := r) hlt.le
      linarith
    · have hk0 : (0 : ℝ) < (2 * g.edges.length : ℕ) := by
        exact_mod_cast (by omega : 0 < 2 * g.edges.length)
      exact lt_mul_of_one_lt_left hk0 hr

/-- **Gap-preserving polynomial-time reduction from `GapLabelCover` to `GapSetCover`**. -/
theorem polyTimeReducible_GapLabelCover_GapSetCover
    {β γ : Type} [Finite β] [Nonempty β] [Finite γ] [DecidableEq γ] [Nonempty γ]
    (encC : (β → γ) ↪ List Bool) {G : PartitionGadget γ} {t : ℕ} (ht : 0 < t)
    (hsep : G.Separates t) {r s : ℝ} (hr : 1 < r)
    (hs : s < (1 - 2 * r / t) * (4 / (t : ℝ) ^ 2)) :
    PromiseProblem.PolyTimeReducible (Graph.encoding encC) encSetCover
      (GapLabelCover β γ 1 s) (GapSetCover r) := by
  classical
  let _ := Fintype.ofFinite β
  let _ := Fintype.ofFinite γ
  let bs : List β := Finset.univ.toList
  let gs : List γ := Finset.univ.toList
  have hbs : ∀ a : β, a ∈ bs := fun a => Finset.mem_toList.2 (Finset.mem_univ a)
  have hgs : ∀ b : γ, b ∈ gs := fun b => Finset.mem_toList.2 (Finset.mem_univ b)
  refine ⟨toSetCoverOf bs gs (Classical.arbitrary γ) G,
    computableInPolyTime_toSetCoverOf encC bs gs _ G, fun g hg => ?_, fun g hg => ?_⟩
  · rw [GapLabelCover, PromiseProblem.mem_yes_gapMax] at hg
    rw [GapSetCover, mem_yes_GapSetCoverFn]
    exact ⟨setSystemOf_coverable hbs hgs G g, setSystemOf_complete hbs hgs G g hg⟩
  · have hm : 0 < g.edges.length := edges_length_pos_of_no_gapLabelCover hg
    rw [GapLabelCover, PromiseProblem.mem_no_gapMax] at hg
    rw [GapSetCover, mem_no_GapSetCoverFn]
    refine ⟨setSystemOf_coverable hbs hgs G g, ?_, ?_⟩
    · by_contra hlt
      push Not at hlt
      dsimp only [toSetCoverOf] at hlt
      push_cast at hlt
      have hsound := setSystemOf_sound hbs hgs ht hsep hm (ρ := r) hlt.le
      linarith
    · have hk0 : (0 : ℝ) < (2 * g.edges.length : ℕ) := by
        exact_mod_cast (by omega : 0 < 2 * g.edges.length)
      exact lt_mul_of_one_lt_left hk0 hr

/-- **Milestone 1 (unweighted Set Cover):** `GapSetCover c` is `NP`-hard for every constant
`c > 1`, unconditionally from `exists_GapLabelCover_npHard` and `boolCubeGadget`. -/
theorem GapSetCover_npHard {c : ℝ} (hc : 1 < c) :
    PromiseProblem.NPHard encSetCover (GapSetCover c) := by
  let t : ℕ := Nat.ceil (4 * c) + 4
  have ht0 : 0 < t := by positivity
  have ht4 : (4 : ℝ) ≤ t := by exact_mod_cast (by omega : 4 ≤ t)
  have hceil : 4 * c ≤ Nat.ceil (4 * c) := Nat.le_ceil _
  have ht_ge : 4 * c ≤ t := by
    have : (Nat.ceil (4 * c) : ℝ) ≤ t := by exact_mod_cast (Nat.le_add_right _ 4)
    linarith
  let δ : ℝ := 1 / (t : ℝ) ^ 2
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by
    have hsq : (1 : ℝ) < (t : ℝ) ^ 2 := by nlinarith
    exact (div_lt_one (by positivity)).2 hsq
  obtain ⟨k, _, hLC⟩ := exists_GapLabelCover_npHard hδ0 hδ1
  let β := Fin k → (Bool × (Fin 6 → Bool)) × (Bool × (Fin 6 → Bool))
  let γ := Fin k → Bool × (Fin 6 → Bool)
  have hfrac : 2 * c / t ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hgap : δ < (1 - 2 * c / t) * (4 / (t : ℝ) ^ 2) := by
    have h1 : 1 / 2 ≤ 1 - 2 * c / t := by linarith
    have h2 : (1 / 2 : ℝ) * (4 / (t : ℝ) ^ 2) ≤ (1 - 2 * c / t) * (4 / (t : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : δ < (1 / 2 : ℝ) * (4 / (t : ℝ) ^ 2) := by
      rw [show (1 / 2 : ℝ) * (4 / (t : ℝ) ^ 2) = 2 / (t : ℝ) ^ 2 by ring]
      dsimp only [δ]
      exact div_lt_div_of_pos_right (by norm_num) (by positivity)
    exact lt_of_lt_of_le h3 h2
  have hred := polyTimeReducible_GapLabelCover_GapSetCover (β := β) (γ := γ)
    (encPi (encPi (encPair encBool (encPi encBool))))
    ht0 (boolCubeGadget_separates γ t) hc hgap
  exact hLC.trans hred

/-- **Milestone 1 (weighted Set Cover):** `GapWeightedSetCover c` is `NP`-hard for every
constant `c > 1`. -/
theorem GapWeightedSetCover_npHard {c : ℝ} (hc : 1 < c) :
    PromiseProblem.NPHard encWeightedSetCover (GapWeightedSetCover c) :=
  (GapSetCover_npHard hc).trans (polyTimeReducible_GapSetCover_GapWeightedSetCover c)

/-- If `P ≠ NP`, `GapSetCover c` does not lie in `PromiseP` for any `c > 1`. -/
theorem GapSetCover_notMem_PromiseP {c : ℝ} (hc : 1 < c) {α : Type} {enc : α ↪ List Bool}
    (hpne : P enc ≠ NP enc) : GapSetCover c ∉ PromiseP encSetCover :=
  (GapSetCover_npHard hc).notMem_PromiseP hpne

/-- If `P ≠ NP`, `GapWeightedSetCover c` does not lie in `PromiseP` for any `c > 1`. -/
theorem GapWeightedSetCover_notMem_PromiseP {c : ℝ} (hc : 1 < c) {α : Type}
    {enc : α ↪ List Bool} (hpne : P enc ≠ NP enc) :
    GapWeightedSetCover c ∉ PromiseP encWeightedSetCover :=
  (GapWeightedSetCover_npHard hc).notMem_PromiseP hpne

/-- No polynomial-time constant-factor approximation algorithm exists for unweighted Set Cover
unless `P = NP`. -/
theorem P_eq_NP_of_setCover_approx_const {A : SetSystem → List ℕ} {c : ℝ} (hc0 : 0 ≤ c)
    (hA : ComputableInPolyTime A encSetSystem (encList encNat))
    (happrox : minSetCover.IsApprox (fun _ => c) A) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  P_eq_NP_of_setCover_approx (GapSetCover_npHard (by linarith : 1 < c + 2)) hc0
    (by linarith : c < c + 2) hA happrox enc

/-- No polynomial-time constant-factor approximation algorithm exists for weighted Set Cover
unless `P = NP`. -/
theorem P_eq_NP_of_weightedSetCover_approx_const {A : WeightedSetSystem → List ℕ} {c : ℝ}
    (hc0 : 0 ≤ c) (hA : ComputableInPolyTime A encWeightedSetSystem (encList encNat))
    (happrox : minWeightedSetCover.IsApprox (fun _ => c) A) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  P_eq_NP_of_weightedSetCover_approx (GapWeightedSetCover_npHard (by linarith : 1 < c + 2)) hc0
    (by linarith : c < c + 2) hA happrox enc

/-- Explicit lower threshold on the separation parameter `t` in terms of `c`, polynomial blowup
degree `p`, edge count `m`, and label cardinality `cardGamma` for the `c * Real.log n` gap
reductions. Asymptotically this threshold grows as `O(p * log m + log log cardGamma)` for fixed
`0 < c < 1 / (4 * log 2)`. -/
@[expose] noncomputable def logGapThreshold (c : ℝ) (p m cardGamma : ℕ) : ℕ :=
  let gap : ℝ := 1 - 4 * Real.log 2 * c
  let δ : ℝ := gap / (8 * c)
  let α : ℝ := δ / 2
  let A₀ : ℕ := Nat.clog 2 (2 * cardGamma + 1)
  let B : ℝ := (p : ℝ) * Real.log m + Real.log ((A₀ + 1 : ℕ) : ℝ)
  let T₀ : ℕ := Nat.ceil (max (α - 1 - Real.log α) 0 / α) + 1
  let T₁ : ℕ := Nat.ceil (1 / (c * Real.log 2)) + 1
  let T₂ : ℕ := Nat.ceil (max B 0 / δ) + 1
  max (max 4 T₀) (max T₁ T₂)

/-- `logGapThreshold` is always at least `4`. -/
theorem four_le_logGapThreshold (c : ℝ) (p m cardGamma : ℕ) :
    4 ≤ logGapThreshold c p m cardGamma :=
  le_trans (le_max_left 4 _) (le_max_left _ _)

private theorem log_add_one_le_mul_of_le {δ : ℝ} (hδ : 0 < δ) {t : ℕ}
    (ht : Nat.ceil (max ((δ / 2) - 1 - Real.log (δ / 2)) 0 / (δ / 2)) + 1 ≤ t) :
    Real.log (t + 1 : ℝ) ≤ δ * t := by
  let α : ℝ := δ / 2
  have hα : 0 < α := by positivity
  let C : ℝ := α - 1 - Real.log α
  have h1 : Real.log (α * ((t : ℝ) + 1)) ≤ α * ((t : ℝ) + 1) - 1 :=
    Real.log_le_sub_one_of_pos (mul_pos hα (by positivity))
  have hmul : Real.log (α * ((t : ℝ) + 1)) = Real.log α + Real.log ((t : ℝ) + 1) :=
    Real.log_mul hα.ne' (by positivity)
  have hbound : Real.log ((t : ℝ) + 1) ≤ α * t + C := by
    dsimp only [C]
    linarith
  have hCt : C ≤ α * t := by
    have hle : max C 0 / α ≤ Nat.ceil (max C 0 / α) := Nat.le_ceil _
    have ht' : (Nat.ceil (max C 0 / α) : ℝ) ≤ t := by
      exact_mod_cast (le_trans (Nat.le_add_right _ 1) ht)
    have hdiv : max C 0 / α ≤ t := hle.trans ht'
    rw [div_le_iff₀ hα] at hdiv
    linarith [le_max_left C 0]
  have hlog : Real.log ((t : ℝ) + 1) ≤ (α + α) * t := by linarith
  have haa : α + α = δ := by dsimp only [α]; ring
  rwa [haa] at hlog

private theorem logGapThreshold_spec {c : ℝ} {p m cardGamma t : ℕ}
    (hc0 : 0 < c) (hc : c < 1 / (4 * Real.log 2))
    (ht : logGapThreshold c p m cardGamma ≤ t) :
    4 ≤ t ∧ 1 < c * (t * Real.log 2) ∧
      c * (((p : ℝ) * Real.log m +
        Real.log ((Nat.clog 2 (2 * cardGamma + 1) + 1 : ℕ) : ℝ)) +
        Real.log ((t : ℝ) + 1) + t * Real.log 2) ≤ (t : ℝ) / 4 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc_lt : 4 * Real.log 2 * c < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hc
    linarith
  let gap : ℝ := 1 - 4 * Real.log 2 * c
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  let δ : ℝ := gap / (8 * c)
  have hδ : 0 < δ := by positivity
  let α : ℝ := δ / 2
  let A₀ : ℕ := Nat.clog 2 (2 * cardGamma + 1)
  let B : ℝ := (p : ℝ) * Real.log m + Real.log ((A₀ + 1 : ℕ) : ℝ)
  let T₀ : ℕ := Nat.ceil (max (α - 1 - Real.log α) 0 / α) + 1
  let T₁ : ℕ := Nat.ceil (1 / (c * Real.log 2)) + 1
  let T₂ : ℕ := Nat.ceil (max B 0 / δ) + 1
  have ht4 : 4 ≤ t := (four_le_logGapThreshold c p m cardGamma).trans ht
  have htT0 : T₀ ≤ t :=
    le_trans (le_max_right 4 _) (le_trans (le_max_left _ _) ht)
  have htT1 : T₁ ≤ t :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) ht)
  have htT2 : T₂ ≤ t :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) ht)
  refine ⟨ht4, ?_, ?_⟩
  · have ht1 : (1 / (c * Real.log 2) : ℝ) < t := by
      have hceil : (1 / (c * Real.log 2) : ℝ) ≤ Nat.ceil (1 / (c * Real.log 2)) := Nat.le_ceil _
      have hlt : (Nat.ceil (1 / (c * Real.log 2)) : ℝ) < t := by
        have hlt_nat : Nat.ceil (1 / (c * Real.log 2)) + 1 ≤ t := htT1
        exact_mod_cast Nat.lt_of_succ_le hlt_nat
      exact lt_of_le_of_lt hceil hlt
    rw [div_lt_iff₀ (mul_pos hc0 hlog2)] at ht1
    linarith
  · have hlogt : Real.log ((t : ℝ) + 1) ≤ δ * t := log_add_one_le_mul_of_le hδ htT0
    have hBt : max B 0 ≤ δ * t := by
      have ht2 : max B 0 / δ ≤ t := by
        have hle : max B 0 / δ ≤ Nat.ceil (max B 0 / δ) := Nat.le_ceil _
        have ht' : (Nat.ceil (max B 0 / δ) : ℝ) ≤ t := by
          exact_mod_cast le_trans (Nat.le_add_right _ 1) htT2
        exact hle.trans ht'
      rw [div_le_iff₀ hδ, mul_comm] at ht2
      exact ht2
    have hB' : B ≤ δ * t := (le_max_left B 0).trans hBt
    have hsum : c * (B + Real.log ((t : ℝ) + 1) + t * Real.log 2) ≤
        c * (2 * δ * t + t * Real.log 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hc0.le
    have hid : c * (2 * δ * t + t * Real.log 2) = (t : ℝ) / 4 := by
      dsimp only [δ, gap]
      field_simp [hc0.ne']
      ring
    linarith

private theorem log_gap_ratio_bounds {c : ℝ} (hc0 : 0 < c) {t m len p A₀ : ℕ}
    (hm : 0 < m) (hlow_len : 2 ^ t ≤ len) (hup_len : len ≤ m ^ p * (2 ^ t * (t * A₀ + 1)))
    (hlog_low : 1 < c * (t * Real.log 2))
    (hlog_high : c * ((p : ℝ) * Real.log m + Real.log ((A₀ + 1 : ℕ) : ℝ) +
      Real.log ((t : ℝ) + 1) + t * Real.log 2) ≤ (t : ℝ) / 4) :
    1 < c * Real.log len ∧ c * Real.log len ≤ (t : ℝ) / 4 := by
  have hlow_real : (2 : ℝ) ^ t ≤ len := by exact_mod_cast hlow_len
  have hlog_ge : t * Real.log 2 ≤ Real.log len := by
    calc (t : ℝ) * Real.log 2
        = Real.log ((2 : ℝ) ^ t) := (Real.log_pow 2 t).symm
      _ ≤ Real.log len := Real.log_le_log (by positivity) hlow_real
  have hratio_gt : 1 < c * Real.log len :=
    lt_of_lt_of_le hlog_low (mul_le_mul_of_nonneg_left hlog_ge hc0.le)
  have hhigh_nat : t * A₀ + 1 ≤ (t + 1) * (A₀ + 1) := by nlinarith
  have hup_nat : len ≤ m ^ p * (2 ^ t * ((t + 1) * (A₀ + 1))) :=
    hup_len.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hhigh_nat))
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hA_pos : (0 : ℝ) < ((A₀ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos A₀
  have hlen_pos : (0 : ℝ) < len := lt_of_lt_of_le (by positivity) hlow_real
  have hup_real : (len : ℝ) ≤
      (m : ℝ) ^ p * ((2 : ℝ) ^ t * (((t : ℝ) + 1) * ((A₀ + 1 : ℕ) : ℝ))) := by
    exact_mod_cast hup_nat
  have hlog_le : Real.log len ≤ ((p : ℝ) * Real.log m + Real.log ((A₀ + 1 : ℕ) : ℝ)) +
      Real.log ((t : ℝ) + 1) + t * Real.log 2 := by
    calc Real.log (len : ℝ)
        ≤ Real.log ((m : ℝ) ^ p * ((2 : ℝ) ^ t * (((t : ℝ) + 1) * ((A₀ + 1 : ℕ) : ℝ)))) :=
            Real.log_le_log hlen_pos hup_real
      _ = Real.log ((m : ℝ) ^ p) +
            Real.log ((2 : ℝ) ^ t * (((t : ℝ) + 1) * ((A₀ + 1 : ℕ) : ℝ))) :=
            Real.log_mul (by positivity) (by positivity)
      _ = (p : ℝ) * Real.log (m : ℝ) +
            (Real.log ((2 : ℝ) ^ t) + Real.log (((t : ℝ) + 1) * ((A₀ + 1 : ℕ) : ℝ))) := by
            rw [Real.log_pow, Real.log_mul (by positivity) (by positivity)]
      _ = (p : ℝ) * Real.log (m : ℝ) +
            (t * Real.log 2 + (Real.log ((t : ℝ) + 1) + Real.log ((A₀ + 1 : ℕ) : ℝ))) := by
            rw [Real.log_pow, Real.log_mul (by positivity) hA_pos.ne']
      _ = ((p : ℝ) * Real.log m + Real.log ((A₀ + 1 : ℕ) : ℝ)) +
            Real.log ((t : ℝ) + 1) + t * Real.log 2 := by ring
  have hratio_le : c * Real.log len ≤ (t : ℝ) / 4 := by
    refine (mul_le_mul_of_nonneg_left hlog_le hc0.le).trans ?_
    simpa [add_assoc] using hlog_high
  exact ⟨hratio_gt, hratio_le⟩

private theorem log_gap_sound_contradiction {c unsat : ℝ} {t len : ℕ}
    (ht0 : 0 < t) (hratio_le : c * Real.log len ≤ (t : ℝ) / 4)
    (hsound : (1 - 2 * (c * Real.log len) / t) * (4 / (t : ℝ) ^ 2) ≤ 1 - unsat)
    (hno : 1 - unsat ≤ 1 / (t : ℝ) ^ 2) : False := by
  have h12 : (1 / 2 : ℝ) ≤ 1 - 2 * (c * Real.log len) / t := by
    have : 2 * (c * Real.log len) / t ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by exact_mod_cast ht0) (by norm_num)]
      linarith
    linarith
  have h2t : 2 * (1 / (t : ℝ) ^ 2) ≤
      (1 - 2 * (c * Real.log len) / t) * (4 / (t : ℝ) ^ 2) := by
    calc 2 * (1 / (t : ℝ) ^ 2)
        = (1 / 2 : ℝ) * (4 / (t : ℝ) ^ 2) := by ring
      _ ≤ (1 - 2 * (c * Real.log len) / t) * (4 / (t : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right h12 (by positivity)
  have h1t : (0 : ℝ) < 1 / (t : ℝ) ^ 2 := by positivity
  linarith

private theorem exists_log_gap_aux {β γ : Type}
    [Fintype γ] [DecidableEq γ]
    {Sys : Type} (groundLen optCost : Sys → ℕ)
    (Coverable : Sys → Prop) (memYes memNo : Sys → ℕ → (Sys → ℝ) → Prop)
    (hYes_iff : ∀ X k r, memYes X k r ↔ Coverable X ∧ optCost X ≤ k)
    (hNo_iff : ∀ X k r, memNo X k r ↔ Coverable X ∧ r X * k ≤ optCost X ∧ (k : ℝ) < r X * k)
    {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / (4 * Real.log 2))
    (g : Graph (β → γ)) (hm : 0 < List.length g.edges) (p : ℕ)
    (sys : PartitionGadget γ → Sys)
    (hcov : ∀ G, Coverable (sys G))
    (hlow : ∀ G, G.size ≤ groundLen (sys G))
    (hup : ∀ G, groundLen (sys G) ≤ List.length g.edges ^ p * G.size)
    (hcomplete : ∀ G, 1 ≤ 1 - ConstraintGraph.unsatVal (g.toGraph projectionEval) →
      optCost (sys G) ≤ 2 * List.length g.edges)
    (hsound : ∀ (G : PartitionGadget γ) {t : ℕ}, 0 < t → G.Separates t →
      ∀ {ρ : ℝ}, (optCost (sys G) : ℝ) ≤ ρ * (2 * List.length g.edges) →
        (1 - 2 * ρ / t) * (4 / (t : ℝ) ^ 2) ≤
          1 - ConstraintGraph.unsatVal (g.toGraph projectionEval))
    {t : ℕ} (ht : logGapThreshold c p g.edges.length (Fintype.card γ) ≤ t) :
    4 ≤ t ∧ ∃ G : PartitionGadget γ, G.Separates t ∧
      G.size = 2 ^ t * (t * Nat.clog 2 (2 * Fintype.card γ + 1) + 1) ∧
      Coverable (sys G) ∧
      (1 ≤ 1 - ConstraintGraph.unsatVal (g.toGraph projectionEval) →
        memYes (sys G) (2 * List.length g.edges) (fun Y => c * Real.log (groundLen Y))) ∧
      (1 - ConstraintGraph.unsatVal (g.toGraph projectionEval) ≤ 1 / (t : ℝ) ^ 2 →
        memNo (sys G) (2 * List.length g.edges) (fun Y => c * Real.log (groundLen Y))) := by
  let A₀ : ℕ := Nat.clog 2 (2 * Fintype.card γ + 1)
  obtain ⟨ht4, hlog_low, hlog_high⟩ := logGapThreshold_spec hc0 hc ht
  obtain ⟨G, hsep, hGsize⟩ := exists_small_partitionGadget γ t
  refine ⟨ht4, G, hsep, hGsize, hcov G, fun hyes => ?_, fun hno => ?_⟩
  · rw [hYes_iff]
    exact ⟨hcov G, hcomplete G hyes⟩
  · rw [hNo_iff]
    have hGt : 2 ^ t ≤ G.size := by
      rw [hGsize]
      exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have hlow_nat : 2 ^ t ≤ groundLen (sys G) := hGt.trans (hlow G)
    have hup_nat : groundLen (sys G) ≤ g.edges.length ^ p * (2 ^ t * (t * A₀ + 1)) := by
      refine (hup G).trans ?_
      rw [hGsize]
    obtain ⟨hratio_gt, hratio_le⟩ := log_gap_ratio_bounds hc0 hm hlow_nat hup_nat hlog_low
      (by simpa only [A₀, add_assoc] using hlog_high)
    have hk0 : (0 : ℝ) < (2 * g.edges.length : ℕ) := by
      exact_mod_cast (by omega : 0 < 2 * g.edges.length)
    refine ⟨hcov G, ?_, lt_mul_of_one_lt_left hk0 hratio_gt⟩
    by_contra hlt
    push Not at hlt
    push_cast at hlt
    have ht0 : 0 < t := by omega
    have hsound' := hsound G ht0 hsep (ρ := c * Real.log (groundLen (sys G))) hlt.le
    exact log_gap_sound_contradiction ht0 hratio_le hsound' hno

/-- **Per-instance logarithmic gap for weighted Set Cover (`c * ln n`)** for any `0 < c < 1 /
(4 * log 2)` and any separation parameter `t ≥ logGapThreshold c 1 g.edges.length |γ|` (using the
`O(t * 2 ^ t * log |γ|)` separating partition gadget `exists_small_partitionGadget`), conditional
on `1 - unsatVal ≤ 1 / t ^ 2`. Upgrading this conditional reduction to hardness requires either
super-constant parallel repetition via a quasi-polynomial reduction (assuming
`NP ⊈ DTIME(n^{O(log log n)})`, not `P ≠ NP` alone) or polynomial-time low-soundness Label Cover
such as Dinur–Steurer (for `P ≠ NP`). -/
theorem exists_weightedSetCover_log_gap {β γ : Type} [Fintype β] [Nonempty β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / (4 * Real.log 2))
    (g : Graph (β → γ)) (hm : 0 < List.length g.edges)
    {t : ℕ} (ht : logGapThreshold c 1 g.edges.length (Fintype.card γ) ≤ t) :
    4 ≤ t ∧ ∃ G : PartitionGadget γ, G.Separates t ∧
      G.size = 2 ^ t * (t * Nat.clog 2 (2 * Fintype.card γ + 1) + 1) ∧
      let bs : List β := Finset.univ.toList
      let gs : List γ := Finset.univ.toList
      let W := weightedSetSystemOf bs gs (Classical.arbitrary γ) G g
      let k := 2 * List.length g.edges
      W.Coverable ∧
      (1 ≤ 1 - ConstraintGraph.unsatVal (g.toGraph projectionEval) →
        (W, k) ∈ (GapWeightedSetCoverFn fun X => c * Real.log (List.length X.ground)).yes) ∧
      (1 - ConstraintGraph.unsatVal (g.toGraph projectionEval) ≤ 1 / (t : ℝ) ^ 2 →
        (W, k) ∈ (GapWeightedSetCoverFn fun X => c * Real.log (List.length X.ground)).no) := by
  let bs : List β := Finset.univ.toList
  let gs : List γ := Finset.univ.toList
  have hbs : ∀ a : β, a ∈ bs := fun a => Finset.mem_toList.2 (Finset.mem_univ a)
  have hgs : ∀ b : γ, b ∈ gs := fun b => Finset.mem_toList.2 (Finset.mem_univ b)
  obtain ⟨ht4, G, hsep, hGsize, hcov, hyes, hno⟩ := exists_log_gap_aux
    (fun X => X.ground.length) WeightedSetSystem.optCoverWeight
    WeightedSetSystem.Coverable (fun X k r => (X, k) ∈ (GapWeightedSetCoverFn r).yes)
    (fun X k r => (X, k) ∈ (GapWeightedSetCoverFn r).no)
    (fun _ _ _ => mem_yes_GapWeightedSetCoverFn) (fun _ _ _ => mem_no_GapWeightedSetCoverFn)
    hc0 hc g hm 1 (fun G => weightedSetSystemOf bs gs (Classical.arbitrary γ) G g)
    (fun G => weightedSetSystemOf_coverable hbs hgs G g)
    (fun G => by rw [weightedSetSystemOf_ground_length]; exact Nat.le_mul_of_pos_left _ hm)
    (fun G => by rw [pow_one, weightedSetSystemOf_ground_length])
    (fun G h => weightedSetSystemOf_complete hbs hgs G g h)
    (fun G _ ht hs _ hwt => weightedSetSystemOf_sound hbs hgs ht hs hm hwt)
    ht
  exact ⟨ht4, G, hsep, hGsize, hcov, hyes, hno⟩

/-- **Per-instance logarithmic gap for unweighted Set Cover (`c * ln n`)** for any `0 < c < 1 /
(4 * log 2)` and any separation parameter `t ≥ logGapThreshold c 3 g.edges.length |γ|`, conditional
on Label Cover soundness `≤ 1 / t ^ 2`. Upgrading this conditional reduction beyond the
constant-round `exists_GapLabelCover_npHard` base requires either super-constant parallel repetition
via a quasi-polynomial reduction (assuming `NP ⊈ DTIME(n^{O(log log n)})`, not `P ≠ NP` alone) or
polynomial-time low-soundness Label Cover such as Dinur–Steurer (for `P ≠ NP`). -/
theorem exists_setCover_log_gap {β γ : Type} [Fintype β] [Nonempty β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / (4 * Real.log 2))
    (g : Graph (β → γ)) (hm : 0 < List.length g.edges)
    {t : ℕ} (ht : logGapThreshold c 3 g.edges.length (Fintype.card γ) ≤ t) :
    4 ≤ t ∧ ∃ G : PartitionGadget γ, G.Separates t ∧
      G.size = 2 ^ t * (t * Nat.clog 2 (2 * Fintype.card γ + 1) + 1) ∧
      let bs : List β := Finset.univ.toList
      let gs : List γ := Finset.univ.toList
      let S := setSystemOf bs gs (Classical.arbitrary γ) G g
      let k := 2 * List.length g.edges
      S.Coverable ∧
      (1 ≤ 1 - ConstraintGraph.unsatVal (g.toGraph projectionEval) →
        (S, k) ∈ (GapSetCoverFn fun X => c * Real.log (List.length X.ground)).yes) ∧
      (1 - ConstraintGraph.unsatVal (g.toGraph projectionEval) ≤ 1 / (t : ℝ) ^ 2 →
        (S, k) ∈ (GapSetCoverFn fun X => c * Real.log (List.length X.ground)).no) := by
  let bs : List β := Finset.univ.toList
  let gs : List γ := Finset.univ.toList
  have hbs : ∀ a : β, a ∈ bs := fun a => Finset.mem_toList.2 (Finset.mem_univ a)
  have hgs : ∀ b : γ, b ∈ gs := fun b => Finset.mem_toList.2 (Finset.mem_univ b)
  obtain ⟨ht4, G, hsep, hGsize, hcov, hyes, hno⟩ := exists_log_gap_aux
    (fun X => X.ground.length) SetSystem.optCoverSize SetSystem.Coverable
    (fun X k r => (X, k) ∈ (GapSetCoverFn r).yes) (fun X k r => (X, k) ∈ (GapSetCoverFn r).no)
    (fun _ _ _ => mem_yes_GapSetCoverFn) (fun _ _ _ => mem_no_GapSetCoverFn)
    hc0 hc g hm 3 (fun G => setSystemOf bs gs (Classical.arbitrary γ) G g)
    (fun G => setSystemOf_coverable hbs hgs G g)
    (fun _ => setSystemOf_ground_length_ge hm)
    (fun _ => setSystemOf_ground_length_le)
    (fun G h => setSystemOf_complete hbs hgs G g h)
    (fun G _ ht hs _ hcard => setSystemOf_sound hbs hgs ht hs hm hcard)
    ht
  exact ⟨ht4, G, hsep, hGsize, hcov, hyes, hno⟩

end Hardness

end Cslib.Complexity
