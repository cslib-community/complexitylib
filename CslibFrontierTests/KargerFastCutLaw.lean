/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.Karger.FastCut
public import CslibFrontierTests.KargerContraction

/-!
# Recursive contraction laws on connected and zero-weight graphs

The connected triangle instantiates the success, cut-support and independent amplification
contracts. A two-vertex zero-weight graph still has an exact answer law, without the positive
minimum-cut hypothesis required by the quantitative success theorem.
-/

@[expose] public section

namespace ComplexityTests.KargerFastCutLaw

open scoped ENNReal
open Cslib Cslib.WeightedCut Cslib.Algorithms.Lean.Karger
open ComplexityTests.KargerContraction

example : fastCutLaw 3 ⟨3, triangle⟩ = answerLaw ⟨3, triangle⟩ :=
  fastCutLaw_leaf (by decide) _

example {v : ℕ} (hv : v ∈ (fastCutLaw 3 ⟨3, triangle⟩).support) :
    ∃ C : Finset (Fin 3), IsNonTrivialCut C ∧ v = cutWeight triangle C :=
  exists_cut_of_mem_support_fastCutLaw (by decide) (isContractionOf_id isMultigraph_triangle) hv

example : (1 : ℝ≥0∞) / 16 ≤
    (fastCutLaw 3 ⟨3, triangle⟩).toOuterMeasure {v | v = minCut triangle} := by
  simpa only [show Nat.log 2 3 = 1 by decide, Nat.reduceAdd, Nat.cast_ofNat] using
    fastCutLaw_root_hit_prob_ge (by decide) isMultigraph_triangle minCut_triangle

example : (fastCutHighProbLaw 3 ⟨3, triangle⟩).toOuterMeasure {v | v ≠ minCut triangle} ≤
    (1 : ℝ≥0∞) / 6 :=
  fastCutHighProbLaw_failure_le (by decide) isMultigraph_triangle minCut_triangle

/-- A connected input that really crosses the recursion cutoff. -/
def cliqueSeven : Fin 7 → Fin 7 → ℕ := fun i j => if i = j then 0 else 1

theorem isMultigraph_cliqueSeven : IsMultigraph cliqueSeven := ⟨by decide, by decide⟩

theorem minCut_cliqueSeven_pos : 0 < minCut cliqueSeven := by
  refine (minCut_pos_iff (by simp) _).mpr fun C hC => ?_
  obtain ⟨u, hu⟩ := hC.1
  obtain ⟨v, hv⟩ := (isNonTrivialCut_compl hC).1
  have huv : u ≠ v := fun h => (Finset.mem_sdiff.mp hv).2 (h ▸ hu)
  have hpos : 0 < cliqueSeven u v := by simp [cliqueSeven, huv]
  have h₁ : cliqueSeven u v ≤ ∑ j ∈ Finset.univ \ C, cliqueSeven u j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv
  have h₂ : (∑ j ∈ Finset.univ \ C, cliqueSeven u j) ≤ cutWeight cliqueSeven C := by
    unfold cutWeight
    exact Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.univ \ C, cliqueSeven i j)
      (fun _ _ => Nat.zero_le _) hu
  exact hpos.trans_le (h₁.trans h₂)

example : (1 : ℝ≥0∞) / 17 ≤
    (fastCutLaw 7 ⟨7, cliqueSeven⟩).toOuterMeasure {v | v = minCut cliqueSeven} := by
  simpa only [show Nat.log 2 7 = 2 by decide, Nat.reduceAdd, Nat.cast_ofNat] using
    fastCutLaw_root_hit_prob_ge (by decide) isMultigraph_cliqueSeven minCut_cliqueSeven_pos

/-- Zero-weight graphs are meaningful inputs, even though they do not satisfy connectedness. -/
def zeroTwo : Fin 2 → Fin 2 → ℕ := fun _ _ => 0

example : IsMultigraph zeroTwo := ⟨by decide, by decide⟩

example : fastCutLaw 2 ⟨2, zeroTwo⟩ = PMF.pure 0 := by
  rw [fastCutLaw_leaf (by decide), answerLaw_eq]
  change ((PMF.pure ((), (⟨2, zeroTwo⟩ : Graph))).map Prod.snd).map
    (fun G => totalDoubledWeight G.weight / 2) = _
  rw [PMF.pure_map, PMF.pure_map]
  rfl

/-- At the first recursive size both branch laws really occur, even if they return equal values.
This checks the exact independent-branch equation, rather than only a success inequality. -/
example (G : Graph) :
    fastCutLaw 7 G =
      let branch := (contractLaw (G, 6)).bind fun child => fastCutLaw 6 child
      branch.bind fun a => branch.map (min a) := by
  simpa only [show Cslib.Algorithms.WordRAM.Karger.fastCutThreshold 7 = 6 by decide] using
    fastCutLaw_node (by decide : 7 ≤ 7) G

end ComplexityTests.KargerFastCutLaw
