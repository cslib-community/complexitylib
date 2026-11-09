/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Encoded.Verifier
public import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.UniformNat
import CslibFrontier.Foundations.Data.Nat.Log

/-!
# Soundness of the encoded edge verifier

Uniform bits select each actual edge with the same probability; padding accepts. Rounding the
edge count up to a power of two loses at most a factor of two in the rejection probability.

## Main results

* `Cslib.PCP.Encoded.Graph.rejectProb_edgeVerifier`: the exact rejection mass.
* `Cslib.PCP.Encoded.Graph.unsatVal_div_two_le_rejectProb`: every proof is rejected with
  probability at least half the graph's gap.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 11.
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Cslib.Complexity Cslib.Probability

variable {C α : Type}

private def indexVerdict (g : Graph C) (eval : C → α → α → Bool) (labels : ℕ → α)
    (index : ℕ) : Bool :=
  g.edges[index]?.elim true (fun edge => eval edge.constraint (labels edge.src) (labels edge.dst))

private theorem indexVerdict_min (g : Graph C) (eval : C → α → α → Bool) (labels : ℕ → α)
    (index : ℕ) :
    indexVerdict g eval labels (min g.edges.length index) = indexVerdict g eval labels index := by
  by_cases hi : index < g.edges.length
  · rw [Nat.min_eq_right hi.le]
  · simp [indexVerdict, Nat.min_eq_left (Nat.le_of_not_gt hi),
      List.getElem?_eq_none (Nat.le_of_not_gt hi)]

private theorem card_reject_indexVerdict (g : Graph C) (eval : C → α → α → Bool)
    (labels : ℕ → α) {bound : ℕ} (hbound : g.edges.length ≤ bound) :
    (Finset.univ.filter fun i : Fin bound => indexVerdict g eval labels i.val = false).card =
      ((g.toGraph eval).unsatEdges labels).card := by
  classical
  symm
  apply Finset.card_bij (fun i _ => Fin.castLE hbound i)
  · intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change indexVerdict g eval labels i.val = false
    simpa only [ConstraintGraph.mem_unsatEdges, ConstraintGraph.Satisfies, toGraph,
      List.get_eq_getElem, indexVerdict,
      List.getElem?_eq_getElem i.isLt, Option.elim_some, Bool.not_eq_true] using hi
  · intro i hi j hj hij
    exact Fin.ext (congrArg (fun index : Fin bound => index.val) hij)
  · intro i hi
    have hi' : indexVerdict g eval labels i.val = false := (Finset.mem_filter.mp hi).2
    have hlt : i.val < g.edges.length := by
      by_contra h
      simp [indexVerdict, List.getElem?_eq_none (Nat.le_of_not_gt h)] at hi'
    refine ⟨⟨i.val, hlt⟩, ?_, rfl⟩
    simpa only [ConstraintGraph.mem_unsatEdges, ConstraintGraph.Satisfies, toGraph,
      List.get_eq_getElem, indexVerdict, List.getElem?_eq_getElem hlt, Option.elim_some,
      Bool.not_eq_true] using hi'

/-- Each violated edge contributes one rejecting random word; all padding words accept. -/
theorem rejectProb_edgeVerifier (width : ℕ) (decode : (Fin width → Bool) → α)
    (eval : C → α → α → Bool) (g : Graph C) (proof : List Bool) :
    ((BitString.uniformList (Nat.clog 2 g.edges.length)).map
      (fun random => (edgeVerifier width decode eval).accepts g proof random)) false =
      (↑((g.toGraph eval).unsatEdges (proofLabels width decode proof)).card : ENNReal) /
        2 ^ Nat.clog 2 g.edges.length := by
  let labels := proofLabels width decode proof
  have hmap : (BitString.uniformList (Nat.clog 2 g.edges.length)).map
      (fun random => (edgeVerifier width decode eval).accepts g proof random) =
      (PMF.uniformOfFintype (Fin (2 ^ Nat.clog 2 g.edges.length))).map
        (fun i => indexVerdict g eval labels i.val) := by
    calc
      _ = ((BitString.uniformList (Nat.clog 2 g.edges.length)).map
            (BitString.boundedBinaryValue g.edges.length)).map (indexVerdict g eval labels) := by
        rw [PMF.map_comp]
        congr 1
        funext random
        exact edgeVerifier_accepts width decode eval g proof random
      _ = _ := by
        rw [BitString.uniformList_boundedBinaryValue, PMF.map_comp]
        congr 1
        funext i
        exact indexVerdict_min g eval labels i.val
  rw [hmap]
  simp [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply, ← Finset.sum_filter,
    card_reject_indexVerdict g eval labels (Nat.le_pow_clog Nat.one_lt_two _), div_eq_mul_inv,
    labels]

/-- Rounding the edge sampling range to a power of two loses at most half the rejection rate. -/
theorem unsatFrac_div_two_le_rejectProb (width : ℕ) (decode : (Fin width → Bool) → α)
    (eval : C → α → α → Bool) (g : Graph C) (proof : List Bool) :
    (g.toGraph eval).unsatFrac (proofLabels width decode proof) / 2 ≤
      (((BitString.uniformList (Nat.clog 2 g.edges.length)).map
        (fun random => (edgeVerifier width decode eval).accepts g proof random)) false).toReal := by
  rcases g.edges.length.eq_zero_or_pos with hzero | hpos
  · simp only [ConstraintGraph.unsatFrac, Fintype.card_fin, hzero, Nat.cast_zero, div_zero,
      zero_div]
    exact ENNReal.toReal_nonneg
  · rw [rejectProb_edgeVerifier, ENNReal.toReal_div]
    simp only [ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      ConstraintGraph.unsatFrac, Fintype.card_fin, div_div]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    have h := Nat.pow_clog_le_mul Nat.one_lt_two hpos.ne'
    exact_mod_cast (by simpa only [Nat.mul_comm] using h)

/-- The graph's unsatisfiability value bounds rejection for every proof word. -/
theorem unsatVal_div_two_le_rejectProb (width : ℕ) (decode : (Fin width → Bool) → α)
    (eval : C → α → α → Bool) (g : Graph C) (proof : List Bool) :
    (g.toGraph eval).unsatVal / 2 ≤
      (((BitString.uniformList (Nat.clog 2 g.edges.length)).map
        (fun random => (edgeVerifier width decode eval).accepts g proof random)) false).toReal :=
  (div_le_div_of_nonneg_right ((g.toGraph eval).unsatVal_le _) (by norm_num)).trans
    (unsatFrac_div_two_le_rejectProb width decode eval g proof)

/-- A positive graph gap makes every proof fail with a fixed positive probability. -/
theorem acceptProb_edgeVerifier_le (width : ℕ) (decode : (Fin width → Bool) → α)
    (eval : C → α → α → Bool) (g : Graph C) (proof : List Bool) :
    (((BitString.uniformList (Nat.clog 2 g.edges.length)).map
      (fun random => (edgeVerifier width decode eval).accepts g proof random)) true).toReal ≤
        1 - (g.toGraph eval).unsatVal / 2 := by
  have h := unsatVal_div_two_le_rejectProb width decode eval g proof
  have hsum := PMF.toReal_true_add_toReal_false
    ((BitString.uniformList (Nat.clog 2 g.edges.length)).map
      (fun random => (edgeVerifier width decode eval).accepts g proof random))
  linarith

end Cslib.PCP.Encoded.Graph
