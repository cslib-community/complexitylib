/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.NativeChild
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.NativeRecovery
import Mathlib.Data.List.GetD

/-!
# Correctness of one native active call

An active call of the native contraction recursion of [OpenAI2026ETH] (§D.4.4–§D.4.7,
pp. 60–64) on a rows-first network of descriptors stores, for each node index `k` of positive
multiplicity and each interpolation point `i`, a value in `A_{p_t}`, and recovers its own value
with native tapered recovery (`NativeRecovery.recover`). This file proves the call correct from
the correctness of its stored values (`NativeCall.val_recover_eq_contraction`): if each stored value
is, in `A_{p_t}`, the sum over the exponent tuples of the products over the groups of the
contractions of the native children (`NativeChild.nativeChild`), then the recovered value is the
contraction of the network in `A_p`.

**The proof** is carried over `O = ℤ_(2)[U] / (f)` with the canonical lifts of the entries
(`DescribedNetwork.toNetwork`, `GaloisRingArith.liftO`), as in §D.4.1 (p. 58). The values at the
nodes are the lifts of the stored lists, so

* modulo `2 ^ {p_t}` they are the right side of (D.16) for the children of `callSplitting`: the
  native children have these contractions (`NativeChild.contraction_nativeChild`), and the sum over
  the exponent lists is the sum over the mode budget (`BudgetTuples.sum_filter_weight_lt_eq`);
* so interpolation and Lemma D.5 recover the contraction modulo `2 ^ p`
  (`TensorNetwork.exists_recoverFromValues_eq_add_of_children`);
* and the lifts reduce in `A_{p + Δ}` to exactly the stored lists, so native recovery computes the
  reduction of the contraction (`NativeRecovery.val_recover_of_eq_add`), with no condition on
  `p_t` beyond Lemma D.5's.

The call's precision `p_t` of the node of valuation `i` is `nodePrecision p h a M i`, and the
shift `Δ` only needs `(a + 1) ∑_t q_t ≤ Δ`.

## Main results

* `Cslib.Circuits.Frontier.NativeCall.val_recover_eq_contraction`: one native active call is
  correct when its stored values are.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.4–§D.4.7, pp. 60–64.
-/

public section

namespace Cslib.Circuits.Frontier.NativeCall

open Finset GaloisRingArith NativeChild NativeRecovery
open ContractionSchedule (nodePrecision)

/-- The node index of a node: `t + 2 ^ a`. -/
theorem toNat_node_add (a k : ℕ) : (node a k + 2 ^ a).toNat = k := by
  rw [node, sub_add_cancel, Int.toNat_natCast]

/-- A product over a range as a list is a product over `Fin`. -/
theorem prod_map_range {M : Type*} [CommMonoid M] (F : ℕ → M) (n : ℕ) :
    ((List.range n).map F).prod = ∏ g : Fin n, F g := by
  rw [← List.map_coe_finRange_eq_range, List.map_map, ← List.ofFn_eq_map, List.prod_ofFn]
  rfl

variable {T : Type} {fl : List ℕ}
  (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))
  {D : DescribedNetwork (VertexDesc T)} {r : ℕ} (hD : D.IsRowsFirstBipartite r)
  (ev : T → List Bool → List ℕ)

include hD in
/-- **One native active call is correct when its stored values are** ([OpenAI2026ETH],
§D.4.4–§D.4.7). Let `D` be a rows-first network of descriptors with `M` edges, and let
`(a, u, h)` meet the hypotheses of Lemma D.5 (`1 ≤ u ≤ M`, `u ≤ a`, `3 M ≤ h u ≤ 3 M + u`), with
`64 ^ a ≤ M` and `(a + 1) ∑_t q_t ≤ Δ`. Let the interpolation values `ζl` have lifts with unit
differences, and more than `M (2 L - 1)` of them. Suppose that at every node index `k` of positive
multiplicity, with the node `t = k - 2 ^ a` of valuation `i` and precision `p_t`, each stored value
`W[k][i']` is, in `A_{p_t}`, the sum over the exponent lists of the packet-major modes of the
products over the `64` groups of the contractions in `A_{p_t}` of the native children. Then native
recovery returns the contraction of `D` in `A_p`. -/
theorem val_recover_eq_contraction {a u h p Δ : ℕ} (hu : 1 ≤ u) (huM : u ≤ D.numEdges)
    (hua : u ≤ a) (hh : 3 * D.numEdges ≤ h * u) (hh' : h * u ≤ 3 * D.numEdges + u)
    (hK : 64 ^ a ≤ D.numEdges)
    (hΔ : (a + 1) * ∑ t ∈ recoveryNodes a, taperMult u h t ≤ Δ) (ζl : List (List ℕ))
    (hζ : Pairwise fun i j : Fin ζl.length =>
      IsUnit (liftO hirr (ζl.getD i []) - liftO hirr (ζl.getD j [])))
    (hn : D.numEdges * (2 * 2 ^ a - 1) < ζl.length) (W : List (List (List ℕ)))
    (hW : ∀ k < 2 ^ (a + 1), k ≠ 2 ^ a → 0 < mult a u h k → ∀ i < ζl.length,
      val (nodePrecision p h a D.numEdges (padicValInt 2 (node a k))) fl
          ((W.getD k []).getD i []) =
        ((BudgetTuples.budgetTuples
            (modeWeights (nativeParentPacking r a D).2.1 (2 ^ (padicValInt 2 (node a k) + 1))
              (nodePrecision p h a D.numEdges (padicValInt 2 (node a k))))
            (nodePrecision p h a D.numEdges (padicValInt 2 (node a k)))).map fun β =>
          ((List.range 64).map fun g =>
            (nativeChild fl a (padicValInt 2 (node a k))
                (nodePrecision p h a D.numEdges (padicValInt 2 (node a k))) (node a k)
                (ζl.getD i []) r D (nativeParentPacking r a D) β g).contraction
              fun d bs => val (nodePrecision p h a D.numEdges (padicValInt 2 (node a k))) fl
                (d.entry ev bs)).prod).sum) :
    val p fl (recover p Δ fl a u h ζl W) =
      D.contraction fun d bs => val p fl (d.entry ev bs) := by
  have hB := AdjoinRoot.algebraMap_mem_integer_padicValuation (monic_monicOf fl) hirr
  have hcard : Fintype.card (Fin D.numEdges) = D.numEdges := Fintype.card_fin _
  have hpk1 : (nativeParentPacking r a D).2.1 = (parentPacking hD a).numPackets := by
    rw [nativeParentPacking_eq hD hK]
  -- The points and the values over `O`: the lifts of the native lists.
  let ζ : Fin ζl.length → RingO hirr := fun i => liftO hirr (ζl.getD i [])
  let v : ℤ → Fin ζl.length → RingO hirr := fun t i =>
    liftO hirr ((W.getD (t + 2 ^ a).toNat []).getD i [])
  -- Modulo `2 ^ {p_t}` the values are the right side of (D.16).
  have hv : ∀ t (ht : t ∈ recoveryNodes a) (hq : 0 < taperMult u h t) (k : Fin ζl.length),
      Ideal.Quotient.mk (nodeIdeal (RingO hirr) (Fintype.card (Fin D.numEdges)) a h p t) (v t k) =
        ∑ β ∈ TensorNetwork.modeBudget (fun Z : Fin (parentPacking hD a).numPackets ×
            Fin (2 ^ (padicValInt 2 t + 1)) ×
            Fin (nodePrecision p h a (Fintype.card (Fin D.numEdges)) (padicValInt 2 t)) =>
              (Z.2.2 : ℕ) + 1)
            (nodePrecision p h a (Fintype.card (Fin D.numEdges)) (padicValInt 2 t)),
          ∏ g, ((parentSplitting hirr hD ev a p u h hua ht hq (ζl.getD k [])).child β
            g).contraction := by
    intro t ht hq k
    obtain ⟨kk, hkk, hkt⟩ : ∃ kk, (kk < 2 ^ (a + 1) ∧ kk ≠ 2 ^ a) ∧ node a kk = t := by
      rw [recoveryNodes_eq_image, mem_image] at ht
      obtain ⟨kk, hk, e⟩ := ht
      exact ⟨kk, by simpa using hk, e⟩
    subst hkt
    have hmult : 0 < mult a u h kk := by rw [mult_eq u h hkk.1]; exact hq
    have hWk := hW kk hkk.1 hkk.2 hmult k k.2
    rw [← hcard] at hWk
    simp only [v, toNat_node_add]
    rw [mk_liftO hirr, hWk, map_list_sum, List.map_map, TensorNetwork.modeBudget,
      BudgetTuples.sum_filter_weight_lt_eq (nodup_modeList _ _ _) mem_modeList
        (fun Z => Nat.succ_pos _), map_modeList_weight, hpk1]
    refine congrArg List.sum (List.map_congr_left fun β _ => ?_)
    simp only [Function.comp_apply]
    rw [map_list_prod, List.map_map, prod_map_range]
    refine Fintype.prod_congr _ _ fun g => ?_
    simp only [Function.comp_apply]
    rw [DescribedNetwork.map_contraction]
    exact contraction_nativeChild hirr hD ev hK hua ht hq (ζl.getD k []) β g
  obtain ⟨b, hb, hx⟩ := TensorNetwork.exists_recoverFromValues_eq_add_of_children (RingO hirr) hB
    (parentNetwork hirr hD ev) (parentSide r) (parentSide_src hD) (parentSide_tgt hD)
    (parentPacking hD a) (p := p) hu (by rwa [hcard]) hua (by rwa [hcard]) (by rwa [hcard]) ζ hζ
    (by rwa [hcard]) v hv
  -- Native recovery computes the reduction of the recovered value.
  have hpt : ∀ t ∈ recoveryNodes a, 0 < taperMult u h t →
      p + 6 * h * 2 ^ (a - padicValInt 2 t) + taperMult u h t * (a + 1) ≤
        nodePrecision p h a D.numEdges (padicValInt 2 t) := by
    intro t _ _
    have h1 : h * (u - padicValInt 2 t) ≤ 8 * D.numEdges :=
      (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (by omega)
    have e1 : 6 * h * 2 ^ (a - padicValInt 2 t) ≤ 8 * h * 2 ^ (a - padicValInt 2 t) :=
      Nat.mul_le_mul_right _ (by omega)
    have e2 : h * (u - padicValInt 2 t) * (a + 1) ≤ 8 * D.numEdges * (a + 1) :=
      Nat.mul_le_mul_right _ h1
    simp only [nodePrecision, taperMult]
    omega
  have hrec := val_recover_of_eq_add hirr (RingO hirr) hB
    (AdjoinRoot.reduction (monic_monicOf fl) hirr (p + Δ)) hΔ
    (fun t => nodePrecision p h a D.numEdges (padicValInt 2 t)) hpt ζ hζ ζl rfl
    (fun i => (reduction_liftO hirr _ _).symm) v W
    (fun k _ _ _ i => ⟨0, by simp only [v, toNat_node_add, reduction_liftO, mul_zero, add_zero]⟩)
    (parentNetwork hirr hD ev).contraction hb hx
  rw [hrec, ← DescribedNetwork.reduction_contraction_toNetwork hD hirr
    (fun d bs => d.entry ev bs) p]
  exact RingHom.congr_fun (AdjoinRoot.castHom_comp_reduction (monic_monicOf fl) hirr
    (Nat.le_add_right p Δ)) _

end Cslib.Circuits.Frontier.NativeCall
