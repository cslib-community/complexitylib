/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceArraySupport
public import Complexity.Foundations.Data.BitString.PaddingSum
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.GetD

/-!
# The actual incidence-network padding contributes exactly one

The added row `[1,0]` forces its edge to false; its column `[1,1]` contributes one. Prove for
actual constructed networks that arbitrary padding leaves the natural polynomial contraction
unchanged, including dead arrays and zero padding. This is the padding step needed to identify
the native contraction with the incidence polynomial in [OpenAI2026ETH], Lemma D.2, pp.55–56.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.polyContraction_network_padding`: actual padded and
  unpadded contractions agree, before truncation or modular reduction.
* `Cslib.Circuits.Frontier.IncidenceNetwork.sumArrays_eq_unpadded`: padding is removed from the
  existing native streamed output, preserving the same actual machine and resource certificates.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.BitString DescribedNetwork Polynomial

private theorem wordBits_prefix {M q : ℕ} (x : Fin (M + q) → Bool) (ports : List ℕ)
    (hp : ∀ e ∈ ports, e < M) :
    wordBits (List.ofFn x) ports =
      wordBits (List.ofFn fun i : Fin M => x (Fin.castAdd q i)) ports := by
  apply List.map_congr_left
  intro e he
  have hm := hp e he
  rw [List.getD_eq_getElem _ _ (by simpa using (show e < M + q by omega)),
    List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_ofFn, List.getElem_ofFn]
  rfl

private theorem padRow_entry (M q : ℕ) (x : Fin (M + q) → Bool) (e : Fin q) :
    ofCoeffList (incEntry (padRow (M + e)).2
      (wordBits (List.ofFn x) (padRow (M + e)).1)) =
        if x (Fin.natAdd M e) = false then (1 : ℕ[X]) else 0 := by
  have hi : M + e.val < (List.ofFn x).length := by simp
  simp only [padRow, wordBits, List.map_singleton, List.getD_eq_getElem _ _ hi,
    List.getElem_ofFn]
  change ofCoeffList [ExplicitTensorNetwork.entry [1, 0] [x (Fin.natAdd M e)]] = _
  cases hx : x (Fin.natAdd M e) <;> simp [ExplicitTensorNetwork.entry, lsbValue, ofCoeffList_cons]

private theorem padCol_entry (M q : ℕ) (x : Fin (M + q) → Bool) (e : Fin q) :
    ofCoeffList (incEntry (padCol (M + e)).2
      (wordBits (List.ofFn x) (padCol (M + e)).1)) = (1 : ℕ[X]) := by
  have hi : M + e.val < (List.ofFn x).length := by simp
  simp only [padCol, wordBits, List.map_singleton, List.getD_eq_getElem _ _ hi,
    List.getElem_ofFn]
  change ofCoeffList [ExplicitTensorNetwork.entry [1, 1] [x (Fin.natAdd M e)]] = _
  cases hx : x (Fin.natAdd M e) <;> simp [ExplicitTensorNetwork.entry, lsbValue, ofCoeffList_cons]

private theorem padRows_product (M q : ℕ) (x : Fin (M + q) → Bool) :
    List.prod ((List.range q).map fun e => ofCoeffList (incEntry (padRow (M + e)).2
      (wordBits (List.ofFn x) (padRow (M + e)).1))) =
        if ∀ e : Fin q, x (Fin.natAdd M e) = false then (1 : ℕ[X]) else 0 := by
  rw [← List.map_coe_finRange_eq_range, List.map_map, ← Fin.prod_univ_def]
  simp only [Function.comp_def, padRow_entry]
  by_cases hp : ∀ e : Fin q, x (Fin.natAdd M e) = false <;>
    simpa only [hp, ↓reduceIte] using
      (Fintype.prod_boole (M₀ := ℕ[X]) (p := fun e : Fin q => x (Fin.natAdd M e) = false))

private theorem padCols_product (M q : ℕ) (x : Fin (M + q) → Bool) :
    List.prod ((List.range q).map fun e => ofCoeffList (incEntry (padCol (M + e)).2
      (wordBits (List.ofFn x) (padCol (M + e)).1))) = (1 : ℕ[X]) := by
  rw [← List.map_coe_finRange_eq_range, List.map_map, ← Fin.prod_univ_def]
  simp [padCol_entry]

private noncomputable def groupProduct (P ℓ J n : ℕ) (sys : List (List (List ℕ)))
    (d : List ℕ) (word : List Bool) : ℕ[X] :=
  (((List.range J).map (rowVertex P ℓ J sys d) ++
    (List.range J).map (colVertex P J n sys d)).map fun v =>
      ofCoeffList (incEntry v.2 (wordBits word v.1))).prod

private theorem groupProduct_prefix (P ℓ J n q : ℕ) (sys : List (List (List ℕ)))
    (d : List ℕ) (x : Fin (numWires J sys d + q) → Bool) :
    groupProduct P ℓ J n sys d (List.ofFn x) =
      groupProduct P ℓ J n sys d
        (List.ofFn fun i => x (Fin.castAdd q i)) := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro v hv
  apply congrArg ofCoeffList
  apply congrArg (incEntry v.2)
  apply wordBits_prefix
  intro e he
  rcases List.mem_append.mp hv with hv | hv
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hv
    exact lt_of_mem_rowPorts (List.mem_range.mp hg) he
  · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hv
    exact lt_of_mem_colPorts (List.mem_range.mp hh) he

/-- Added forcing rows and constant-one columns leave the actual natural polynomial contraction
unchanged. No graph, padding law or contraction value is supplied by the caller. -/
theorem polyContraction_network_padding (P ℓ J K s n : ℕ)
    (sys : List (List (List ℕ))) (d : List ℕ) :
    (network P ℓ J K s n sys d).2.polyContraction incEntry =
      (network P ℓ J K 0 n sys d).2.polyContraction incEntry := by
  classical
  by_cases hl : live J K d = true
  · let M := numWires J sys d
    let q := s - M
    have hshape : (network P ℓ J K s n sys d).2.numEdges = M + q := by
      simp [network, mainWires, hl, M, q]
    have hmain : (network P ℓ J K 0 n sys d).2.polyContraction incEntry =
        ∑ x : Fin M → Bool, groupProduct P ℓ J n sys d (List.ofFn x) := by
      have hn : (network P ℓ J K 0 n sys d).2 =
          ⟨M, (List.range J).map (rowVertex P ℓ J sys d) ++
            (List.range J).map (colVertex P J n sys d)⟩ := by
        simp [network, rows, cols, mainWires, hl, M]
      rw [hn]
      rfl
    rw [hmain]
    unfold polyContraction contraction
    rw [hshape]
    change (∑ x : Fin (M + q) → Bool, List.prod (List.map
      (fun v : List ℕ × Desc => ofCoeffList (incEntry v.2 (wordBits (List.ofFn x) v.1)))
      (network P ℓ J K s n sys d).2.vertices)) = _
    have hterm (x : Fin (M + q) → Bool) :
        List.prod (List.map
          (fun v : List ℕ × Desc => ofCoeffList (incEntry v.2 (wordBits (List.ofFn x) v.1)))
          (network P ℓ J K s n sys d).2.vertices) =
          if ∀ e : Fin q, x (Fin.natAdd M e) = false then
            groupProduct P ℓ J n sys d (List.ofFn fun i => x (Fin.castAdd q i)) else 0 := by
      simp only [network, rows, cols, hl, ↓reduceIte, mainWires, List.map_append,
        List.prod_append, List.map_map, Function.comp_def]
      rw [padRows_product M q x, padCols_product M q x]
      have hg := groupProduct_prefix P ℓ J n q sys d x
      unfold groupProduct at hg
      simp only [List.map_append, List.prod_append, List.map_map, Function.comp_def] at hg
      unfold groupProduct
      simp only [List.map_append, List.prod_append, List.map_map, Function.comp_def]
      split_ifs <;> simp_all only [mul_one, mul_zero, zero_mul]
      rfl
    rw [Finset.sum_congr rfl (fun x _ => hterm x)]
    exact sum_padding_false M q (fun x : Fin M → Bool =>
      groupProduct P ℓ J n sys d (List.ofFn x))
  · have hd : live J K d = false := Bool.eq_false_iff.mpr hl
    rw [polyContraction_eq_zero_of_dead P ℓ J K s n sys d hd,
      polyContraction_eq_zero_of_dead P ℓ J K 0 n sys d hd]

/-- Actual scalar readback also ignores padding; this changes neither the native program nor
its already certified binary resource bounds. -/
theorem truncCoeffSum_network_padding (P ℓ J K s n : ℕ)
    (sys : List (List (List ℕ))) (d : List ℕ) :
    Cslib.Complexity.CountingSimulation.truncCoeffSum incEntry
        (P, ℓ, network P ℓ J K s n sys d) =
      Cslib.Complexity.CountingSimulation.truncCoeffSum incEntry
        (P, ℓ, network P ℓ J K 0 n sys d) := by
  rw [Cslib.Complexity.CountingSimulation.truncCoeffSum_eq,
    Cslib.Complexity.CountingSimulation.truncCoeffSum_eq, polyContraction_network_padding]

/-- The existing native sum's actual output is the sum of the unpadded array contractions.
This is a proved output identity of the same charged machine, not a faster replacement oracle. -/
theorem sumArrays_eq_unpadded (k : ℕ) (p : ArrayInput) :
    sumArrays k p =
      (∑ i ∈ Finset.range (degreeCount k p),
        Cslib.Complexity.CountingSimulation.truncCoeffSum incEntry
          (p.1 + 1, p.1 + 1, network (p.1 + 1) (p.1 + 1) (Nat.ceilQuarter p.1)
            (degreeCap k p) 0 p.1 p.2 (arrayAt (degreeCap k p) (Nat.ceilQuarter p.1) i))) %
        2 ^ (p.1 + 1) := by
  rw [sumArrays_eq]
  apply congrArg (fun z : ℕ => z % 2 ^ (p.1 + 1))
  apply Finset.sum_congr rfl
  intro i _
  exact truncCoeffSum_network_padding (p.1 + 1) (p.1 + 1) (Nat.ceilQuarter p.1)
    (degreeCap k p) (sizeParam p.1) p.1 p.2
    (arrayAt (degreeCap k p) (Nat.ceilQuarter p.1) i)

end Cslib.Circuits.Frontier.IncidenceNetwork
