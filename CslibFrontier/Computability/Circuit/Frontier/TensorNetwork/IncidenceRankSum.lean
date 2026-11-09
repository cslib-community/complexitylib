/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceWireRanks
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidencePadding
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceColumnWeights
import all CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.TruncatedRing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.List.GetD

/-!
# Exact finite-sum reconstruction of the native incidence contractions

Remove unused binary ranks from the actual contraction and reindex the surviving assignments by
fitting combination-rank tuples. The proof derives each rejected term's zero row and uses the
physical wire/rank bijection. It includes cap-dead arrays, impossible capacities and empty wire
spaces. The resulting sum is an identity of the actual polynomial and native scalar output;
it is not an alternative exhaustive implementation or a supplied correctness contract.

The actual scalar output is also recovered from the integer grouped incidence-monomial sum.
Its identification with the original finite per-test `systemIncidencePolynomial`, and thus the
original assignment count, remains separate; this file does not claim that missing endpoint.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.CombinationRanks`: fitting local subset ranks.
* `Cslib.Circuits.Frontier.IncidenceNetwork.rankPolynomial`: the finite sum of actual entry
  products at their uniquely reconstructed wire assignments.
* `Cslib.Circuits.Frontier.IncidenceNetwork.rankIncidencePolynomial`: integer group coefficient
  products with declared-variable weights, summed over fitting ranks at the actual cap.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.polyContraction_eq_rankPolynomial`: exact removal of
  unused ranks and finite-sum reindexing, including actual padding.
* `Cslib.Circuits.Frontier.IncidenceNetwork.sumArrays_eq_rankPolynomials`: the native streamed
  output is the coefficient sum of those reconstructed polynomials, modulo its actual modulus.
* `Cslib.Circuits.Frontier.IncidenceNetwork.sumArrays_eq_rankIncidenceResidue`: exact native
  scalar recovery from the complete grouped incidence-monomial sum, with no supplied congruence.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF pp.55–56.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.BitString DescribedNetwork Polynomial
open Cslib.Complexity.CountingSimulation

/-- One valid subset rank for every actual group pair. Impossible capacities give an empty type. -/
abbrev CombinationRanks (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) :=
  (b : Fin (J * J)) →
    Fin ((pairInc J sys (b / J) (b % J)).length.choose (d.getD b 0))

private abbrev WideRanks (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) :=
  (b : Fin (J * J)) → Fin (2 ^ blockWidth J sys d b)

private theorem capacity_le (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (b : Fin (J * J)) :
    (pairInc J sys (b / J) (b % J)).length.choose (d.getD b 0) ≤
      2 ^ blockWidth J sys d b := by
  rw [blockWidth, width, Nat.div_add_mod']
  exact Nat.le_pow_clog Nat.one_lt_two _

private def widen (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (q : CombinationRanks J sys d) : WideRanks J sys d :=
  fun b => Fin.castLE (capacity_le J sys d b) (q b)

private noncomputable def assignmentProduct (P ℓ J K n : ℕ)
    (sys : List (List (List ℕ))) (d : List ℕ) (word : List Bool) : ℕ[X] :=
  ((network P ℓ J K 0 n sys d).2.vertices.map fun v =>
    ofCoeffList (incEntry v.2 (wordBits word v.1))).prod

private noncomputable def wideTerm (P ℓ J K n : ℕ) (sys : List (List (List ℕ)))
    (d : List ℕ) (q : WideRanks J sys d) : ℕ[X] :=
  assignmentProduct P ℓ J K n sys d (List.ofFn ((wireRankEquiv J sys d).symm q))

/-- Sum of the actual natural entry products at the unique assignments of fitting subset ranks.
This mathematical sum is not used as an exponentially enumerating replacement machine. -/
noncomputable def rankPolynomial (P ℓ J K n : ℕ) (sys : List (List (List ℕ)))
    (d : List ℕ) : ℕ[X] :=
  ∑ q : CombinationRanks J sys d, wideTerm P ℓ J K n sys d (widen J sys d q)

private theorem valid_row_iff (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (word : List Bool) (g : ℕ) :
    validIndices (rowBlocks J sys d g)
      (blockIndices (rowBlocks J sys d g) (wordBits word (rowPorts J sys d g))) = true ↔
      ∀ h < J, wireIndex J sys d word g h <
        (pairInc J sys g h).length.choose (d.getD (g * J + h) 0) := by
  rw [blockIndices_rowPorts]
  simp only [rowBlocks, validIndices, List.zip_map', List.all_map,
    List.all_eq_true, List.mem_range, Function.comp_def, decide_eq_true_eq]

private theorem assignmentProduct_dead (P ℓ J K n : ℕ) (sys : List (List (List ℕ)))
    (d : List ℕ) (word : List Bool) (hd : live J K d = false) :
    assignmentProduct P ℓ J K n sys d word = 0 := by
  apply List.prod_eq_zero
  apply List.mem_map.mpr
  refine ⟨deadRow, ?_, ?_⟩
  · simp [network, rows, hd]
  · simp [deadRow, incEntry, wordBits, tableEntry, ExplicitTensorNetwork.entry]

private theorem wideTerm_invalid (P ℓ J K n : ℕ) (sys : List (List (List ℕ)))
    (d : List ℕ) (q : WideRanks J sys d)
    (hq : ¬ ∀ b, (q b : ℕ) < (pairInc J sys (b / J) (b % J)).length.choose (d.getD b 0)) :
    wideTerm P ℓ J K n sys d q = 0 := by
  classical
  by_cases hl : live J K d = true
  · obtain ⟨b, hb⟩ := not_forall.mp hq
    have hJ : 0 < J := by nlinarith [b.isLt]
    have hg : b.val / J < J := (Nat.div_lt_iff_lt_mul hJ).mpr b.isLt
    have hh : b.val % J < J := Nat.mod_lt _ hJ
    let x := (wireRankEquiv J sys d).symm q
    have hr : wireIndex J sys d (List.ofFn x) (b / J) (b % J) = q b := by
      rw [← wireRankEquiv_apply]
      exact congrArg (fun z => (z b).val) ((wireRankEquiv J sys d).apply_symm_apply q)
    have hz : validIndices (rowBlocks J sys d (b / J))
        (blockIndices (rowBlocks J sys d (b / J))
          (wordBits (List.ofFn x) (rowPorts J sys d (b / J)))) = false := by
      apply Bool.eq_false_iff.mpr
      intro hv
      have h := (valid_row_iff J sys d (List.ofFn x) (b / J)).mp hv (b % J) hh
      rw [Nat.div_add_mod', hr] at h
      exact hb h
    apply List.prod_eq_zero
    apply List.mem_map.mpr
    refine ⟨rowVertex P ℓ J sys d (b / J), ?_, ?_⟩
    · simp only [network, rows, hl, ↓reduceIte]
      apply List.mem_append_left
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨b / J, List.mem_range.mpr hg, rfl⟩
    · change ofCoeffList (rowEntry (P, ℓ, _, rowBlocks J sys d (b / J))
        (wordBits (List.ofFn x) (rowPorts J sys d (b / J)))) = 0
      rw [rowEntry_of_not_valid hz]
      simp
  · exact assignmentProduct_dead P ℓ J K n sys d _ (Bool.eq_false_iff.mpr hl)

private theorem sum_wide_eq_fitting (P ℓ J K n : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) :
    (∑ q : WideRanks J sys d, wideTerm P ℓ J K n sys d q) = rankPolynomial P ℓ J K n sys d := by
  classical
  let S := Finset.univ.filter (fun q : WideRanks J sys d =>
    ∀ b, (q b : ℕ) < (pairInc J sys (b / J) (b % J)).length.choose (d.getD b 0))
  have hs : (∑ q ∈ S, wideTerm P ℓ J K n sys d q) =
      ∑ q : WideRanks J sys d, wideTerm P ℓ J K n sys d q := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q _ hq
    apply wideTerm_invalid
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hq
  rw [← hs]
  unfold rankPolynomial
  symm
  apply Finset.sum_bij (fun q _ => widen J sys d q)
  · intro q _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun b => (q b).isLt⟩
  · intro q _ r _ he
    funext b
    apply Fin.ext
    exact congrArg (fun z => (z b).val) he
  · intro q hq
    have hb := (Finset.mem_filter.mp hq).2
    refine ⟨fun b => ⟨q b, hb b⟩, Finset.mem_univ _, ?_⟩
    funext b
    apply Fin.ext
    rfl
  · intro q _
    rfl

private noncomputable def rankWord (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (q : CombinationRanks J sys d) : List Bool :=
  List.ofFn ((wireRankEquiv J sys d).symm (widen J sys d q))

private theorem rankWord_valid (J : ℕ) (hJ : 0 < J) (sys : List (List (List ℕ)))
    (d : List ℕ) (q : CombinationRanks J sys d) (g : ℕ) (hg : g < J) :
    validIndices (rowBlocks J sys d g) (blockIndices (rowBlocks J sys d g)
      (wordBits (rankWord J sys d q) (rowPorts J sys d g))) = true := by
  apply (valid_row_iff _ _ _ _ _).mpr
  intro h hh
  have hb : g * J + h < J * J := by nlinarith
  let b : Fin (J * J) := ⟨g * J + h, hb⟩
  have hb₁ : b.val / J = g := by
    dsimp only [b]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hJ, Nat.div_eq_of_lt hh, Nat.zero_add]
  have hb₂ : b.val % J = h := by
    dsimp only [b]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hh]
  have hr := wireRankEquiv_apply J sys d ((wireRankEquiv J sys d).symm (widen J sys d q)) b
  rw [(wireRankEquiv J sys d).apply_symm_apply, hb₁, hb₂] at hr
  have hc : (pairInc J sys (b / J) (b % J)).length.choose (d.getD b 0) =
      (pairInc J sys g h).length.choose (d.getD (g * J + h) 0) := by
    rw [hb₁, hb₂]
  have hq := (q b).isLt.trans_eq hc
  unfold rankWord
  rw [← hr]
  exact hq

/-- The integer incidence-monomial coefficient and declared free-variable weight, at a fitting
rank tuple. The cap check is the actual array check. This is a source polynomial specification,
not an executable replacement counter. -/
noncomputable def rankIncidenceTerm (ℓ J K n : ℕ) (sys : List (List (List ℕ)))
    (d : List ℕ) (q : CombinationRanks J sys d) : ℤ[X] :=
  if live J K d then
    (∏ g ∈ Finset.range J, subsetMobius
      (rowPolynomial ℓ ((List.residueClass J sys.length g).map (sys.getD · [])))
      (rowSelected J sys d (rankWord J sys d q) g).toFinset) *
      C ((2 : ℤ) ^ unselectedCount (List.range n) (allRowSelected J sys d (rankWord J sys d q)))
  else 0

/-- Grouped incidence-monomial sum at fitting ranks, with the actual global degree cap. -/
noncomputable def rankIncidencePolynomial (ℓ J K n : ℕ) (sys : List (List (List ℕ)))
    (d : List ℕ) : ℤ[X] := ∑ q : CombinationRanks J sys d, rankIncidenceTerm ℓ J K n sys d q

private theorem prod_range {R : Type*} [CommMonoid R] (N : ℕ) (f : ℕ → R) :
    ((List.range N).map f).prod = ∏ i ∈ Finset.range N, f i := by
  rw [← List.map_coe_finRange_eq_range, List.map_map, ← Fin.prod_univ_def, Finset.prod_range]
  rfl

private theorem wideTerm_ring (P ℓ J K n : ℕ) (hJ : 0 < J) (sys : List (List (List ℕ)))
    (d : List ℕ) (q : CombinationRanks J sys d) :
    truncNatHom P ℓ (wideTerm P ℓ J K n sys d (widen J sys d q)) =
      truncRingHom P ℓ (rankIncidenceTerm ℓ J K n sys d q) := by
  by_cases hl : live J K d = true
  · have hr (g : ℕ) (hg : g ∈ Finset.range J) :
        GaloisRingArith.val P (truncFl ℓ)
          (incEntry (rowVertex P ℓ J sys d g).2
            (wordBits (rankWord J sys d q) (rowPorts J sys d g))) =
          truncRingHom P ℓ (subsetMobius
            (rowPolynomial ℓ ((List.residueClass J sys.length g).map (sys.getD · [])))
            (rowSelected J sys d (rankWord J sys d q) g).toFinset) := by
      rw [val_rowVertex, ite_eq_left (rankWord_valid J hJ sys d q g (Finset.mem_range.mp hg))]
      rfl
    unfold wideTerm assignmentProduct
    rw [map_list_prod]
    simp only [List.map_map, Function.comp_def, truncNatHom_ofCoeffList, network, rows, cols,
      hl, ↓reduceIte, mainWires, Nat.zero_sub, List.range_zero, List.map_nil, List.append_nil,
      List.map_append, List.prod_append, prod_range]
    change (∏ g ∈ Finset.range J, GaloisRingArith.val P (truncFl ℓ)
      (incEntry (rowVertex P ℓ J sys d g).2
        (wordBits (rankWord J sys d q) (rowPorts J sys d g)))) *
      (∏ h ∈ Finset.range J, GaloisRingArith.val P (truncFl ℓ)
        (incEntry (colVertex P J n sys d h).2
          (wordBits (rankWord J sys d q) (colPorts J sys d h)))) = _
    rw [Finset.prod_congr rfl hr, val_colVertices_prod P ℓ J n hJ sys d (rankWord J sys d q)]
    simp only [rankIncidenceTerm, hl, ↓reduceIte, map_mul, map_prod, truncRingHom_C,
      Int.cast_pow, Int.cast_ofNat]
  · unfold wideTerm
    rw [assignmentProduct_dead P ℓ J K n sys d _ (Bool.eq_false_iff.mpr hl)]
    simp [rankIncidenceTerm, hl]

/-- The actual padded contraction is exactly the finite sum over fitting subset-rank tuples.
Unused binary ranks are proved zero; there is no assumed contraction/output correspondence. -/
theorem polyContraction_eq_rankPolynomial (P ℓ J K s n : ℕ)
    (sys : List (List (List ℕ))) (d : List ℕ) :
    (network P ℓ J K s n sys d).2.polyContraction incEntry =
      rankPolynomial P ℓ J K n sys d := by
  rw [polyContraction_network_padding]
  by_cases hl : live J K d = true
  · have hn : (network P ℓ J K 0 n sys d).2 =
        ⟨numWires J sys d, (List.range J).map (rowVertex P ℓ J sys d) ++
          (List.range J).map (colVertex P J n sys d)⟩ := by
      simp [network, rows, cols, mainWires, hl]
    have he : (network P ℓ J K 0 n sys d).2.polyContraction incEntry =
        ∑ x : Fin (numWires J sys d) → Bool,
          assignmentProduct P ℓ J K n sys d (List.ofFn x) := by
      unfold assignmentProduct
      rw [hn]
      rfl
    rw [he, ← sum_wide_eq_fitting]
    exact ((wireRankEquiv J sys d).symm.sum_comp
      (fun x => assignmentProduct P ℓ J K n sys d (List.ofFn x))).symm
  · have hd : live J K d = false := Bool.eq_false_iff.mpr hl
    rw [polyContraction_eq_zero_of_dead P ℓ J K 0 n sys d hd]
    symm
    apply Finset.sum_eq_zero
    intro q _
    exact assignmentProduct_dead P ℓ J K n sys d _ hd

/-- Exact grouped incidence-polynomial identity for every actual padded contraction. All rank
support and entry/weight correspondences are proved, rather than supplied as hypotheses. -/
theorem truncNatHom_polyContraction_eq_rankIncidencePolynomial (P ℓ J K s n : ℕ)
    (hJ : 0 < J) (sys : List (List (List ℕ))) (d : List ℕ) :
    truncNatHom P ℓ ((network P ℓ J K s n sys d).2.polyContraction incEntry) =
      truncRingHom P ℓ (rankIncidencePolynomial ℓ J K n sys d) := by
  rw [polyContraction_eq_rankPolynomial, rankPolynomial, rankIncidencePolynomial,
    map_sum, map_sum]
  exact Finset.sum_congr rfl fun q _ => wideTerm_ring P ℓ J K n hJ sys d q

/-- The actual native stream, including output reconstruction, is the coefficient sum of the
fitting-rank polynomials. This changes no machine or previously proved binary resource bound. -/
theorem sumArrays_eq_rankPolynomials (k : ℕ) (p : ArrayInput) :
    sumArrays k p =
      (∑ i ∈ Finset.range (degreeCount k p), ∑ j ∈ Finset.range (p.1 + 1),
        (rankPolynomial (p.1 + 1) (p.1 + 1) (Nat.ceilQuarter p.1) (degreeCap k p) p.1 p.2
          (arrayAt (degreeCap k p) (Nat.ceilQuarter p.1) i)).coeff j % 2 ^ (p.1 + 1)) %
        2 ^ (p.1 + 1) := by
  rw [sumArrays_eq]
  apply congrArg (fun z : ℕ => z % 2 ^ (p.1 + 1))
  apply Finset.sum_congr rfl
  intro i _
  rw [buildArray, truncCoeffSum_eq, lemmaNetwork, polyContraction_eq_rankPolynomial]

private theorem coeff_modEq_incidence (P ℓ J K s n : ℕ) (hJ : 0 < J)
    (sys : List (List (List ℕ))) (d : List ℕ) (j : ℕ) (hj : j < ℓ) :
    (((network P ℓ J K s n sys d).2.polyContraction incEntry).coeff j : ℤ) ≡
      (rankIncidencePolynomial ℓ J K n sys d).coeff j [ZMOD (2 : ℤ) ^ P] := by
  have h := truncNatHom_polyContraction_eq_rankIncidencePolynomial P ℓ J K s n hJ sys d
  change truncRingHom P ℓ
    (((network P ℓ J K s n sys d).2.polyContraction incEntry).map (Nat.castRingHom ℤ)) = _ at h
  simpa only [coeff_map, Nat.coe_castRingHom] using truncRingHom_eq_iff.mp h j hj

/-- Exact global finite-sum readback: the actual native output is the least residue of the
summed grouped incidence-monomial coefficients. The original finite per-test incidence-polynomial
identification is not an assumption of this theorem and remains a separate obligation. -/
theorem sumArrays_eq_rankIncidenceResidue (k : ℕ) (p : ArrayInput) (hn : 1 ≤ p.1) :
    (Polynomial.sumCoeffsBelow (p.1 + 1)
      (∑ i ∈ Finset.range (degreeCount k p),
        rankIncidencePolynomial (p.1 + 1) (Nat.ceilQuarter p.1) (degreeCap k p) p.1 p.2
          (arrayAt (degreeCap k p) (Nat.ceilQuarter p.1) i)) %
        (2 : ℤ) ^ (p.1 + 1)).toNat = sumArrays k p := by
  let G := fun i => (lemmaNetwork (degreeCap k p) p.1 p.2
    (arrayAt (degreeCap k p) (Nat.ceilQuarter p.1) i)).2
  let Q := ∑ i ∈ Finset.range (degreeCount k p),
    rankIncidencePolynomial (p.1 + 1) (Nat.ceilQuarter p.1) (degreeCap k p) p.1 p.2
      (arrayAt (degreeCap k p) (Nat.ceilQuarter p.1) i)
  have hc (j : ℕ) (hj : j < p.1 + 1) :
      ((∑ i ∈ Finset.range (degreeCount k p), ((G i).polyContraction incEntry).coeff j : ℕ) : ℤ) ≡
        Q.coeff j [ZMOD (2 : ℤ) ^ (p.1 + 1)] := by
    dsimp only [Q]
    rw [finsetSum_coeff]
    push_cast
    apply Int.ModEq.sum
    intro i _
    exact coeff_modEq_incidence (p.1 + 1) (p.1 + 1) (Nat.ceilQuarter p.1) (degreeCap k p)
      (sizeParam p.1) p.1 (Nat.ceilQuarter_pos hn) p.2
      (arrayAt (degreeCap k p) (Nat.ceilQuarter p.1) i) j hj
  have hm := truncSum_modEq (entry := incEntry) (build := buildArray k)
    (modulus := fun p : ArrayInput => 2 ^ (p.1 + 1)) (count := degreeCount k)
    (c := p) (P := p.1 + 1) (ℓ := p.1 + 1) rfl G
    (fun i _ => ⟨(lemmaNetwork (degreeCap k p) p.1 p.2
      (arrayAt (degreeCap k p) (Nat.ceilQuarter p.1) i)).1, rfl⟩)
    (fun j => Q.coeff j) hc
  change (sumArrays k p : ℤ) % (2 : ℤ) ^ (p.1 + 1) =
    Polynomial.sumCoeffsBelow (p.1 + 1) Q % (2 : ℤ) ^ (p.1 + 1) at hm
  have hlt : sumArrays k p < 2 ^ (p.1 + 1) := by
    rw [sumArrays_eq]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast hlt)] at hm
  simpa only [Int.toNat_natCast] using congrArg Int.toNat hm.symm

end Cslib.Circuits.Frontier.IncidenceNetwork
