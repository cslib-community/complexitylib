/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceRankSum
import all Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceRankSum
import all Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceBlockCoverage
import Mathlib.Data.List.Sublists
import Mathlib.Data.Fintype.BigOperators

/-!
# Global incidence selection sum of the actual native stream

Eliminate the computed degree arrays and all combination ranks from the actual streamed output.
Each family of incidence sublists of total size at most the computed cap occurs exactly once;
all other arrays contribute zero. This is a mathematical finite-sum identity, not a replacement
implementation enumerating powersets.

The selections still use the executable test-group coordinates. Identifying their polynomial
with `systemIncidencePolynomial` on original equation coordinates is a separate obligation.
Consequently this module does not assert original assignment-count correctness or the complete
sharper-counter endpoint of [OpenAI2026ETH], Lemma D.2, PDF pp.55–56.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.selectionPolynomial`: the capped family sum.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.sum_rankIncidencePolynomial_eq_selectionPolynomial`:
  complete global reindexing, including zero contribution from cap-dead arrays.
* `Cslib.Circuits.Frontier.IncidenceNetwork.sumArrays_eq_selectionResidue`: actual native output
  recovered from this family sum, without a supplied polynomial identity.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.BitString Polynomial Finset

/-- Mathematical families of sublists of the actual incidence blocks. No algorithm here
executes this finite set; it specifies the terms covered by the streamed array/rank decoder. -/
noncomputable def selectionFamilies (J : ℕ) (sys : List (List (List ℕ))) :
    Finset (Fin (J * J) → List (ℕ × ℕ)) :=
  Fintype.piFinset fun b => (pairInc J sys (b / J) (b % J)).sublists.toFinset

/-- Selected incidences at a row group, in actual block order. -/
def selectionRow (J : ℕ) (parts : Fin (J * J) → List (ℕ × ℕ)) (g : Fin J) :
    List (ℕ × ℕ) :=
  (List.finRange J).flatMap fun h : Fin J => parts ⟨g * J + h, by nlinarith [g.isLt, h.isLt]⟩

/-- The capped grouped incidence polynomial, with no array or subset-rank indices remaining.
The free-variable weight retains every declared variable, including those outside all scopes. -/
noncomputable def selectionPolynomial (ℓ J K n : ℕ) (sys : List (List (List ℕ))) : ℤ[X] :=
  ∑ parts ∈ (selectionFamilies J sys).filter (fun parts => ∑ b, (parts b).length ≤ K),
    (∏ g : Fin J, subsetMobius
      (rowPolynomial ℓ ((List.residueClass J sys.length g).map (sys.getD · [])))
      (selectionRow J parts g).toFinset) *
      C ((2 : ℤ) ^ unselectedCount (List.range n)
        ((List.finRange J).flatMap (selectionRow J parts)))

private def rankParts (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (q : CombinationRanks J sys d) (b : Fin (J * J)) : List (ℕ × ℕ) :=
  selectBlock (pairInc J sys (b / J) (b % J), d.getD b 0) (q b)

private theorem length_rankParts (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (q : CombinationRanks J sys d) (b : Fin (J * J)) :
    (rankParts J sys d q b).length = d.getD b 0 := by
  change (chosenBy (pairInc J sys (b / J) (b % J))
    (unrankCombination _ _ (q b))).length = _
  rw [length_chosenBy _ _ (length_unrankCombination _ _ _)]
  exact count_true_unrankCombination (q b).isLt

/-- Membership means each component is a sublist of its actual incidence block. -/
theorem mem_selectionFamilies (J : ℕ) (sys : List (List (List ℕ)))
    (parts : Fin (J * J) → List (ℕ × ℕ)) :
    parts ∈ selectionFamilies J sys ↔
      ∀ b, (parts b).Sublist (pairInc J sys (b / J) (b % J)) := by
  simp [selectionFamilies, Fintype.mem_piFinset]

private theorem live_iff_sum (J K : ℕ) (d : List ℕ) :
    live J K d = true ↔ ∑ b : Fin (J * J), d.getD b 0 ≤ K := by
  rw [live, decide_eq_true_eq, ← List.map_coe_finRange_eq_range, List.map_map,
    ← Fin.sum_univ_def]
  rfl

private theorem rankParts_injective (J K : ℕ) (sys : List (List (List ℕ))) :
    Function.Injective (fun p : Σ i : Fin (arrayCount K J),
        CombinationRanks J sys (arrayAt K J i) =>
      rankParts J sys (arrayAt K J p.1) p.2) := by
  intro p r he
  rcases p with ⟨i, q⟩
  rcases r with ⟨j, u⟩
  have hd : arrayAt K J i = arrayAt K J j := by
    apply List.ext_getElem (by simp)
    intro b hb hb'
    have hb'' : b < J * J := by simpa using hb
    have h := congrArg List.length (congrFun he ⟨b, hb''⟩)
    simpa only [length_rankParts, List.getD_eq_getElem _ _ hb,
      List.getD_eq_getElem _ _ hb'] using h
  have hij := arrayAt_injective K J hd
  subst j
  have hq : q = u := by
    funext b
    apply Fin.ext
    apply unrankCombination_injective (q b).isLt (u b).isLt
    apply chosenBy_injective _ (nodup_pairInc _ _ _ _) _ _
      (length_unrankCombination _ _ _) (length_unrankCombination _ _ _)
    exact congrFun he b
  subst u
  rfl

private theorem rankParts_surjective (J K : ℕ) (sys : List (List (List ℕ)))
    (parts : Fin (J * J) → List (ℕ × ℕ))
    (hp : parts ∈ selectionFamilies J sys) (hc : ∑ b, (parts b).length ≤ K) :
    ∃ i : Fin (arrayCount K J), ∃ q : CombinationRanks J sys (arrayAt K J i),
      live J K (arrayAt K J i) = true ∧ rankParts J sys (arrayAt K J i) q = parts := by
  classical
  let ps := List.ofFn parts
  have hl : ps.length = J * J := List.length_ofFn
  have htotal : (ps.map List.length).sum ≤ K := by
    simpa only [ps, List.map_ofFn, List.sum_ofFn, Function.comp_def] using hc
  have hsub : ∀ b < ps.length,
      (ps.getD b []).Sublist (pairInc J sys (b / J) (b % J)) := by
    intro b hb
    have hb' : b < J * J := by simpa only [ps, List.length_ofFn] using hb
    simpa only [ps, List.getD_eq_getElem _ _ hb, List.getElem_ofFn] using
      (mem_selectionFamilies J sys parts).mp hp ⟨b, hb'⟩
  obtain ⟨i, ⟨hi, hr⟩, _⟩ := array_and_ranks_coverage K J sys ps hl htotal hsub
  have hget (b : Fin (J * J)) : (arrayAt K J i).getD b 0 = (parts b).length := by
    rw [hi]
    change (ps.map List.length).getD b (([] : List (ℕ × ℕ)).length) = _
    rw [List.getD_map ps [] List.length,
      List.getD_eq_getElem ps [] (by simpa only [ps, List.length_ofFn] using b.isLt)]
    simp only [ps, List.getElem_ofFn]
  have hex (b : Fin (J * J)) : ∃ r : Fin ((pairInc J sys (b / J) (b % J)).length.choose
      ((arrayAt K J i).getD b 0)),
      selectBlock (pairInc J sys (b / J) (b % J), (arrayAt K J i).getD b 0) r = parts b := by
    obtain ⟨r, hr, _⟩ := hr b (by simpa only [ps, List.length_ofFn] using b.isLt)
    refine ⟨r, ?_⟩
    rw [List.getD_eq_getElem ps [] (by simpa only [ps, List.length_ofFn] using b.isLt)] at hr
    simpa only [ps, List.getElem_ofFn] using hr
  choose q hq using hex
  refine ⟨i, q, (live_iff_sum J K _).mpr ?_, funext hq⟩
  simpa only [hget] using hc

private theorem rowSelected_rankParts (J : ℕ) (hJ : 0 < J)
    (sys : List (List (List ℕ))) (d : List ℕ) (q : CombinationRanks J sys d) (g : Fin J) :
    rowSelected J sys d (rankWord J sys d q) g = selectionRow J (rankParts J sys d q) g := by
  rw [rowSelected, blockIndices_rowPorts, rowBlocks, selected, List.zip_map', List.flatMap_map,
    ← List.map_coe_finRange_eq_range, List.flatMap_map]
  unfold selectionRow
  apply List.flatMap_congr
  intro h _
  let b : Fin (J * J) := ⟨g * J + h, by nlinarith [g.isLt, h.isLt]⟩
  have hb₁ : b.val / J = g := by
    dsimp only [b]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hJ, Nat.div_eq_of_lt h.isLt, Nat.zero_add]
  have hb₂ : b.val % J = h := by
    dsimp only [b]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h.isLt]
  have he := wireRankEquiv_apply J sys d ((wireRankEquiv J sys d).symm (widen J sys d q)) b
  rw [(wireRankEquiv J sys d).apply_symm_apply, hb₁, hb₂] at he
  change selectBlock _ (wireIndex J sys d (rankWord J sys d q) g h) = rankParts J sys d q b
  change (q b : ℕ) = wireIndex J sys d (rankWord J sys d q) g h at he
  generalize hqr : (q b : ℕ) = r at he ⊢
  unfold rankParts
  rw [hqr, hb₁, hb₂, ← he]

/-- Remove all actual degree and rank indices from the global incidence polynomial. Every capped
family occurs once. In particular, no polynomial equality or desired count is a premise. -/
theorem sum_rankIncidencePolynomial_eq_selectionPolynomial (ℓ J K n : ℕ) (hJ : 0 < J)
    (sys : List (List (List ℕ))) :
    (∑ i ∈ range (arrayCount K J),
      rankIncidencePolynomial ℓ J K n sys (arrayAt K J i)) =
      selectionPolynomial ℓ J K n sys := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [rankIncidencePolynomial]
  rw [← Fintype.sum_sigma (fun p : Σ i : Fin (arrayCount K J),
    CombinationRanks J sys (arrayAt K J i) =>
      rankIncidenceTerm ℓ J K n sys (arrayAt K J p.1) p.2)]
  let candidates := (univ : Finset (Σ i : Fin (arrayCount K J),
    CombinationRanks J sys (arrayAt K J i))).filter (fun p => live J K (arrayAt K J p.1))
  have hz : (∑ p ∈ candidates, rankIncidenceTerm ℓ J K n sys (arrayAt K J p.1) p.2) =
      ∑ p : Σ i : Fin (arrayCount K J), CombinationRanks J sys (arrayAt K J i),
        rankIncidenceTerm ℓ J K n sys (arrayAt K J p.1) p.2 := by
    apply sum_subset (filter_subset _ _)
    intro p _ hp
    have hn : live J K (arrayAt K J p.1) ≠ true := by simpa only [candidates, mem_filter,
      mem_univ, true_and] using hp
    simp [rankIncidenceTerm, hn]
  rw [← hz, selectionPolynomial]
  apply sum_bij (fun p _ => rankParts J sys (arrayAt K J p.1) p.2)
  · intro p hp
    have hl := (mem_filter.mp hp).2
    apply mem_filter.mpr
    constructor
    · apply (mem_selectionFamilies _ _ _).mpr
      intro b
      exact selectBlock_sublist _ _
    · simpa only [length_rankParts] using (live_iff_sum J K _).mp hl
  · intro p _ q _ he
    exact rankParts_injective J K sys he
  · intro parts hp
    obtain ⟨i, q, hl, he⟩ := rankParts_surjective J K sys parts (mem_filter.mp hp).1
      (mem_filter.mp hp).2
    exact ⟨⟨i, q⟩, mem_filter.mpr ⟨mem_univ _, hl⟩, he⟩
  · intro p hp
    have hl := (mem_filter.mp hp).2
    simp only [rankIncidenceTerm, hl, ↓reduceIte]
    rw [← Fin.prod_univ_eq_prod_range]
    have hr := rowSelected_rankParts J hJ sys (arrayAt K J p.1) p.2
    simp only [hr]
    congr 3
    rw [allRowSelected, ← List.map_coe_finRange_eq_range (n := J), List.flatMap_map]
    congr 1
    exact List.flatMap_congr fun g _ => hr g

/-- Native scalar readback from the capped incidence-family sum, after complete global
array/rank reindexing. The source per-equation coordinate identification remains separate. -/
theorem sumArrays_eq_selectionResidue (k : ℕ) (p : ArrayInput) (hn : 1 ≤ p.1) :
    (sumCoeffsBelow (p.1 + 1)
      (selectionPolynomial (p.1 + 1) (Nat.ceilQuarter p.1) (degreeCap k p) p.1 p.2) %
        (2 : ℤ) ^ (p.1 + 1)).toNat = sumArrays k p := by
  rw [← sum_rankIncidencePolynomial_eq_selectionPolynomial _ _ _ _
    (Nat.ceilQuarter_pos hn) p.2]
  exact sumArrays_eq_rankIncidenceResidue k p hn

end Cslib.Circuits.Frontier.IncidenceNetwork
