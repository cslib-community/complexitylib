/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceArraySum
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceBlockCoverage
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ContractionZero
import Mathlib.Data.List.GetD

/-!
# The actual native degree-array sum has the source support

The full radix box is larger than the arrays used in [OpenAI2026ETH], Lemma D.2 (PDF pp.55–56).
Prove that all extra arrays contribute exactly zero: exceeding the global cap writes the dead
row, and exceeding any local capacity forces a zero group row, including zero-width blocks.
Thus the existing native loop sums exactly the source-feasible arrays. Its actual binary time
and original-input workspace certificates are unchanged. Equality of this supported contraction
sum with the sparse-system solution count remains a separate global reconstruction obligation.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.FeasibleArray`: the actual cap/capacity conditions.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.array_and_ranks_coverage`: every selected monomial
  has exactly one decoded array and exactly one actual local rank at every group pair.
* `Cslib.Circuits.Frontier.IncidenceNetwork.polyContraction_eq_zero_of_not_feasible`: every extra
  full-box array has zero contraction, before modular reduction.
* `Cslib.Circuits.Frontier.IncidenceNetwork.sumArrays_eq_feasible`: the actual native output is
  exactly the modular sum over source-feasible decoded arrays.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF pp.55–56.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.Complexity.CountingSimulation

/-- The source array conditions, on actual degree coordinates and actual deduplicated incidences.
No graph, valid-index proof, output or runtime contract is supplied in this predicate. -/
@[expose] def FeasibleArray (J K : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) : Prop :=
  live J K d = true ∧ ∀ g < J, ∀ h < J,
    d.getD (g * J + h) 0 ≤ (pairInc J sys g h).length

/-- A selected incidence monomial determines exactly one actual decoded array and exactly one
valid local rank at every pair. Its total degree supplies all coordinate bounds. The incidence
lists and their distinctness are computed from the system; no ranks are supplied as advice. -/
theorem array_and_ranks_coverage (K J : ℕ) (sys : List (List (List ℕ)))
    (parts : List (List (ℕ × ℕ))) (hlen : parts.length = J * J)
    (hdegree : (parts.map List.length).sum ≤ K)
    (hparts : ∀ b < parts.length,
      (parts.getD b []).Sublist (pairInc J sys (b / J) (b % J))) :
    ∃! i : Fin (arrayCount K J), arrayAt K J i = parts.map List.length ∧
      ∀ b < parts.length,
        ∃! r : Fin ((pairInc J sys (b / J) (b % J)).length.choose
          ((arrayAt K J i).getD b 0)),
          selectBlock (pairInc J sys (b / J) (b % J), (arrayAt K J i).getD b 0) r =
            parts.getD b [] := by
  obtain ⟨i, hi, _⟩ := selected_degrees_coverage K J parts hlen hdegree
  refine ⟨i, ⟨hi, ?_⟩, fun j hj => arrayAt_injective K J (hj.1.trans hi.symm)⟩
  intro b hb
  rw [hi, show (parts.map List.length).getD b 0 = (parts.getD b []).length from
    List.getD_map parts [] List.length]
  exact selectBlock_coverage _ (nodup_pairInc J sys (b / J) (b % J)) _ (hparts b hb)

/-- An impossible group-pair degree makes the actual row procedure return the zero list,
regardless of the word. In particular, a zero-width block is still checked. -/
theorem rowEntry_eq_zero_of_impossible (P ℓ J : ℕ) (sys : List (List (List ℕ)))
    (d : List ℕ) (g h : ℕ) (hh : h < J)
    (hd : (pairInc J sys g h).length < d.getD (g * J + h) 0) (bs : List Bool) :
    incEntry (rowVertex P ℓ J sys d g).2 bs = [] := by
  change rowEntry (P, ℓ, _, rowBlocks J sys d g) bs = []
  have hm : (pairInc J sys g h, d.getD (g * J + h) 0) ∈ rowBlocks J sys d g :=
    List.mem_map.mpr ⟨h, List.mem_range.mpr hh, rfl⟩
  have hz := validIndices_false_of_impossible (rowBlocks J sys d g) bs hm hd
  simp [rowEntry, hz]

/-- Exceeding the global degree cap writes a dead row and annihilates the whole contraction. -/
theorem polyContraction_eq_zero_of_dead (P ℓ J K s n : ℕ)
    (sys : List (List (List ℕ))) (d : List ℕ) (hd : live J K d = false) :
    (network P ℓ J K s n sys d).2.polyContraction incEntry = 0 := by
  apply DescribedNetwork.contraction_eq_zero_of_vertex _ _ (v := deadRow)
  · simp [network, rows, hd]
  · intro bs
    cases hb : Cslib.BitString.lsbValue bs <;>
      simp [deadRow, incEntry, tableEntry, ExplicitTensorNetwork.entry, hb]

/-- Exceeding one local capacity gives zero at every wire assignment, including padding bits. -/
theorem polyContraction_eq_zero_of_capacity (P ℓ J K s n : ℕ)
    (sys : List (List (List ℕ))) (d : List ℕ) (g h : ℕ) (hg : g < J) (hh : h < J)
    (hd : (pairInc J sys g h).length < d.getD (g * J + h) 0) :
    (network P ℓ J K s n sys d).2.polyContraction incEntry = 0 := by
  by_cases hl : live J K d = true
  · apply DescribedNetwork.contraction_eq_zero_of_vertex _ _ (v := rowVertex P ℓ J sys d g)
    · simp only [network, rows, hl, ↓reduceIte]
      apply List.mem_append_left
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨g, List.mem_range.mpr hg, rfl⟩
    · intro bs
      rw [rowEntry_eq_zero_of_impossible P ℓ J sys d g h hh hd bs]
      simp
  · exact polyContraction_eq_zero_of_dead P ℓ J K s n sys d (Bool.eq_false_iff.mpr hl)

/-- All extra full-box arrays contribute zero, independently of the original system's semantics. -/
theorem polyContraction_eq_zero_of_not_feasible (P ℓ J K s n : ℕ)
    (sys : List (List (List ℕ))) (d : List ℕ) (hd : ¬ FeasibleArray J K sys d) :
    (network P ℓ J K s n sys d).2.polyContraction incEntry = 0 := by
  by_cases hl : live J K d = true
  · have hbad : ¬ ∀ g < J, ∀ h < J,
        d.getD (g * J + h) 0 ≤ (pairInc J sys g h).length := fun h => hd ⟨hl, h⟩
    simp only [not_forall, not_le] at hbad
    obtain ⟨g, hg, h, hh, hb⟩ := hbad
    exact polyContraction_eq_zero_of_capacity P ℓ J K s n sys d g h hg hh (by omega)
  · exact polyContraction_eq_zero_of_dead P ℓ J K s n sys d (Bool.eq_false_iff.mpr hl)

/-- The actual coefficient-sum contribution of any extra decoded array is zero. -/
theorem truncCoeffSum_buildArray_eq_zero (k : ℕ) (p : ArrayInput) (i : ℕ)
    (hi : ¬ FeasibleArray (Nat.ceilQuarter p.1) (degreeCap k p) p.2
      (arrayAt (degreeCap k p) (Nat.ceilQuarter p.1) i)) :
    truncCoeffSum incEntry (buildArray k (p, i)) = 0 := by
  rw [buildArray, truncCoeffSum_eq, lemmaNetwork,
    polyContraction_eq_zero_of_not_feasible _ _ _ _ _ _ _ _ hi]
  simp

open Classical in
/-- The proved native loop's exact output can discard every extra radix-box index. This is an
identity of its actual output, not a replacement algorithm or a supplied reconstruction premise. -/
theorem sumArrays_eq_feasible (k : ℕ) (p : ArrayInput) :
    sumArrays k p =
      (∑ i ∈ (Finset.range (degreeCount k p)).filter (fun i =>
        FeasibleArray (Nat.ceilQuarter p.1) (degreeCap k p) p.2
          (arrayAt (degreeCap k p) (Nat.ceilQuarter p.1) i)),
        truncCoeffSum incEntry (buildArray k (p, i))) % 2 ^ (p.1 + 1) := by
  classical
  rw [sumArrays_eq]
  congr 1
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hnot
  apply truncCoeffSum_buildArray_eq_zero
  simpa only [Finset.mem_filter, hi, true_and] using hnot

end Cslib.Circuits.Frontier.IncidenceNetwork
