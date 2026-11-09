/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.ForestRecordQueries
import CslibFrontier.Tactic.Synthesis

/-!
# Synthesizing the transient compressed-forest reachability flag

Given a circuit `c` computing `f : BitString n → BitString n`, a depth circuit `depth`, and
`tables : ForestCircuitTables f L`, this module synthesizes the 1-bit circuit deciding reachability
`∃ t, f^[t] (inputLeft z) = inputRight z` whenever the target `inputRight z` is transient
(`0 < transientDepth f (inputRight z)`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.transientForestCost`: gate budget of the transient
  compressed-forest reachability subcircuit.

## Main results

* `Cslib.Circuits.Boolean.Iteration.synthesis_transient_forest_reachability`: synthesizes a 1-bit
  circuit deciding reachability to transient targets within `transientForestCost`.

## References

* Adapted from lean/Proofs/ForestQuerySynthesis.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

variable {n : ℕ}

/-- Gate budget for the transient compressed-forest reachability query. -/
def transientForestCost (n s d M E L : ℕ) : ℕ :=
  2 + d + 6 * L * s +
    dictionaryCost n (n + 1 + (n + 1)) M (2 * L + 2) +
    dictionaryCost n (n + (n + 1 + (n + 1)) + (n + 3)) E (2 * L + 1) +
    (2 * L + 1) * (41 * n + 41) + (24 * n + 50)

/-- Synthesize the transient reachability flag from a depth circuit and forest tables. -/
theorem synthesis_transient_forest_reachability
    (c : Circuit signature n n) (L : ℕ) (hL : 0 < L)
    (depth : Circuit signature n (n + 2))
    (hd : ∀ x, word (depth.eval interpretation x) =
      BitVec.ofNat (n + 2) (transientDepth (c.eval interpretation) x))
    (tables : ForestCircuitTables (c.eval interpretation) L) :
    ∃ out : Circuit signature (n + n) 1,
      (∀ z, 0 < transientDepth (c.eval interpretation) (inputRight z) →
        (out.eval interpretation z 0 = true ↔
          ∃ t, (c.eval interpretation)^[t] (inputLeft z) = inputRight z)) ∧
      out.size ≤ transientForestCost n c.size depth.size
        tables.markCount tables.edgeTable.count L := by
  let f := c.eval interpretation
  let K := 2 * L
  let Q := K + 1
  let b := Synthesis.Builder.start interpretation (inputs (n + n))
  let b := b.add ((Synthesis.const false).union (Synthesis.const true))
  synthesis_step b using synthesis_depthWord f depth hd b.wires inputRight
  synthesis_step b using Synthesis.orbit (t := K) c inputLeft
  synthesis_step b using Synthesis.orbit (t := K) c inputRight
  have hxTrace (j : Fin Q) : wires (fun z => f^[j.val] (inputLeft z)) ⊆ b.wires := by
    have := Synthesis.subset_stages (fun j => wires fun z => f^[j] (inputLeft z))
      (Nat.le_of_lt_succ j.isLt)
    synthesis_available
  have hyTrace (j : Fin Q) : wires (fun z => f^[j.val] (inputRight z)) ⊆ b.wires := by
    have := Synthesis.subset_stages (fun j => wires fun z => f^[j] (inputRight z))
      (Nat.le_of_lt_succ j.isLt)
    synthesis_available
  let markQueries : BitString (n + n) → Fin (Q + 1) → BitString n :=
    fun z j => Fin.lastCases (inputRight z) (fun i : Fin Q => f^[i.val] (inputLeft z)) j
  have hmarkQ (j : Fin (Q + 1)) : wires (fun z => markQueries z j) ⊆ b.wires := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [markQueries, Fin.lastCases_last]
      synthesis_available
    · simpa only [markQueries, Fin.lastCases_castSucc] using hxTrace i
  obtain ⟨mFlags, mRecords, hmDict, hmSynth⟩ := synthesis_fixed_dictionary b.wires
    tables.marks tables.marks_injective
    (fun i => forestLabelWord tables.low tables.high (tables.marks i)) markQueries hmarkQ
  let b := b.add hmSynth
  obtain ⟨eFlags, eRecords, heDict, heSynth⟩ := synthesis_fixed_dictionary b.wires
    tables.edgeTable.key tables.edgeTable.key_injective
    (fun i => forestAnchorWord f tables.low tables.high (tables.edgeTable.start i))
    (fun z (j : Fin Q) => f^[j.val] (inputRight z)) (by synthesis_available)
  let b := b.add heSynth
  synthesis_step b using synthesis_prefix_hit b.wires
      (fun z (j : Fin Q) => f^[j.val] (inputLeft z)) inputRight
  obtain ⟨foundH, markLabels, hmarkSpec, hmarkSynth⟩ := synthesis_selected_mark f L tables
    b.wires (by synthesis_available)
    (fun z (j : Fin Q) => f^[j.val] (inputLeft z))
    (fun z (j : Fin Q) => mFlags z j.castSucc)
    (fun z (j : Fin Q) => mRecords z j.castSucc)
    (by synthesis_available) (by synthesis_available)
    (fun z j => by simpa [markQueries] using hmDict z j.castSucc)
  let b := b.add hmarkSynth
  obtain ⟨foundA, anchorState, anchorLabels, hanchorSpec, hanchorSynth⟩ :=
    synthesis_selected_anchor f L tables
      (fun j => Nat.le_of_lt_succ j.isLt)
      (fun k hk => ⟨⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩)
      b.wires (by synthesis_available) (by synthesis_available)
      (fun z => mFlags z (Fin.last Q)) (fun z => mRecords z (Fin.last Q))
      (by synthesis_available) (by synthesis_available)
      (fun z => by simpa [markQueries] using hmDict z (Fin.last Q))
      eFlags eRecords (by synthesis_available) (by synthesis_available) heDict
  let b := b.add hanchorSynth
  synthesis_step b using Synthesis.orbit (t := K) c anchorState
  synthesis_step b using synthesis_interval_containment b.wires markLabels anchorLabels
  let intervalBit : BooleanFunction (n + n) := fun z =>
    (!(forestLowWord (markLabels z)).ult (forestLowWord (anchorLabels z))) &&
    (!(forestHighWord (anchorLabels z)).ult (forestLowWord (markLabels z)))
  have haTrace (j : Fin Q) : wires (fun z => f^[j.val] (anchorState z)) ⊆ b.wires := by
    have := Synthesis.subset_stages (fun j => wires fun z => f^[j] (anchorState z))
      (Nat.le_of_lt_succ j.isLt)
    synthesis_available
  synthesis_step b using synthesis_prefix_hit b.wires
      (fun z (j : Fin Q) => f^[j.val] (anchorState z)) inputRight
  let verifyBit : BooleanFunction (n + n) :=
    fun z => decide (∃ j : Fin Q, f^[j.val] (anchorState z) = inputRight z)
  let shortBit : BooleanFunction (n + n) :=
    fun z => decide (∃ j : Fin Q, f^[j.val] (inputLeft z) = inputRight z)
  have hfinal : Synthesis interpretation b.wires
      {fun z => shortBit z || (foundH z && foundA z && verifyBit z && intervalBit z)} 4 :=
    (Synthesis.of_mem (by synthesis_available)).or
      (((Synthesis.of_mem (by synthesis_available)).and
        (Synthesis.of_mem (by synthesis_available))).and
          (Synthesis.of_mem (by synthesis_available)) |>.and
            (Synthesis.of_mem (by synthesis_available)))
  let b := b.add hfinal
  have hchain := b.finish
    (t := {fun z => shortBit z || (foundH z && foundA z && verifyBit z && intervalBit z)})
    (by synthesis_available) le_rfl
  obtain ⟨out, hout, hsize⟩ := hchain.exists_circuit
  refine ⟨out, fun z hyPos => ?_, hsize.trans ?_⟩
  · rw [hout z]
    change (shortBit z || (foundH z && foundA z && verifyBit z && intervalBit z)) = true ↔ _
    let hChosen : BitString n :=
      if h : foundH z = true then
        f^[(Classical.choose ((hmarkSpec z).1 h)).val] (inputLeft z)
      else inputLeft z
    have hHsound : foundH z = true →
        hChosen ∈ forestMarks f tables.H ∧
          ∃ d ≤ 2 * L, f^[d] (inputLeft z) = hChosen := by
      intro hf
      have hspec := Classical.choose_spec ((hmarkSpec z).1 hf)
      set j := Classical.choose ((hmarkSpec z).1 hf)
      have hjeq : hChosen = f^[j.val] (inputLeft z) := dite_eq_left_of_eq_true (eq_true hf)
      exact ⟨hjeq ▸ hspec.1, j.val, Nat.le_of_lt_succ j.isLt, hjeq.symm⟩
    have hHcomplete : (∃ d ≤ 2 * L, f^[d] (inputLeft z) ∈ forestMarks f tables.H) →
        foundH z = true := by
      rintro ⟨d, hd, hmem⟩
      exact (hmarkSpec z).2 ⟨⟨d, Nat.lt_succ_of_le hd⟩, hmem⟩
    have hAsound : foundA z = true → ForestAnchor f tables.H L (inputRight z) (anchorState z) :=
      fun hf => ((hanchorSpec z).1 hf).1
    have hAcomplete : (∃ b, ForestAnchor f tables.H L (inputRight z) b) → foundA z = true :=
      (hanchorSpec z).2
    have hnav := forest_navigation_spec f tables.H L hL tables.cover tables.low tables.high
      tables.interval (inputLeft z) (inputRight z) hChosen (anchorState z) hyPos
      (foundH z) (foundA z) hHsound hHcomplete hAsound hAcomplete
    rw [hnav]
    have hshortIff : shortBit z = true ↔ ∃ i ≤ 2 * L, f^[i] (inputLeft z) = inputRight z := by
      simp only [shortBit, decide_eq_true_eq]
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j.val, Nat.le_of_lt_succ j.isLt, hj⟩
      · rintro ⟨i, hi, he⟩
        exact ⟨⟨i, Nat.lt_succ_of_le hi⟩, he⟩
    have hverifyIff : verifyBit z = true ↔
        ∃ i ≤ 2 * L, f^[i] (anchorState z) = inputRight z := by
      simp only [verifyBit, decide_eq_true_eq]
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j.val, Nat.le_of_lt_succ j.isLt, hj⟩
      · rintro ⟨i, hi, he⟩
        exact ⟨⟨i, Nat.lt_succ_of_le hi⟩, he⟩
    have hintIff (hfH : foundH z = true) (hfA : foundA z = true) :
        intervalBit z = true ↔
          (tables.low (anchorState z) ≤ tables.low hChosen ∧
            tables.low hChosen ≤ tables.high (anchorState z)) := by
      have hmEq : markLabels z = forestLabelWord tables.low tables.high hChosen := by
        have hspec := Classical.choose_spec ((hmarkSpec z).1 hfH)
        have hjeq : hChosen = f^[(Classical.choose ((hmarkSpec z).1 hfH)).val] (inputLeft z) :=
          dite_eq_left_of_eq_true (eq_true hfH)
        rw [hjeq]
        exact hspec.2
      have haEq : anchorLabels z = forestLabelWord tables.low tables.high (anchorState z) :=
        ((hanchorSpec z).1 hfA).2
      dsimp only [intervalBit]
      rw [hmEq, haEq]
      exact forest_label_interval tables.low tables.high (anchorState z) hChosen
    rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      hshortIff, hverifyIff]
    constructor
    · rintro (hs | ⟨⟨⟨hfH, hfA⟩, hv⟩, hi⟩)
      · exact Or.inl hs
      · exact Or.inr ⟨hfH, hfA, hv, (hintIff hfH hfA).mp hi⟩
    · rintro (hs | ⟨hfH, hfA, hv, hi⟩)
      · exact Or.inl hs
      · exact Or.inr ⟨⟨⟨hfH, hfA⟩, hv⟩, (hintIff hfH hfA).mpr hi⟩
  · dsimp +zetaDelta [Synthesis.Builder.add, Synthesis.Builder.start] at hsize ⊢
    unfold transientForestCost
    rw [show 2 * L + 1 + 1 = 2 * L + 2 by omega]
    nlinarith

end Cslib.Circuits.Boolean.Iteration
