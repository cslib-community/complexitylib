/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.ForestCircuitRecords
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.Selection
import Mathlib.Tactic.Linarith

/-!
# Prefix-hit, mark-selection, anchor-selection, and interval-containment subcircuits

This module builds the four query subcircuits needed to evaluate `forest_navigation_spec` after the
shared dictionary lookups have returned candidate mark and compressed-edge records:
* `synthesis_prefix_hit`: tests whether a target state appears along an available `Q`-step orbit
  prefix;
* `synthesis_selected_mark`: selects a hit mark's interval label word from `Q` candidate records;
* `synthesis_selected_anchor`: filters compressed-edge records by `transientDepth f y ≤
  transientDepth f a`, combines with direct target-mark hits, and selects an anchor `(a, low a,
  high a)`;
* `synthesis_interval_containment`: tests `low a ≤ low h ∧ low h ≤ high a` on unpacked `(n + 1)`-bit
  words.

## Main results

* `Cslib.Circuits.Boolean.Iteration.synthesis_prefix_hit`
* `Cslib.Circuits.Boolean.Iteration.synthesis_selected_mark`
* `Cslib.Circuits.Boolean.Iteration.synthesis_selected_anchor`
* `Cslib.Circuits.Boolean.Iteration.synthesis_interval_containment`

## References

* Adapted from lean/Proofs/ForestRecordQueries.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

variable {n : ℕ}

/-- Test whether a target state appears anywhere along an available orbit prefix. -/
theorem synthesis_prefix_hit {a Q : ℕ} (s : Set (BooleanFunction a))
    (trace : BitString a → Fin Q → BitString n)
    (target : BitString a → BitString n)
    (htrace : ∀ j : Fin Q, wires (fun z => trace z j) ⊆ s)
    (htarget : wires target ⊆ s) :
    Synthesis interpretation s
      {fun z => decide (∃ j : Fin Q, trace z j = target z)}
      (Q * (6 * n + 2) + 1) := by
  have hex := Synthesis.exists_mem (s := s) Finset.univ
    (fun j : Fin Q => fun z => decide (trace z j = target z)) (fun _ => 6 * n + 1)
    (fun j _ => synthesis_bits_eq s (fun z => trace z j) target (htrace j) htarget)
  refine (Synthesis.congr_iff hex ?_).mono Set.Subset.rfl Set.Subset.rfl ?_
  · intro z
    simp only [decide_eq_true_eq, Finset.mem_univ, true_and]
  · simp [Finset.sum_const, smul_eq_mul]

/-- Select one marked vertex from a prefix and report whether any mark was seen. -/
theorem synthesis_selected_mark {a Q : ℕ} (f : BitString n → BitString n)
    (L : ℕ) (tables : ForestCircuitTables f L)
    (s : Set (BooleanFunction a)) (hz : (fun _ => false) ∈ s)
    (trace : BitString a → Fin Q → BitString n)
    (flags : BitString a → Fin Q → Bool)
    (records : BitString a → Fin Q → BitString (n + 1 + (n + 1)))
    (hflags : ∀ j, (fun z => flags z j) ∈ s)
    (hrec : ∀ j, wires (fun z => records z j) ⊆ s)
    (hdict : ∀ z j, (flags z j = true ↔ ∃ i, tables.marks i = trace z j) ∧
      ∀ i, tables.marks i = trace z j →
        records z j = forestLabelWord tables.low tables.high (tables.marks i)) :
    ∃ (found : BooleanFunction a)
      (chosen : BitString a → BitString (n + 1 + (n + 1))),
      (∀ z, (found z = true → ∃ j : Fin Q, trace z j ∈ forestMarks f tables.H ∧
          chosen z = forestLabelWord tables.low tables.high (trace z j)) ∧
        ((∃ j : Fin Q, trace z j ∈ forestMarks f tables.H) → found z = true)) ∧
      Synthesis interpretation s ({found} ∪ wires chosen) (Q * (8 * n + 9) + 1) := by
  let chosen : BitString a → BitString (n + 1 + (n + 1)) :=
    fun z => chooseRecord (flags z) (records z) (fun _ => false) Q
  let found : BooleanFunction a := fun z => decide (∃ j : Fin Q, flags z j = true)
  have hchoose := synthesis_chooseRecord s flags records (fun _ _ => false)
    hflags (fun j bit => hrec j ⟨bit, rfl⟩) (fun _ => hz)
  have hfound_raw := Synthesis.exists_mem (s := s) Finset.univ
    (fun j : Fin Q => fun z => flags z j) (fun _ => 0)
    (fun j _ => Synthesis.of_mem (hflags j))
  have hfound : Synthesis interpretation s {found} (Q + 1) := by
    refine (Synthesis.congr_iff hfound_raw ?_).mono Set.Subset.rfl Set.Subset.rfl ?_
    · intro z
      simp only [found, decide_eq_true_eq, Finset.mem_univ, true_and]
    · simp [Finset.sum_const, smul_eq_mul]
  refine ⟨found, chosen, fun z => ⟨?_, ?_⟩, (hfound.union hchoose).mono Set.Subset.rfl
    Set.Subset.rfl (by lia)⟩
  · intro hf
    have hex : ∃ j : Fin Q, j.val < Q ∧ flags z j = true := by
      obtain ⟨j, hj⟩ := of_decide_eq_true hf
      exact ⟨j, j.isLt, hj⟩
    obtain ⟨j, _, hj, hch⟩ := chooseRecord_spec (flags z) (records z) (fun _ => false) Q hex
    obtain ⟨i, hi⟩ := (hdict z j).1.mp hj
    have hmem : trace z j ∈ forestMarks f tables.H := (tables.marks_mem _).mpr ⟨i, hi⟩
    refine ⟨j, hmem, ?_⟩
    dsimp [chosen]
    rw [hch, (hdict z j).2 i hi, hi]
  · rintro ⟨j, hj⟩
    obtain ⟨i, hi⟩ := (tables.marks_mem _).mp hj
    exact decide_eq_true ⟨j, (hdict z j).1.mpr ⟨i, hi⟩⟩

/-- Filter edge-key hits by depth, add direct target-mark hits, and select one anchor record. -/
theorem synthesis_selected_anchor {Q : ℕ} (f : BitString n → BitString n)
    (L : ℕ) (tables : ForestCircuitTables f L)
    (hQ : ∀ j : Fin Q, j.val ≤ 2 * L)
    (hQcomplete : ∀ k ≤ 2 * L, ∃ j : Fin Q, j.val = k)
    (s : Set (BooleanFunction (n + n)))
    (hy : wires (inputRight (n := n)) ⊆ s)
    (hdy : ∀ bit : Fin (n + 3), (fun z => (depthWord f (inputRight z)).getLsbD bit.val) ∈ s)
    (yMarkFlag : BooleanFunction (n + n))
    (yMarkRecord : BitString (n + n) → BitString (n + 1 + (n + 1)))
    (hyFlag : yMarkFlag ∈ s)
    (hyRec : wires yMarkRecord ⊆ s)
    (hyDict : ∀ z, (yMarkFlag z = true ↔ ∃ i, tables.marks i = inputRight z) ∧
      ∀ i, tables.marks i = inputRight z →
        yMarkRecord z = forestLabelWord tables.low tables.high (tables.marks i))
    (edgeFlags : BitString (n + n) → Fin Q → Bool)
    (edgeRecords : BitString (n + n) → Fin Q → BitString (n + (n + 1 + (n + 1)) + (n + 3)))
    (heFlags : ∀ j, (fun z => edgeFlags z j) ∈ s)
    (heRec : ∀ j, wires (fun z => edgeRecords z j) ⊆ s)
    (heDict : ∀ z j,
      (edgeFlags z j = true ↔
        ∃ i, tables.edgeTable.key i = f^[j.val] (inputRight z)) ∧
      ∀ i, tables.edgeTable.key i = f^[j.val] (inputRight z) →
        edgeRecords z j = forestAnchorWord f tables.low tables.high (tables.edgeTable.start i)) :
    ∃ (foundA : BooleanFunction (n + n))
      (anchorState : BitString (n + n) → BitString n)
      (anchorLabels : BitString (n + n) → BitString (n + 1 + (n + 1))),
      (∀ z, (foundA z = true →
          ForestAnchor f tables.H L (inputRight z) (anchorState z) ∧
            anchorLabels z = forestLabelWord tables.low tables.high (anchorState z)) ∧
        ((∃ b, ForestAnchor f tables.H L (inputRight z) b) → foundA z = true)) ∧
      Synthesis interpretation s
        ({foundA} ∪ wires anchorState ∪ wires anchorLabels)
        (Q * (21 * n + 28) + 2) := by
  let elig : BitString (n + n) → Fin Q → Bool := fun z j =>
    edgeFlags z j &&
      !(forestAnchorDepth (edgeRecords z j)).ult (depthWord f (inputRight z))
  have helig_row (j : Fin Q) :
      Synthesis interpretation s {fun z => elig z j} (5 * (n + 3) + 4) := by
    have hda (bit : Fin (n + 3)) :
        (fun z => (forestAnchorDepth (edgeRecords z j)).getLsbD bit.val) ∈ s := by
      simpa only [forestAnchorDepth, getLsbD_word] using
        heRec j ⟨Fin.natAdd (n + (n + 1 + (n + 1))) bit, rfl⟩
    have hult := Synthesis.word_ult (s := s)
      (fun z => forestAnchorDepth (edgeRecords z j))
      (fun z => depthWord f (inputRight z)) hda hdy
    have hge := hult.not
    have hand := (Synthesis.of_mem (heFlags j)).and hge
    simpa only [elig, Nat.zero_add] using hand
  have helig := Synthesis.family (I := interpretation) (s := s)
    (fun j z => elig z j) (fun _ => 5 * (n + 3) + 4) helig_row
  let s1 := s ∪ Set.range (fun j z => elig z j)
  let baseRec : BitString (n + n) → BitString (n + (n + 1 + (n + 1))) :=
    fun z => Fin.append (inputRight z) (yMarkRecord z)
  let candRec : BitString (n + n) → Fin Q → BitString (n + (n + 1 + (n + 1))) :=
    fun z j i => edgeRecords z j (Fin.castAdd (n + 3) i)
  have hcand (j : Fin Q) (bit : Fin (n + (n + 1 + (n + 1)))) :
      (fun z => candRec z j bit) ∈ s1 :=
    Or.inl (heRec j ⟨Fin.castAdd (n + 3) bit, rfl⟩)
  have hbase (bit : Fin (n + (n + 1 + (n + 1)))) : (fun z => baseRec z bit) ∈ s1 := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) bit
    · simp only [baseRec, Fin.append_left]
      exact Or.inl (hy ⟨i, rfl⟩)
    · simp only [baseRec, Fin.append_right]
      exact Or.inl (hyRec ⟨i, rfl⟩)
  let chosenPair : BitString (n + n) → BitString (n + (n + 1 + (n + 1))) :=
    fun z => chooseRecord (elig z) (candRec z) (baseRec z) Q
  have hchoose := synthesis_chooseRecord s1 elig candRec baseRec
    (fun j => Or.inr ⟨j, rfl⟩) hcand hbase
  let anyElig : BooleanFunction (n + n) := fun z => decide (∃ j : Fin Q, elig z j = true)
  have hany_raw := Synthesis.exists_mem (s := s1) Finset.univ
    (fun j : Fin Q => fun z => elig z j) (fun _ => 0)
    (fun j _ => Synthesis.of_mem (Or.inr ⟨j, rfl⟩))
  have hany : Synthesis interpretation s1 {anyElig} (Q + 1) := by
    refine (Synthesis.congr_iff hany_raw ?_).mono Set.Subset.rfl Set.Subset.rfl ?_
    · intro z
      simp only [anyElig, decide_eq_true_eq, Finset.mem_univ, true_and]
    · simp [Finset.sum_const, smul_eq_mul]
  let foundA : BooleanFunction (n + n) := fun z => yMarkFlag z || anyElig z
  have hfoundA : Synthesis interpretation s1 {foundA} (Q + 2) :=
    ((Synthesis.of_mem (Or.inl hyFlag)).or hany).mono Set.Subset.rfl Set.Subset.rfl (by omega)
  let anchorState : BitString (n + n) → BitString n :=
    fun z i => chosenPair z (Fin.castAdd (n + 1 + (n + 1)) i)
  let anchorLabels : BitString (n + n) → BitString (n + 1 + (n + 1)) :=
    fun z i => chosenPair z (Fin.natAdd n i)
  have htotal := helig.trans (hfoundA.union hchoose)
  refine ⟨foundA, anchorState, anchorLabels, fun z => ⟨?_, ?_⟩,
    htotal.mono Set.Subset.rfl ?_ ?_⟩
  · intro hf
    rw [tables.edgeTable.anchor_iff]
    by_cases hex : ∃ j : Fin Q, elig z j = true
    · obtain ⟨j₀, hj₀⟩ := hex
      obtain ⟨j, _, hj, hch⟩ := chooseRecord_spec (elig z) (candRec z) (baseRec z) Q
        ⟨j₀, j₀.isLt, hj₀⟩
      have hje : edgeFlags z j = true ∧
          (!(forestAnchorDepth (edgeRecords z j)).ult (depthWord f (inputRight z))) = true := by
        simpa [elig] using hj
      obtain ⟨i, hi⟩ := (heDict z j).1.mp hje.1
      have hrec := (heDict z j).2 i hi
      have hstate : anchorState z = tables.edgeTable.start i := by
        funext b
        have hc := congrFun hch (Fin.castAdd (n + 1 + (n + 1)) b)
        simpa [anchorState, candRec, hrec, forestAnchorWord] using hc
      have hlabels : anchorLabels z =
          forestLabelWord tables.low tables.high (tables.edgeTable.start i) := by
        funext b
        have hc := congrFun hch (Fin.natAdd n b)
        simpa [anchorLabels, candRec, hrec, forestAnchorWord] using hc
      have hdepth : transientDepth f (inputRight z) ≤
          transientDepth f (tables.edgeTable.start i) := by
        have h1 := hje.2
        simp only [hrec, forestAnchorDepth_bits, Bool.not_eq_true', BitVec.ult,
          decide_eq_false_iff_not, not_lt, toNat_depthWord] at h1
        exact h1
      exact ⟨Or.inr ⟨i, j.val, hstate.symm, hQ j, hstate ▸ hdepth, hi.symm⟩,
        hlabels.trans (by rw [hstate])⟩
    · have hnone : ∀ j : Fin Q, elig z j = false :=
        fun j => Bool.eq_false_iff.mpr fun hj => hex ⟨j, hj⟩
      have hch := chooseRecord_of_forall_eq_false (elig z) (candRec z) (baseRec z) hnone Q
      have hanyF : anyElig z = false :=
        decide_eq_false fun ⟨j, hj⟩ => by rw [hnone j] at hj; cases hj
      have hyTrue : yMarkFlag z = true := by
        simpa [foundA, hanyF] using hf
      obtain ⟨i, hi⟩ := (hyDict z).1.mp hyTrue
      have hymem : inputRight z ∈ forestMarks f tables.H := (tables.marks_mem _).mpr ⟨i, hi⟩
      have hstate : anchorState z = inputRight z := by
        funext b
        have hc := congrFun hch (Fin.castAdd (n + 1 + (n + 1)) b)
        simpa [anchorState, chosenPair, baseRec] using hc
      have hlabels : anchorLabels z =
          forestLabelWord tables.low tables.high (inputRight z) := by
        funext b
        have hc := congrFun hch (Fin.natAdd n b)
        have hyr := (hyDict z).2 i hi
        simpa [anchorLabels, chosenPair, baseRec, hyr, hi] using hc
      exact ⟨Or.inl ⟨hymem, hstate⟩, hlabels.trans (by rw [hstate])⟩
  · rintro ⟨b, hb⟩
    rw [tables.edgeTable.anchor_iff] at hb
    rcases hb with ⟨hymem, rfl⟩ | ⟨i, k, rfl, hk, hdepth, hkey⟩
    · obtain ⟨i, hi⟩ := (tables.marks_mem _).mp hymem
      have hyTrue : yMarkFlag z = true := (hyDict z).1.mpr ⟨i, hi⟩
      simp [foundA, hyTrue]
    · obtain ⟨j, rfl⟩ := hQcomplete k hk
      have heTrue : edgeFlags z j = true := (heDict z j).1.mpr ⟨i, hkey.symm⟩
      have hrec := (heDict z j).2 i hkey.symm
      have hdTrue :
          (!(forestAnchorDepth (edgeRecords z j)).ult (depthWord f (inputRight z))) = true := by
        simp only [hrec, forestAnchorDepth_bits, Bool.not_eq_true', BitVec.ult,
          decide_eq_false_iff_not, not_lt, toNat_depthWord]
        exact hdepth
      have hjTrue : elig z j = true := by simp [elig, heTrue, hdTrue]
      have hanyTrue : anyElig z = true := decide_eq_true ⟨j, hjTrue⟩
      simp [foundA, hanyTrue]
  · rintro _ ((rfl | ⟨b, rfl⟩) | ⟨b, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨Fin.castAdd (n + 1 + (n + 1)) b, rfl⟩
    · exact Or.inr ⟨Fin.natAdd n b, rfl⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    nlinarith

/-- Compare the two unpacked interval words of the selected mark and anchor records. -/
theorem synthesis_interval_containment {a : ℕ} (s : Set (BooleanFunction a))
    (markLabels anchorLabels : BitString a → BitString (n + 1 + (n + 1)))
    (hmark : wires markLabels ⊆ s) (hanchor : wires anchorLabels ⊆ s) :
    Synthesis interpretation s
      {fun z =>
        (!(forestLowWord (markLabels z)).ult (forestLowWord (anchorLabels z))) &&
        (!(forestHighWord (anchorLabels z)).ult (forestLowWord (markLabels z)))}
      (24 * n + 27) := by
  have hmLow (bit : Fin (n + 1)) :
      (fun z => (forestLowWord (markLabels z)).getLsbD bit.val) ∈ s := by
    simpa only [forestLowWord, getLsbD_word] using hmark ⟨Fin.castAdd (n + 1) bit, rfl⟩
  have haLow (bit : Fin (n + 1)) :
      (fun z => (forestLowWord (anchorLabels z)).getLsbD bit.val) ∈ s := by
    simpa only [forestLowWord, getLsbD_word] using hanchor ⟨Fin.castAdd (n + 1) bit, rfl⟩
  have haHigh (bit : Fin (n + 1)) :
      (fun z => (forestHighWord (anchorLabels z)).getLsbD bit.val) ∈ s := by
    simpa only [forestHighWord, getLsbD_word] using hanchor ⟨Fin.natAdd (n + 1) bit, rfl⟩
  have h1 := (Synthesis.word_ult (s := s) (fun z => forestLowWord (markLabels z))
    (fun z => forestLowWord (anchorLabels z)) hmLow haLow).not
  have h2 := (Synthesis.word_ult (s := s) (fun z => forestHighWord (anchorLabels z))
    (fun z => forestLowWord (markLabels z)) haHigh hmLow).not
  exact (h1.and h2).mono Set.Subset.rfl Set.Subset.rfl (by omega)

end Cslib.Circuits.Boolean.Iteration
