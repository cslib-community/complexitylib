/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.TranscriptTree
import CslibFrontier.Computability.DecisionTree.Observations
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
Transcript-tree clients: noninjective observations, zero input coordinates, cancelled repeated
wires, unattainable activation patterns, and a comparison tree computing a nonconstant circuit.
-/

open Cslib Cslib.Circuits Finset
open Cslib.Circuits.Boolean.WeightedThreshold

namespace ThresholdTranscriptTests

universe u v w

-- Four inputs but only two observation vectors; the unused coordinate is not charged.
example : ∃ t : DecisionTree Unit Bool,
    (∀ x : Bool × Bool, t.eval (fun _ => x.1) = x.1) ∧ t.depth ≤ 1 ∧ t.leafCount ≤ 2 := by
  classical
  obtain ⟨t, ht, hd, hl⟩ := DecisionTree.exists_of_observations (univ : Finset (Bool × Bool))
    univ_nonempty (fun x (_ : Unit) => x.1) (fun (_ : Unit) x => x.1) Prod.fst
    (fun _ _ _ _ h => congrFun h ()) (by
      intro S _ _ hne
      obtain ⟨x, hx, y, hy, hxy⟩ := hne
      refine ⟨(), (), fun _ _ => rfl, ?_⟩
      intro b
      by_cases hxb : x.1 = b
      · exact ⟨x, mem_filter.mpr ⟨hx, hxb⟩⟩
      · have hyb : y.1 = b := by
          have hxy' : x.1 ≠ y.1 := fun h => hxy (funext fun _ => h)
          cases hxi : x.1 <;> cases hyi : y.1 <;> cases b <;> simp_all
        exact ⟨y, mem_filter.mpr ⟨hy, hyb⟩⟩)
  refine ⟨t, fun x => ht x (mem_univ _), hd, hl.trans ?_⟩
  exact (card_le_card (subset_univ _)).trans_eq (by decide)

-- A zero-bit cube still has one input, so a nullary gate gives one leaf at depth zero.
private def nullary : Program signature 0 1 :=
  Program.empty.gate ⟨⟨0, Fin.elim0, 0⟩, Fin.elim0⟩

example : ∃ t : DecisionTree (SeparableComparison (Fin 0 → Bool) (Fin 0 → Bool)) Bool,
    (∀ x y, t.eval (fun q => q.eval x y) = true) ∧ t.depth = 0 ∧ t.leafCount = 1 := by
  classical
  have hg : inputGates nullary = ∅ := by ext i; simp
  obtain ⟨t, ht, hd, hl⟩ := exists_gate_readout_tree nullary
    (finSumFinEquiv : Fin 0 ⊕ Fin 0 ≃ Fin 0).symm (fun z => z 0)
  refine ⟨t, ?_, Nat.eq_zero_of_le_zero (by simpa only [hg, card_empty] using hd),
    Nat.le_antisymm (hl.trans (card_image_le.trans (by decide))) t.leafCount_pos⟩
  intro x y
  rw [ht]
  change (Program.empty.gate _).eval interpretation _ (Fin.last 0) = true
  rw [Program.eval_gate_last]
  norm_num [Line.eval, interpretation]

private def cancelled : Program signature 1 1 :=
  Program.empty.gate ⟨⟨2, ![1, -1], 0⟩, fun _ => .input 0⟩

-- Repeated-wire cancellation gives a depth-zero tree despite two syntactic argument slots.
example : ∃ t : DecisionTree (SeparableComparison (Fin 1 → Bool) (Fin 0 → Bool)) Bool,
    (∀ x y, t.eval (fun q => q.eval x y) = true) ∧ t.depth = 0 := by
  classical
  have hg : inputGates cancelled = ∅ := by
    ext gate
    simp only [mem_inputGates, Finset.notMem_empty, iff_false, not_exists]
    intro i
    fin_cases gate; fin_cases i
    change ¬lineWeight (⟨⟨2, ![1, -1], 0⟩, fun _ => .input 0⟩ : Line signature 1 1)
      (.input 0) ≠ 0
    dsimp only [lineWeight]
    norm_num [Fin.sum_univ_two]
  obtain ⟨t, ht, hd, _⟩ := exists_gate_readout_tree cancelled
    (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1).symm (fun z => z 0)
  refine ⟨t, ?_, Nat.eq_zero_of_le_zero (by simpa only [hg, card_empty] using hd)⟩
  intro x y
  rw [ht]
  change (Program.empty.gate _).eval interpretation _ (Fin.last 0) = true
  rw [Program.eval_gate_last]
  dsimp only [Line.eval, interpretation, Function.comp_apply, Wire.elim]
  simp [Fin.sum_univ_two]

private def readOnce : Program signature 1 1 :=
  Program.empty.gate ⟨⟨1, fun _ => 1, 1⟩, fun _ => .input 0⟩

private def readTwice : Program signature 1 2 :=
  readOnce.gate ⟨⟨1, fun _ => 1, 1⟩, fun _ => .input 0⟩

private theorem readTwice_eval (x : Fin 1 → Bool) :
    readTwice.eval interpretation x = fun _ => x 0 := by
  funext gate
  fin_cases gate
  · change (Program.empty.gate _).eval interpretation x (Fin.last 0) = x 0
    rw [Program.eval_gate_last]
    cases hx : x 0 <;>
      dsimp only [Line.eval, interpretation, Function.comp_apply, Wire.elim] <;> norm_num [hx]
  · change (readOnce.gate _).eval interpretation x (Fin.last 1) = x 0
    rw [Program.eval_gate_last]
    cases hx : x 0 <;>
      dsimp only [Line.eval, interpretation, Function.comp_apply, Wire.elim] <;> norm_num [hx]

private theorem readTwice_transcripts_card_le : (univ.image (transcript readTwice)).card ≤ 2 := by
  classical
  calc
    (univ.image (transcript readTwice)).card ≤
        (univ.image (fun b : Bool => fun _ : inputGates readTwice => b)).card :=
      card_le_card (by
        intro z hz
        obtain ⟨x, _, rfl⟩ := mem_image.mp hz
        exact mem_image.mpr ⟨x 0, mem_univ _, (congrArg
          (fun z : Fin 2 → Bool => fun i : inputGates readTwice => z i)
          (readTwice_eval x)).symm⟩)
    _ ≤ 2 := card_image_le.trans (by decide)

-- Two input-reading gates have only the equal-bit transcripts: two leaves suffice, not four.
example : (inputGates readTwice).card = 2 ∧
    ∃ t : DecisionTree (SeparableComparison (Fin 1 → Bool) (Fin 0 → Bool)) Bool,
      (∀ x y, t.eval (fun q => q.eval x y) = x 0) ∧ t.depth ≤ 2 ∧ t.leafCount ≤ 2 := by
  classical
  have hg : inputGates readTwice = univ := by
    ext gate
    simp only [mem_inputGates, mem_univ, iff_true]
    refine ⟨0, ?_⟩
    fin_cases gate <;>
      change lineWeight (⟨⟨1, fun _ => 1, 1⟩, fun _ => .input 0⟩ : Line signature 1 2)
        (.input 0) ≠ 0
    all_goals dsimp only [lineWeight]; norm_num
  obtain ⟨t, ht, hd, hl⟩ := exists_gate_readout_tree readTwice
    (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1).symm (fun z => z 1)
  refine ⟨by simp [hg], t, ?_, by simpa only [hg, card_univ, Fintype.card_fin] using hd,
    hl.trans readTwice_transcripts_card_le⟩
  · intro x y
    rw [ht, readTwice_eval]
    rfl

private def andCircuit : Circuit signature 2 1 :=
  ⟨Program.empty.gate ⟨⟨2, fun _ => 1, 2⟩, Wire.input⟩, fun _ => .gate 0⟩

-- The final native-circuit endpoint computes both-sided conjunction, including threshold ties.
example : ∃ t : DecisionTree (SeparableComparison (Fin 1 → Bool) (Fin 1 → Bool)) (Fin 1 → Bool),
    ∀ x y, t.eval (fun q => q.eval x y) 0 = (x 0 && y 0) := by
  obtain ⟨t, ht, _, _⟩ := exists_circuit_tree andCircuit
    (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm
    (fun _ => ⟨(0 : Fin 1), rfl⟩)
  refine ⟨t, fun x y => ?_⟩
  rw [ht]
  change (Program.empty.gate _).eval interpretation (inputOfSplit _ x y) (Fin.last 0) = _
  rw [Program.eval_gate_last]
  cases hx : x 0 <;> cases hy : y 0 <;>
    dsimp only [Line.eval, interpretation, Function.comp_apply, Wire.elim] <;>
    norm_num [Fin.sum_univ_two, inputOfSplit, finSumFinEquiv, Fin.addCases, hx, hy]

-- Noninjective query relabeling keeps unreachable branches rather than silently pruning them.
private def repeatedQueries : DecisionTree Bool Nat :=
  .node false (.leaf 0) (.node true (.leaf 1) (.leaf 2))

example : (repeatedQueries.mapQueries (fun _ => ())).depth = 2 ∧
    (repeatedQueries.mapQueries (fun _ => ())).leafCount = 3 ∧
    ∀ b, (repeatedQueries.mapQueries (fun _ => ())).eval (fun _ => b) = if b then 2 else 0 := by
  refine ⟨rfl, rfl, ?_⟩
  intro b
  cases b <;> rfl

example {ι : Type u} {κ : Type v} {β : Type w} (f : ι → κ)
    (t : DecisionTree ι β) (x : κ → Bool) :
    (t.mapQueries f).eval x = t.eval (x ∘ f) ∧
    (t.mapQueries f).depth = t.depth ∧ (t.mapQueries f).leafCount = t.leafCount :=
  ⟨DecisionTree.eval_mapQueries f t x, DecisionTree.depth_mapQueries f t,
    DecisionTree.leafCount_mapQueries f t⟩

-- The existing public comparison has exactly its former scores and threshold.
example {n g : Nat} {L R : Type*} [Fintype L] [Fintype R]
    (p : Program signature n g) (split : Fin n ≃ L ⊕ R) (gate : Fin g)
    (previous : Fin g → Bool) :
    gateComparison p split gate previous =
      ⟨(fun x => ∑ i, inputWeight p gate (split.symm (.inl i)) * (x i).toNat),
       (fun y => ∑ i, inputWeight p gate (split.symm (.inr i)) * (y i).toNat),
       (p.lines gate).op.threshold - ∑ j, gateWeight p gate j * (previous j).toNat⟩ := by
  have hweight (w : Fin n → ℝ) (c : ℝ) (i : Fin n) :
      lineWeight (⟨⟨n, w, c⟩, Wire.input⟩ : Line signature n 0) (.input i) = w i := by
    change (∑ a : Fin n with Wire.input a = (Wire.input i : Wire n 0), w a) = w i
    simp [Finset.sum_filter]
  simp only [gateComparison, lineComparison, gateQuery, hweight]

-- The native-line conversion also handles repeated slots and exact threshold ties directly.
private def cancellingQuery : Line signature 1 0 :=
  ⟨⟨2, ![1, -1], 0⟩, fun _ => .input 0⟩

example (x : Fin 1 → Bool) : cancellingQuery.eval interpretation x Fin.elim0 = true := by
  dsimp only [cancellingQuery, Line.eval, interpretation, Function.comp_apply, Wire.elim]
  simp [Fin.sum_univ_two]

example (x : Fin 1 → Bool) (y : Fin 0 → Bool) :
    (lineComparison cancellingQuery (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1).symm).eval x y =
      true := by
  rw [lineComparison_eval]
  dsimp only [cancellingQuery, Line.eval, interpretation, Function.comp_apply, Wire.elim]
  simp [Fin.sum_univ_two]

-- The new endpoint exposes actual linear queries, even on the zero-dimensional cube.
example : ∃ t : DecisionTree (Line signature 0 0) Bool,
    (∀ x, t.eval (fun q => q.eval interpretation x Fin.elim0) = true) ∧
      t.depth = 0 ∧ t.leafCount = 1 := by
  classical
  obtain ⟨t, ht, hd, hl⟩ := exists_linear_transcript_tree nullary
    (fun x => nullary.eval interpretation x 0)
    (fun _ _ h => congrFun (eval_eq_of_transcript_eq nullary h) 0)
  have hg : inputGates nullary = ∅ := by ext i; simp
  refine ⟨t, ?_, Nat.eq_zero_of_le_zero (by simpa only [hg, card_empty] using hd),
    Nat.le_antisymm (hl.trans (card_image_le.trans (by decide))) t.leafCount_pos⟩
  intro x
  rw [ht]
  change (Program.empty.gate _).eval interpretation x (Fin.last 0) = true
  rw [Program.eval_gate_last]
  norm_num [Line.eval, interpretation]

-- A native linear-query tree computes the same nonconstant circuit before choosing any split.
example : ∃ t : DecisionTree (Line signature 2 0) (Fin 1 → Bool),
    (∀ x, t.eval (fun q => q.eval interpretation x Fin.elim0) = andCircuit.eval interpretation x) ∧
    t.depth ≤ 1 ∧ t.leafCount ≤ 2 := by
  classical
  obtain ⟨t, ht, hd, hl⟩ := exists_linear_transcript_tree andCircuit.program
    (andCircuit.eval interpretation)
    (fun _ _ h => circuit_eval_eq_of_transcript_eq andCircuit
      (fun _ => ⟨(0 : Fin 1), rfl⟩) h)
  refine ⟨t, ht, hd.trans (card_le_card (subset_univ _)), hl.trans ?_⟩
  have hcard : Fintype.card (inputGates andCircuit.program) ≤ 1 := by
    change Fintype.card (inputGates andCircuit.program) ≤ andCircuit.size
    simpa only [Fintype.card_coe, card_univ, Fintype.card_fin] using
      card_le_card (subset_univ (inputGates andCircuit.program))
  exact (card_le_card (subset_univ _)).trans (by
    simpa only [card_univ, Fintype.card_fun, Fintype.card_bool, pow_one] using
      (Nat.pow_le_pow_right two_pos hcard))

-- The native-query endpoint also keeps the attained-pattern bound of two, below 2^2.
example : ∃ t : DecisionTree (Line signature 1 0) Bool,
    (∀ x, t.eval (fun q => q.eval interpretation x Fin.elim0) = x 0) ∧
      t.depth ≤ 2 ∧ t.leafCount ≤ 2 := by
  classical
  obtain ⟨t, ht, hd, hl⟩ := exists_linear_transcript_tree readTwice
    (fun x => readTwice.eval interpretation x 1)
    (fun _ _ h => congrFun (eval_eq_of_transcript_eq readTwice h) 1)
  refine ⟨t, ?_, hd.trans (card_le_card (subset_univ _)), hl.trans readTwice_transcripts_card_le⟩
  intro x
  rw [ht, readTwice_eval]

-- Free input outputs cannot acquire a zero-depth certificate from an empty transcript.
example : ¬ ∃ t : DecisionTree (Line signature 1 0) Bool,
    t.depth ≤ (inputGates (Program.empty : Program signature 1 0)).card ∧
      ∀ x, t.eval (fun q => q.eval interpretation x Fin.elim0) = x 0 := by
  rintro ⟨t, hd, ht⟩
  have hg : inputGates (Program.empty : Program signature 1 0) = ∅ :=
    Finset.eq_empty_of_forall_notMem (fun i => Fin.elim0 i)
  have hd' : t.depth = 0 := Nat.eq_zero_of_le_zero (by simpa only [hg, card_empty] using hd)
  cases t with
  | leaf b =>
    have hf := ht fun _ => false
    have ht := ht fun _ => true
    exact Bool.false_ne_true (hf.symm.trans ht)
  | node q left right => simp [DecisionTree.depth] at hd'

end ThresholdTranscriptTests
