/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold
import Complexity.Computability.DecisionTree.Observations
public import Complexity.Computability.DecisionTree.Separable
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max

/-!
# Weighted threshold transcripts as linear-query trees

A native weighted threshold program has a decision tree whose queries are native threshold
lines reading only original inputs. It computes any output determined by the restricted
transcript, has depth at most the number of input-reading gates, and has at most as many leaves
as attained transcripts. Only nonempty answer branches are constructed.

The same tree gives a separable comparison tree for every split of the input coordinates by
relabeling its queries. This preserves its exact structural depth and leaf count. All threshold
comparisons retain the convention that equality returns `true`.

This construction is semantic and noncomputable; no efficient compiler is asserted.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.gateQuery`: a native input-only threshold line,
  with fixed earlier gate contributions absorbed into its threshold.
* `Cslib.Circuits.Boolean.WeightedThreshold.inputOfSplit`: assemble the two sides of an input.
* `Cslib.Circuits.Boolean.WeightedThreshold.lineComparison`: express an input-only threshold
  line as a separable comparison across a coordinate split.
* `Cslib.Circuits.Boolean.WeightedThreshold.gateComparison`: express a gate query with fixed earlier
  gate values as a separable comparison across a coordinate split.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.exists_linear_transcript_tree`: a transcript
  determines a tree of native linear threshold queries, independent of any coordinate split.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_transcript_tree`: the corresponding
  separable comparison tree for any split.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_gate_readout_tree`: every fixed readout of
  the complete gate valuation is covered.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_circuit_tree`: designated gate outputs are
  computed simultaneously.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Lemma 3.1]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

variable {n g : ℕ} {β : Type*}

/-- With preceding gate values fixed, a gate is a native threshold line on original inputs.
Its coefficients are aggregated by actual input wire, so cancelled slots contribute zero. -/
def gateQuery (p : Program signature n g) (gate : Fin g) (previous : Fin g → Bool) :
    Line signature n 0 :=
  ⟨⟨n, inputWeight p gate,
    (p.lines gate).op.threshold - ∑ j, gateWeight p gate j * (previous j).toNat⟩, Wire.input⟩

/-- Earlier gate values suffice to evaluate the input-only query; current and later values
do not affect it because their coefficients vanish. -/
theorem gateQuery_eval_eq (p : Program signature n g) (gate : Fin g)
    (previous : Fin g → Bool) (x : Fin n → Bool)
    (hprevious : ∀ j < gate, previous j = p.eval interpretation x j) :
    (gateQuery p gate previous).eval interpretation x Fin.elim0 =
      p.eval interpretation x gate := by
  have hsum : (∑ j, gateWeight p gate j * (previous j).toNat) =
      ∑ j, gateWeight p gate j * (p.eval interpretation x j).toNat := by
    apply sum_congr rfl
    intro j _
    by_cases hj : j < gate
    · rw [hprevious j hj]
    · rw [gateWeight_eq_zero_of_le p gate j (le_of_not_gt hj)]
      simp
  rw [eval_gate_eq p x gate]
  change decide ((p.lines gate).op.threshold - ∑ j, gateWeight p gate j * (previous j).toNat ≤
    ∑ i, inputWeight p gate i * (x i).toNat) = _
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, hsum, sub_le_iff_le_add]

private theorem exists_varying_query (p : Program signature n g)
    (S : Finset (Fin n → Bool)) (hS : S.Nonempty)
    (hne : ∃ x ∈ S, ∃ y ∈ S, transcript p x ≠ transcript p y) :
    ∃ (q : Line signature n 0) (i : inputGates p),
      (∀ x ∈ S, q.eval interpretation x Fin.elim0 = transcript p x i) ∧
      ∀ b : Bool, (S.filter fun x => transcript p x i = b).Nonempty := by
  classical
  let varying : Finset (inputGates p) := univ.filter fun i =>
    ∃ x ∈ S, ∃ y ∈ S, transcript p x i ≠ transcript p y i
  have hv : varying.Nonempty := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hne
    obtain ⟨i, hi⟩ := not_forall.mp (fun h => hxy (funext h))
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, x, hx, y, hy, hi⟩⟩
  let i := varying.min' hv
  have hi : i ∈ varying := min'_mem _ _
  obtain ⟨x₀, hx₀⟩ := hS
  have hprevious (x) (hx : x ∈ S) : ∀ j : Fin g, j < i.val →
      p.eval interpretation x₀ j = p.eval interpretation x j := by
    apply eval_eq_of_forall_mem_inputGates_lt p i.val
    intro j hj hjlt
    by_contra hne
    have hjv : (⟨j, hj⟩ : inputGates p) ∈ varying :=
      mem_filter.mpr ⟨mem_univ _, x₀, hx₀, x, hx, hne⟩
    exact (not_le_of_gt hjlt) (varying.min'_le _ hjv)
  refine ⟨gateQuery p i.val (p.eval interpretation x₀), i, ?_, ?_⟩
  · intro x hx
    exact gateQuery_eval_eq p i.val _ x (hprevious x hx)
  · obtain ⟨x, hx, y, hy, hxy⟩ := (mem_filter.mp hi).2
    intro b
    by_cases hxb : transcript p x i = b
    · exact ⟨x, mem_filter.mpr ⟨hx, hxb⟩⟩
    · have hyb : transcript p y i = b := by
        cases hxi : transcript p x i <;> cases hyi : transcript p y i <;>
          cases b <;> simp_all
      exact ⟨y, mem_filter.mpr ⟨hy, hyb⟩⟩

/-- Any output determined by the restricted transcript has a native linear-query tree.
The tree is independent of coordinate splits; its leaves count only attainable transcripts. -/
theorem exists_linear_transcript_tree (p : Program signature n g)
    (output : (Fin n → Bool) → β)
    (hout : ∀ x y, transcript p x = transcript p y → output x = output y) :
    ∃ t : DecisionTree (Line signature n 0) β,
      (∀ x, t.eval (fun q => q.eval interpretation x Fin.elim0) = output x) ∧
      t.depth ≤ (inputGates p).card ∧ t.leafCount ≤ (univ.image (transcript p)).card := by
  classical
  obtain ⟨t, ht, hd, hl⟩ := DecisionTree.exists_of_observations
    (univ : Finset (Fin n → Bool)) univ_nonempty (transcript p)
    (fun (q : Line signature n 0) x => q.eval interpretation x Fin.elim0) output
    (fun _ _ _ _ h => hout _ _ h)
    (fun S _ hS hne => exists_varying_query p S hS hne)
  exact ⟨t, fun x => ht x (mem_univ _), by simpa only [Fintype.card_coe] using hd, hl⟩

variable {L R : Type*} [Fintype L] [Fintype R]

/-- Assemble the left and right input coordinates using their partition equivalence. -/
def inputOfSplit (split : Fin n ≃ L ⊕ R) (x : L → Bool) (y : R → Bool) : Fin n → Bool :=
  Sum.elim x y ∘ split

/-- A native input-only threshold line is separable across every coordinate split.
Repeated argument slots are aggregated by actual input wire. -/
def lineComparison (q : Line signature n 0) (split : Fin n ≃ L ⊕ R) :
    SeparableComparison (L → Bool) (R → Bool) where
  left x := ∑ i, lineWeight q (.input (split.symm (.inl i))) * (x i).toNat
  right y := ∑ i, lineWeight q (.input (split.symm (.inr i))) * (y i).toNat
  threshold := q.op.threshold

/-- Splitting a native input-only line preserves its answer, including threshold equality. -/
theorem lineComparison_eval (q : Line signature n 0) (split : Fin n ≃ L ⊕ R)
    (x : L → Bool) (y : R → Bool) :
    (lineComparison q split).eval x y =
      q.eval interpretation (inputOfSplit split x y) Fin.elim0 := by
  rw [line_eval_eq]
  simp only [Fintype.sum_empty, add_zero]
  rw [← split.symm.sum_comp (fun i =>
    lineWeight q (.input i) * ((inputOfSplit split x y i).toNat : ℝ)), Fintype.sum_sum_type]
  simp only [SeparableComparison.eval, lineComparison, inputOfSplit, Function.comp_apply,
    Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr]
  rfl

/-- With preceding gate values fixed, the remaining gate equation is a separable comparison
of its direct input contributions. -/
def gateComparison (p : Program signature n g) (split : Fin n ≃ L ⊕ R) (gate : Fin g)
    (previous : Fin g → Bool) : SeparableComparison (L → Bool) (R → Bool) :=
  lineComparison (gateQuery p gate previous) split

/-- Earlier gate values suffice to evaluate the comparison; current and later values do not
affect it because their coefficients vanish. -/
theorem gateComparison_eval_eq (p : Program signature n g) (split : Fin n ≃ L ⊕ R)
    (gate : Fin g) (previous : Fin g → Bool) (x : L → Bool) (y : R → Bool)
    (hprevious : ∀ j < gate,
      previous j = p.eval interpretation (inputOfSplit split x y) j) :
    (gateComparison p split gate previous).eval x y =
      p.eval interpretation (inputOfSplit split x y) gate :=
  (lineComparison_eval _ split x y).trans (gateQuery_eval_eq p gate previous _ hprevious)

omit [Fintype L] [Fintype R] in
/-- Any output determined by the restricted transcript has a separable comparison tree of
depth at most the input-reading count and with at most one leaf per attainable transcript. -/
theorem exists_transcript_tree (p : Program signature n g) (split : Fin n ≃ L ⊕ R)
    (output : (Fin n → Bool) → β)
    (hout : ∀ x y, transcript p x = transcript p y → output x = output y) :
    ∃ t : DecisionTree (SeparableComparison (L → Bool) (R → Bool)) β,
      (∀ x y, t.eval (fun q => q.eval x y) = output (inputOfSplit split x y)) ∧
      t.depth ≤ (inputGates p).card ∧ t.leafCount ≤ (univ.image (transcript p)).card := by
  classical
  let : Fintype (L ⊕ R) := Fintype.ofEquiv (Fin n) split
  let : Fintype L := Fintype.ofInjective (Sum.inl : L → L ⊕ R) Sum.inl_injective
  let : Fintype R := Fintype.ofInjective (Sum.inr : R → L ⊕ R) Sum.inr_injective
  obtain ⟨t, ht, hd, hl⟩ := exists_linear_transcript_tree p output hout
  refine ⟨t.mapQueries (fun q => lineComparison q split), ?_,
    (DecisionTree.depth_mapQueries _ _).trans_le hd,
    (DecisionTree.leafCount_mapQueries _ _).trans_le hl⟩
  intro x y
  simpa only [DecisionTree.eval_mapQueries, Function.comp_def, lineComparison_eval] using
    ht (inputOfSplit split x y)

omit [Fintype L] [Fintype R] in
/-- A fixed readout of all native gate values satisfies the transcript-tree bounds. -/
theorem exists_gate_readout_tree (p : Program signature n g) (split : Fin n ≃ L ⊕ R)
    (readout : (Fin g → Bool) → β) :
    ∃ t : DecisionTree (SeparableComparison (L → Bool) (R → Bool)) β,
      (∀ x y, t.eval (fun q => q.eval x y) =
        readout (p.eval interpretation (inputOfSplit split x y))) ∧
      t.depth ≤ (inputGates p).card ∧ t.leafCount ≤ (univ.image (transcript p)).card :=
  exists_transcript_tree p split (fun x => readout (p.eval interpretation x))
    (fun _ _ h => congrArg readout (eval_eq_of_transcript_eq p h))

omit [Fintype L] [Fintype R] in
/-- A circuit whose outputs select gates has a comparison tree computing all designated
outputs simultaneously, under the same depth and attainable-transcript leaf bounds. -/
theorem exists_circuit_tree {m : ℕ} (c : Circuit signature n m) (split : Fin n ≃ L ⊕ R)
    (houtputs : ∀ output, ∃ gate, c.outputs output = .gate gate) :
    ∃ t : DecisionTree (SeparableComparison (L → Bool) (R → Bool)) (Fin m → Bool),
      (∀ x y, t.eval (fun q => q.eval x y) = c.eval interpretation (inputOfSplit split x y)) ∧
      t.depth ≤ (inputGates c.program).card ∧
      t.leafCount ≤ (univ.image (transcript c.program)).card :=
  exists_transcript_tree c.program split (c.eval interpretation)
    (fun _ _ h => circuit_eval_eq_of_transcript_eq c houtputs h)

end Cslib.Circuits.Boolean.WeightedThreshold
