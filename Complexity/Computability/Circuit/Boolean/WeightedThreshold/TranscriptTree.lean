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
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Threshold transcript trees and native scalar stages

A native weighted threshold program has a decision tree whose queries are native threshold
lines reading only original inputs. It computes any output determined by the restricted
transcript, has depth at most the number of input-reading gates, and has at most as many leaves
as attained transcripts. Only nonempty answer branches are constructed.

The same tree gives a separable comparison tree for every split of the input coordinates by
relabeling its queries. This preserves its exact structural depth and leaf count. All threshold
comparisons retain the convention that equality returns `true`.

The circuit-to-tree construction is semantic and noncomputable; no efficient compiler is asserted.

In the other direction, `ScalarStage.append` emits a native adaptive scalar stage: one input-free
indicator per supplied history pattern followed by one scalar query. A unique matching pattern
selects its threshold; no match selects a baseline that can pad a terminated path with `false`.
Earlier gate values and input coefficients are preserved. The helpers add no input-reading gates,
and the query adds exactly one when its direct input vector is nonzero. With zero direct vector,
zero selected thresholds and baseline one, the same stage recognizes whether any supplied pattern
matches. These are stage-local results, not yet a whole-tree compiler or its global size/activity
bound.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.gateQuery`: a native input-only threshold line,
  with fixed earlier gate contributions absorbed into its threshold.
* `Cslib.Circuits.Boolean.WeightedThreshold.inputOfSplit`: assemble the two sides of an input.
* `Cslib.Circuits.Boolean.WeightedThreshold.lineComparison`: express an input-only threshold
  line as a separable comparison across a coordinate split.
* `Cslib.Circuits.Boolean.WeightedThreshold.gateComparison`: express a gate query with fixed earlier
  gate values as a separable comparison across a coordinate split.
* `Cslib.Circuits.Boolean.WeightedThreshold.ScalarStage.prefixLine`, `.prefixBank`, `.queryLine`,
  `.append`: native prefix indicators, their bank, a scalar query, and an adaptive stage.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.gateComparison_eval_eq`,
  `Cslib.Circuits.Boolean.WeightedThreshold.gateQuery_eval_eq`: earlier gate values suffice to
  evaluate comparisons and queries.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_linear_transcript_tree`: a transcript
  determines a tree of native linear threshold queries, independent of any coordinate split.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_transcript_tree`: the corresponding
  separable comparison tree for any split.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_gate_readout_tree`: every fixed readout of
  the complete gate valuation is covered.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_circuit_tree`: designated gate outputs are
  computed simultaneously.
* `Cslib.Circuits.Boolean.WeightedThreshold.ScalarStage.prefixLine_eval`, `.eval_append_last`,
  `.eval_append_of_match`, `.eval_append_of_no_match`: indicator, selection and padding semantics.
* `Cslib.Circuits.Boolean.WeightedThreshold.ScalarStage.eval_append_readout`: the same constructor
  realizes the OR of its supplied pattern indicators without reading original inputs.
* `Cslib.Circuits.Boolean.WeightedThreshold.ScalarStage.eval_append_castSucc`,
  `.inputWeight_append_castSucc`, `.inputWeight_append_flag`, `.inputWeight_append_last`,
  `.card_inputGates_append`: preservation and exact direct-input cost of an emitted stage.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Lemma 3.1 and the
  stage construction in the proof of Theorem 4.1][ThresholdCircuitRepresentations2026]
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

/-! ### Native scalar stages selected by transcript prefixes -/

namespace ScalarStage

variable {d m : ℕ}

/-- A single input-free gate testing whether selected earlier gates match a Boolean pattern.
The selection may repeat wires; an inconsistent pattern then evaluates to `false`. -/
def prefixLine (reads : Fin d → Fin g) (pattern : Fin d → Bool) : Line signature n g :=
  ⟨⟨d, fun j => if pattern j then 1 else -1, ∑ j, ((pattern j).toNat : ℝ)⟩,
    fun j => .gate (reads j)⟩

private theorem prefixScore_iff (pattern values : Fin d → Bool) :
    (∑ j, ((pattern j).toNat : ℝ)) ≤
        ∑ j, (if pattern j then (1 : ℝ) else -1) * (values j).toNat ↔ values = pattern := by
  have hle (j : Fin d) :
      (if pattern j then (1 : ℝ) else -1) * (values j).toNat ≤ (pattern j).toNat := by
    cases pattern j <;> cases values j <;> norm_num
  constructor
  · intro hsum
    funext j
    by_contra hne
    have hlt : (if pattern j then (1 : ℝ) else -1) * (values j).toNat <
        (pattern j).toNat := by
      cases hp : pattern j <;> cases hv : values j <;> simp_all
    have hstrict := sum_lt_sum (fun i (_ : i ∈ (univ : Finset (Fin d))) => hle i)
      ⟨j, mem_univ j, hlt⟩
    exact (not_lt_of_ge hsum) hstrict
  · intro h
    subst values
    apply le_of_eq
    apply sum_congr rfl
    intro j _
    cases pattern j <;> norm_num

/-- The prefix gate tests equality of the selected history with the pattern. -/
theorem prefixLine_eval (reads : Fin d → Fin g) (pattern : Fin d → Bool)
    (x : Fin n → Bool) (z : Fin g → Bool) :
    (prefixLine reads pattern).eval interpretation x z =
      decide ((fun j => z (reads j)) = pattern) := by
  change decide ((∑ j, ((pattern j).toNat : ℝ)) ≤
    ∑ j, (if pattern j then (1 : ℝ) else -1) * (z (reads j)).toNat) = _
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  exact prefixScore_iff pattern _

/-- Prefix indicators have no coefficient on any original input. -/
theorem prefixLine_inputWeight (reads : Fin d → Fin g) (pattern : Fin d → Bool)
    (i : Fin n) : lineWeight (prefixLine reads pattern) (.input i) = 0 := by
  simp [lineWeight, prefixLine]

/-- Append a bank of prefix indicators, all reading the original program's selected gates.
The program index charges exactly one new gate per supplied pattern. -/
def prefixBank (p : Program signature n g) (reads : Fin d → Fin g) :
    (m : ℕ) → (Fin m → Fin d → Bool) → Program signature n (g + m)
  | 0, _ => p
  | m + 1, patterns =>
      (prefixBank p reads m (fun i => patterns i.castSucc)).gate
        (prefixLine (fun j => (reads j).castAdd m) (patterns (Fin.last m)))

/-- Extending a program by a prefix bank preserves its earlier gate values. -/
theorem prefixBank_eval_castAdd (p : Program signature n g) (reads : Fin d → Fin g)
    (patterns : Fin m → Fin d → Bool) (x : Fin n → Bool) (j : Fin g) :
    (prefixBank p reads m patterns).eval interpretation x (j.castAdd m) =
      p.eval interpretation x j := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change ((prefixBank p reads m (fun i => patterns i.castSucc)).gate
      (prefixLine (fun k => (reads k).castAdd m) (patterns (Fin.last m)))).eval
        interpretation x (j.castAdd m).castSucc = _
    rw [Program.eval_gate_castSucc]
    exact ih (fun i => patterns i.castSucc)

/-- Each newly appended bank gate computes its own pattern indicator. -/
theorem prefixBank_eval_natAdd (p : Program signature n g) (reads : Fin d → Fin g)
    (patterns : Fin m → Fin d → Bool) (x : Fin n → Bool) : ∀ i : Fin m,
    (prefixBank p reads m patterns).eval interpretation x (Fin.natAdd g i) =
      decide ((fun j => p.eval interpretation x (reads j)) = patterns i) := by
  induction m with
  | zero => intro i; exact i.elim0
  | succ m ih =>
    intro i
    induction i using Fin.lastCases with
    | last =>
      change ((prefixBank p reads m (fun i => patterns i.castSucc)).gate
        (prefixLine (fun j => (reads j).castAdd m) (patterns (Fin.last m)))).eval
          interpretation x (Fin.last (g + m)) = _
      rw [Program.eval_gate_last, prefixLine_eval]
      simp only [prefixBank_eval_castAdd]
    | cast i =>
      change ((prefixBank p reads m (fun j => patterns j.castSucc)).gate
        (prefixLine (fun j => (reads j).castAdd m) (patterns (Fin.last m)))).eval
          interpretation x (Fin.natAdd g i).castSucc = _
      rw [Program.eval_gate_castSucc]
      exact ih (fun j => patterns j.castSucc) i

private theorem lineWeight_castSucc_input (line : Line signature n g) (i : Fin n) :
    lineWeight (line.mapWires Wire.Renaming.castSucc) (.input i) =
      lineWeight line (.input i) := by
  have hw (wire : Wire n g) : wire.castSucc = .input i ↔ wire = .input i := by
    cases wire <;> simp
  simp only [lineWeight, Line.mapWires_op, Line.mapWires_wires,
    Wire.Renaming.castSucc_apply, hw]
  rfl

private theorem inputWeight_gate_castSucc (p : Program signature n g)
    (line : Line signature n g) (j : Fin g) (i : Fin n) :
    inputWeight (p.gate line) j.castSucc i = inputWeight p j i := by
  simp only [inputWeight, Program.lines_gate_castSucc, lineWeight_castSucc_input]

private theorem inputWeight_gate_last (p : Program signature n g)
    (line : Line signature n g) (i : Fin n) :
    inputWeight (p.gate line) (Fin.last g) i = lineWeight line (.input i) := by
  simp only [inputWeight, Program.lines_gate_last, lineWeight_castSucc_input]

open scoped Classical in
private theorem card_inputGates_gate (p : Program signature n g) (line : Line signature n g) :
    (inputGates (p.gate line)).card = (inputGates p).card +
      if ∃ i, lineWeight line (.input i) ≠ 0 then 1 else 0 := by
  classical
  simp only [inputGates, card_filter]
  rw [Fin.sum_univ_castSucc]
  simp only [inputWeight_gate_castSucc, inputWeight_gate_last]

/-- A prefix bank preserves the effective input coefficients of every earlier gate. -/
theorem prefixBank_inputWeight_castAdd (p : Program signature n g) (reads : Fin d → Fin g)
    (patterns : Fin m → Fin d → Bool) (j : Fin g) (i : Fin n) :
    inputWeight (prefixBank p reads m patterns) (j.castAdd m) i = inputWeight p j i := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change inputWeight ((prefixBank p reads m (fun k => patterns k.castSucc)).gate
      (prefixLine (fun k => (reads k).castAdd m) (patterns (Fin.last m))))
        (j.castAdd m).castSucc i = _
    rw [inputWeight_gate_castSucc]
    exact ih (fun k => patterns k.castSucc)

/-- Every new bank gate has zero direct input vector, including with repeated history wires. -/
theorem prefixBank_inputWeight_natAdd (p : Program signature n g) (reads : Fin d → Fin g)
    (patterns : Fin m → Fin d → Bool) (i : Fin n) : ∀ j : Fin m,
    inputWeight (prefixBank p reads m patterns) (Fin.natAdd g j) i = 0 := by
  induction m with
  | zero => intro j; exact j.elim0
  | succ m ih =>
    intro j
    induction j using Fin.lastCases with
    | last =>
      change inputWeight ((prefixBank p reads m (fun k => patterns k.castSucc)).gate
        (prefixLine (fun k => (reads k).castAdd m) (patterns (Fin.last m))))
          (Fin.last (g + m)) i = 0
      rw [inputWeight_gate_last, prefixLine_inputWeight]
    | cast j =>
      change inputWeight ((prefixBank p reads m (fun k => patterns k.castSucc)).gate
        (prefixLine (fun k => (reads k).castAdd m) (patterns (Fin.last m))))
          (Fin.natAdd g j).castSucc i = 0
      rw [inputWeight_gate_castSucc]
      exact ih (fun k => patterns k.castSucc) j

/-- Appending any prefix bank adds no input-reading gates. -/
theorem card_inputGates_prefixBank (p : Program signature n g) (reads : Fin d → Fin g)
    (patterns : Fin m → Fin d → Bool) :
    (inputGates (prefixBank p reads m patterns)).card = (inputGates p).card := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [prefixBank, card_inputGates_gate]
    simp [prefixLine_inputWeight, ih]

/-- A native scalar query with direct input vector `w`, plus a weighted sum of earlier flags. -/
def queryLine (w : Fin n → ℝ) (flags : Fin m → Fin g) (adjust : Fin m → ℝ)
    (baseline : ℝ) : Line signature n g :=
  ⟨⟨n + m, Fin.addCases w adjust, baseline⟩,
    Fin.addCases Wire.input (fun j => .gate (flags j))⟩

open scoped Classical in
/-- The query line evaluates the direct input score plus its flag adjustments. -/
theorem queryLine_eval (w : Fin n → ℝ) (flags : Fin m → Fin g) (adjust : Fin m → ℝ)
    (baseline : ℝ) (x : Fin n → Bool) (z : Fin g → Bool) :
    (queryLine w flags adjust baseline).eval interpretation x z =
      decide (baseline ≤ (∑ i, w i * (x i).toNat) +
        ∑ j, adjust j * (z (flags j)).toNat) := by
  change decide (baseline ≤ ∑ a : Fin (n + m), (Fin.addCases w adjust a : ℝ) *
    ((Wire.elim x z (Fin.addCases (Wire.input : Fin n → Wire n g)
      (fun j : Fin m => Wire.gate (flags j)) a)).toNat : ℝ)) = _
  rw [Fin.sum_univ_add]
  simp

/-- The effective coefficient on an original input is exactly the supplied coefficient. -/
theorem queryLine_inputWeight (w : Fin n → ℝ) (flags : Fin m → Fin g)
    (adjust : Fin m → ℝ) (baseline : ℝ) (i : Fin n) :
    lineWeight (queryLine w flags adjust baseline) (.input i) = w i := by
  change (∑ a : Fin (n + m) with
    (Fin.addCases (Wire.input : Fin n → Wire n g)
      (fun j : Fin m => Wire.gate (flags j)) a : Wire n g) = Wire.input i,
      (Fin.addCases w adjust a : ℝ)) = w i
  rw [sum_filter, Fin.sum_univ_add]
  simp

/-- Append one adaptive scalar stage: a bank of `m` prefix indicators and one query.
A matching pattern contributes `baseline - threshold`, so a unique match selects that threshold.
No match leaves the baseline unchanged. The output gate is `Fin.last (g + m)`. -/
def append (p : Program signature n g) (reads : Fin d → Fin g)
    (patterns : Fin m → Fin d → Bool) (w : Fin n → ℝ)
    (thresholds : Fin m → ℝ) (baseline : ℝ) : Program signature n (g + m + 1) :=
  (prefixBank p reads m patterns).gate
    (queryLine w (Fin.natAdd g) (fun i => baseline - thresholds i) baseline)

/-- Appending a scalar stage preserves every earlier gate value. -/
theorem eval_append_castSucc (p : Program signature n g) (reads : Fin d → Fin g)
    (patterns : Fin m → Fin d → Bool) (w : Fin n → ℝ)
    (thresholds : Fin m → ℝ) (baseline : ℝ) (x : Fin n → Bool) (j : Fin g) :
    (append p reads patterns w thresholds baseline).eval interpretation x
        (j.castAdd m).castSucc = p.eval interpretation x j := by
  rw [append, Program.eval_gate_castSucc, prefixBank_eval_castAdd]

open scoped Classical in
/-- Exact semantics of the emitted query, without assuming distinct or reachable patterns. -/
theorem eval_append_last (p : Program signature n g) (reads : Fin d → Fin g)
    (patterns : Fin m → Fin d → Bool) (w : Fin n → ℝ)
    (thresholds : Fin m → ℝ) (baseline : ℝ) (x : Fin n → Bool) :
    (append p reads patterns w thresholds baseline).eval interpretation x (Fin.last (g + m)) =
      decide (baseline ≤ (∑ i, w i * (x i).toNat) +
        ∑ a, (baseline - thresholds a) *
          (decide ((fun j => p.eval interpretation x (reads j)) = patterns a)).toNat) := by
  rw [append, Program.eval_gate_last, queryLine_eval]
  simp only [prefixBank_eval_natAdd]

open scoped Classical in
/-- A unique matching prefix selects its threshold, with equality returning `true`. -/
theorem eval_append_of_match (p : Program signature n g) (reads : Fin d → Fin g)
    (patterns : Fin m → Fin d → Bool) (w : Fin n → ℝ)
    (thresholds : Fin m → ℝ) (baseline : ℝ) (x : Fin n → Bool) (a : Fin m)
    (hinj : Function.Injective patterns)
    (hmatch : (fun j => p.eval interpretation x (reads j)) = patterns a) :
    (append p reads patterns w thresholds baseline).eval interpretation x (Fin.last (g + m)) =
      decide (thresholds a ≤ ∑ i, w i * (x i).toNat) := by
  have hsum : (∑ b, (baseline - thresholds b) *
      (decide ((fun j => p.eval interpretation x (reads j)) = patterns b)).toNat) =
        baseline - thresholds a := by
    rw [sum_eq_single a]
    · simp [hmatch]
    · intro b _ hba
      have hne : (fun j => p.eval interpretation x (reads j)) ≠ patterns b :=
        fun h => hba (hinj (h.symm.trans hmatch))
      simp [hne]
    · intro h
      exact (h (mem_univ a)).elim
  rw [eval_append_last, hsum, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  constructor <;> intro h <;> linarith

/-- No matching live prefix pads the transcript with `false` when the score is below baseline. -/
theorem eval_append_of_no_match (p : Program signature n g) (reads : Fin d → Fin g)
    (patterns : Fin m → Fin d → Bool) (w : Fin n → ℝ)
    (thresholds : Fin m → ℝ) (baseline : ℝ) (x : Fin n → Bool)
    (hmiss : ∀ a, (fun j => p.eval interpretation x (reads j)) ≠ patterns a)
    (hscore : (∑ i, w i * (x i).toNat) < baseline) :
    (append p reads patterns w thresholds baseline).eval interpretation x (Fin.last (g + m)) =
      false := by
  rw [eval_append_last]
  simp [hmiss, not_le.mpr hscore]

open scoped Classical in
/-- With zero direct vector and selected thresholds, baseline one computes the OR of the
pattern indicators. This input-free readout uses the same stage constructor and permits
repeated patterns as well as an empty accepting bank. -/
theorem eval_append_readout (p : Program signature n g) (reads : Fin d → Fin g)
    (patterns : Fin m → Fin d → Bool) (x : Fin n → Bool) :
    (append p reads patterns (fun _ => 0) (fun _ => 0) 1).eval interpretation x
        (Fin.last (g + m)) =
      decide (∃ a, (fun j => p.eval interpretation x (reads j)) = patterns a) := by
  classical
  rw [eval_append_last, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  simp only [zero_mul, sum_const_zero, zero_add, sub_zero, one_mul]
  constructor
  · intro hs
    by_contra hn
    have hmiss (a : Fin m) : (fun j => p.eval interpretation x (reads j)) ≠ patterns a :=
      fun ha => hn ⟨a, ha⟩
    norm_num [hmiss] at hs
  · rintro ⟨a, ha⟩
    have hle := single_le_sum
      (f := fun b : Fin m =>
        ((decide ((fun j => p.eval interpretation x (reads j)) = patterns b)).toNat : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (mem_univ a)
    simpa [ha] using hle

/-- The scalar stage preserves all prior direct input coefficients. -/
theorem inputWeight_append_castSucc (p : Program signature n g) (reads : Fin d → Fin g)
    (patterns : Fin m → Fin d → Bool) (w : Fin n → ℝ)
    (thresholds : Fin m → ℝ) (baseline : ℝ) (j : Fin g) (i : Fin n) :
    inputWeight (append p reads patterns w thresholds baseline) (j.castAdd m).castSucc i =
      inputWeight p j i := by
  rw [append, inputWeight_gate_castSucc, prefixBank_inputWeight_castAdd]

/-- The helper gates of a scalar stage have zero direct input coefficients. -/
theorem inputWeight_append_flag (p : Program signature n g) (reads : Fin d → Fin g)
    (patterns : Fin m → Fin d → Bool) (w : Fin n → ℝ)
    (thresholds : Fin m → ℝ) (baseline : ℝ) (j : Fin m) (i : Fin n) :
    inputWeight (append p reads patterns w thresholds baseline) (Fin.natAdd g j).castSucc i =
      0 := by
  rw [append, inputWeight_gate_castSucc, prefixBank_inputWeight_natAdd]

/-- The new query's direct input vector is exactly `w`. -/
theorem inputWeight_append_last (p : Program signature n g) (reads : Fin d → Fin g)
    (patterns : Fin m → Fin d → Bool) (w : Fin n → ℝ)
    (thresholds : Fin m → ℝ) (baseline : ℝ) (i : Fin n) :
    inputWeight (append p reads patterns w thresholds baseline) (Fin.last (g + m)) i = w i := by
  rw [append, inputWeight_gate_last, queryLine_inputWeight]

open scoped Classical in
/-- A scalar stage adds exactly one input-reading gate when `w ≠ 0`, and none when `w = 0`.
Its program index counts `m + 1` new gates; the `m` prefix helpers are input-free. -/
theorem card_inputGates_append (p : Program signature n g) (reads : Fin d → Fin g)
    (patterns : Fin m → Fin d → Bool) (w : Fin n → ℝ)
    (thresholds : Fin m → ℝ) (baseline : ℝ) :
    (inputGates (append p reads patterns w thresholds baseline)).card =
      (inputGates p).card + if w = 0 then 0 else 1 := by
  classical
  rw [append, card_inputGates_gate, card_inputGates_prefixBank]
  simp only [queryLine_inputWeight]
  by_cases h : w = 0
  · simp [h]
  · have hex : ∃ i, w i ≠ 0 := by
      by_contra hn
      apply h
      funext i
      by_contra hi
      exact hn ⟨i, hi⟩
    simp [h, hex]

end ScalarStage

end Cslib.Circuits.Boolean.WeightedThreshold
