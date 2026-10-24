/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold
public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Capacity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar-block and direction-run capacity of native weighted threshold programs

A native program gives a block decomposition by revealing its gate values in topological order.
The history is its existing gate evaluation, masked to the gates already processed. Each gate
with a nonzero effective coefficient on an original input has capacity cost four. Every other
gate has cost one, even when its output changes with earlier gate values. Repeated argument
wires are counted through their aggregated coefficients, so cancelling input weights do not
create an input-reading block.

More generally, when the gates are partitioned into `B` consecutive runs along single input
directions (`DirectionRuns`), for each fixed valuation of the gates in preceding runs, run `i`
with `rᵢ` input-reading gates has at most `2 ^ rᵢ` pieces as a function of its shared directional
projection (`piecesAtMost_evalFrom`), forming a one-dimensional block with at most `2 ^ rᵢ - 1`
changes and cost at most `4 · 2 ^ rᵢ`. This yields `2 ^ n < 16 * K ^ 2 * 2 ^ |inputGates|` (C2)
and the `B`-run bound `2 ^ n < 4 * K ^ 2 * 4 ^ B * 2 ^ |inputGates|` (C3), alongside the
multilevel threshold transition bound `2 ^ n < 4 * K ^ 2 * max 1 (4 * T)` (C2′).

The resulting capacity bounds apply to any fixed Boolean readout of the gate values. The
single-output circuit corollaries require that the output wire selects a gate: an original-input
wire is not part of this readout.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.blockDecomposition`: a native program as scalar blocks.
* `Cslib.Circuits.Boolean.WeightedThreshold.evalFrom`: gate evaluation with fixed overrides and
  parametric input contributions.
* `Cslib.Circuits.Boolean.WeightedThreshold.DirectionRuns`: a partition of the gates into
  consecutive runs along single input directions, with `DirectionRuns.size`, `gateRuns`,
  `singleRun`, and `DirectionRuns.toBlockDecomposition`.
* `Cslib.Circuits.Boolean.WeightedThreshold.multilevelDecomposition`: a multilevel threshold
  representation `F (∑ i, w i * (x i).toNat)` as a single scalar block.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.cost_blockDecomposition`: exact cost `4 ^ |inputGates|`.
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_mul_four_pow_inputGates`,
  `Cslib.Circuits.Boolean.WeightedThreshold.lt_two_mul_add_two_mul_inputGates`: the C1 bounds.
* `Cslib.Circuits.Boolean.WeightedThreshold.piecesAtMost_evalFrom`,
  `Cslib.Circuits.Boolean.WeightedThreshold.changesAtMost_evalFrom`: Lemma 2 (at most `2 ^ r`
  pieces and `2 ^ r - 1` changes for a directional run of `r` active gates with fixed prior gates).
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_direction`,
  `Cslib.Circuits.Boolean.WeightedThreshold.lt_of_direction`: the C2 single-direction bounds.
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_runs`,
  `Cslib.Circuits.Boolean.WeightedThreshold.lt_of_runs`: the C3 direction-run bounds.
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_multilevel`,
  `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_sub_lt_of_multilevel`: the C2′ multilevel
  threshold bounds.

## References

* [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*, Threshold and its internal
  lemmas][Schlesinger2026Algebraic]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

variable {n g : ℕ}

private theorem changesAtMost_threshold {H : Type*} (out : Bool → H) (c : ℝ) :
    ChangesAtMost (fun t => out (decide (c ≤ t))) 1 := by
  intro z hz S hS
  have hcut (i) (hi : i ∈ S) : z i < c ∧ c ≤ z (i + 1) := by
    have hn : ¬ c ≤ z i := by
      intro hc
      exact hS i hi (by simp [hc, hc.trans (hz (Nat.le_succ i))])
    have hp : c ≤ z (i + 1) := by
      by_contra hn'
      exact hS i hi (by simp [hn, hn'])
    exact ⟨lt_of_not_ge hn, hp⟩
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact (not_lt_of_ge ((hcut i hi).2.trans (hz h))) (hcut j hj).1
  · exact (not_lt_of_ge ((hcut j hj).2.trans (hz h))) (hcut i hi).1

private theorem masked_eval_succ (p : Program signature n g) (gate : Fin g) (x : Fin n → Bool) :
    (fun j : Fin g => if j.val < gate.val + 1 then p.eval interpretation x j else false) =
      Function.update (fun j => if j.val < gate.val then p.eval interpretation x j else false)
        gate (decide ((p.lines gate).op.threshold ≤
          (∑ i, inputWeight p gate i * (x i).toNat) +
          ∑ j, gateWeight p gate j *
            (if j.val < gate.val then p.eval interpretation x j else false).toNat)) := by
  have heval := eval_gate_eq p x gate
  have hsum : (∑ j, gateWeight p gate j * (p.eval interpretation x j).toNat) =
      ∑ j, gateWeight p gate j *
        (if j.val < gate.val then p.eval interpretation x j else false).toNat := by
    apply sum_congr rfl
    intro j _
    by_cases hj : j < gate
    · simp [hj]
    · simp [hj, gateWeight_eq_zero_of_le p gate j (le_of_not_gt hj)]
  rw [hsum] at heval
  funext j
  by_cases hj : j = gate
  · subst j
    simpa using heval
  · rw [Function.update_of_ne hj]
    have hv : j.val ≠ gate.val := fun h => hj (Fin.ext h)
    have heq : (j.val < gate.val + 1) ↔ j.val < gate.val := by omega
    simp only [heq]

private theorem masked_eval_step (p : Program signature n g) (gate : Fin g) :
    (BlockKind.oneDim (if gate ∈ inputGates p then 1 else 0)).Step
      (fun x j => if j.val < gate.val then p.eval interpretation x j else false)
      (fun x j => if j.val < gate.val + 1 then p.eval interpretation x j else false) := by
  classical
  by_cases hgate : gate ∈ inputGates p
  · simp only [hgate, ite_true, BlockKind.Step]
    refine ⟨inputWeight p gate,
      fun z t => Function.update z gate (decide ((p.lines gate).op.threshold ≤
        t + ∑ j, gateWeight p gate j * (z j).toNat)), ?_, ?_⟩
    · intro z
      exact (changesAtMost_threshold (Function.update z gate) _).comp_monotone
        (monotone_id.add_const _)
    · exact masked_eval_succ p gate
  · simp only [hgate, ite_false, BlockKind.Step]
    refine ⟨fun _ => 0,
      fun z _ => Function.update z gate (decide ((p.lines gate).op.threshold ≤
        ∑ j, gateWeight p gate j * (z j).toNat)), ?_, ?_⟩
    · intro z
      exact ChangesAtMost.const _
    · intro x
      simpa only [inputWeight_eq_zero_of_not_mem p hgate, zero_mul, sum_const_zero,
        zero_add] using masked_eval_succ p gate x

/-- Revealing the existing gate evaluation one gate at a time gives a scalar block decomposition.
The output may be any fixed Boolean readout of the gate values. -/
noncomputable def blockDecomposition (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) :
    BlockDecomposition (fun x => readout (p.eval interpretation x)) (Fin g → Bool) where
  length := g
  kind := fun i => .oneDim (if h : i < g then if ⟨i, h⟩ ∈ inputGates p then 1 else 0 else 0)
  history := fun i x j => if j.val < i then p.eval interpretation x j else false
  output := readout
  history_zero := by simp
  step := fun i hi => by simpa only [dite_eq_left hi] using masked_eval_step p ⟨i, hi⟩
  output_history := fun x => by simp

/-- Every effective input-reading gate costs four, and every other gate costs one. -/
theorem cost_blockDecomposition (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) :
    (blockDecomposition p readout).cost = 4 ^ (inputGates p).card := by
  classical
  simp only [BlockDecomposition.cost, blockDecomposition]
  rw [← Fin.prod_univ_eq_prod_range]
  simp only [dite_eq_left, Fin.isLt]
  have hcost (j : Fin g) :
      (BlockKind.oneDim (if j ∈ inputGates p then 1 else 0)).cost =
        if j ∈ inputGates p then 4 else 1 := by
    by_cases h : j ∈ inputGates p <;> simp [h, BlockKind.cost]
  simp only [hcost]
  rw [Finset.prod_ite_mem_eq]
  simp

/-- **C1 capacity bound.** Any Boolean readout of a weighted program's gate values computing a
function whose two fibers are `K`-rectangle-free satisfies this input-reading-gate bound. -/
theorem two_pow_lt_mul_four_pow_inputGates (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * 4 ^ (inputGates p).card := by
  have h := (blockDecomposition p readout).two_pow_lt_mul_cost
    (fun b => by simpa only [hreadout] using hf b)
  simpa only [cost_blockDecomposition] using h

/-- The C1 bound for a single-output circuit whose output selects a gate. -/
theorem circuit_two_pow_lt_mul_four_pow_inputGates (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) {f : Cslib.BooleanFunction n} {K : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * 4 ^ (inputGates c.program).card := by
  obtain ⟨gate, hgate⟩ := houtput
  apply two_pow_lt_mul_four_pow_inputGates c.program (fun z => z gate) ?_ hf
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

/-! ### Parametric gate evaluation and piece bounds (Lemma 2) -/

/-- The gate values when every gate in `fixed` takes the value given by `η`, and every other
gate `gate` receives the real input contribution `z gate` in place of its weighted input sum. -/
noncomputable def evalFrom (p : Program signature n g) (fixed : Finset (Fin g))
    (η : Fin g → Bool) (z : Fin g → ℝ) (gate : Fin g) : Bool :=
  if gate ∈ fixed then η gate else
    decide ((p.lines gate).op.threshold ≤ z gate +
      ∑ prior : Fin g, if _h : prior < gate then
        gateWeight p gate prior * (evalFrom p fixed η z prior).toNat else 0)
termination_by gate

private theorem evalFrom_eq (p : Program signature n g) (fixed : Finset (Fin g)) (η : Fin g → Bool)
    (z : Fin g → ℝ) (gate : Fin g) :
    evalFrom p fixed η z gate = if gate ∈ fixed then η gate else
      decide ((p.lines gate).op.threshold ≤ z gate +
        ∑ prior : Fin g, if prior < gate then
          gateWeight p gate prior * (evalFrom p fixed η z prior).toNat else 0) := by
  rw [evalFrom]
  simp only [dite_eq_ite]

/-- Overriding gates by their true values and feeding the other gates their true weighted input
sums recovers the ordinary evaluation, gate by gate. -/
theorem evalFrom_eq_eval (p : Program signature n g) {fixed : Finset (Fin g)} {η : Fin g → Bool}
    {z : Fin g → ℝ} {x : Fin n → Bool} (gate : Fin g)
    (hfix : ∀ prior ≤ gate, prior ∈ fixed → η prior = p.eval interpretation x prior)
    (hz : ∀ prior ≤ gate, prior ∉ fixed → z prior = ∑ i, inputWeight p prior i * (x i).toNat) :
    evalFrom p fixed η z gate = p.eval interpretation x gate := by
  induction gate using Fin.strong_induction_on with
  | h gate ih =>
    by_cases hgate : gate ∈ fixed
    · rw [evalFrom_eq, ite_eq_left hgate]
      exact hfix gate le_rfl hgate
    · rw [evalFrom_eq, ite_eq_right hgate, eval_gate_eq, hz gate le_rfl hgate]
      have hsum : (∑ prior : Fin g, if prior < gate then
            gateWeight p gate prior * (evalFrom p fixed η z prior).toNat else 0) =
          ∑ prior : Fin g, gateWeight p gate prior * (p.eval interpretation x prior).toNat := by
        apply sum_congr rfl
        intro prior _
        by_cases hprior : prior < gate
        · rw [ite_eq_left hprior, ih prior hprior
            (fun k hk => hfix k (hk.trans hprior.le))
            (fun k hk => hz k (hk.trans hprior.le))]
        · rw [ite_eq_right hprior, gateWeight_eq_zero_of_le p gate prior (le_of_not_gt hprior),
            zero_mul]
      rw [hsum]

/-- The values of the first `d` gates under `evalFrom`, as functions of the parameter `t`. -/
private noncomputable def prefixValues (p : Program signature n g) (fixed : Finset (Fin g))
    (η : Fin g → Bool) (slope : Fin g → ℝ) (d : ℕ) (t : ℝ) : Fin g → Bool :=
  fun gate => if gate.1 < d then evalFrom p fixed η (fun k => slope k * t) gate else false

open scoped Classical in
/-- The number of unfixed gates with a nonzero slope among the first `d` gates. -/
private noncomputable def activeCount (fixed : Finset (Fin g)) (slope : Fin g → ℝ) (d : ℕ) : ℕ :=
  (Finset.univ.filter fun gate : Fin g => gate.1 < d ∧ gate ∉ fixed ∧ slope gate ≠ 0).card

private theorem activeCount_succ (fixed : Finset (Fin g)) (slope : Fin g → ℝ) {d : ℕ}
    (j₀ : Fin g) (hj₀ : j₀.1 = d) :
    activeCount fixed slope (d + 1) = activeCount fixed slope d +
      if j₀ ∉ fixed ∧ slope j₀ ≠ 0 then 1 else 0 := by
  classical
  unfold activeCount
  split_ifs with hc
  · rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter fun j : Fin g =>
      j.1 < d ∧ j ∉ fixed ∧ slope j ≠ 0) (a := j₀) (by simp [hj₀])]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hj : j.1 = d
      · left
        exact Fin.ext (hj.trans hj₀.symm)
      · right
        exact ⟨by omega, h2, h3⟩
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · exact ⟨by omega, hc⟩
      · exact ⟨by omega, h2, h3⟩
  · rw [add_zero]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, h2, h3⟩
      by_contra hj
      have : j = j₀ := Fin.ext (by omega)
      subst this
      exact hc ⟨h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by omega, h2, h3⟩

private theorem prefixValues_succ (p : Program signature n g) (fixed : Finset (Fin g))
    (η : Fin g → Bool) (slope : Fin g → ℝ) {d : ℕ} (j₀ : Fin g) (hj₀ : j₀.1 = d) (t : ℝ) :
    prefixValues p fixed η slope (d + 1) t = Function.update (prefixValues p fixed η slope d t)
      j₀ (evalFrom p fixed η (fun k => slope k * t) j₀) := by
  funext j
  by_cases hj : j = j₀
  · subst hj
    simp [prefixValues, hj₀]
  · rw [Function.update_of_ne hj]
    have hj' : j.1 ≠ d := fun h => hj (Fin.ext (h.trans hj₀.symm))
    simp only [prefixValues]
    by_cases hlt : j.1 < d
    · rw [ite_eq_left hlt, ite_eq_left (by omega)]
    · rw [ite_eq_right hlt, ite_eq_right (by omega)]

private theorem evalFrom_next (p : Program signature n g) (fixed : Finset (Fin g))
    (η : Fin g → Bool) (slope : Fin g → ℝ) {d : ℕ} (j₀ : Fin g) (hj₀ : j₀.1 = d) (t : ℝ) :
    evalFrom p fixed η (fun k => slope k * t) j₀ =
      if j₀ ∈ fixed then η j₀ else
        decide ((p.lines j₀).op.threshold ≤ slope j₀ * t +
          ∑ k : Fin g, if k < j₀ then
            gateWeight p j₀ k * (prefixValues p fixed η slope d t k).toNat else 0) := by
  rw [evalFrom_eq]
  have hsum : (∑ k : Fin g, if k < j₀ then
      gateWeight p j₀ k * (evalFrom p fixed η (fun k => slope k * t) k).toNat else 0) =
      ∑ k : Fin g, if k < j₀ then
        gateWeight p j₀ k * (prefixValues p fixed η slope d t k).toNat else 0 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · have hk' : k.1 < d := hj₀ ▸ hk
      simp [prefixValues, hk']
    · rfl
  rw [hsum]

private theorem bool_eq_of_toNat_eq : ∀ a b : Bool, a.toNat = b.toNat → a = b := by decide

private theorem bool_eq_of_not_toNat_eq : ∀ a b : Bool, (!a).toNat = (!b).toNat → a = b := by
  decide

private theorem piecesAtMost_prefixValues (p : Program signature n g) (fixed : Finset (Fin g))
    (η : Fin g → Bool) (slope : Fin g → ℝ) (d : ℕ) :
    PiecesAtMost (prefixValues p fixed η slope d) (2 ^ activeCount fixed slope d) := by
  induction d with
  | zero =>
    refine ⟨fun _ => 0, monotone_const, fun _ => by positivity, fun t t' _ => ?_⟩
    funext j
    simp [prefixValues]
  | succ d ih =>
    by_cases hd : d < g
    swap
    · have heq : prefixValues p fixed η slope (d + 1) = prefixValues p fixed η slope d := by
        funext t j
        simp only [prefixValues]
        rw [ite_eq_left (by omega), ite_eq_left (by omega)]
      have hcount : activeCount fixed slope (d + 1) = activeCount fixed slope d := by
        unfold activeCount
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨_, h2⟩ => ⟨by omega, h2⟩, fun ⟨_, h2⟩ => ⟨by omega, h2⟩⟩
      rw [heq, hcount]
      exact ih
    obtain ⟨π, mono, lt, fac⟩ := ih
    obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin g, j₀.1 = d := ⟨⟨d, hd⟩, rfl⟩
    let F : (Fin g → Bool) → ℝ := fun v => ∑ k : Fin g,
      if k < j₀ then gateWeight p j₀ k * (v k).toNat else 0
    have hsucc := prefixValues_succ p fixed η slope j₀ hj₀
    have hnext := evalFrom_next p fixed η slope j₀ hj₀
    rw [activeCount_succ fixed slope j₀ hj₀]
    by_cases hfix : j₀ ∈ fixed
    · simp only [hfix, not_true_eq_false, false_and, ite_false, add_zero]
      refine ⟨π, mono, lt, fun t t' e => ?_⟩
      rw [hsucc t, hsucc t', fac t t' e, hnext t, hnext t', ite_eq_left hfix, ite_eq_left hfix]
    by_cases hslope : slope j₀ = 0
    · simp only [hslope, ne_eq, not_true_eq_false, and_false, ite_false, add_zero]
      refine ⟨π, mono, lt, fun t t' e => ?_⟩
      rw [hsucc t, hsucc t', hnext t, hnext t', ite_eq_right hfix, ite_eq_right hfix, hslope,
        zero_mul, zero_mul, fac t t' e]
    simp only [hfix, not_false_eq_true, hslope, ne_eq, and_self, ite_true]
    let val : ℝ → Bool := fun t => evalFrom p fixed η (fun k => slope k * t) j₀
    have hval : ∀ t, val t = decide ((p.lines j₀).op.threshold ≤ slope j₀ * t +
        F (prefixValues p fixed η slope d t)) := by
      intro t
      simp only [val, F]
      rw [hnext t, ite_eq_right hfix]
    let b : ℝ → ℕ := fun t => (if 0 < slope j₀ then val t else !val t).toNat
    have hb1 : ∀ t, b t ≤ 1 := fun t => Bool.toNat_le _
    have hbmono : ∀ t t', t ≤ t' → π t = π t' → b t ≤ b t' := by
      intro t t' htt' e
      have hv := fac t t' e
      simp only [b, hval, hv]
      by_cases hpos : 0 < slope j₀
      · simp only [hpos, ite_true]
        have : slope j₀ * t ≤ slope j₀ * t' := mul_le_mul_of_nonneg_left htt' hpos.le
        by_cases h : (p.lines j₀).op.threshold ≤
            slope j₀ * t + F (prefixValues p fixed η slope d t')
        · have h' : (p.lines j₀).op.threshold ≤
              slope j₀ * t' + F (prefixValues p fixed η slope d t') := by linarith
          simp [h, h']
        · simp [h]
      · simp only [hpos, ite_false]
        have hneg : slope j₀ < 0 := lt_of_le_of_ne (not_lt.mp hpos) hslope
        have : slope j₀ * t' ≤ slope j₀ * t := mul_le_mul_of_nonpos_left htt' hneg.le
        by_cases h : (p.lines j₀).op.threshold ≤
            slope j₀ * t' + F (prefixValues p fixed η slope d t')
        · have h' : (p.lines j₀).op.threshold ≤
              slope j₀ * t + F (prefixValues p fixed η slope d t') := by linarith
          simp [h, h']
        · simp [h, Bool.toNat_le]
    refine ⟨fun t => 2 * π t + b t, ?_, ?_, ?_⟩
    · intro t t' htt'
      rcases (mono htt').lt_or_eq with h | h
      · have := hb1 t
        simp only
        omega
      · have := hbmono t t' htt' h
        simp only
        omega
    · intro t
      have := lt t
      have := hb1 t
      change 2 * π t + b t < 2 ^ (activeCount fixed slope d + 1)
      rw [pow_succ]
      omega
    · intro t t' e
      simp only at e
      have h1 := hb1 t
      have h2 := hb1 t'
      have hπ : π t = π t' := by omega
      have hbb : b t = b t' := by omega
      have hgg : val t = val t' := by
        simp only [b] at hbb
        by_cases hpos : 0 < slope j₀
        · simp only [hpos, ite_true] at hbb
          exact bool_eq_of_toNat_eq _ _ hbb
        · simp only [hpos, ite_false] at hbb
          exact bool_eq_of_not_toNat_eq _ _ hbb
      rw [hsucc t, hsucc t', fac t t' hπ]
      exact congrArg _ hgg

open scoped Classical in
/-- **Lemma 2 (pieces of a run).** If every gate outside `fixed` receives the input contribution
`slope gate * t`, and the gates in `fixed` are set by `η`, the gate values have at most `2 ^ r`
pieces as functions of `t`, where `r` counts the gates outside `fixed` with a nonzero slope. -/
theorem piecesAtMost_evalFrom (p : Program signature n g) (fixed : Finset (Fin g))
    (η : Fin g → Bool) (slope : Fin g → ℝ) :
    PiecesAtMost (fun t => evalFrom p fixed η (fun gate => slope gate * t))
      (2 ^ (Finset.univ.filter fun gate => gate ∉ fixed ∧ slope gate ≠ 0).card) := by
  have h := piecesAtMost_prefixValues p fixed η slope g
  have heq : prefixValues p fixed η slope g =
      fun t => evalFrom p fixed η (fun gate => slope gate * t) := by
    funext t gate
    simp [prefixValues]
  have hcount : activeCount fixed slope g =
      (Finset.univ.filter fun gate => gate ∉ fixed ∧ slope gate ≠ 0).card := by
    unfold activeCount
    congr 1
    ext gate
    simp
  rw [heq, hcount] at h
  exact h

open scoped Classical in
/-- **Lemma 2, change form.** The same run of gates changes at most `2 ^ r - 1` times. -/
theorem changesAtMost_evalFrom (p : Program signature n g) (fixed : Finset (Fin g))
    (η : Fin g → Bool) (slope : Fin g → ℝ) :
    ChangesAtMost (fun t => evalFrom p fixed η (fun gate => slope gate * t))
      (2 ^ (Finset.univ.filter fun gate => gate ∉ fixed ∧ slope gate ≠ 0).card - 1) :=
  (piecesAtMost_evalFrom p fixed η slope).changesAtMost

/-! ### Direction runs and block decompositions -/

/-- A split of the gates into `B` consecutive runs, numbered by the monotone map `run`, such
that every gate of run `i` reads the inputs along the direction `dir i`: its input weight
vector is a real multiple of `dir i`. A gate that reads no input fits every direction. -/
structure DirectionRuns (p : Program signature n g) (B : ℕ) where
  /-- The run of each gate. -/
  run : Fin g → ℕ
  /-- Runs are consecutive in the gate order. -/
  monotone : Monotone run
  /-- There are at most `B` runs. -/
  run_lt : ∀ gate, run gate < B
  /-- The direction of each run. -/
  dir : ℕ → Fin n → ℝ
  /-- Every gate reads the inputs along the direction of its run. -/
  along : ∀ gate, ∃ c : ℝ, inputWeight p gate = c • dir (run gate)

open scoped Classical in
/-- The number of input-reading gates in run `i`. -/
noncomputable def DirectionRuns.size {p : Program signature n g} {B : ℕ}
    (R : DirectionRuns p B) (i : ℕ) : ℕ :=
  ((inputGates p).filter fun gate => R.run gate = i).card

/-- The sizes `R.size i` of the runs partition the input-reading gates of `p`. -/
theorem DirectionRuns.sum_size {p : Program signature n g} {B : ℕ} (R : DirectionRuns p B) :
    ∑ i ∈ Finset.range B, R.size i = (inputGates p).card := by
  classical
  unfold DirectionRuns.size
  exact (Finset.card_eq_sum_card_fiberwise
    (fun gate _ => Finset.mem_range.mpr (R.run_lt gate))).symm

/-- The split of the gates into single-gate runs, each along its own input weight vector. -/
def gateRuns (p : Program signature n g) : DirectionRuns p g where
  run gate := gate.1
  monotone := fun _ _ h => h
  run_lt gate := gate.2
  dir i := if h : i < g then inputWeight p ⟨i, h⟩ else 0
  along gate := ⟨1, by simp⟩

/-- The single run of a program whose input weight vectors are all multiples of `w`. -/
def singleRun (p : Program signature n g) (w : Fin n → ℝ)
    (along : ∀ gate, ∃ c : ℝ, inputWeight p gate = c • w) : DirectionRuns p 1 where
  run _ := 0
  monotone := monotone_const
  run_lt _ := Nat.one_pos
  dir _ := w
  along := along

/-- The slope of a gate of run `i` along the direction of the run, and zero elsewhere. -/
private noncomputable def DirectionRuns.slope {p : Program signature n g} {B : ℕ}
    (R : DirectionRuns p B) (i : ℕ) (gate : Fin g) : ℝ :=
  open scoped Classical in
  if R.run gate = i ∧ gate ∈ inputGates p then (R.along gate).choose else 0

private theorem DirectionRuns.weightedSum_eq {p : Program signature n g} {B : ℕ}
    (R : DirectionRuns p B) {i : ℕ} {gate : Fin g} (hgate : R.run gate = i) (x : Fin n → Bool) :
    (∑ input, inputWeight p gate input * (x input).toNat) =
      R.slope i gate * ∑ input, R.dir i input * (x input).toNat := by
  classical
  by_cases hm : gate ∈ inputGates p
  · subst hgate
    have hspec := fun input => congrFun (R.along gate).choose_spec input
    simp only [Pi.smul_apply, smul_eq_mul] at hspec
    simp only [DirectionRuns.slope, hm, and_self, ite_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun input _ => ?_
    rw [hspec input, mul_assoc]
  · simp [DirectionRuns.slope, hm, inputWeight_eq_zero_of_not_mem p hm]

/-- The block decomposition of a program along a split into direction runs: the history after
`i` blocks holds the values of the gates of the first `i` runs, and the output applies `readout`
to the complete gate valuation. -/
noncomputable def DirectionRuns.toBlockDecomposition (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {B : ℕ} (R : DirectionRuns p B) :
    BlockDecomposition (fun x => readout (p.eval interpretation x)) (Fin g → Bool) where
  length := B
  kind i := .oneDim (2 ^ R.size i - 1)
  history i x := fun gate => if R.run gate < i then p.eval interpretation x gate else false
  output := readout
  history_zero x y := by
    funext gate
    simp
  step i _ := by
    classical
    let fixed : Finset (Fin g) := Finset.univ.filter fun gate => R.run gate < i
    refine ⟨R.dir i, fun η t gate => if R.run gate < i + 1 then
      evalFrom p fixed η (fun k => R.slope i k * t) gate else false, ?_, ?_⟩
    · intro η
      have hp := (piecesAtMost_evalFrom p fixed η (R.slope i)).comp
        (fun v gate => if R.run gate < i + 1 then v gate else false)
      have hcount : (Finset.univ.filter fun gate => gate ∉ fixed ∧ R.slope i gate ≠ 0).card ≤
          R.size i := by
        unfold DirectionRuns.size
        apply Finset.card_le_card
        intro gate hgate
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hgate ⊢
        have hc : R.run gate = i ∧ gate ∈ inputGates p := by
          by_contra hc
          exact hgate.2 (ite_eq_right hc)
        exact ⟨hc.2, hc.1⟩
      exact (hp.mono (Nat.pow_le_pow_right Nat.two_pos hcount)).changesAtMost
    · intro x
      funext gate
      by_cases hgate : R.run gate < i + 1
      · simp only [hgate, ite_true]
        symm
        apply evalFrom_eq_eval
        · intro prior _ hpf
          simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and] at hpf
          simp [hpf]
        · intro prior hle hpf
          simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hpf
          have hrun : R.run prior = i := by
            have := R.monotone hle
            omega
          exact (R.weightedSum_eq hrun x).symm
      · simp [hgate]
  output_history x := by
    congr 1
    funext gate
    simp [R.run_lt gate]

private theorem DirectionRuns.cost_toBlockDecomposition (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {B : ℕ} (R : DirectionRuns p B) :
    (R.toBlockDecomposition p readout).cost =
      ∏ i ∈ Finset.range B, (BlockKind.oneDim (2 ^ R.size i - 1)).cost :=
  rfl

/-! ### Capacity and logarithmic corollaries (C1, C2, C3, C2′) -/

private theorem two_pow_succ_le (r : ℕ) : 2 ^ (r + 1) ≤ 4 ^ r + 1 := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    have h4 : 1 ≤ 4 ^ r := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ 2 (r + 1), pow_succ 4 r]
    omega

private theorem cost_oneDim_le_four_pow (r : ℕ) : (BlockKind.oneDim (2 ^ r - 1)).cost ≤ 4 ^ r := by
  rcases r with _ | r
  · simp [BlockKind.cost]
  · have h1 : 1 < 2 ^ (r + 1) := Nat.one_lt_two_pow (by omega)
    have h2 : 2 ^ (r + 1) - 1 ≠ 0 := by omega
    have h3 := two_pow_succ_le r
    simp only [BlockKind.cost, h2, ite_false]
    rw [pow_succ 4 r]
    omega

private theorem cost_oneDim_le_four_mul (r : ℕ) :
    (BlockKind.oneDim (2 ^ r - 1)).cost ≤ 4 * 2 ^ r := by
  have := Nat.one_le_two_pow (n := r)
  simp only [BlockKind.cost]
  split_ifs <;> omega

/-- The capacity cost of `BlockKind.oneDim T` equals `max 1 (4 * T)`. -/
theorem cost_oneDim_eq_max (T : ℕ) : (BlockKind.oneDim T).cost = max 1 (4 * T) := by
  simp only [BlockKind.cost]
  split_ifs with hT
  · simp [hT]
  · omega

/-- The product of the one-dimensional block costs over all runs is at most
`4 ^ (inputGates p).card`. -/
theorem DirectionRuns.prod_cost_le_four_pow {p : Program signature n g} {B : ℕ}
    (R : DirectionRuns p B) :
    ∏ i ∈ Finset.range B, (BlockKind.oneDim (2 ^ R.size i - 1)).cost ≤
      4 ^ (inputGates p).card := by
  calc ∏ i ∈ Finset.range B, (BlockKind.oneDim (2 ^ R.size i - 1)).cost
      ≤ ∏ i ∈ Finset.range B, 4 ^ R.size i :=
        Finset.prod_le_prod fun i _ => cost_oneDim_le_four_pow _
    _ = 4 ^ (inputGates p).card := by rw [Finset.prod_pow_eq_pow_sum, R.sum_size]

private theorem DirectionRuns.prod_cost_le_four_pow_mul {p : Program signature n g} {B : ℕ}
    (R : DirectionRuns p B) :
    ∏ i ∈ Finset.range B, (BlockKind.oneDim (2 ^ R.size i - 1)).cost ≤
      4 ^ B * 2 ^ (inputGates p).card := by
  calc ∏ i ∈ Finset.range B, (BlockKind.oneDim (2 ^ R.size i - 1)).cost
      ≤ ∏ i ∈ Finset.range B, 4 * 2 ^ R.size i :=
        Finset.prod_le_prod fun i _ => cost_oneDim_le_four_mul _
    _ = 4 ^ B * 2 ^ (inputGates p).card := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        Finset.prod_pow_eq_pow_sum, R.sum_size]

/-- Binary logarithms of a capacity bound with `K ≤ 2 ^ k` and `X ≤ 2 ^ e`. -/
private theorem lt_of_two_pow_lt_mul {n k K X e : ℕ} (hK : K ≤ 2 ^ k) (hX : X ≤ 2 ^ e)
    (h : 2 ^ n < 4 * K ^ 2 * X) : n < 2 * k + 2 + e := by
  have hle : 4 * K ^ 2 * X ≤ 2 ^ (2 * k + 2 + e) := by
    calc 4 * K ^ 2 * X ≤ 4 * (2 ^ k) ^ 2 * 2 ^ e :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hK _)) hX
      _ = 2 ^ (2 * k + 2 + e) := by
          rw [pow_add, pow_add, ← pow_mul, mul_comm k 2]
          ring
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (h.trans_le hle)

/-- **Theorem U for threshold programs.** Split the gates of a threshold program into `B`
consecutive runs along single directions, with `rᵢ` input-reading gates in run `i`. Then
`2 ^ n < 4 * K ^ 2 * ∏ i, cᵢ`, where `cᵢ = 4 * (2 ^ rᵢ - 1)` if `rᵢ ≥ 1` and `cᵢ = 1`
otherwise. -/
private theorem two_pow_lt_of_directionRuns (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {B : ℕ} (R : DirectionRuns p B)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * ∏ i ∈ Finset.range B, (BlockKind.oneDim (2 ^ R.size i - 1)).cost := by
  have h := (R.toBlockDecomposition p readout).two_pow_lt_mul_cost
    (fun b => by simpa only [hreadout] using hf b)
  simpa only [DirectionRuns.cost_toBlockDecomposition] using h

/-- **C1, logarithmic form.** With `K ≤ 2 ^ k`, every threshold program computing `f` has
`n < 2 * k + 2 + 2 * |inputGates p|`. -/
theorem lt_two_mul_add_two_mul_inputGates (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hK : K ≤ 2 ^ k) (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    n < 2 * k + 2 + 2 * (inputGates p).card :=
  lt_of_two_pow_lt_mul hK (by rw [pow_mul]; norm_num)
    (two_pow_lt_mul_four_pow_inputGates p readout hreadout hf)

/-- The logarithmic C1 bound for a single-output circuit whose output selects a gate. -/
theorem circuit_lt_two_mul_add_two_mul_inputGates (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hK : K ≤ 2 ^ k) (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    n < 2 * k + 2 + 2 * (inputGates c.program).card :=
  lt_of_two_pow_lt_mul hK (by rw [pow_mul]; norm_num)
    (circuit_two_pow_lt_mul_four_pow_inputGates c houtput hcomputes hf)

/-- **C2: one direction.** If every input weight vector of a threshold program computing `f` is a
real multiple of one vector `w`, then `2 ^ n < 16 * K ^ 2 * 2 ^ |inputGates p|`. -/
theorem two_pow_lt_of_direction (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) (w : Fin n → ℝ)
    (along : ∀ gate, ∃ c : ℝ, inputWeight p gate = c • w)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 16 * K ^ 2 * 2 ^ (inputGates p).card := by
  have h := (two_pow_lt_of_directionRuns p readout (singleRun p w along) hreadout hf).trans_le
    (Nat.mul_le_mul_left _ (singleRun p w along).prod_cost_le_four_pow_mul)
  calc 2 ^ n < 4 * K ^ 2 * (4 ^ 1 * 2 ^ (inputGates p).card) := h
    _ = 16 * K ^ 2 * 2 ^ (inputGates p).card := by ring

/-- **C2, logarithmic form.** With `K ≤ 2 ^ k`, a threshold program computing `f` whose input
weight vectors are all multiples of one vector has `n < 2 * k + 4 + |inputGates p|`. -/
theorem lt_of_direction (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) (w : Fin n → ℝ)
    (along : ∀ gate, ∃ c : ℝ, inputWeight p gate = c • w)
    {f : Cslib.BooleanFunction n} {K k : ℕ} (hK : K ≤ 2 ^ k)
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    n < 2 * k + 4 + (inputGates p).card := by
  have h := two_pow_lt_of_direction p readout w along hreadout hf
  have := lt_of_two_pow_lt_mul (n := n) (X := 4 * 2 ^ (inputGates p).card)
    (e := (inputGates p).card + 2) hK (by rw [pow_add]; omega) (h.trans_eq (by ring))
  omega

/-- The C2 single-direction bound for a single-output circuit whose output selects a gate. -/
theorem circuit_two_pow_lt_of_direction (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) (w : Fin n → ℝ)
    (along : ∀ gate, ∃ a : ℝ, inputWeight c.program gate = a • w)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 16 * K ^ 2 * 2 ^ (inputGates c.program).card := by
  obtain ⟨gate, hgate⟩ := houtput
  apply two_pow_lt_of_direction c.program (fun z => z gate) w along ?_ hf
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

/-- The logarithmic C2 single-direction bound for a single-output circuit whose output selects a
gate. -/
theorem circuit_lt_of_direction (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) (w : Fin n → ℝ)
    (along : ∀ gate, ∃ a : ℝ, inputWeight c.program gate = a • w)
    {f : Cslib.BooleanFunction n} {K k : ℕ} (hK : K ≤ 2 ^ k)
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    n < 2 * k + 4 + (inputGates c.program).card := by
  obtain ⟨gate, hgate⟩ := houtput
  apply lt_of_direction c.program (fun z => z gate) w along hK ?_ hf
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

/-- **C3: direction runs.** If the gates of a threshold program computing `f` split into `B`
consecutive runs along single directions, then `2 ^ n < 4 * K ^ 2 * 4 ^ B * 2 ^ |inputGates p|`. -/
theorem two_pow_lt_of_runs (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {B : ℕ} (R : DirectionRuns p B)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * 4 ^ B * 2 ^ (inputGates p).card := by
  have h := (two_pow_lt_of_directionRuns p readout R hreadout hf).trans_le
    (Nat.mul_le_mul_left _ R.prod_cost_le_four_pow_mul)
  calc 2 ^ n < 4 * K ^ 2 * (4 ^ B * 2 ^ (inputGates p).card) := h
    _ = 4 * K ^ 2 * 4 ^ B * 2 ^ (inputGates p).card := by ring

/-- **C3, logarithmic form.** With `K ≤ 2 ^ k` and `B` direction runs,
`n < 2 * k + 2 + 2 * B + |inputGates p|`. -/
theorem lt_of_runs (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {B : ℕ} (R : DirectionRuns p B)
    {f : Cslib.BooleanFunction n} {K k : ℕ} (hK : K ≤ 2 ^ k)
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    n < 2 * k + 2 + 2 * B + (inputGates p).card := by
  have h := two_pow_lt_of_runs p readout R hreadout hf
  have := lt_of_two_pow_lt_mul (n := n) (X := 4 ^ B * 2 ^ (inputGates p).card)
    (e := 2 * B + (inputGates p).card) hK (by rw [pow_add, pow_mul]; norm_num)
    (h.trans_eq (by ring))
  omega

/-- The C3 direction-run bound for a single-output circuit whose output selects a gate. -/
theorem circuit_two_pow_lt_of_runs (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) {B : ℕ} (R : DirectionRuns c.program B)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * 4 ^ B * 2 ^ (inputGates c.program).card := by
  obtain ⟨gate, hgate⟩ := houtput
  apply two_pow_lt_of_runs c.program (fun z => z gate) R ?_ hf
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

/-- The logarithmic C3 direction-run bound for a single-output circuit whose output selects a
gate. -/
theorem circuit_lt_of_runs (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) {B : ℕ} (R : DirectionRuns c.program B)
    {f : Cslib.BooleanFunction n} {K k : ℕ} (hK : K ≤ 2 ^ k)
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    n < 2 * k + 2 + 2 * B + (inputGates c.program).card := by
  obtain ⟨gate, hgate⟩ := houtput
  apply lt_of_runs c.program (fun z => z gate) R hK ?_ hf
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

/-- The one-block decomposition of a multilevel threshold function `F (∑ i, w i * (x i).toNat)`. -/
def multilevelDecomposition {f : Cslib.BooleanFunction n} (w : Fin n → ℝ) (F : ℝ → Bool) {T : ℕ}
    (hF : ChangesAtMost F T) (hfF : ∀ x, f x = F (∑ i, w i * (x i).toNat)) :
    BlockDecomposition f Bool where
  length := 1
  kind _ := .oneDim T
  history i x := if i = 0 then false else F (∑ j, w j * (x j).toNat)
  output := id
  history_zero _ _ := rfl
  step _ _ := ⟨w, fun _ t => F t, fun _ => hF, fun x => by simp⟩
  output_history x := by simp [hfF x]

/-- **C2′: multilevel threshold representations.** If `f x = F (∑ i, w i * (x i).toNat)` for a
function `F` changing at most `T` times, then `2 ^ n < 4 * K ^ 2 * max 1 (4 * T)`. -/
theorem two_pow_lt_of_multilevel {f : Cslib.BooleanFunction n} {K : ℕ}
    (w : Fin n → ℝ) (F : ℝ → Bool) {T : ℕ} (hF : ChangesAtMost F T)
    (hfF : ∀ x, f x = F (∑ i, w i * (x i).toNat))
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * max 1 (4 * T) := by
  have h := (multilevelDecomposition w F hF hfF).two_pow_lt_mul_cost hf
  simpa [BlockDecomposition.cost, multilevelDecomposition, cost_oneDim_eq_max] using h

/-- **C2′, logarithmic form.** With `K ≤ 2 ^ k` and `2 * k + 4 ≤ n`, a multilevel threshold
representation `f x = F (∑ i, w i * (x i).toNat)` needs more than `2 ^ (n - (2 * k + 4))`
transitions. -/
theorem two_pow_sub_lt_of_multilevel {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hK : K ≤ 2 ^ k) (w : Fin n → ℝ) (F : ℝ → Bool) {T : ℕ} (hF : ChangesAtMost F T)
    (hfF : ∀ x, f x = F (∑ i, w i * (x i).toNat))
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) (hn : 2 * k + 4 ≤ n) :
    2 ^ (n - (2 * k + 4)) < T := by
  have h := two_pow_lt_of_multilevel w F hF hfF hf
  by_contra hT
  push Not at hT
  have hX : max 1 (4 * T) ≤ 2 ^ (n - (2 * k + 2)) := by
    have h1 : 1 ≤ 2 ^ (n - (2 * k + 2)) := Nat.one_le_two_pow
    have h2 : 4 * T ≤ 2 ^ (n - (2 * k + 2)) := by
      have : 2 ^ (n - (2 * k + 2)) = 4 * 2 ^ (n - (2 * k + 4)) := by
        rw [show n - (2 * k + 2) = (n - (2 * k + 4)) + 2 by omega, pow_add]
        ring
      omega
    exact max_le h1 h2
  have := lt_of_two_pow_lt_mul hK hX h
  omega

end Cslib.Circuits.Boolean.WeightedThreshold
