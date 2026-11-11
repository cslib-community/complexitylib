/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.RatBinary
public import CslibFrontier.Probability.StochasticOracle.PartialCoverThreshold
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.IterateWhile
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Mathlib.Tactic

/-!
# Native exact repetition-threshold search

Theorem 4 of [Wang2027] (PDF pp. 10–11) uses the least exponent with `q^r ≤ δ`.
The native loop multiplies exact binary rationals and tests the budget after each
multiplication. Its round count and intermediate bit lengths are derived from
that least exponent; no supplied stopping time or runtime certificate is input.
This addresses threshold computation, not the remaining native greedy scan.

## Main definitions

* `Parameters`, `encoding`: binary rational failure probability and budget.
* `State`, `stateEncoding`, `step`: runtime power and unary index, including original data.

## Main results

* `uniform_threshold`: one native threshold machine with derived time and space bounds.
* `count_eq_repetitions`: its output is the exact source logarithmic ceiling.
-/

public section
namespace Cslib.Probability.StochasticOracle.PartialCover.ThresholdNative
open Instance Turing.MultiTapeTM

/-- Runtime probability and risk budget; both rational magnitudes are binary. -/
structure Parameters where
  /-- Per-call failure probability. -/
  q : ℚ
  /-- Positive failure budget, including budgets at least one. -/
  budget : ℚ
  deriving DecidableEq

/-- Binary rational probability followed by binary rational budget, the former framed. -/
enc_structure encoding : Parameters where q : encRatBin, budget : encRatBin

/-- Source parameter conditions, separate from all resource conclusions. -/
structure Valid (p : Parameters) : Prop where
  /-- Positive failure probability. -/
  q_pos : 0 < p.q
  /-- Failure is strictly below certainty. -/
  q_lt_one : p.q < 1
  /-- Positive risk budget. -/
  budget_pos : 0 < p.budget

/-- The source domain on which the power search terminates. -/
abbrev Input := {p : Parameters // Valid p}

/-- The same probability/budget bytes; domain proofs have no runtime encoding. -/
abbrev inputEncoding : Input ↪ List Bool :=
  ⟨fun x => encoding x.val, fun _ _ h => Subtype.ext (encoding.injective h)⟩

/-- Actual runtime data. The index is unary because the source bound is polynomial
in the numerical repetition count, rather than its binary length. -/
structure State where
  /-- Original probability and budget, preserved by every multiplication. -/
  parameters : Parameters
  /-- Current exact power of the failure probability. -/
  power : ℚ
  /-- Number of performed multiplications. -/
  index : ℕ
  deriving DecidableEq

/-- Framed original data, framed binary power, then the unary index. -/
enc_structure stateEncoding : State where
  parameters : encoding, power : encRatBin, index : encUnary

/-- Start at exponent zero, including the zero-repetition case. -/
@[expose] def initial (p : Parameters) : Option State := some ⟨p, 1, 0⟩

/-- Stop on the first budget-satisfying exact power; otherwise multiply once. -/
@[expose] def step (state : Option State) : Option State :=
  state.elim none fun s =>
    if s.power ≤ s.parameters.budget then none
    else some ⟨s.parameters, s.power * s.parameters.q, s.index + 1⟩

/-- Read the last pre-stop index. -/
@[expose] def finish (state : Option State) : ℕ := state.elim 0 State.index

/-- The minimal exponent is computed by the existing exact rational search. -/
@[expose] def count (x : Input) : ℕ :=
  rationalRepetitions x.val.q x.val.budget x.property.q_pos x.property.q_lt_one
    x.property.budget_pos

/-- The computed native index is exactly the source's logarithmic ceiling. -/
theorem count_eq_repetitions (x : Input) :
    count x = repetitions (x.val.q : ℝ) (x.val.budget : ℝ) :=
  rationalRepetitions_eq _ _ x.property.q_pos x.property.q_lt_one x.property.budget_pos

private def powerState (p : Parameters) (i : ℕ) : State := ⟨p, p.q ^ i, i⟩

private theorem iterate_eq (x : Input) (i : ℕ) (hi : i ≤ count x) :
    step^[i] (initial x.val) = some (powerState x.val i) := by
  induction i with
  | zero => simp [initial, powerState]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hn : ¬x.val.q ^ i ≤ x.val.budget := by
      intro h
      have hle := (pow_le_iff_rationalRepetitions_le x.val.q x.val.budget
        x.property.q_pos x.property.q_lt_one x.property.budget_pos i).mp h
      change count x ≤ i at hle
      omega
    simp [step, powerState, hn, pow_succ]

private theorem q_computable : ComputableInPolyTime Parameters.q encoding encRatBin :=
  encoding_q_deg.computableInPolyTime
private theorem budget_computable : ComputableInPolyTime Parameters.budget encoding encRatBin :=
  encoding_budget_deg.computableInPolyTime
private theorem parameters_computable : ComputableInPolyTime State.parameters stateEncoding
    encoding := stateEncoding_parameters_deg.computableInPolyTime
private theorem power_computable : ComputableInPolyTime State.power stateEncoding encRatBin :=
  stateEncoding_power_deg.computableInPolyTime
private theorem index_computable : ComputableInPolyTime State.index stateEncoding encUnary :=
  stateEncoding_index_deg.computableInPolyTime
attribute [local fun_prop] q_computable budget_computable parameters_computable
  power_computable index_computable

@[local fun_prop] private theorem mk_computable {α : Type} {enc : α ↪ List Bool}
    {p : α → Parameters} {v : α → ℚ} {i : α → ℕ}
    (hp : ComputableInPolyTime p enc encoding)
    (hv : ComputableInPolyTime v enc encRatBin)
    (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun x => State.mk (p x) (v x) (i x)) enc stateEncoding :=
  (hp.prod (hv.prod hi)).of_enc_eq fun _ => rfl

private theorem computable_initial : ComputableInPolyTime initial encoding
    (encOption stateEncoding) := by unfold initial; fun_prop

private theorem computable_test : ComputableInPolyTime
    (fun s : State => decide (s.power ≤ s.parameters.budget)) stateEncoding encBool := by
  have hb := ComputableInPolyTime.comp budget_computable parameters_computable
  have pair := power_computable.prod hb
  have h := ComputableInPolyTime.comp ComputableInPolyTime.ratBin_le pair
  simpa only [Function.comp_def] using h

private theorem computable_advance : ComputableInPolyTime (fun s : State =>
    some (State.mk s.parameters (s.power * s.parameters.q) (s.index + 1)))
    stateEncoding (encOption stateEncoding) := by
  have hq := ComputableInPolyTime.comp q_computable parameters_computable
  have hm := ComputableInPolyTime.comp ComputableInPolyTime.ratBin_mul
    (power_computable.prod hq)
  have hi := ComputableInPolyTime.unary_add.comp (index_computable.prod (.const 1))
  have hs := mk_computable parameters_computable hm hi
  have h := (ComputableInPolyTime.optionSome stateEncoding).comp hs
  simpa only [Function.comp_def] using h

private theorem computable_body : ComputableInPolyTime (fun s : State =>
    if decide (s.power ≤ s.parameters.budget) then none
    else some (State.mk s.parameters (s.power * s.parameters.q) (s.index + 1)))
    stateEncoding (encOption stateEncoding) :=
  .ite computable_test (.const none) computable_advance

private theorem computable_step : ComputableInPolyTime step (encOption stateEncoding)
    (encOption stateEncoding) := by
  have h := ComputableInPolyTime.optionElimWithInput (body := fun (_ : Option State) (s : State) =>
      if decide (s.power ≤ s.parameters.budget) then none
      else some (State.mk s.parameters (s.power * s.parameters.q) (s.index + 1)))
      ComputableInPolyTime.id' (.const none)
      (computable_body.comp (ComputableInPolyTime.snd (encOption stateEncoding) stateEncoding))
  refine h.of_enc_eq ?_
  intro o
  cases o <;> simp [step]

private theorem computable_finish : ComputableInPolyTime finish (encOption stateEncoding)
    encUnary := by unfold finish; fun_prop

/-- Uniform native exact threshold computation. The polynomial constants are
independent of both rational inputs. The derived resource parameter includes the
actual numerical threshold and the binary input length; no bound is assumed. -/
theorem uniform_threshold : ∃ c d : ℕ, ComputableInTimeAndSpace count inputEncoding encUnary
    (fun x => c * (count x + 1) * (count x + (inputEncoding x).length + 1) ^ d)
    (fun x => c * (count x + (inputEncoding x).length + 1) ^ d) := by
  let r := count
  let l := fun x : Input => 20 * (count x + 1) * ((inputEncoding x).length + 1)
  have hval : ComputableInPolyTime (fun x : Input => x.val) inputEncoding encoding :=
    .of_eq fun _ => rfl
  have hsize (x : Input) (i : ℕ) (hi : i ≤ r x) :
      (encOption stateEncoding (step^[i] (initial x.val))).length ≤ l x := by
    rw [iterate_eq x i hi]
    have hw := Rat.binaryWidth_prod_le (List.replicate i x.val.q)
    simp only [List.prod_replicate, List.map_replicate, List.sum_replicate, nsmul_eq_mul] at hw
    have hp := length_encRatBin_le (x.val.q ^ i)
    have hq := binaryWidth_le_length_encRatBin x.val.q
    have hwidth : x.val.q.binaryWidth ≤ (inputEncoding x).length := by
      exact hq.trans (by simp [inputEncoding, encoding_apply]; omega)
    simp only [encOption_some, List.length_cons, stateEncoding_apply, stateEncodingFields,
      length_encPair, encUnary_apply, List.length_replicate, powerState]
    change 2 * (inputEncoding x).length + 1 +
      (2 * (encRatBin (x.val.q ^ i)).length + 1 + i) + 1 ≤ l x
    dsimp only [l, r] at hi ⊢
    have hmul := Nat.mul_le_mul hi hwidth
    nlinarith
  have hne (x : Input) (i : ℕ) (hi : i < r x) :
      encOption stateEncoding (step^[i + 1] (initial x.val)) ≠ [] := by
    change i < count x at hi
    rw [iterate_eq x (i + 1) (by omega)]
    simp
  have hnil (x : Input) : encOption stateEncoding
      (step^[r x + 1] (initial x.val)) = [] := by
    rw [Function.iterate_succ_apply', iterate_eq x (r x) le_rfl]
    have ht := (pow_le_iff_rationalRepetitions_le x.val.q x.val.budget
      x.property.q_pos x.property.q_lt_one x.property.budget_pos (r x)).mpr le_rfl
    simp [step, powerState, ht]
  obtain ⟨c, d, h⟩ := exists_computableInTimeAndSpace_iterateWhile
    (computable_initial.comp hval) computable_step computable_finish hsize hne hnil
  have hout : (fun x : Input => finish (step^[r x] (initial x.val))) = count := by
    funext x
    rw [iterate_eq x (r x) le_rfl]
    rfl
  simp only [Function.comp_def] at h
  rw [hout] at h
  have hpow (x : Input) : (l x + (inputEncoding x).length + 1) ^ d ≤
      21 ^ d * (count x + (inputEncoding x).length + 1) ^ (2 * d) := by
    have hb : l x + (inputEncoding x).length + 1 ≤
        21 * (count x + (inputEncoding x).length + 1) ^ 2 := by dsimp [l]; nlinarith
    simpa only [Nat.mul_pow, ← pow_mul] using Nat.pow_le_pow_left hb d
  refine ⟨c * 21 ^ d, 2 * d, h.mono (fun x => ?_) (fun x => ?_)⟩
  · simpa only [r, mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_le_mul_left (c * (count x + 1)) (hpow x)
  · simpa only [mul_assoc] using Nat.mul_le_mul_left c (hpow x)

end Cslib.Probability.StochasticOracle.PartialCover.ThresholdNative
