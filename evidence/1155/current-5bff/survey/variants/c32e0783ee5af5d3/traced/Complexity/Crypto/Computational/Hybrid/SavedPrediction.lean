/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Hybrid.Sequence
public import Complexity.Crypto.Computational.Prediction
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Tactic.PPT


import Diag1155.Measure
/-!
# Saving the randomness of a coordinate predictor

A predictor description stores the sampled surrounding examples, a trial bit, and the test's
coins. It contains no program for generating those examples, so its size does not recursively
include earlier predictors used during training. The evaluator accepts arbitrary word codes;
the decoder is total even when a boosting loop truncates a description.
Replay is pointwise in the supplied observation; reusing a description also reuses its coins.

The saved test input is split into two encoded fragments around the missing labeled example.
This avoids requiring an efficient inverse for an arbitrary observation or parameter encoding.

## Main definitions

* `Description`, `evaluate`: finite saved data and a total deterministic evaluator.
* `save`, `splice`, `sample`: sample the context and coins before receiving an observation.
* `codeBound`: bound every saved description independently of the source algorithms.

## Main results

* `isPolyTime_evaluate`: evaluation is deterministic polynomial time on every code.
* `eval_sample`, `exists_evaluator`: exact replay from one fixed efficient evaluator.
* `length_sample_le`, `isPPTOn_sample`: all-execution size and strict PPT certificates.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Games 3--5 and the following prediction reduction.
  [Holenstein2006].
  We save the sampled context explicitly to bound descriptions in the constructive learner.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/


diag1155_install
@[expose] public section

namespace Cslib.Crypto.SavedPrediction

open ProbComp Probability BitString Turing.MultiTapeTM

/-- Finite data needed to reuse one coordinate predictor on arbitrary observations. -/
structure Description where
  /-- Padding coordinates reject the test. -/
  active : Bool
  /-- The trial label inserted with the new observation. -/
  trial : Bool
  /-- Encoded test input before the inserted example. -/
  front : List Bool
  /-- Encoded test input after the inserted example. -/
  back : List Bool
  /-- The test's saved random tape. -/
  coins : List Bool
  deriving DecidableEq

namespace Description

/-- Encode a description using the shared pair representation. -/
def encoding : Description ↪ List Bool :=
  ⟨fun desc => encPair encBool
    (encPair encBool (encPair encBits (encPair encBits encBits)))
      (desc.active, desc.trial, desc.front, desc.back, desc.coins), by
    intro left right h
    have hfields := (encPair encBool
      (encPair encBool (encPair encBits (encPair encBits encBits)))).injective h
    cases left
    cases right
    simpa using hfields⟩

/-- Decode any word. Missing or malformed fields use the total pair projections. -/
def decode (code : List Bool) : Description where
  active := (unframe code).headD false
  trial := (unframe (dropFrame code)).headD false
  front := unframe (dropFrame (dropFrame code))
  back := unframe (dropFrame (dropFrame (dropFrame code)))
  coins := dropFrame (dropFrame (dropFrame (dropFrame code)))

@[simp] theorem decode_encoding (desc : Description) : decode (encoding desc) = desc := by
  cases desc
  simp only [decode, encoding, Function.Embedding.coeFn_mk, encPair_apply,
    unframe_frame_append, dropFrame_frame_append, encBool_apply, List.headD_cons,
    encBits, Function.Embedding.refl_apply]

@[simp] theorem length_encoding (desc : Description) :
    (encoding desc).length =
      2 * (desc.front.length + desc.back.length) + desc.coins.length + 8 := by
  simp only [encoding, Function.Embedding.coeFn_mk, length_encPair, encBool_apply,
    List.length_singleton, encBits, Function.Embedding.refl_apply]
  lia

/-- Insert a labeled example directly into the saved encoded input. -/
def input (desc : Description) (observation : List Bool) : List Bool :=
  desc.front ++ encPair encBits encBits
    (encPair encBits encBool (observation, desc.trial), desc.back)

@[simp] theorem length_input (desc : Description) (observation : List Bool) :
    (desc.input observation).length =
      desc.front.length + desc.back.length + 4 * observation.length + 5 := by
  simp only [input, List.length_append, length_encPair, encBool_apply, List.length_singleton,
    encBits, Function.Embedding.refl_apply]
  lia

end Description

/-- Evaluate a saved predictor with a fixed total word evaluator for the original test. -/
def evaluate (test : List Bool → List Bool → List Bool) (code observation : List Bool) : Bool :=
  let desc := Description.decode code
  if desc.active && (test desc.coins (desc.input observation)).headD false then
    desc.trial else !desc.trial

/-- Evaluation is deterministic polynomial time on every code, including truncated codes. -/
@[fun_prop]
theorem isPolyTime_evaluate {test : List Bool → List Bool → List Bool}
    (htest : ComputableInPolyTime (fun pair => test pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun pair => evaluate test pair.1 pair.2)
      (encPair encBits encBits) encBool := by
  dsimp only [evaluate, Description.decode, Description.input]
  fun_prop

/-- A tape long enough for every observation up to the supplied width. -/
def coinBudget (c d width : ℕ) (front back : List Bool) : ℕ :=
  c * (front.length + back.length + 4 * width + 6) ^ d

/-- Attach one random tape to an already sampled context. -/
noncomputable def save (c d width : ℕ) (trial : Bool) (front back : List Bool) :
    ProbComp (List Bool) := do
  let coins ← sampleList (coinBudget c d width front back)
  return Description.encoding ⟨true, trial, front, back, coins⟩

/-- Drawing and saving the common tape has a strict PPT certificate. -/
theorem isPPTOn_save {Param : Type} {input : Param ↪ List Bool}
    {front back : Param → List Bool} {width : Param → ℕ} {trial : Param → Bool} (c d : ℕ)
    (hfront : ComputableInPolyTime front input encBits)
    (hback : ComputableInPolyTime back input encBits)
    (hwidth : ComputableInPolyTime width input encUnary)
    (htrial : ComputableInPolyTime trial input encBool) :
    IsPPTOn input encBits (fun a => save c d (width a) (trial a) (front a) (back a)) := by
  simp only [save, coinBudget, Description.encoding, Function.Embedding.coeFn_mk]
  ppt

attribute [program_certificate] isPPTOn_save

variable {α : Type}

/-- Sample and save the surrounding examples before any target observation is supplied. -/
noncomputable def splice (sample : α ↪ List Bool) (base : List Bool)
    (replacement original : ProbComp (α × Bool)) (before after : ℕ)
    (c d width : ℕ) (trial : Bool) : ProbComp (List Bool) := do
  let front ← OracleComp.replicate before replacement
  let back ← OracleComp.replicate after original
  let front := encPair encBits (encList (encPair sample encBool))
    (base, front)
  let back := encList (encPair sample encBool) back
  save c d width trial front back

/-- Sample a reusable predictor description, including the fair trial and rejected padding. -/
noncomputable def sample (encoding : α ↪ List Bool) (base : List Bool)
    (replacement original : ProbComp (α × Bool)) (count c d width : ℕ) : ProbComp (List Bool) := do
  let trial ← ProbComp.uniform Bool
  let split ← sampleDyadicIndex count
  if split < count then
    splice encoding base replacement original split (count - split - 1) c d width trial
  else return Description.encoding ⟨false, trial, [], [], []⟩

private theorem input_splice (encoding : α ↪ List Bool) (base : List Bool)
    (front back : List (α × Bool)) (trial : Bool) (coins : List Bool) (observation : α) :
    (Description.mk true trial
      (encPair encBits (encList (encPair encoding encBool)) (base, front))
      (encList (encPair encoding encBool) back) coins).input (encoding observation) =
      encPair encBits (encList (encPair encoding encBool))
        (base, front ++ (observation, trial) :: back) := by
  simp [Description.input, encPair, List.append_assoc, encBits,
    encList_append, encList_cons]

private theorem coinBudget_ge (desc : Description) (observation : List Bool) (c d width : ℕ)
    (hwidth : observation.length ≤ width) :
    c * ((desc.input observation).length + 1) ^ d ≤
      coinBudget c d width desc.front desc.back := by
  rw [Description.length_input]
  unfold coinBudget
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  lia

/-- Replaying a saved splice has exactly the original trial predictor's distribution. Only the
target observation needs a size bound; the surrounding samples choose their own coin budget. -/
theorem eval_splice (encoding : α ↪ List Bool) (base : List Bool)
    (replacement original : ProbComp (α × Bool)) (before after c d width : ℕ) (trial : Bool)
    (test : List (α × Bool) → ProbComp Bool) (raw : List Bool → List Bool → List Bool)
    (hrealize : ∀ values budget,
      c * ((encPair encBits (encList (encPair encoding encBool))
        (base, values)).length + 1) ^ d ≤ budget →
      ProbComp.eval (test values) = (uniformList budget).map (fun coins =>
        (raw coins (encPair encBits (encList (encPair encoding encBool))
          (base, values))).headD false))
    (observation : α) (hwidth : (encoding observation).length ≤ width) :
    ProbComp.eval ((fun code => evaluate raw code (encoding observation)) <$>
      splice encoding base replacement original before after c d width trial) =
      ProbComp.eval (trialPredictor
        (fun trial => spliceTest replacement original before after test (observation, trial))
        trial) := by
  simp only [splice, save, trialPredictor, spliceTest, map_bind, map_pure, ProbComp.eval_bind]
  congr 1
  funext front
  congr 1
  funext back
  let desc : Description := ⟨true, trial,
    encPair encBits (encList (encPair encoding encBool)) (base, front),
    encList (encPair encoding encBool) back, []⟩
  have hbudget := coinBudget_ge desc (encoding observation) c d width hwidth
  rw [input_splice] at hbudget
  rw [ProbComp.eval_map, hrealize _ _ hbudget]
  simp [evaluate, Function.comp_def, desc, Description.input, encList_append, encList_cons,
    List.append_assoc, PMF.map]

/-- Sampling all predictor randomness once preserves every bounded observation's prediction
law, including rejected padding coordinates. -/
theorem eval_sample (encoding : α ↪ List Bool) (base : List Bool)
    (replacement original : ProbComp (α × Bool)) (count c d width : ℕ)
    (test : List (α × Bool) → ProbComp Bool) (raw : List Bool → List Bool → List Bool)
    (hrealize : ∀ values budget,
      c * ((encPair encBits (encList (encPair encoding encBool))
        (base, values)).length + 1) ^ d ≤ budget →
      ProbComp.eval (test values) = (uniformList budget).map (fun coins =>
        (raw coins (encPair encBits (encList (encPair encoding encBool))
          (base, values))).headD false))
    (observation : α) (hwidth : (encoding observation).length ≤ width) :
    ProbComp.eval ((fun code => evaluate raw code (encoding observation)) <$>
      sample encoding base replacement original count c d width) =
      ProbComp.eval (bitPredictor
        (fun trial => sequenceTest replacement original count test (observation, trial))) := by
  simp only [sample, bitPredictor, sequenceTest, trialPredictor, map_bind, ProbComp.eval_bind]
  congr 1
  funext trial
  congr 1
  funext split
  by_cases hsplit : split < count
  · simpa only [hsplit, ite_true, trialPredictor] using
      eval_splice encoding base replacement original split (count - split - 1) c d width trial
        test raw hrealize observation hwidth
  · simp [hsplit, evaluate]

/-- Encoded surrounding examples and the public test parameter occupy this many bits. -/
def contextBound (baseSize count width : ℕ) : ℕ :=
  2 * baseSize + count * (4 * width + 5) + 1

/-- The complete description bound depends on sample sizes and the fixed test clock, not on
the program or stored state used to generate the surrounding examples. -/
def codeBound (baseSize count c d width : ℕ) : ℕ :=
  let context := contextBound baseSize count width
  2 * context + c * (context + 4 * width + 6) ^ d + 8

/-- The saved-description budget is polynomial time in the parameter and sample sizes.
The clock coefficients belong to the fixed test, so the exponent is constant. -/
@[program_certificate]
theorem isPolyTime_codeBound {Param : Type} {input : Param ↪ List Bool}
    {baseSize count width : Param → ℕ} (c d : ℕ)
    (hbase : ComputableInPolyTime baseSize input encUnary)
    (hcount : ComputableInPolyTime count input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary) :
    ComputableInPolyTime (fun a => codeBound (baseSize a) (count a) c d (width a))
      input encUnary := by
  unfold codeBound contextBound
  polytime

private theorem length_save {c d width : ℕ} {trial : Bool} {front back code : List Bool}
    (hcode : code ∈ (ProbComp.eval (save c d width trial front back)).support) :
    code.length = 2 * (front.length + back.length) + coinBudget c d width front back + 8 := by
  rw [save, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hcode
  obtain ⟨coins, hcoins, hcode⟩ := hcode
  rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hcode
  subst code
  have hlength := length_of_mem_support_uniformList (by
    simpa only [eval_sampleList] using hcoins)
  simpa only [Description.length_encoding] using congrArg
    (fun length => 2 * (front.length + back.length) + length + 8) hlength

private theorem length_labeledList_le (encoding : α ↪ List Bool) {values : List (α × Bool)}
    {width : ℕ} (hwidth : ∀ value ∈ values, (encoding value.1).length ≤ width) :
    (encList (encPair encoding encBool) values).length ≤
      values.length * (4 * width + 5) := by
  have h := length_encList_le (encPair encoding encBool)
    values (b := 2 * width + 2) (by
      intro value hmem
      have := hwidth value hmem
      simp only [length_encPair, encBool_apply,
        List.length_singleton]
      lia)
  convert h using 1
  congr 1
  lia

/-- Saving a fixed coordinate has a uniform description bound on every execution. -/
theorem length_splice_le (encoding : α ↪ List Bool) (base : List Bool)
    (replacement original : ProbComp (α × Bool)) (before after c d width : ℕ) (trial : Bool)
    (hreplacement : ∀ value ∈ (ProbComp.eval replacement).support,
      (encoding value.1).length ≤ width)
    (horiginal : ∀ value ∈ (ProbComp.eval original).support,
      (encoding value.1).length ≤ width)
    {code : List Bool}
    (hcode : code ∈ (ProbComp.eval
      (splice encoding base replacement original before after c d width trial)).support) :
    code.length ≤ codeBound base.length (before + after) c d width := by
  simp only [splice, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hcode
  obtain ⟨front, hfront, back, hback, hcode⟩ := hcode
  obtain ⟨hfrontLength, hfrontSupport⟩ :=
    (ProbComp.mem_support_replicate_iff _ _ _).mp hfront
  obtain ⟨hbackLength, hbackSupport⟩ :=
    (ProbComp.mem_support_replicate_iff _ _ _).mp hback
  have hfrontSize := length_labeledList_le encoding
    (fun value hmem => hreplacement value (hfrontSupport value hmem))
  have hbackSize := length_labeledList_le encoding
    (fun value hmem => horiginal value (hbackSupport value hmem))
  have hcontext :
      (encPair encBits (encList (encPair encoding encBool))
        (base, front)).length + (encList (encPair encoding encBool) back).length ≤
      contextBound base.length (before + after) width := by
    simp only [length_encPair, encBits, Function.Embedding.refl_apply]
    unfold contextBound
    rw [hfrontLength] at hfrontSize
    rw [hbackLength] at hbackSize
    nlinarith
  rw [length_save hcode]
  dsimp only [codeBound, coinBudget]
  gcongr

/-- Every generated description fits a bound independent of the source algorithms' internal
state. Padding descriptions satisfy the same bound, including when `count = 0`. -/
theorem length_sample_le (encoding : α ↪ List Bool) (base : List Bool)
    (replacement original : ProbComp (α × Bool)) (count c d width : ℕ)
    (hreplacement : ∀ value ∈ (ProbComp.eval replacement).support,
      (encoding value.1).length ≤ width)
    (horiginal : ∀ value ∈ (ProbComp.eval original).support,
      (encoding value.1).length ≤ width)
    {code : List Bool}
    (hcode : code ∈ (ProbComp.eval
      (sample encoding base replacement original count c d width)).support) :
    code.length ≤ codeBound base.length count c d width := by
  simp only [sample, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hcode
  obtain ⟨trial, _, split, _, hcode⟩ := hcode
  split_ifs at hcode with hsplit
  · have hsize := length_splice_le encoding base replacement original split
      (count - split - 1) c d width trial hreplacement horiginal hcode
    apply hsize.trans
    dsimp only [codeBound, contextBound]
    gcongr <;> lia
  · rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hcode
    subst code
    simp [codeBound]

/-- A PPT test supplies one fixed efficient evaluator for all saved descriptions. No decoder
for either the public parameter or observation representation is required. -/
theorem exists_evaluator {Param : Type} {input : Param ↪ List Bool} {output : α ↪ List Bool}
    {test : Param → List (α × Bool) → ProbComp Bool}
    (htest : IsPPTOn (encPair input (encList (encPair output encBool)))
      encBool (fun pair => test pair.1 pair.2)) :
    ∃ (c d : ℕ) (predict : List Bool → List Bool → Bool),
      ComputableInPolyTime (fun pair => predict pair.1 pair.2)
        (encPair encBits encBits) encBool ∧
      ∀ a replacement original count width observation, (output observation).length ≤ width →
        ProbComp.eval ((fun code => predict code (output observation)) <$>
          sample output (input a) replacement original count c d width) =
          ProbComp.eval (bitPredictor (fun trial =>
            sequenceTest replacement original count (test a) (observation, trial))) := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime]
  obtain ⟨c, d, raw, hefficient, hrealize⟩ := htest.exists_padded_bool_coin_evaluator
  refine ⟨c, d, evaluate raw, (isPolyTime_evaluate (.of_tidy hefficient)).tidy, ?_⟩
  intro a replacement original count width observation hwidth
  apply eval_sample output (input a) replacement original count c d width (test a) raw
    (fun values budget hbudget => hrealize (a, values) budget hbudget) observation hwidth

/-- Saving context and coins is strict PPT whenever the sources and numerical bounds are. -/
theorem isPPTOn_splice {Param : Type} {input : Param ↪ List Bool} {output : α ↪ List Bool}
    {base : Param → List Bool} {replacement original : Param → ProbComp (α × Bool)}
    {before after width : Param → ℕ} {trial : Param → Bool} (c d : ℕ)
    (hbase : ComputableInPolyTime base input encBits)
    (hreplacement : IsPPTOn input (encPair output encBool) replacement)
    (horiginal : IsPPTOn input (encPair output encBool) original)
    (hbefore : ComputableInPolyTime before input encUnary)
    (hafter : ComputableInPolyTime after input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary)
    (htrial : ComputableInPolyTime trial input encBool) :
    IsPPTOn input encBits (fun a =>
      splice output (base a) (replacement a) (original a) (before a) (after a) c d (width a)
        (trial a)) := by
  have hbase := hbase.tidy
  have hbefore := hbefore.tidy
  have hafter := hafter.tidy
  have hwidth := hwidth.tidy
  have htrial := htrial.tidy
  unfold splice
  apply (hreplacement.replicate (.of_tidy hbefore)).bind_with
  apply ((horiginal.preprocess
    (ComputableInPolyTime.fst input (encList (encPair output encBool)))).replicate
      (.of_tidy (hafter.comp (ComputableTidilyInPolyTime.fst input
        (encList (encPair output encBool)))))).bind_with
  apply isPPTOn_save c d <;> exact .of_tidy (by fun_prop)

attribute [program_certificate] isPPTOn_splice

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- The random-coordinate description sampler is a uniform strict PPT program. -/
theorem isPPTOn_sample {Param : Type} {input : Param ↪ List Bool} {output : α ↪ List Bool}
    {base : Param → List Bool} {replacement original : Param → ProbComp (α × Bool)}
    {count width : Param → ℕ} (c d : ℕ)
    (hbase : ComputableInPolyTime base input encBits)
    (hreplacement : IsPPTOn input (encPair output encBool) replacement)
    (horiginal : IsPPTOn input (encPair output encBool) original)
    (hcount : ComputableInPolyTime count input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary) :
    IsPPTOn input encBits (fun a =>
      sample output (base a) (replacement a) (original a) (count a) c d (width a)) := by
  have hbase := hbase.tidy
  have hcount := hcount.tidy
  have hwidth := hwidth.tidy
  unfold sample Description.encoding
  ppt

attribute [program_certificate hreplacement] isPPTOn_sample

end Cslib.Crypto.SavedPrediction
