/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Classes.Inclusions
public import Complexity.Computability.Complexity.Classes.Oracle.Closure
public import Complexity.Computability.Complexity.Classes.Oracle.Lowness
public import Complexity.Computability.Complexity.Classes.Oracle.PolyTime
public import Complexity.Computability.Complexity.Classes.PP.Closure
public import Complexity.Computability.Complexity.Classes.Space
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Complexity.Reduction.OneOne
public import Complexity.Computability.Complexity.Reduction.TruthTableVariants
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Polynomial-time Turing reductions and the Turing bridge

A polynomial-time Turing reduction (Cook reduction) `A ≤ᵖ_T B` allows adaptive queries to an
oracle for `B` within polynomial time [Ladner, Lynch and Selman][LadnerLynchSelman1975],
[Arora and Barak, Section 3.4][AroraBarak09].

## Main definitions

* `Cslib.Complexity.PolyTimeTuringReducible`: polynomial-time Turing reducibility.
* `Cslib.Complexity.PolyTimeTuringHard`, `Cslib.Complexity.PolyTimeTuringComplete`: hardness and
  completeness under polynomial-time Turing reductions.
* `Cslib.Complexity.NPTuringHard`, `Cslib.Complexity.NPTuringComplete`: Turing hardness and
  completeness for `NP`.
* `Cslib.Complexity.PPTuringHard`, `Cslib.Complexity.PPTuringComplete`: Turing hardness and
  completeness for `PP`.
* `Cslib.Complexity.PSPACETuringHard`, `Cslib.Complexity.PSPACETuringComplete`: Turing hardness and
  completeness for `PSPACE`.

## Main results

* `Cslib.Complexity.polyTimeTuringReducible_iff_mem_PWithOracle`: **the Turing bridge**,
  `A ≤ᵖ_T B ↔ A ∈ P^(encB '' B)`.
* `Cslib.Complexity.polyTimeTuringReducible_bits_iff_mem_PWithOracle`: for word languages,
  `A ≤ᵖ_T B ↔ A ∈ P^B`.
* `Cslib.Complexity.PolyTimeReducible.polyTimeTuringReducible`: many-one reductions are Turing
  reductions (`≤ₘ ⇒ ≤_T`).
* `Cslib.Complexity.PolyTimeOneOneReducible.polyTimeTuringReducible`: one-one reductions are Turing
  reductions (`≤₁ ⇒ ≤_T`).
* `Cslib.Complexity.computableInPolyTimeWithOracle_map_mem`,
  `Cslib.Complexity.computableInPolyTimeWithOracle_truthTableAnswers`: answering a polynomial-time
  batch of oracle queries in polynomial time relative to the oracle.
* `Cslib.Complexity.PolyTimeTruthTableReducible.polyTimeTuringReducible`,
  `Cslib.Complexity.PolyTimeKTruthTableReducible.polyTimeTuringReducible`,
  `Cslib.Complexity.PolyTimeBTTReducible.polyTimeTuringReducible`,
  `Cslib.Complexity.PolyTimePTTReducible.polyTimeTuringReducible`,
  `Cslib.Complexity.PolyTimeDTTReducible.polyTimeTuringReducible`,
  `Cslib.Complexity.PolyTimeCTTReducible.polyTimeTuringReducible`: truth-table, `k`-truth-table,
  bounded, positive, disjunctive, and conjunctive truth-table reductions are Turing reductions
  (`≤_tt, ≤_{k-tt}, ≤_btt, ≤_ptt, ≤_dtt, ≤_ctt ⇒ ≤_T`).
* `Cslib.Complexity.PolyTimeTuringReducible.refl`: reflexivity.
* `Cslib.Complexity.ComputableInPolyTimeWithOracle.of_mem_PWithOracle`,
  `Cslib.Complexity.PWithOracle_subset_of_mem_PWithOracle`,
  `Cslib.Complexity.NPWithOracle_subset_of_mem_PWithOracle`: oracle substitution when the oracle
  language itself belongs to `P^O`.
* `Cslib.Complexity.PolyTimeTuringReducible.mem_PWithOracle`: `P^O` is closed under Turing
  reductions to word languages.
* `Cslib.Complexity.PolyTimeTuringReducible.trans`: transitivity of polynomial-time Turing
  reductions through word languages (`≤_T ∘ ≤_T ⇒ ≤_T`).
* `Cslib.Complexity.PolyTimeReducible.trans_turing`: pre-composition with a many-one reduction
  (`≤ₘ ∘ ≤_T ⇒ ≤_T`).
* `Cslib.Complexity.PolyTimeTuringReducible.compl_left`: complementation of the source language.
* `Cslib.Complexity.PolyTimeTuringReducible.compl_self`: a language's complement Turing-reduces to
  the language itself (`Aᶜ ≤_T A`).
* `Cslib.Complexity.PolyTimeTuringReducible.mem_P`: `P` is closed under Turing reductions to word
  languages.
* `Cslib.Complexity.PolyTimeHard.polyTimeTuringHard`: many-one hardness implies Turing hardness.
* `Cslib.Complexity.PolyTimeHard.polyTimeTuringHard_of_turing`: transferring many-one hardness
  across a Turing reduction.
* Hardness transfer to `P`:
  * `Cslib.Complexity.NPHard.P_eq_NP_of_turing_mem_P`: if an NP-hard problem Turing-reduces to a
    problem in `P`, then `P = NP`.
  * `Cslib.Complexity.PolyTimeHard.P_eq_PP_of_turing_mem_P`: if a PP-hard problem Turing-reduces
    to a problem in `P`, then `P = PP`.
  * `Cslib.Complexity.PSPACEHard.P_eq_PSPACE_of_turing_mem_P`: if a PSPACE-hard problem
    Turing-reduces to a problem in `P`, then `P = PSPACE`.
* `Cslib.Complexity.NPHard.NP_eq_coNP_of_turing_mem_NP_inter_coNP`: if an NP-hard problem
  Turing-reduces to a problem in `NP ∩ coNP`, then `NP = coNP`.

## References

* [R. E. Ladner, N. A. Lynch, A. L. Selman, *A comparison of polynomial time
  reducibilities*][LadnerLynchSelman1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β γ : Type}
variable {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : γ ↪ List Bool}
variable {A : Set α} {B : Set β} {L : Set γ}

/-- `A` is polynomial-time Turing reducible to `B` (`A ≤ᵖ_T B`): some algorithm deciding `A` runs
in polynomial time relative to an oracle for the encoded language of `B`
[Ladner, Lynch and Selman][LadnerLynchSelman1975].

Query and resource conventions: an algorithm is represented by a single deterministic, adaptive
`WordQueryComp` program certified by `IsOraclePPTOn`. The clock is polynomial in `|encA a|`,
with each query symbol costing one step, bounding both query length and the number of queries
via `IsOraclePPTOn.query_bounds`. Oracle evaluation itself takes one step. -/
def PolyTimeTuringReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α)
    (B : Set β) : Prop :=
  A ∈ PWithOracle (encB '' B) encA

/-- **The Turing bridge**: `A ≤ᵖ_T B` if and only if `A ∈ P^B` with respect to the encoded oracle
language `encB '' B`. -/
theorem polyTimeTuringReducible_iff_mem_PWithOracle :
    PolyTimeTuringReducible encA encB A B ↔ A ∈ PWithOracle (encB '' B) encA :=
  Iff.rfl

/-- On bitstring languages with the default encoding `encBits`, `A ≤ᵖ_T B` is exactly `A ∈ P^B`. -/
theorem polyTimeTuringReducible_bits_iff_mem_PWithOracle {B : Set (List Bool)} :
    PolyTimeTuringReducible encA encBits A B ↔ A ∈ PWithOracle B encA := by
  have : encBits '' B = B := Set.image_id B
  rw [polyTimeTuringReducible_iff_mem_PWithOracle, this]

open Classical in
/-- Every polynomial-time many-one reduction is a polynomial-time Turing reduction making a
single query to the oracle. -/
theorem PolyTimeReducible.polyTimeTuringReducible
    (h : PolyTimeReducible encA encB A B) : PolyTimeTuringReducible encA encB A B := by
  obtain ⟨f, hf, hAB⟩ := h
  refine ⟨fun a => decide (encB (f a) ∈ encB '' B), ?_, fun a => ?_⟩
  · rw [computableInPolyTimeWithOracle_iff_polyTimeOracleProgram]
    exact PolyTimeOracleProgram.of_query (req := fun a => encB (f a)) hf.encoding_comp
      fun _ hA => hA ▸ rfl
  · dsimp only
    rw [decide_eq_true_iff, encB.injective.mem_set_image, hAB a]

/-- A one-one reduction is a polynomial-time Turing reduction. -/
theorem PolyTimeOneOneReducible.polyTimeTuringReducible
    (h : PolyTimeOneOneReducible encA encB A B) : PolyTimeTuringReducible encA encB A B :=
  h.polyTimeReducible.polyTimeTuringReducible

/-! ### Truth-table reductions are Turing reductions -/

/-- One step of `queryWords`: ask the first remaining word, and append whether its reply begins
with `true` to the accumulated answer word. -/
def queryWordsStep (s : List (List Bool) × List Bool) :
    WordQueryComp Unit (List (List Bool) × List Bool) :=
  if s.1.isEmpty then pure s else
    (fun reply => (s.1.tail, s.2 ++ [reply == [true]])) <$>
      (List.take 1 <$> OracleComp.query ((), s.1.headD []))

/-- Ask the oracle every word of the list, in order, and collect the one-bit answers. -/
def queryWords (words : List (List Bool)) : WordQueryComp Unit (List Bool) :=
  Prod.snd <$> OracleComp.iterate words.length queryWordsStep (words, [])

private theorem interpret_queryWordsStep (s : List (List Bool) × List Bool) :
    OracleComp.interpret ProbOracleComp.query (queryWordsStep s) =
      if s.1.isEmpty then pure s else
        (fun reply => (s.1.tail, s.2 ++ [reply == [true]])) <$>
          (List.take 1 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), s.1.headD [])) := by
  unfold queryWordsStep
  split <;> simp [OracleComp.interpret_map, OracleComp.interpret_query]

/-- Asking every word of a list and collecting the one-bit answers is strict oracle PPT: each step
pops one word from the framed list and appends one bit to the answer word, so the encoded state
never grows. -/
theorem isOraclePPTOn_queryWords :
    Probability.IsOraclePPTOn (encList encBits) encBits
      (fun words => OracleComp.interpret ProbOracleComp.query (queryWords words)) := by
  simp only [queryWords, OracleComp.interpret_map, OracleComp.interpret_iterate]
  refine Probability.IsOraclePPTOn.map' (Probability.IsOraclePPTOn.iterate_of_bounded_growth'
    (stateEncoding := encPair (encList encBits) encBits) (by fun_prop) (by fun_prop) ?_
    (growth := 0) ?_) (by fun_prop)
  · simp only [interpret_queryWordsStep]
    refine Probability.IsOraclePPTOn.cond' (by fun_prop)
      (ComputableInPolyTime.id'.isOraclePPTOn) ?_
    exact Probability.IsOraclePPTOn.map_with'
      (Probability.IsOraclePPTOn.query_take' () (by fun_prop) (by fun_prop))
      (by fun_prop)
  · intro state next hnext
    rw [interpret_queryWordsStep] at hnext
    obtain ⟨words, acc⟩ := state
    cases words with
    | nil => rw [OracleComp.eq_of_mem_supportWith_pure hnext]; simp
    | cons word words =>
      obtain ⟨reply, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      simp only [length_encPair, encBits_apply, List.length_append, List.length_singleton,
        List.tail_cons, length_encList, List.map_cons, List.sum_cons]
      omega

open Classical in
private theorem interpret_id_queryWordsStep (O : Set (List Bool)) (word : List Bool)
    (words : List (List Bool)) (acc : List Bool) :
    OracleComp.interpret (m := Id) (languageOracle O) (queryWordsStep (word :: words, acc)) =
      (words, acc ++ [decide (word ∈ O)]) := by
  simp only [queryWordsStep, List.isEmpty_cons, Bool.false_eq_true, ite_false]
  change (fun reply : List Bool => (words, acc ++ [reply == [true]]))
    (List.take 1 (languageOracle O ((), word))) = _
  rw [languageOracle_apply]
  cases decide (word ∈ O) <;> rfl

open Classical in
/-- Interpreting `queryWords words` against `languageOracle O` returns the list of membership
decisions `words.map (fun word => decide (word ∈ O))`. -/
theorem interpret_queryWords (O : Set (List Bool)) (words : List (List Bool)) :
    OracleComp.interpret (m := Id) (languageOracle O) (queryWords words) =
      words.map fun word => decide (word ∈ O) := by
  have key : ∀ (words : List (List Bool)) (acc : List Bool),
      OracleComp.interpret (m := Id) (languageOracle O)
        (OracleComp.iterate words.length queryWordsStep (words, acc)) =
        ([], acc ++ words.map fun word => decide (word ∈ O)) := by
    intro words
    induction words with
    | nil => intro acc; simp only [List.length_nil, List.map_nil, List.append_nil]; rfl
    | cons word words ih =>
      intro acc
      rw [List.length_cons, OracleComp.iterate_succ_bind, OracleComp.interpret_bind]
      change OracleComp.interpret (m := Id) (languageOracle O)
        (OracleComp.iterate words.length queryWordsStep
          (OracleComp.interpret (m := Id) (languageOracle O)
            (queryWordsStep (word :: words, acc)))) = _
      rw [interpret_id_queryWordsStep, ih]
      simp [List.append_assoc]
  unfold queryWords
  rw [OracleComp.interpret_map, key]
  simp only [List.nil_append]
  rfl

open Classical in
/-- Evaluating membership in `O` across a list of words is computable in polynomial time relative
to `O`. -/
theorem computableInPolyTimeWithOracle_map_mem (O : Set (List Bool)) :
    ComputableInPolyTimeWithOracle O
      (fun words : List (List Bool) => words.map fun word => decide (word ∈ O))
      (encList encBits) encBits :=
  ⟨queryWords, isOraclePPTOn_queryWords, interpret_queryWords O⟩

/-- Computing the semantic answer word `truthTableAnswers (q ⁻¹' B) r` of a polynomial-time batch
of queries `(r, q)` is polynomial time relative to the encoded oracle language `encB '' B`. -/
theorem computableInPolyTimeWithOracle_truthTableAnswers {r : α → ℕ} {q : α × ℕ → β}
    (hr : ComputableInPolyTime r encA encUnary)
    (hq : ComputableInPolyTime q (encPair encA encUnary) encB) :
    ComputableInPolyTimeWithOracle (encB '' B) (truthTableAnswers (q ⁻¹' B) r) encA encBits := by
  classical
  have hbatch : ComputableInPolyTime
      (fun a => (List.range (r a)).map fun i => encB (q (a, i))) encA (encList encBits) :=
    ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.range.comp hr) hq.encoding_comp
  have hq_mem := (computableInPolyTimeWithOracle_map_mem (encB '' B)).preprocess hbatch
  convert hq_mem using 2
  rw [truthTableAnswers_eq_map_range, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp

/-- **Every polynomial-time truth-table reduction is a polynomial-time Turing reduction**
(`≤_tt ⇒ ≤_T`) [Ladner, Lynch and Selman][LadnerLynchSelman1975]. -/
theorem PolyTimeTruthTableReducible.polyTimeTuringReducible
    (h : PolyTimeTruthTableReducible encA encB A B) :
    PolyTimeTuringReducible encA encB A B := by
  obtain ⟨r, q, d, hr, hq, hd, hA⟩ := h
  exact ⟨fun a => d (a, truthTableAnswers (q ⁻¹' B) r a),
    (computableInPolyTimeWithOracle_truthTableAnswers (B := B) hr hq).map_with
      (g := fun a ans => d (a, ans)) hd, hA⟩

/-- Every `k`-truth-table reduction is a polynomial-time Turing reduction (`≤_{k-tt} ⇒ ≤_T`). -/
theorem PolyTimeKTruthTableReducible.polyTimeTuringReducible {k : ℕ}
    (h : PolyTimeKTruthTableReducible k encA encB A B) :
    PolyTimeTuringReducible encA encB A B :=
  h.polyTimeBTTReducible.polyTimeTruthTableReducible.polyTimeTuringReducible

/-- Every bounded truth-table reduction is a polynomial-time Turing reduction (`≤_btt ⇒ ≤_T`). -/
theorem PolyTimeBTTReducible.polyTimeTuringReducible
    (h : PolyTimeBTTReducible encA encB A B) :
    PolyTimeTuringReducible encA encB A B :=
  h.polyTimeTruthTableReducible.polyTimeTuringReducible

/-- Every positive truth-table reduction is a polynomial-time Turing reduction (`≤_ptt ⇒ ≤_T`). -/
theorem PolyTimePTTReducible.polyTimeTuringReducible
    (h : PolyTimePTTReducible encA encB A B) :
    PolyTimeTuringReducible encA encB A B :=
  h.polyTimeTruthTableReducible.polyTimeTuringReducible

/-- Every disjunctive truth-table reduction is a polynomial-time Turing reduction
(`≤_dtt ⇒ ≤_T`). -/
theorem PolyTimeDTTReducible.polyTimeTuringReducible
    (h : PolyTimeDTTReducible encA encB A B) :
    PolyTimeTuringReducible encA encB A B :=
  h.polyTimeTruthTableReducible.polyTimeTuringReducible

/-- Every conjunctive truth-table reduction is a polynomial-time Turing reduction
(`≤_ctt ⇒ ≤_T`). -/
theorem PolyTimeCTTReducible.polyTimeTuringReducible
    (h : PolyTimeCTTReducible encA encB A B) :
    PolyTimeTuringReducible encA encB A B :=
  h.polyTimeTruthTableReducible.polyTimeTuringReducible

/-! ### Oracle substitution and transitivity of Turing reductions -/

/-- One simulated instruction of a finite oracle machine `machine` when each query to its oracle is
answered by running the deterministic oracle program `prog`. -/
private def oracleAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (prog : List Bool → WordQueryComp Unit Bool)
    (cfg : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :
    WordQueryComp Unit (Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :=
  if (machine.pendingQuery cfg).isSome then
    (fun b => machine.receiveBit (cfg, b)) <$> prog (machine.pendingRequest cfg)
  else
    pure (machine.localStep cfg)

private theorem interpret_oracleAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (prog : List Bool → WordQueryComp Unit Bool)
    (cfg : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :
    OracleComp.interpret ProbOracleComp.query (oracleAnswerStep machine prog cfg) =
      if (machine.pendingQuery cfg).isSome then
        (fun b => machine.receiveBit (cfg, b)) <$>
          OracleComp.interpret ProbOracleComp.query (prog (machine.pendingRequest cfg))
      else
        pure (machine.localStep cfg) := by
  unfold oracleAnswerStep
  split <;> simp [OracleComp.interpret_map]

private theorem isOraclePPTOn_oracleAnswerStep {k : ℕ} {Control : Type} [Finite Control]
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    {prog : List Bool → WordQueryComp Unit Bool}
    (hprog : Probability.IsOraclePPTOn encBits encBool
      (fun w => OracleComp.interpret ProbOracleComp.query (prog w))) :
    Probability.IsOraclePPTOn encFiniteConfig encFiniteConfig
      (fun cfg =>
        OracleComp.interpret ProbOracleComp.query (oracleAnswerStep machine prog cfg)) := by
  simp only [interpret_oracleAnswerStep]
  exact Probability.IsOraclePPTOn.cond'
    ((ComputableInPolyTime.of_finite Option.isSome).comp machine.pendingQuery_pt)
    ((hprog.preprocess' machine.pendingRequest_pt).map_with'
      (f := fun cfg b => machine.receiveBit (cfg, b)) machine.receiveBit_pt)
    machine.localStep_pt.isOraclePPTOn

private theorem spaceBound_of_mem_support_oracleAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (prog : List Bool → WordQueryComp Unit Bool)
    {inputSize steps : ℕ}
    {cfg next : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit}
    (hcfg : Turing.MultiTapeMachine.FiniteConfig.SpaceBound inputSize steps 1 cfg)
    (hnext : next ∈ OracleComp.support
      (OracleComp.interpret ProbOracleComp.query (oracleAnswerStep machine prog cfg))) :
    Turing.MultiTapeMachine.FiniteConfig.SpaceBound inputSize (steps + 1) 1 next := by
  rw [interpret_oracleAnswerStep] at hnext
  split_ifs at hnext with hq
  · obtain ⟨b, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    have hstep := machine.spaceBound_answerStep (fun _ => b) hcfg
    rw [machine.answerStep_bit (fun _ => b)] at hstep
    simpa [hq] using hstep
  · rw [OracleComp.eq_of_mem_supportWith_pure hnext]
    have hstep := machine.spaceBound_answerStep (fun _ => false) hcfg
    rw [machine.answerStep_bit (fun _ => false)] at hstep
    simpa [hq] using hstep

private theorem interpret_id_oracleAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    {prog : List Bool → WordQueryComp Unit Bool} {O : Set (List Bool)} {g : List Bool → Bool}
    (hg : ∀ w, OracleComp.interpret (m := Id) (languageOracle O) (prog w) = g w)
    (cfg : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :
    OracleComp.interpret (m := Id) (languageOracle O) (oracleAnswerStep machine prog cfg) =
      machine.answerStep (fun q => [g q.2]) cfg := by
  rw [machine.answerStep_bit]
  unfold oracleAnswerStep
  split_ifs with hq
  · rw [OracleComp.interpret_map, hg]
    rfl
  · rfl

open Classical in
/-- **Oracle substitution for polynomial-time Boolean computations**: if an oracle language `O₁`
belongs to `P^{O₂}` and `f : α → Bool` is computable in polynomial time relative to `O₁`, then
`f` is computable in polynomial time relative to `O₂`. -/
theorem ComputableInPolyTimeWithOracle.of_mem_PWithOracle {O₁ O₂ : Set (List Bool)} {f : α → Bool}
    (hO₁ : O₁ ∈ PWithOracle O₂ encBits)
    (hf : ComputableInPolyTimeWithOracle O₁ f encA encBool) :
    ComputableInPolyTimeWithOracle O₂ f encA encBool := by
  obtain ⟨g, ⟨prog, hprog, hg⟩, hgO₁⟩ := hO₁
  have hg' : g = fun w => decide (w ∈ O₁) := funext fun w =>
    Bool.eq_iff_iff.mpr ⟨fun h => decide_eq_true ((hgO₁ w).mpr h),
      fun h => (hgO₁ w).mp (of_decide_eq_true h)⟩
  subst hg'
  obtain ⟨program, hcert, hprogram⟩ := hf
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Fin m) (Oracle := Unit)
  have hcount : ComputableInPolyTime (fun a => c * ((encA a).length + 1) ^ d) encA
      encUnary :=
    ((ComputableInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      (ComputableInPolyTime.encoding_length encA)).of_enc_eq fun a => by simp
  have hinit : ComputableInPolyTime
      (fun a => Turing.MultiTapeMachine.FiniteConfig.init (k := k) (Oracle := Unit)
        machine.initial (encA a))
      encA encFiniteConfig := by
    refine (((ComputableInPolyTime.of_eq fun _ => rfl :
        ComputableInPolyTime encA encA encBits).prod
      (ComputableInPolyTime.const (encOut :=
        encPair (encFinite (Option (Fin m)))
          (encPair encUnary (encPair (encPi (Index := Fin k) (encBiTape encBool)) encBits)))
        (some machine.initial, 1, fun _ => Cslib.Turing.BiTape.nil, []))).prod
      (ComputableInPolyTime.const
        (encOut := encPi (Index := Unit) (encPair encBits (encBiTape encBool)))
        fun _ : Unit => ([], Cslib.Turing.BiTape.nil))).of_enc_eq fun a => ?_
    simp [Turing.MultiTapeMachine.FiniteConfig.init, Turing.FiniteCfg.init]
  have hbound : PolyBounded (fun a => (encA a).length)
      (fun a => cf * ((encA a).length + c * ((encA a).length + 1) ^ d + 1 + 1)) :=
    PolyBounded.mono (PolyBounded.of_polynomiallyBounded (fun a => (encA a).length)
      (bound := fun L => cf * (L + c * (L + 1) ^ d + 1 + 1)) (by fun_prop)) fun _ => le_rfl
  have hit := (Probability.IsOraclePPTOn.iterate_spec' hcount hinit
    (isOraclePPTOn_oracleAnswerStep machine hprog)
    (fun a i cfg => Turing.MultiTapeMachine.FiniteConfig.SpaceBound (encA a).length i 1 cfg)
    (fun _ => Turing.MultiTapeMachine.FiniteConfig.spaceBound_init _ _ _)
    (fun _ _ _ _ hinv _ hnext =>
      spaceBound_of_mem_support_oracleAnswerStep machine prog hinv hnext)
    hbound
    (fun _ _ _ hi hinv => (hcf _ _ _ _ hinv).trans (Nat.mul_le_mul_left cf (by omega)))).1
  refine ⟨fun a => (fun cfg => cfg.tapes.output.headD false) <$>
    OracleComp.iterate (c * ((encA a).length + 1) ^ d) (oracleAnswerStep machine prog)
      (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a)), ?_, fun a => ?_⟩
  · simp only [OracleComp.interpret_map, OracleComp.interpret_iterate]
    exact hit.map' (by fun_prop)
  · rw [OracleComp.interpret_map, OracleComp.interpret_id_iterate]
    simp only [interpret_id_oracleAnswerStep machine hg]
    change ((machine.answerStep (languageOracle O₁))^[c * ((encA a).length + 1) ^ d]
      (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a))).tapes.output.headD
        false = f a
    rw [← machine.interpret_run_pure_false, hrun a (languageOracle O₁), ← hprogram a]
    simp

/-- If `O₁ ∈ P^{O₂}`, then `P^{O₁} ⊆ P^{O₂}`. -/
theorem PWithOracle_subset_of_mem_PWithOracle {O₁ O₂ : Set (List Bool)}
    (hO₁ : O₁ ∈ PWithOracle O₂ encBits) (enc : α ↪ List Bool) :
    PWithOracle O₁ enc ⊆ PWithOracle O₂ enc :=
  fun _ ⟨f, hf, hL⟩ => ⟨f, hf.of_mem_PWithOracle hO₁, hL⟩

/-- If `O₁ ∈ P^{O₂}`, then `NP^{O₁} ⊆ NP^{O₂}`. -/
theorem NPWithOracle_subset_of_mem_PWithOracle {O₁ O₂ : Set (List Bool)}
    (hO₁ : O₁ ∈ PWithOracle O₂ encBits) (enc : α ↪ List Bool) :
    NPWithOracle O₁ enc ⊆ NPWithOracle O₂ enc :=
  fun _ ⟨p, V, hV, hL⟩ => ⟨p, V, hV.of_mem_PWithOracle hO₁, hL⟩

/-- **`P` relative to an oracle is closed under polynomial-time Turing reductions to word
languages.** -/
theorem PolyTimeTuringReducible.mem_PWithOracle {B O : Set (List Bool)}
    (hAB : PolyTimeTuringReducible encA encBits A B) (hB : B ∈ PWithOracle O encBits) :
    A ∈ PWithOracle O encA := by
  rw [polyTimeTuringReducible_bits_iff_mem_PWithOracle] at hAB
  exact PWithOracle_subset_of_mem_PWithOracle hB encA hAB

/-- **Polynomial-time Turing reductions through word languages compose (`≤_T ∘ ≤_T ⇒ ≤_T`).** -/
@[trans]
theorem PolyTimeTuringReducible.trans {B : Set (List Bool)}
    (hAB : PolyTimeTuringReducible encA encBits A B)
    (hBC : PolyTimeTuringReducible encBits encL B L) :
    PolyTimeTuringReducible encA encL A L :=
  hAB.mem_PWithOracle hBC

/-- Every problem reduces to itself under polynomial-time Turing reductions. -/
@[refl]
theorem PolyTimeTuringReducible.refl (encA : α ↪ List Bool) (A : Set α) :
    PolyTimeTuringReducible encA encA A A :=
  (PolyTimeReducible.refl encA A).polyTimeTuringReducible

/-- Pre-composing a polynomial-time Turing reduction with a polynomial-time many-one reduction
yields a polynomial-time Turing reduction. -/
theorem PolyTimeReducible.trans_turing
    (hAL : PolyTimeReducible encA encL A L)
    (hLB : PolyTimeTuringReducible encL encB L B) :
    PolyTimeTuringReducible encA encB A B :=
  hAL.mem_PWithOracle hLB

/-- Negating the boolean output of the decider reduces the complement `Aᶜ` to `B`. -/
theorem PolyTimeTuringReducible.compl_left
    (h : PolyTimeTuringReducible encA encB A B) :
    PolyTimeTuringReducible encA encB Aᶜ B := by
  obtain ⟨f, hf, hA⟩ := h
  refine ⟨fun a => !f a, hf.map (g := (!·)) (by fun_prop), fun a => ?_⟩
  simp [Set.mem_compl_iff, hA a]

/-- A language's complement is polynomial-time Turing reducible to the language itself. -/
theorem PolyTimeTuringReducible.compl_self (encA : α ↪ List Bool) (A : Set α) :
    PolyTimeTuringReducible encA encA Aᶜ A :=
  (PolyTimeTuringReducible.refl encA A).compl_left

/-- **`P` is closed under polynomial-time Turing reductions to word languages.** -/
theorem PolyTimeTuringReducible.mem_P {B : Set (List Bool)}
    (h : PolyTimeTuringReducible encA encBits A B) (hB : B ∈ P encBits) : A ∈ P encA := by
  rw [polyTimeTuringReducible_bits_iff_mem_PWithOracle] at h
  rwa [← PWithOracle_eq_P hB encA]

/-- `B` is hard for the class `C` under polynomial-time Turing reductions: every problem in `C`
Turing-reduces to `B`. -/
def PolyTimeTuringHard (C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α))
    (encB : β ↪ List Bool) (B : Set β) : Prop :=
  HardUnder (fun enc => PolyTimeTuringReducible enc encB) @C B

/-- `B` is complete for the class `C` under polynomial-time Turing reductions: it belongs to `C`
and is Turing-hard for `C`. -/
def PolyTimeTuringComplete (C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α))
    (encB : β ↪ List Bool) (B : Set β) : Prop :=
  CompleteUnder (fun enc => PolyTimeTuringReducible enc encB) @C encB B

/-- Hardness for `NP` under polynomial-time Turing reductions. -/
abbrev NPTuringHard (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeTuringHard @NP encB B

/-- Completeness for `NP` under polynomial-time Turing reductions. -/
abbrev NPTuringComplete (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeTuringComplete @NP encB B

/-- Hardness for `PP` under polynomial-time Turing reductions. -/
abbrev PPTuringHard (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeTuringHard PP encB B

/-- Completeness for `PP` under polynomial-time Turing reductions. -/
abbrev PPTuringComplete (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeTuringComplete PP encB B

/-- Hardness for `PSPACE` under polynomial-time Turing reductions. -/
abbrev PSPACETuringHard (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeTuringHard @PSPACE encB B

/-- Completeness for `PSPACE` under polynomial-time Turing reductions. -/
abbrev PSPACETuringComplete (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeTuringComplete @PSPACE encB B

/-- Every problem hard for `C` under polynomial-time many-one reductions is also hard for `C`
under polynomial-time Turing reductions. -/
theorem PolyTimeHard.polyTimeTuringHard {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    (h : PolyTimeHard C encB B) : PolyTimeTuringHard C encB B :=
  HardUnder.mono (fun _ _ hr => hr.polyTimeTuringReducible) h

/-- A problem that is Turing-reducible from a many-one hard problem is Turing-hard. -/
theorem PolyTimeHard.polyTimeTuringHard_of_turing {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    (hL : PolyTimeHard C encL L) (hLB : PolyTimeTuringReducible encL encB L B) :
    PolyTimeTuringHard C encB B :=
  HardUnder.trans (fun _ _ hr h_t => hr.trans_turing h_t) hL hLB

/-- **Hardness transfer to `P`**: if a problem hard for `C` under many-one reductions Turing-reduces
to a problem `B ∈ P`, then `C ⊆ P`. -/
theorem PolyTimeHard.subset_P_of_turing_mem_P
    {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    {B : Set (List Bool)} (hL : PolyTimeHard C encL L)
    (hLB : PolyTimeTuringReducible encL encBits L B) (hB : B ∈ P encBits)
    {α : Type} (encA : α ↪ List Bool) : C encA ⊆ P encA :=
  fun A hA => (hL.polyTimeTuringHard_of_turing hLB encA A hA).mem_P hB

/-- **NP-hardness transfer**: if an NP-hard problem Turing-reduces to a language in `P`, then
`P = NP`. -/
theorem NPHard.P_eq_NP_of_turing_mem_P {B : Set (List Bool)}
    (hL : NPHard encL L) (hLB : PolyTimeTuringReducible encL encBits L B)
    (hB : B ∈ P encBits) : P encBits = NP encBits :=
  Set.Subset.antisymm P_subset_NP (hL.subset_P_of_turing_mem_P hLB hB encBits)

/-- **PP-hardness transfer**: if a PP-hard problem Turing-reduces to a language in `P`, then
`P = PP`. -/
theorem PolyTimeHard.P_eq_PP_of_turing_mem_P {B : Set (List Bool)}
    (hL : PolyTimeHard PP encL L) (hLB : PolyTimeTuringReducible encL encBits L B)
    (hB : B ∈ P encBits) : P encBits = PP encBits :=
  Set.Subset.antisymm P_subset_PP (hL.subset_P_of_turing_mem_P hLB hB encBits)

/-- **PSPACE-hardness transfer**: if a PSPACE-hard problem Turing-reduces to a language in `P`,
then `P = PSPACE`. -/
theorem PSPACEHard.P_eq_PSPACE_of_turing_mem_P {B : Set (List Bool)}
    (hL : PSPACEHard encL L) (hLB : PolyTimeTuringReducible encL encBits L B)
    (hB : B ∈ P encBits) : P encBits = PSPACE encBits :=
  Set.Subset.antisymm P_subset_PSPACE (hL.subset_P_of_turing_mem_P hLB hB encBits)

/-- A problem that is Turing-hard for `C` and belongs to `P` forces `C ⊆ P`. -/
theorem PolyTimeTuringHard.subset_P_of_mem_P
    {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    {B : Set (List Bool)} (hB_hard : PolyTimeTuringHard C encBits B) (hB : B ∈ P encBits)
    {α : Type} (encA : α ↪ List Bool) : C encA ⊆ P encA :=
  fun A hA => (hB_hard encA A hA).mem_P hB

/-- If an NP-Turing-hard problem is in `P`, then `P = NP`. -/
theorem NPTuringHard.P_eq_NP_of_mem_P {B : Set (List Bool)}
    (hB_hard : NPTuringHard encBits B) (hB : B ∈ P encBits) : P encBits = NP encBits :=
  Set.Subset.antisymm P_subset_NP (hB_hard.subset_P_of_mem_P hB encBits)

/-- If a PP-Turing-hard problem is in `P`, then `P = PP`. -/
theorem PPTuringHard.P_eq_PP_of_mem_P {B : Set (List Bool)}
    (hB_hard : PPTuringHard encBits B) (hB : B ∈ P encBits) : P encBits = PP encBits :=
  Set.Subset.antisymm P_subset_PP (hB_hard.subset_P_of_mem_P hB encBits)

/-- If a PSPACE-Turing-hard problem is in `P`, then `P = PSPACE`. -/
theorem PSPACETuringHard.P_eq_PSPACE_of_mem_P {B : Set (List Bool)}
    (hB_hard : PSPACETuringHard encBits B) (hB : B ∈ P encBits) : P encBits = PSPACE encBits :=
  Set.Subset.antisymm P_subset_PSPACE (hB_hard.subset_P_of_mem_P hB encBits)

/-- If an NP-hard problem Turing-reduces to a problem in `NP ∩ coNP`, then `NP = coNP`. -/
theorem NPHard.NP_eq_coNP_of_turing_mem_NP_inter_coNP {B : Set (List Bool)}
    (hL : NPHard encL L) (hLB : PolyTimeTuringReducible encL encBits L B)
    (hB_np : B ∈ NP encBits) (hB_conp : B ∈ coNP encBits) :
    NP encBits = coNP encBits := by
  have hsub : NP encBits ⊆ coNP encBits := fun A hA => by
    have ht : PolyTimeTuringReducible encBits encBits A B :=
      hL.polyTimeTuringHard_of_turing hLB encBits A hA
    rw [polyTimeTuringReducible_bits_iff_mem_PWithOracle] at ht
    exact (PWithOracle_subset_NP_inter_coNP hB_np hB_conp ht).2
  ext A
  constructor
  · exact fun hA => hsub hA
  · intro hA
    rw [mem_coNP] at hA
    have hAc := hsub hA
    rw [mem_coNP, compl_compl] at hAc
    exact hAc

end Cslib.Complexity
