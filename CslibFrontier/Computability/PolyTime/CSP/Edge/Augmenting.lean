/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Edge.Buffer
public import CslibFrontier.Computability.PolyTime.CSP.Table
public import CslibFrontier.Computability.PolyTime.CSP.Occurrence
public import CslibFrontier.Logics.Propositional.CSP.Edge.Augmenting
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.GetD
import Mathlib.Data.List.ProdSigma
import CslibFrontier.Logics.Propositional.CNF.Occurrence

/-!
# Finite buffers for the two-phase edge-CSP augmentation

The input contains the existing explicit-table CSP, two occurrence bit buffers, and an excluded
starting variable. Positions retain constraint and scope order. All scans traverse actual lists;
no loop is paid for by a binary variable name or a table's declared arity.

This module compiles the two phases of Lemma 31 of [KazdaKolmogorovRolinek2018], arXiv v6,
Section 6.1, printed p. 15. The improving comparison is supplied as input; this routine does not
find it or solve the CSP. Walk codes represent the existing `CSP.Walk`, without introducing
another trail predicate.

## Main definitions

* `Input`: the complete explicit-table input, with two finite occurrence label buffers.
* `WalkCode`, `code`, `decode`: the representation bridge to the existing incidence walks.
* `run`: the total finite implementation, rejecting incorrect buffer widths.

## Main results

* `computableInPolyTime_run`: uniform ordinary native polynomial time in the full framed input.
* `run_eq`: exact agreement with `EdgeInstance.augmentingWalk`, without semantic assumptions.
* `run_spec`: decoded augmentation and the combined exchange bound for a valid improvement.
-/

public section

namespace Cslib.Complexity.CSP.EdgeAugmenting

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM

/-- Complete augmentation input, with bits in constraint-then-scope occurrence order. -/
structure Input where
  /-- The original CSP, with explicit table relations and binary variable names. -/
  body : CSP Table ℕ
  /-- Original occurrence labels. -/
  labels : List Bool
  /-- Supplied improving comparison, in the same positional order. -/
  comparison : List Bool
  /-- Variable excluded only as the start, not as the terminal variable. -/
  excluded : ℕ

/-- The CSP, original bits and comparison bits are framed in field order; the final variable
name is binary. Tables include their binary arity and explicitly framed Boolean rows. -/
enc_structure encInput : Input where
  body : (encCSP encTable encNat), labels : (encList encBool),
  comparison : (encList encBool), excluded : encNat

/-- A representation of an existing walk by global occurrence indices. -/
structure WalkCode where
  /-- Starting variable, encoded in binary. -/
  start : ℕ
  /-- Global occurrence indices in each ordered exchange, retaining repeated constraints. -/
  steps : List (ℕ × ℕ)
  deriving DecidableEq, Repr

/-- A binary start, framed, followed by framed pairs of binary global occurrence indices. -/
enc_structure encWalkCode : WalkCode where
  start : encNat, steps : (encList (encPair encNat encNat))

/-- Project the existing walk to global occurrence indices. -/
@[expose] def code {F : CSP Table ℕ} (w : Walk F) : WalkCode :=
  ⟨w.start, w.steps.map fun (o, p) => (occurrenceIndex o, occurrenceIndex p)⟩

private def distance (f g : List Bool) : ℕ :=
  (f.zip g).countP fun a => a.1 != a.2

private def repairPair (F : CSP Table ℕ) (f g : List Bool) : Option (Record × Record) :=
  ((CSP.occurrences F).product (CSP.occurrences F)).find? fun a =>
    decide (a.1.1 = a.2.1) && decide (a.1 ≠ a.2) &&
      (readRecord F g a.1 != readRecord F f a.1) &&
      (readRecord F g a.2 != readRecord F f a.2) &&
      !inconsistent F f a.1.2.2 && inconsistent F g a.1.2.2 &&
      valid F (flip g [(CSP.occurrences F).idxOf a.1, (CSP.occurrences F).idxOf a.2])

private def repairStep (input : Input) (state : List Bool × ℕ) : List Bool × ℕ :=
  (repairPair input.body input.labels state.1).elim state fun a =>
    (flip state.1 [(CSP.occurrences input.body).idxOf a.1,
      (CSP.occurrences input.body).idxOf a.2], state.2 + 1)

/-- First phase on finite buffers. The unary clock counts actual occurrence disagreements. -/
def repair (input : Input) : List Bool × ℕ :=
  (repairStep input)^[distance input.labels input.comparison] (input.comparison, 0)

private def findStart (input : Input) (g : List Bool) : Option Record :=
  (CSP.occurrences input.body).find? fun o => decide (o.2.2 ≠ input.excluded) &&
    inconsistent input.body input.labels o.2.2 && !inconsistent input.body g o.2.2

private def flipped (input : Input) (w : WalkCode) : List Bool :=
  flip input.labels (w.steps.flatMap fun a => [a.1, a.2])

private def recordAt (F : CSP Table ℕ) (i : ℕ) : Record :=
  (CSP.occurrences F).getD i (0, 0, 0)

private def finish (input : Input) (w : WalkCode) : ℕ :=
  w.steps.reverse.head?.elim w.start fun a => (recordAt input.body a.2).2.2

private def walkPair (input : Input) (g : List Bool) (w : WalkCode) :
    Option (Record × Record) :=
  let current := flipped input w
  ((CSP.occurrences input.body).product (CSP.occurrences input.body)).find? fun a =>
    decide (a.1.2.2 = finish input w) && decide (a.1.1 = a.2.1) && decide (a.1 ≠ a.2) &&
      (readRecord input.body current a.1 != readRecord input.body g a.1) &&
      (readRecord input.body current a.2 != readRecord input.body g a.2) &&
      valid input.body (flip current [(CSP.occurrences input.body).idxOf a.1,
        (CSP.occurrences input.body).idxOf a.2])

private def walkStep (input : Input) (g : List Bool)
    (state : WalkCode × Bool) : WalkCode × Bool :=
  if state.2 then state else
    (walkPair input g state.1).elim state fun a =>
      (⟨state.1.start, state.1.steps ++ [((CSP.occurrences input.body).idxOf a.1,
        (CSP.occurrences input.body).idxOf a.2)]⟩,
        inconsistent input.body input.labels a.2.2.2)

/-- Second phase on finite buffers. A stopped bit preserves the first reached original defect;
an exhausted or unsuccessful scan rejects. -/
def buildWalk (input : Input) (g : List Bool) (start : ℕ) : Option WalkCode :=
  let final := (walkStep input g)^[distance input.labels g] (⟨start, []⟩, false)
  if final.2 then some final.1 else none

/-- Total finite implementation of the two phases. Both buffers must have exactly the actual
occurrence count; malformed widths reject before either phase. -/
def run (input : Input) : Option WalkCode :=
  if input.labels.length = (CSP.occurrences input.body).length ∧
      input.comparison.length = (CSP.occurrences input.body).length then
    let fixed := (repair input).1
    (findStart input fixed).elim none fun o => buildWalk input fixed o.2.2
  else none

/-- Work representation: the binary start is framed, and bounded occurrence positions are
unary. This internal representation is converted to the binary `encWalkCode` on output. -/
enc_structure encWalkCodeWork : WalkCode where
  start : encNat, steps : (encList (encPair encUnary encUnary))

private theorem poly_inputBody : ComputableInPolyTime Input.body encInput
    (encCSP encTable encNat) := encInput_body_deg.computableInPolyTime
private theorem poly_inputLabels : ComputableInPolyTime Input.labels encInput
    (encList encBool) := encInput_labels_deg.computableInPolyTime
private theorem poly_inputComparison : ComputableInPolyTime Input.comparison encInput
    (encList encBool) := encInput_comparison_deg.computableInPolyTime
private theorem poly_inputExcluded : ComputableInPolyTime Input.excluded encInput encNat :=
  encInput_excluded_deg.computableInPolyTime
private theorem poly_workStart : ComputableInPolyTime WalkCode.start encWalkCodeWork encNat :=
  encWalkCodeWork_start_deg.computableInPolyTime
private theorem poly_workSteps : ComputableInPolyTime WalkCode.steps encWalkCodeWork
    (encList (encPair encUnary encUnary)) := encWalkCodeWork_steps_deg.computableInPolyTime
private theorem poly_workMk :
    ComputableInPolyTime (fun p : ℕ × List (ℕ × ℕ) => WalkCode.mk p.1 p.2)
      encWalkCodeWorkFields encWalkCodeWork := encWalkCodeWork_mk_deg.computableInPolyTime
attribute [local fun_prop] poly_inputBody poly_inputLabels poly_inputComparison poly_inputExcluded
  poly_workStart poly_workSteps poly_workMk

attribute [local fun_prop] poly_zipIdx poly_product poly_idxOf poly_records
  poly_readRecord poly_readWith poly_semWith poly_valid poly_inconsistent poly_flip
  poly_validWith poly_inconsistentWith

private theorem poly_distance :
    ComputableInPolyTime (fun p : List Bool × List Bool => distance p.1 p.2)
      (encPair (encList encBool) (encList encBool)) encUnary := by
  unfold distance
  fun_prop

attribute [local fun_prop] poly_distance

private abbrev encRepairArgs := encPair (encCSP encTable encNat)
  (encPair (encList encBool) (encList encBool))

private theorem poly_repairPair :
    ComputableInPolyTime (fun p : CSP Table ℕ × List Bool × List Bool =>
      repairPair p.1 p.2.1 p.2.2) encRepairArgs (encOption (encPair encRecord encRecord)) := by
  unfold repairPair
  apply ComputableInPolyTime.findWithInput
  · exact (poly_product encRecord encRecord).comp
      ((poly_records.comp (by fun_prop)).prod (poly_records.comp (by fun_prop)))
  · fun_prop

attribute [local fun_prop] poly_repairPair

private abbrev encRepairState := encPair (encList encBool) encUnary

private theorem poly_repairStep :
    ComputableInPolyTime (fun p : Input × (List Bool × ℕ) => repairStep p.1 p.2)
      (encPair encInput encRepairState) encRepairState := by
  unfold repairStep
  fun_prop

private theorem poly_repair :
    ComputableInPolyTime repair encInput encRepairState := by
  unfold repair
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.iterateWithInput_of_bounded_growth
    (show ComputableInPolyTime (fun x : Input => distance x.labels x.comparison)
      encInput encUnary from by fun_prop).tidy
    (show ComputableInPolyTime (fun x : Input => (x.comparison, 0))
      encInput encRepairState from by fun_prop).tidy poly_repairStep.tidy
    (growth := fun _ => 1)
  refine ⟨.const 1, ?_⟩
  intro input state
  rcases state with ⟨g, k⟩
  unfold repairStep
  cases repairPair input.body input.labels g <;>
    simp [length_encList, length_flip, encUnary_apply]; omega

attribute [local fun_prop] poly_repair

private theorem poly_findStart :
    ComputableInPolyTime (fun p : Input × List Bool => findStart p.1 p.2)
      (encPair encInput (encList encBool)) (encOption encRecord) := by
  unfold findStart
  apply ComputableInPolyTime.findWithInput (poly_records.comp (by fun_prop))
  fun_prop

private theorem poly_flipped :
    ComputableInPolyTime (fun p : Input × WalkCode => flipped p.1 p.2)
      (encPair encInput encWalkCodeWork) (encList encBool) := by
  unfold flipped
  fun_prop

private theorem poly_recordAt :
    ComputableInPolyTime (fun p : CSP Table ℕ × ℕ => recordAt p.1 p.2)
      (encPair (encCSP encTable encNat) encUnary) encRecord := by
  unfold recordAt
  exact .of_tidy (ComputableTidilyInPolyTime.listGetD_binary (0, 0, 0)
    (poly_records.comp (ComputableInPolyTime.fst (encCSP encTable encNat) encUnary)).tidy
    (ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.snd (encCSP encTable encNat) encUnary).tidy))

attribute [local fun_prop] poly_findStart poly_flipped poly_recordAt

private theorem poly_finish :
    ComputableInPolyTime (fun p : Input × WalkCode => finish p.1 p.2)
      (encPair encInput encWalkCodeWork) encNat := by
  unfold finish
  apply ComputableInPolyTime.optionElimWithInput (encB := encPair encUnary encUnary)
  · fun_prop
  · fun_prop
  · fun_prop

attribute [local fun_prop] poly_finish

private abbrev encWalkArgs := encPair (encPair encInput (encList encBool)) encWalkCodeWork

private theorem poly_walkPair :
    ComputableInPolyTime (fun p : (Input × List Bool) × WalkCode =>
      walkPair p.1.1 p.1.2 p.2) encWalkArgs (encOption (encPair encRecord encRecord)) := by
  unfold walkPair
  dsimp only
  apply ComputableInPolyTime.findWithInput
  · exact (poly_product encRecord encRecord).comp
      ((poly_records.comp (by fun_prop)).prod (poly_records.comp (by fun_prop)))
  · fun_prop

private theorem poly_walkPairWith {α : Type} {e : α ↪ List Bool}
    {input : α → Input} {bits : α → List Bool} {w : α → WalkCode}
    (hi : ComputableInPolyTime input e encInput)
    (hb : ComputableInPolyTime bits e (encList encBool))
    (hw : ComputableInPolyTime w e encWalkCodeWork) :
    ComputableInPolyTime (fun x => walkPair (input x) (bits x) (w x))
      e (encOption (encPair encRecord encRecord)) :=
by
  simpa only [Function.comp_def] using poly_walkPair.comp ((hi.prod hb).prod hw)

attribute [local fun_prop] poly_walkPair poly_walkPairWith

private abbrev encWalkState := encPair encWalkCodeWork encBool

private theorem poly_walkStep :
    ComputableInPolyTime (fun p : (Input × List Bool) × (WalkCode × Bool) =>
      walkStep p.1.1 p.1.2 p.2)
      (encPair (encPair encInput (encList encBool)) encWalkState) encWalkState := by
  unfold walkStep
  apply ComputableInPolyTime.ite (by fun_prop) (by fun_prop)
  apply ComputableInPolyTime.optionElimWithInput (encB := encPair encRecord encRecord)
  · fun_prop
  · fun_prop
  · fun_prop

private theorem poly_buildWalk :
    ComputableInPolyTime (fun p : (Input × List Bool) × ℕ =>
      buildWalk p.1.1 p.1.2 p.2)
      (encPair (encPair encInput (encList encBool)) encNat) (encOption encWalkCodeWork) := by
  have hloop : ComputableInPolyTime
      (fun p : (Input × List Bool) × ℕ =>
        (walkStep p.1.1 p.1.2)^[distance p.1.1.labels p.1.2] (⟨p.2, []⟩, false))
      (encPair (encPair encInput (encList encBool)) encNat) encWalkState := by
    apply ComputableInPolyTime.of_tidy
    apply ComputableTidilyInPolyTime.iterateWith_of_bounded_growth
      (par := fun p : (Input × List Bool) × ℕ => p.1)
      (step := fun p : Input × List Bool => walkStep p.1 p.2)
      (count := fun p : (Input × List Bool) × ℕ => distance p.1.1.labels p.1.2)
      (init := fun p : (Input × List Bool) × ℕ => ((⟨p.2, []⟩ : WalkCode), false))
      (ComputableInPolyTime.fst (encPair encInput (encList encBool)) encNat).tidy
      (show ComputableInPolyTime
        (fun p : (Input × List Bool) × ℕ => distance p.1.1.labels p.1.2)
        (encPair (encPair encInput (encList encBool)) encNat) encUnary from
        poly_distance.comp
          (((poly_inputLabels.comp (ComputableInPolyTime.fst encInput (encList encBool))).comp
            (ComputableInPolyTime.fst (encPair encInput (encList encBool)) encNat)).prod
          ((ComputableInPolyTime.snd encInput (encList encBool)).comp
            (ComputableInPolyTime.fst (encPair encInput (encList encBool)) encNat)))).tidy
      (((poly_workMk.comp
        ((ComputableInPolyTime.snd (encPair encInput (encList encBool)) encNat).prod
          (ComputableInPolyTime.const []))).prod (ComputableInPolyTime.const false)).tidy)
      poly_walkStep.tidy
      (growth := fun p => (CSP.occurrences p.1.1.body).length * 12 + 6)
    · have hr : ComputableInPolyTime
          (fun p : (Input × List Bool) × ℕ => (CSP.occurrences p.1.1.body).length)
          (encPair (encPair encInput (encList encBool)) encNat) encUnary := by fun_prop
      exact (hr.polyBounded.mul (.const 12)).add (.const 6)
    · intro p state
      rcases state with ⟨w, stopped⟩
      by_cases hs : stopped = true
      · simp [walkStep, hs]
      · cases hp : walkPair p.1.1 p.1.2 w with
        | none => simp [walkStep, hs, hp]
        | some a =>
          rcases a with ⟨o, q⟩
          have ho : (CSP.occurrences p.1.1.body).idxOf o ≤ (CSP.occurrences p.1.1.body).length :=
            List.idxOf_le_length
          have hq : (CSP.occurrences p.1.1.body).idxOf q ≤ (CSP.occurrences p.1.1.body).length :=
            List.idxOf_le_length
          simp only [walkStep, hs, hp, Option.elim_some]
          simp only [length_encPair, encWalkCodeWork_apply, length_encList,
            encUnary_apply, List.length_replicate]
          cases inconsistent p.1.1.body p.1.1.labels q.2.2 <;> simp <;> omega
  unfold buildWalk
  fun_prop

private theorem poly_buildWalkWith {α : Type} {e : α ↪ List Bool}
    {input : α → Input} {bits : α → List Bool} {start : α → ℕ}
    (hi : ComputableInPolyTime input e encInput)
    (hb : ComputableInPolyTime bits e (encList encBool))
    (hs : ComputableInPolyTime start e encNat) :
    ComputableInPolyTime (fun x => buildWalk (input x) (bits x) (start x))
      e (encOption encWalkCodeWork) := by
  simpa only [Function.comp_def] using poly_buildWalk.comp ((hi.prod hb).prod hs)

attribute [local fun_prop] poly_buildWalk poly_buildWalkWith

private theorem poly_output : ComputableInPolyTime (fun w : WalkCode => w)
    encWalkCodeWork encWalkCode := by
  have hsteps : ComputableInPolyTime (fun w : WalkCode => w.steps)
      encWalkCodeWork (encList (encPair encNat encNat)) := by
    have hb := ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary
    have hm := ComputableInPolyTime.map
      ((hb.comp (ComputableInPolyTime.fst encUnary encUnary)).prod
        (hb.comp (ComputableInPolyTime.snd encUnary encUnary)) :
        ComputableInPolyTime (fun p : ℕ × ℕ => (p.1, p.2))
        (encPair encUnary encUnary) (encPair encNat encNat))
    simpa only [Function.comp_def, List.map_id'] using
      hm.comp encWalkCodeWork_steps_deg.computableInPolyTime
  exact (encWalkCodeWork_start_deg.computableInPolyTime.prod hsteps).of_enc_eq fun _ => rfl

/-- Uniform native polynomial time on complete framed inputs, without validity, edge-instance,
even-delta-matroid or improvement assumptions. Width errors reject; all other data are processed
by list scans and occurrence clocks. -/
@[fun_prop] theorem computableInPolyTime_run :
    ComputableInPolyTime run encInput (encOption encWalkCode) := by
  have hwork : ComputableInPolyTime run encInput (encOption encWalkCodeWork) := by
    unfold run
    apply ComputableInPolyTime.ite_decide (by fun_prop) _ (by fun_prop)
    apply ComputableInPolyTime.optionElimWithInput (encB := encRecord)
    · fun_prop
    · fun_prop
    · fun_prop
  simpa only [Option.map_id'] using
    ComputableInPolyTime.optionMapWithInput (f := fun (_ : Input) (w : WalkCode) => w)
      (encC := encWalkCode) hwork
      (poly_output.comp (ComputableInPolyTime.snd encInput encWalkCodeWork))

/-- Decode global positions into the existing dependent occurrence type. Out-of-range indices
reject. This is a representation bridge, with no additional mathematical walk predicate. -/
@[expose] def decode (F : CSP Table ℕ) (w : WalkCode) : Option (Walk F) := do
  let steps ← w.steps.mapM fun (o, p) => do
    let a ← (incidenceList F)[o]?
    let b ← (incidenceList F)[p]?
    pure (a, b)
  pure ⟨w.start, steps⟩

/-- The walk representation is lossless, including empty walks and repeated constraint visits. -/
theorem decode_code {F : CSP Table ℕ} (w : Walk F) : decode F (code w) = some w := by
  rcases w with ⟨start, steps⟩
  have hm : steps.mapM (fun a : Occurrence F × Occurrence F => some a) = some steps := by
    simpa only [List.map_id, Option.pure_def, id_eq] using
      (List.mapM_pure (m := Option) (l := steps) (f := id))
  simp [decode, code, List.mapM_map, Function.comp_def, getElem?_occurrenceIndex, hm]

private theorem buffer_eq {F : CSP Table ℕ} (bits : List Bool)
    (hlen : bits.length = (incidenceList F).length) :
    bits = (incidenceList F).map (labeling F bits) := by
  apply List.ext_getElem
  · simpa using hlen
  · intro i hi hj
    have ho : i < (incidenceList F).length := by omega
    have he := (incidenceList_nodup F).idxOf_getElem i ho
    simp only [List.getElem_map, labeling, occurrenceIndex, he,
      List.getD_eq_getElem _ _ hi]

private theorem distance_eq {F : CSP Table ℕ} (f g : List Bool)
    (hf : f.length = (incidenceList F).length)
    (hg : g.length = (incidenceList F).length) :
    distance f g = hammingDist (labeling F f) (labeling F g) := by
  have hu : (incidenceList F).toFinset = Finset.univ := by
    ext o
    simp [mem_incidenceList]
  conv_lhs => rw [buffer_eq f hf, buffer_eq g hg]
  rw [distance, List.zip_map', List.countP_map, hammingDist, ← hu,
    (incidenceList_nodup F).card_eq_countP]
  congr 1

private theorem pairs_records (F : CSP Table ℕ) :
    (CSP.occurrences F).product (CSP.occurrences F) =
      ((incidenceList F).product (incidenceList F)).map
        (fun (o, p) => (o.record, p.record)) := by
  simp [occurrences_eq_map_incidenceList, List.product, List.flatMap_map,
    List.map_flatMap, List.map_map,
    Function.comp_def]

private theorem repairPair_eq (F : CSP Table ℕ) (f g : List Bool)
    (hg : g.length = (incidenceList F).length) :
    repairPair F f g =
      (EdgeInstance.findPair F (EdgeInstance.RepairMove Table.sem
        (labeling F f) (labeling F g))).map fun (o, p) => (o.record, p.record) := by
  unfold repairPair EdgeInstance.findPair
  rw [pairs_records, List.find?_map]
  congr 2
  funext a
  rcases a with ⟨o, p⟩
  have hflip := labeling_flip g [o, p] hg
  have hne : o.record ≠ p.record ↔ o ≠ p := Occurrence.record_injective.ne_iff
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  change (decide (o.1.val = p.1.val) && decide (o.record ≠ p.record) &&
    (readRecord F g o.record != readRecord F f o.record) &&
    (readRecord F g p.record != readRecord F f p.record) &&
    !inconsistent F f o.var && inconsistent F g o.var &&
    valid F (flip g [(CSP.occurrences F).idxOf o.record,
      (CSP.occurrences F).idxOf p.record]) = true) ↔ _
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    read_record, record_index, valid_eq, inconsistent_eq,
    hne, Fin.val_inj, EdgeInstance.RepairMove]
  simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
    Finset.insert_empty] at hflip
  rw [hflip]
  simp only [← decide_not, decide_eq_true_eq]
  tauto


private theorem repair_length (input : Input) (n : ℕ) (state : List Bool × ℕ) :
    ((repairStep input)^[n] state).1.length = state.1.length := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    unfold repairStep
    cases repairPair input.body input.labels state.1 <;> simp [length_flip]

private theorem repair_iter (input : Input) (n : ℕ) (g : List Bool) (k : ℕ)
    (hg : g.length = (incidenceList input.body).length) :
    let actual := EdgeInstance.repair Table.sem (labeling input.body input.labels) n
      (labeling input.body g)
    labeling input.body ((repairStep input)^[n] (g, k)).1 = actual.1 ∧
      ((repairStep input)^[n] (g, k)).2 = k + actual.2 := by
  induction n generalizing g k with
  | zero => simp [EdgeInstance.repair]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have hstep : repairStep input (g, k) =
        ((EdgeInstance.findPair input.body (EdgeInstance.RepairMove Table.sem
          (labeling input.body input.labels) (labeling input.body g))).map
          (fun (a : Occurrence input.body × Occurrence input.body) =>
            (a.1.record, a.2.record))).elim (g, k) fun a =>
            (flip g [(CSP.occurrences input.body).idxOf a.1,
              (CSP.occurrences input.body).idxOf a.2], k + 1) := by
      simp only [repairStep, repairPair_eq _ _ _ hg]
    rw [hstep]
    cases hs : EdgeInstance.findPair input.body (EdgeInstance.RepairMove Table.sem
        (labeling input.body input.labels) (labeling input.body g)) with
    | none =>
      have hfixed : ∀ n, (repairStep input)^[n] (g, k) = (g, k) := by
        intro n
        apply Function.iterate_fixed
        simp [repairStep, repairPair_eq _ _ _ hg, hs]
      simp only [Option.map_none, Option.elim_none, hfixed, EdgeInstance.repair, hs,
        Nat.add_zero, and_self]
    | some a =>
      rcases a with ⟨o, p⟩
      have hl := labeling_flip g [o, p] hg
      have hi := ih (flip g [occurrenceIndex o, occurrenceIndex p]) (k + 1)
        (by simpa only [length_flip] using hg)
      simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
        Finset.insert_empty] at hl
      simpa only [Option.map_some, Option.elim_some, Prod.fst, Prod.snd, record_index,
        EdgeInstance.repair, hs, hl,
        Nat.add_assoc, Nat.add_comm 1] using hi

private theorem recordAt_index {F : CSP Table ℕ} (o : Occurrence F) :
    recordAt F (occurrenceIndex o) = o.record := by
  have hi := occurrenceIndex_lt o
  simp [recordAt, occurrences_eq_map_incidenceList, List.getD_eq_getElem?_getD,
    getElem?_occurrenceIndex]

private theorem flipped_eq (input : Input) (w : Walk input.body)
    (hlen : input.labels.length = (incidenceList input.body).length) :
    labeling input.body (flipped input (code w)) = w.flip (labeling input.body input.labels) := by
  have he : (code w).steps.flatMap (fun (o, p) => [o, p]) =
      w.edges.map occurrenceIndex := by
    simp [code, Walk.edges, Walk.edgesOf, List.flatMap_map, List.map_flatMap]
  rw [flipped, he, labeling_flip _ _ hlen]
  rfl

private theorem finish_eq (input : Input) (w : Walk input.body) :
    finish input (code w) = w.finish := by
  rcases w with ⟨r, s⟩
  induction s using List.reverseRecOn with
  | nil => rfl
  | append_singleton s a ih =>
    rcases a with ⟨o, p⟩
    simp [finish, code, List.map_append, recordAt_index, Walk.finish,
      Walk.finishFrom_append, Walk.finishFrom, Occurrence.record]

private theorem walkPair_eq (input : Input) (g : List Bool) (w : Walk input.body)
    (hlen : input.labels.length = (incidenceList input.body).length) :
    walkPair input g (code w) =
      (EdgeInstance.findPair input.body (EdgeInstance.WalkMove Table.sem
        (labeling input.body g) (w.flip (labeling input.body input.labels)) w.finish)).map
        fun (o, p) => (o.record, p.record) := by
  unfold walkPair EdgeInstance.findPair
  rw [pairs_records, List.find?_map]
  congr 2
  funext a
  rcases a with ⟨o, p⟩
  have hf : (flipped input (code w)).length = (incidenceList input.body).length := by
    rw [flipped, length_flip, hlen]
  have hflip := labeling_flip (flipped input (code w)) [o, p] hf
  have hne : o.record ≠ p.record ↔ o ≠ p := Occurrence.record_injective.ne_iff
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  change (decide (o.var = finish input (code w)) && decide (o.1.val = p.1.val) &&
    decide (o.record ≠ p.record) &&
    (readRecord input.body (flipped input (code w)) o.record != readRecord input.body g o.record) &&
    (readRecord input.body (flipped input (code w)) p.record != readRecord input.body g p.record) &&
    valid input.body (flip (flipped input (code w))
      [(CSP.occurrences input.body).idxOf o.record,
        (CSP.occurrences input.body).idxOf p.record]) = true) ↔ _
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, read_record,
    record_index, valid_eq, hne, Fin.val_inj, finish_eq, EdgeInstance.WalkMove]
  simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
    Finset.insert_empty] at hflip
  rw [hflip, flipped_eq _ _ hlen]
  tauto

private theorem walkStep_stopped (input : Input) (g : List Bool) (w : WalkCode) (n : ℕ) :
    (walkStep input g)^[n] (w, true) = (w, true) :=
  Function.iterate_fixed (by simp [walkStep]) n

private theorem buildWalk_iter (input : Input) (g : List Bool) (n : ℕ)
    (w : Walk input.body)
    (hlen : input.labels.length = (incidenceList input.body).length) :
    (let final := (walkStep input g)^[n] (code w, false)
      if final.2 then some final.1 else none) =
      (EdgeInstance.buildWalk Table.sem (labeling input.body input.labels)
        (labeling input.body g) n w).map code := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have hstep : walkStep input g (code w, false) =
        ((EdgeInstance.findPair input.body (EdgeInstance.WalkMove Table.sem
          (labeling input.body g) (w.flip (labeling input.body input.labels)) w.finish)).map
          (fun a => (a.1.record, a.2.record))).elim (code w, false) fun a =>
            (⟨(code w).start, (code w).steps ++ [((CSP.occurrences input.body).idxOf a.1,
              (CSP.occurrences input.body).idxOf a.2)]⟩,
              inconsistent input.body input.labels a.2.2.2) := by
      simp only [walkStep, Bool.false_eq_true, ite_false, walkPair_eq _ _ _ hlen]
    rw [hstep]
    cases hs : EdgeInstance.findPair input.body (EdgeInstance.WalkMove Table.sem
        (labeling input.body g) (w.flip (labeling input.body input.labels)) w.finish) with
    | none =>
      have hfixed : (walkStep input g) (code w, false) = (code w, false) := by
        simp [walkStep, walkPair_eq _ _ _ hlen, hs]
      simp only [Option.map_none, Option.elim_none, Function.iterate_fixed hfixed]
      simp [EdgeInstance.buildWalk, hs]
    | some a =>
      rcases a with ⟨o, p⟩
      have he : (⟨(code w).start, (code w).steps ++
          [(occurrenceIndex o, occurrenceIndex p)]⟩ : WalkCode) = code (w.snoc o p) := by
        simp [code, Walk.snoc, List.map_append]
      simp only [Option.map_some, Option.elim_some, record_index, he, inconsistent_eq]
      have hvar : p.record.2.2 = p.var := rfl
      rw [hvar]
      by_cases hp : Inconsistent (labeling input.body input.labels) p.var
      · simp [hp, walkStep_stopped, EdgeInstance.buildWalk, hs]
      · simpa only [hp, decide_false, EdgeInstance.buildWalk, hs, ite_false] using
          ih (w.snoc o p)

private theorem findStart_eq (input : Input) (g : List Bool) :
    findStart input g =
      (EdgeInstance.findStart input.body (labeling input.body input.labels)
        (labeling input.body g) input.excluded).map Occurrence.record := by
  unfold findStart EdgeInstance.findStart
  rw [occurrences_eq_map_incidenceList, List.find?_map]
  congr 2
  funext o
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  change (decide (o.var ≠ input.excluded) && inconsistent input.body input.labels o.var &&
    !inconsistent input.body g o.var = true) ↔ _
  simp [inconsistent_eq, and_assoc]

/-- Exact compilation of the mathematical two-phase routine, including its deterministic scan
order, both Hamming clocks and failure cases. Only the two exact buffer-width guards are needed. -/
theorem run_eq (input : Input)
    (hf : input.labels.length = (incidenceList input.body).length)
    (hg : input.comparison.length = (incidenceList input.body).length) :
    run input = (EdgeInstance.augmentingWalk Table.sem
      (labeling input.body input.labels) (labeling input.body input.comparison)
      input.excluded).map code := by
  have hr := repair_iter input (distance input.labels input.comparison)
    input.comparison 0 hg
  have hlength : (repair input).1.length = (incidenceList input.body).length :=
    (repair_length input (distance input.labels input.comparison)
      (input.comparison, 0)).trans hg
  have he : labeling input.body (repair input).1 =
      (EdgeInstance.repair Table.sem (labeling input.body input.labels)
        (hammingDist (labeling input.body input.labels)
          (labeling input.body input.comparison)) (labeling input.body input.comparison)).1 := by
    simpa only [repair, distance_eq _ _ hf hg] using hr.1
  simp only [run, occurrences_eq_map_incidenceList, List.length_map, hf, hg, and_self, ite_true,
    findStart_eq, EdgeInstance.augmentingWalk, ← he]
  cases hs : EdgeInstance.findStart input.body (labeling input.body input.labels)
      (labeling input.body (repair input).1) input.excluded with
  | none => rfl
  | some o =>
    simp only [Option.map_some]
    simp only [Option.elim_some]
    unfold buildWalk
    rw [distance_eq _ _ hf hlength]
    exact buildWalk_iter input _ _ ⟨o.var, []⟩ hf

/-- A valid improving comparison yields an actual augmenting walk, decoded into the existing
model. The start alone avoids the excluded variable; the exchange bound is the original one. -/
theorem run_spec (input : Input)
    (hfwidth : input.labels.length = (incidenceList input.body).length)
    (hgwidth : input.comparison.length = (incidenceList input.body).length)
    (hedge : EdgeInstance input.body) (heven : EdgeInstance.EvenConstraints Table.sem input.body)
    (hf : ValidLabeling Table.sem (labeling input.body input.labels))
    (hg : ValidLabeling Table.sem (labeling input.body input.comparison))
    (hlt : (defects (labeling input.body input.comparison)).card <
      (defects (labeling input.body input.labels)).card) :
    ∃ w : Walk input.body, run input = some (code w) ∧ decode input.body (code w) = some w ∧
      w.IsAugmenting Table.sem (labeling input.body input.labels) ∧
      w.start ≠ input.excluded ∧
      2 * ((repair input).2 + w.steps.length) ≤
        hammingDist (labeling input.body input.labels) (labeling input.body input.comparison) := by
  obtain ⟨w, hw, ha, hx, hb⟩ := hedge.augmentingWalk_spec heven hf hg hlt input.excluded
  refine ⟨w, ?_, decode_code w, ha, hx, ?_⟩
  · rw [run_eq input hfwidth hgwidth, hw, Option.map_some]
  · have hk := (repair_iter input (distance input.labels input.comparison)
        input.comparison 0 hgwidth).2
    simp only [Nat.zero_add, distance_eq _ _ hfwidth hgwidth] at hk
    change 2 * ((repair input).2 + w.steps.length) ≤ _
    have hk' : (repair input).2 =
        (EdgeInstance.repair Table.sem (labeling input.body input.labels)
          (hammingDist (labeling input.body input.labels) (labeling input.body input.comparison))
          (labeling input.body input.comparison)).2 := by
      simpa only [repair, distance_eq _ _ hfwidth hgwidth] using hk
    rw [hk']
    exact hb

/-- Repair flips bits without changing the comparison buffer's width, on every input. -/
theorem length_repair (input : Input) : (repair input).1.length = input.comparison.length :=
  repair_length input (distance input.labels input.comparison) (input.comparison, 0)

private theorem walk_length (input : Input) (g : List Bool) (n : ℕ) (s : WalkCode × Bool) :
    ((walkStep input g)^[n] s).1.steps.length ≤ s.1.steps.length + n := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have hb := ih (walkStep input g s)
    have hs : (walkStep input g s).1.steps.length ≤ s.1.steps.length + 1 := by
      unfold walkStep
      split
      · omega
      · cases walkPair input g s.1 <;> simp
    omega

/-- Every successful output has at most the original buffer's length in steps, independently
of semantic validity. With the width guard this is the actual occurrence count. -/
theorem run_steps_length_le (input : Input) {w : WalkCode} (hw : run input = some w) :
    w.steps.length ≤ input.labels.length := by
  unfold run at hw
  split at hw
  · cases ho : findStart input (repair input).1 with
    | none => simp only [ho, Option.elim_none] at hw; cases hw
    | some o =>
      simp only [ho, Option.elim_some] at hw
      unfold buildWalk at hw
      dsimp only at hw
      split at hw
      · have he := Option.some.inj hw
        rw [← he]
        have hb := walk_length input (repair input).1
          (distance input.labels (repair input).1) (⟨o.2.2, []⟩, false)
        have hc : distance input.labels (repair input).1 ≤ input.labels.length :=
          List.countP_le_length.trans (by simp)
        have hb' : ((walkStep input (repair input).1)^[distance input.labels (repair input).1]
            ((⟨o.2.2, []⟩ : WalkCode), false)).1.steps.length ≤
              distance input.labels (repair input).1 := by simpa using hb
        exact hb'.trans hc
      · cases hw
  · cases hw

/-- The width guard rejects either short or long original/comparison buffers. -/
theorem run_eq_none_of_length (input : Input)
    (h : input.labels.length ≠ (incidenceList input.body).length ∨
      input.comparison.length ≠ (incidenceList input.body).length) : run input = none := by
  simp only [run, occurrences_eq_map_incidenceList, List.length_map]
  split
  · exact (h.elim (fun hn => hn ‹_ ∧ _›.1) (fun hn => hn ‹_ ∧ _›.2)).elim
  · rfl

end Cslib.Complexity.CSP.EdgeAugmenting
