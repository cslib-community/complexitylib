/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Multicover.Native
public import CslibFrontier.Probability.StochasticOracle.PartialCoverThresholdNative
public import CslibFrontier.Probability.StochasticOracle.PartialCoverAsymptotics
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Mathlib.Tactic

/-!
# Native threshold, greedy scan and emitted-plan composition

Theorem 4 of [Wang2027] (PDF pp. 10–11), for finite runtime eligibility masks
and binary rational costs/probability/budget. The same native computation derives
the sufficient threshold from `δ/n`, executes the complete greedy planner and
emits original source labels. Its resource parameter is binary input length plus
the numerical threshold; no threshold or runtime certificate is an input field.

## Main definitions

* `Request`, `encoding`: original ground size, oracle table and rational risk data.
* `count`, `plan`, `labels`: derived threshold, complete plan and source-label output.

## Main results

* `uniform_plan`: uniform native time/space bounds for the composition.
* `decoded_labels_eq`: actual output indices decode to the source greedy batch.
* `risk_bill`: source risk/approximation bounds for the same emitted output.
* `labels_lt`: source indices are constructed from the original table.
-/

public section
namespace Cslib.Probability.StochasticOracle.PartialCover.GreedyNative
open Turing.MultiTapeTM Cslib.Algorithms.Lean
open Multicover

/-- Original runtime data, with no repetition count supplied. -/
structure Request where
  /-- Ground-prefix size, in unary. -/
  ground : ℕ
  /-- Eligibility/cost rows. Source identifiers are their table positions; the
  serialized generic row labels are replaced by `numberedRows`. -/
  rows : List Native.Row
  /-- Binary rational failure probability and global risk budget. -/
  parameters : ThresholdNative.Parameters
  deriving DecidableEq

/-- Framed unary ground size, framed oracle rows and binary rational risk parameters. -/
enc_structure requestEncoding : Request where ground : encUnary,
  rows : (encList Native.rowEncoding), parameters : ThresholdNative.encoding

/-- The source domain, independently of coverage feasibility or algorithm resources. -/
structure Valid (x : Request) : Prop where
  /-- Nonempty ground for the sufficient per-element risk budget. -/
  ground_pos : 0 < x.ground
  /-- Source probability and risk budget conditions. -/
  parameters_valid : ThresholdNative.Valid x.parameters

/-- Valid source requests; the validity proofs are erased from the runtime word. -/
abbrev Input := {x : Request // Valid x}

/-- Exactly the original request bytes; no count or proof bits are appended. -/
abbrev encoding : Input ↪ List Bool :=
  ⟨fun x => requestEncoding x.val, fun _ _ h => Subtype.ext (requestEncoding.injective h)⟩

/-- Actual preprocessing computes the sufficient per-element budget by exact division. -/
@[expose] def scaled (x : Request) : ThresholdNative.Parameters :=
  ⟨x.parameters.q, x.parameters.budget / x.ground⟩

/-- The actual per-element parameters, with their source-domain proof erased. -/
@[expose] def thresholdInput (x : Input) : ThresholdNative.Input :=
  ⟨scaled x.val, x.property.parameters_valid.q_pos, x.property.parameters_valid.q_lt_one,
    div_pos x.property.parameters_valid.budget_pos (by exact_mod_cast x.property.ground_pos)⟩

/-- Construct source oracle indices from actual runtime table positions. -/
@[expose] def numberedRows (x : Request) : List Native.Row :=
  x.rows.zipIdx.map fun tagged => { tagged.1 with label := tagged.2 }

/-- Numbering changes no eligibility or cost in the mathematical source instance. -/
theorem numbered_interpret (x : Request) (n : ℕ) :
    (numberedRows x).map (Native.interpret n) = x.rows.map (Native.interpret n) := by
  simp only [numberedRows, List.map_map]
  change x.rows.zipIdx.map (fun tagged => Native.interpret n tagged.1) = _
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map (Native.interpret n)) (List.zipIdx_map_fst 0 x.rows)

/-- The sufficient threshold is computed from the original input, not passed by a caller. -/
@[expose] def count (x : Input) : ℕ := ThresholdNative.count (thresholdInput x)

/-- Complete native greedy plan from original risk data and the derived threshold. -/
@[expose] def plan (x : Input) : List Native.Row :=
  Native.batch ⟨x.val.ground, count x, numberedRows x.val⟩

/-- Actual original source identifiers, in emitted-call order. -/
@[expose] def labels (x : Input) : List ℕ := (plan x).map Native.Row.label

/-- Source resource parameter: binary input length plus the computed numerical threshold. -/
@[expose] def size (x : Input) : ℕ := count x + (encoding x).length

private def Budgeted {α β : Type} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) (measure : α → ℕ) : Prop :=
  ∃ T S, PolyBounded measure T ∧ PolyBounded measure S ∧ ComputableInO f encIn encOut T S

private theorem budgeted_poly {α β : Type} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {measure : α → ℕ}
    (hf : ComputableInPolyTime f encIn encOut)
    (hn : PolyBounded measure (fun x => (encIn x).length)) : Budgeted f encIn encOut measure := by
  obtain ⟨t, s, ht, hs, k, Control, hfin, machine, hm⟩ := hf
  refine ⟨fun x => t (encIn x).length, fun x => s (encIn x).length + t (encIn x).length,
    (PolyBounded.of_polynomiallyBounded id ht).comp hn,
    ((PolyBounded.of_polynomiallyBounded id hs).comp hn).add
      ((PolyBounded.of_polynomiallyBounded id ht).comp hn), ?_⟩
  refine ComputableInO.of_bounds ⟨k, Control, hfin, machine, hm⟩ 1
    (fun _ => by omega) (fun _ => by omega) (fun x => ?_)
  have hl := (hm x).length_output_le
  change (encOut (f x)).length ≤ t (encIn x).length at hl
  omega

private theorem after_poly {α β γ : Type} {f : β → γ} {g : α → β}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {measure : α → ℕ} (hf : ComputableInPolyTime f encMid encOut)
    (hg : Budgeted g encIn encMid measure) : Budgeted (f ∘ g) encIn encOut measure := by
  obtain ⟨tg, sg, htg, hsg, hg⟩ := hg
  obtain ⟨tf, sf, htf, hsf, hf⟩ := budgeted_poly hf (measure := fun y => (encMid y).length) .self
  obtain ⟨c, hc⟩ := hg.length_le
  have hn : PolyBounded measure (fun x => (encMid (g x)).length) :=
    ((PolyBounded.const c).mul (hsg.add (.const 1))).mono hc
  exact ⟨_, _, htg.add (htf.comp hn), hsg.add (hsf.comp hn), hf.comp hg⟩

private theorem input_length : PolyBounded size (fun x => (encoding x).length) :=
  PolyBounded.self.mono fun _ => Nat.le_add_left _ _
private theorem count_bound : PolyBounded size count :=
  PolyBounded.self.mono fun _ => Nat.le_add_right _ _

private theorem ground_computable : ComputableInPolyTime Request.ground requestEncoding
    encUnary :=
  requestEncoding_ground_deg.computableInPolyTime
private theorem rows_computable : ComputableInPolyTime Request.rows requestEncoding
    (encList Native.rowEncoding) := requestEncoding_rows_deg.computableInPolyTime
private theorem parameters_computable : ComputableInPolyTime Request.parameters requestEncoding
    ThresholdNative.encoding := requestEncoding_parameters_deg.computableInPolyTime
private theorem scaled_computable : ComputableInPolyTime scaled requestEncoding
    ThresholdNative.encoding := by
  have hq := ThresholdNative.encoding_q_deg.computableInPolyTime.comp parameters_computable
  have hd := ThresholdNative.encoding_budget_deg.computableInPolyTime.comp parameters_computable
  have hn := ComputableInPolyTime.ratBin_natCast.comp
    (ComputableInPolyTime.unary_to_binary.comp ground_computable)
  have hb := ComputableInPolyTime.ratBin_div.comp (hd.prod hn)
  exact (hq.prod hb).of_enc_eq fun _ => rfl

private theorem threshold_computable : ComputableInPolyTime thresholdInput encoding
    ThresholdNative.inputEncoding := by
  have hv : ComputableInPolyTime (fun x : Input => x.val) encoding requestEncoding :=
    .of_eq fun _ => rfl
  exact (scaled_computable.comp hv).of_enc_eq fun _ => rfl

private theorem numbered_computable : ComputableInPolyTime numberedRows requestEncoding
    (encList Native.rowEncoding) := by
  let encTagged := encPair Native.rowEncoding encUnary
  have hzip := (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.zipIdx Native.rowEncoding)).comp rows_computable
  have hold := ComputableInPolyTime.fst Native.rowEncoding encUnary
  have hindex := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.snd Native.rowEncoding encUnary)
  have hm := Native.rowEncoding_mask_deg.computableInPolyTime.comp hold
  have hc := Native.rowEncoding_cost_deg.computableInPolyTime.comp hold
  have hrenum : ComputableInPolyTime (fun p : Native.Row × ℕ => { p.1 with label := p.2 })
      encTagged Native.rowEncoding := (hindex.prod (hm.prod hc)).of_enc_eq fun _ => rfl
  exact ComputableInPolyTime.mapWithInput hzip
    (hrenum.comp (ComputableInPolyTime.snd requestEncoding encTagged))

private def assemble (p : Input × ℕ) : Native.Input :=
  ⟨p.1.val.ground, p.2, numberedRows p.1.val⟩

private theorem assemble_computable : ComputableInPolyTime assemble
    (encPair encoding encUnary) Native.inputEncoding := by
  have hv : ComputableInPolyTime (fun x : Input => x.val) encoding requestEncoding :=
    .of_eq fun _ => rfl
  have hg := ground_computable.comp hv
  have hr := numbered_computable.comp hv
  have hfirst := ComputableInPolyTime.fst encoding encUnary
  have hcount := ComputableInPolyTime.snd encoding encUnary
  exact ((hg.comp hfirst).prod (hcount.prod (hr.comp hfirst))).of_enc_eq fun _ => rfl

private theorem count_native : Budgeted count encoding encUnary size := by
  obtain ⟨tp, sp, htp, hsp, hp⟩ := budgeted_poly threshold_computable input_length
  obtain ⟨k, hk⟩ := hp.length_le
  have hword : PolyBounded size
      (fun x => (ThresholdNative.inputEncoding (thresholdInput x)).length) :=
    ((PolyBounded.const k).mul (hsp.add (.const 1))).mono hk
  let m := fun y : ThresholdNative.Input => ThresholdNative.count y +
    (ThresholdNative.inputEncoding y).length
  have hm : PolyBounded size (fun x => m (thresholdInput x)) :=
    count_bound.add hword
  have hr : PolyBounded m ThresholdNative.count :=
    PolyBounded.self.mono fun _ => Nat.le_add_right _ _
  obtain ⟨c, d, hc⟩ := ThresholdNative.uniform_threshold
  let T := fun y : ThresholdNative.Input =>
    c * (ThresholdNative.count y + 1) * (m y + 1) ^ d
  let S := fun y : ThresholdNative.Input => c * (m y + 1) ^ d + ThresholdNative.count y
  have hT : PolyBounded m T :=
    ((PolyBounded.const c).mul (hr.add (.const 1))).mul ((PolyBounded.self.add (.const 1)).pow d)
  have hS : PolyBounded m S :=
    ((PolyBounded.const c).mul ((PolyBounded.self.add (.const 1)).pow d)).add hr
  have ho : ComputableInO ThresholdNative.count ThresholdNative.inputEncoding encUnary T S := by
    refine ComputableInO.of_bounds hc 1
      (fun _ => by dsimp [T, m]; omega) (fun _ => by dsimp [S, m]; omega) ?_
    intro y
    simp only [encUnary_apply, List.length_replicate]
    dsimp [S]
    omega
  refine ⟨_, _, htp.add (hT.comp hm), hsp.add (hS.comp hm), ?_⟩
  exact (ho.comp hp).of_enc_eq fun _ => rfl

/-- A uniform native machine executes preprocessing, exact threshold search,
all greedy iterations and original-label output. Resources are bounded by fixed
polynomials in `size`, independently of all runtime inputs. -/
theorem uniform_plan : ∃ T S : Input → ℕ,
    PolyBounded size T ∧ PolyBounded size S ∧
      ComputableInTimeAndSpace labels encoding (encList encNat) T S := by
  obtain ⟨tc, sc, htc, hsc, hc⟩ := count_native
  have hid : ComputableInO (fun x : Input => x) encoding encoding
      (fun x => (encoding x).length) (fun x => (encoding x).length) := .of_eq fun _ => rfl
  have hpair : Budgeted (fun x : Input => (x, count x)) encoding
      (encPair encoding encUnary) size :=
    ⟨_, _, input_length.add htc, input_length.add hsc, hid.prod hc⟩
  obtain ⟨T, S, hT, hS, ho⟩ := after_poly Native.labels_computable
    (after_poly assemble_computable hpair)
  have hf : ComputableInO labels encoding (encList encNat) T S := ho.of_enc_eq fun _ => rfl
  obtain ⟨c, hf, _⟩ := hf
  exact ⟨_, _, (PolyBounded.const c).mul (hT.add (.const 1)),
    (PolyBounded.const c).mul (hS.add (.const 1)), hf⟩

/-- The derived threshold equals the source's sufficient logarithmic ceiling. -/
theorem count_eq (x : Input) : count x =
    Instance.repetitions (x.val.parameters.q : ℝ)
      ((x.val.parameters.budget : ℝ) / x.val.ground) := by
  simpa only [count, thresholdInput, scaled, Rat.cast_div, Rat.cast_natCast] using
    ThresholdNative.count_eq_repetitions (thresholdInput x)

/-- The emitted runtime rows decode to the exact source greedy plan for the
sufficient logarithmic repetition threshold. -/
theorem plan_eq (x : Input) : (plan x).map (Native.interpret x.val.ground) =
    Multicover.batch (x.val.rows.map (Native.interpret x.val.ground))
      (Instance.repetitions (x.val.parameters.q : ℝ)
        ((x.val.parameters.budget : ℝ) / x.val.ground)) := by
  rw [← count_eq x]
  have h := Native.batch_eq (⟨x.val.ground, count x, numberedRows x.val⟩ : Native.Input)
  simpa only [plan, numbered_interpret] using h

/-- Emitted identifiers are actual original oracle positions, derived by the code
rather than supplied as a validity promise about arbitrary caller labels. -/
theorem labels_lt (x : Input) {j : ℕ} (hj : j ∈ labels x) : j < x.val.rows.length := by
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hj
  have hm := Native.batch_mem (⟨x.val.ground, count x, numberedRows x.val⟩ : Native.Input) hr
  obtain ⟨tagged, ht, he⟩ := List.mem_map.mp hm
  subst row
  exact (List.snd_lt_of_mem_zipIdx ht).trans_le (by omega)

/-- Decode a source identifier against the original runtime oracle table. The
fallback is unreachable on the output, by `labels_lt`. -/
@[expose] def oracleAt (x : Request) (j : ℕ) : Oracle (Fin x.ground) :=
  Native.interpret x.ground (x.rows[j]?.getD ⟨0, [], 0⟩)

/-- The actual emitted identifier list, decoded from the original input, equals
exactly the source greedy batch. No output-correspondence premise is assumed. -/
theorem decoded_labels_eq (x : Input) : (labels x).map (oracleAt x.val) =
    Multicover.batch (x.val.rows.map (Native.interpret x.val.ground))
      (Instance.repetitions (x.val.parameters.q : ℝ)
        ((x.val.parameters.budget : ℝ) / x.val.ground)) := by
  rw [labels, List.map_map]
  have he : (plan x).map (fun row => oracleAt x.val row.label) =
      (plan x).map (Native.interpret x.val.ground) := by
    apply List.map_congr_left
    intro row hr
    have hm := Native.batch_mem
      (⟨x.val.ground, count x, numberedRows x.val⟩ : Native.Input) hr
    obtain ⟨⟨old, j⟩, ht, rfl⟩ := List.mem_map.mp hm
    have hg := List.mem_zipIdx_iff_getElem?.mp ht
    simp only [oracleAt, hg, Option.getD_some, Native.interpret]
  exact he.trans (plan_eq x)

/-- The native output inherits the source risk/cost comparison against every
risk-feasible benchmark. The only feasibility assumptions describe input oracle
eligibilities, nonnegative costs and the benchmark's risk, not a desired output. -/
theorem risk_bill (x : Input) {m : ℕ}
    (I : Instance (Fin x.val.ground) (Fin m)) (hground : I.ground = Finset.univ)
    (hcover : ∀ e : Fin x.val.ground, ∃ row ∈ x.val.rows, row.mask[e.val]?.getD false = true)
    (hcost : ∀ row ∈ x.val.rows, 0 ≤ row.cost)
    (hδone : x.val.parameters.budget < 1) (benchmark : List (Oracle (Fin x.val.ground)))
    (hsub : ∀ row ∈ benchmark, row ∈ x.val.rows.map (Native.interpret x.val.ground))
    (hrisk : (∑ e ∈ I.ground, (x.val.parameters.q : ℝ) ^
      Instance.chances e (benchmark.map Oracle.eligible)) ≤ x.val.parameters.budget) :
    let calls := (labels x).map (oracleAt x.val)
    (∑ e ∈ I.ground, (x.val.parameters.q : ℝ) ^ Instance.chances e
      (calls.map Oracle.eligible)) ≤ x.val.parameters.budget ∧
    (bill calls : ℝ) ≤ Asymptotics.factor x.val.parameters.q x.val.parameters.budget
      x.val.ground * (bill benchmark : ℝ) := by
  dsimp only
  rw [decoded_labels_eq]
  have hU : I.ground.Nonempty := by
    rw [hground]
    exact ⟨⟨0, x.property.ground_pos⟩, Finset.mem_univ _⟩
  have hc : ∀ e, ∃ row ∈ x.val.rows.map (Native.interpret x.val.ground), e ∈ row.eligible := by
    intro e
    obtain ⟨row, hr, he⟩ := hcover e
    exact ⟨_, List.mem_map.mpr ⟨row, hr, rfl⟩, by simpa [Native.interpret] using he⟩
  have hw : ∀ row ∈ x.val.rows.map (Native.interpret x.val.ground), 0 ≤ row.cost := by
    intro row hr
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hr
    exact hcost original ho
  have h := greedy_risk_bill I hground hU (x.val.rows.map (Native.interpret x.val.ground))
    benchmark hc hw hsub
    (by exact_mod_cast x.property.parameters_valid.q_pos)
    (by exact_mod_cast x.property.parameters_valid.q_lt_one)
    (by exact_mod_cast x.property.parameters_valid.budget_pos)
    (by exact_mod_cast hδone) hrisk
  simpa only [Fintype.card_fin, Asymptotics.factor] using h

end Cslib.Probability.StochasticOracle.PartialCover.GreedyNative
