/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Multicover.Greedy
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.RatBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Mathlib.Tactic

/-!
# Uniform native greedy multicover planning

Runtime masks describe eligibility over the ground prefix. Missing mask bits are
false; excess mask bits are ignored. Costs are exact binary rationals and labels
are binary source identifiers. The source's numerical repetition demand is unary.
The algorithm scans all rows, ignores zero gain and keeps the earlier row on ties,
then updates residual demand and repeats. [Wang2027], Theorem 4, PDF pp. 10–11.

## Main definitions

* `Row`, `Input`: original runtime labels, eligibility masks, costs and demand.
* `select`, `decrement`, `batch`: executable scan and repeated greedy plan.

## Main results

* `batch_computable`, `labels_computable`: uniform native planning and binary-label output.
* `batch_eq`: decoded runtime output equals the proved source greedy batch.
* `batch_mem`: every emitted row is an original input row.
-/

public section
namespace Cslib.Algorithms.Lean.Multicover.Native
open Turing.MultiTapeTM

/-- One source oracle, including its runtime label and rational cost bound. -/
structure Row where
  /-- Original source identifier, preserved in the emitted plan. -/
  label : ℕ
  /-- Membership bits in the ground prefix, with absent bits interpreted as false. -/
  mask : List Bool
  /-- Exact rational cost. -/
  cost : ℚ
  deriving DecidableEq

/-- Binary label, framed eligibility word and binary rational cost. -/
enc_structure rowEncoding : Row where label : encNat, mask : encBits, cost : encRatBin

/-- Finite runtime instance; no validity or resource conclusion is an input field. -/
structure Input where
  /-- Ground-prefix size, in unary. -/
  ground : ℕ
  /-- Required repetitions per element, in unary. -/
  repetitions : ℕ
  /-- Ordered oracle rows, allowing repeated selections. -/
  rows : List Row
  deriving DecidableEq

/-- Unary ground size, unary repetition count, then framed oracle rows. -/
enc_structure inputEncoding : Input where
  ground : encUnary, repetitions : encUnary, rows : (encList rowEncoding)

/-- Number of currently unsatisfied eligible elements, counted exactly once. -/
@[expose] def gain (demand : List ℕ) (row : Row) : ℕ :=
  ((List.range demand.length).filter fun j =>
    (row.mask[j]?.getD false) && decide (0 < demand[j]?.getD 0)).length

/-- Exact cost per positive marginal; division by zero is never used for selection. -/
@[expose] def ratio (demand : List ℕ) (row : Row) : ℚ := row.cost / gain demand row

/-- Compare a row with the suffix winner, ignoring zero gain and preferring this
earlier row at equal cost/gain. -/
@[expose] def consider (demand : List ℕ) (best : Option Row) (row : Row) : Option Row :=
  if gain demand row = 0 then best
  else best.elim (some row) fun other => some (if ratio demand row ≤ ratio demand other
    then row else other)

/-- The same right-to-left scan and earlier-row tie rule as `Multicover.choose`. -/
@[expose] def select (demand : List ℕ) : List Row → Option Row
  | [] => none
  | row :: rows => consider demand (select demand rows) row

/-- Remove one unmet requirement at every eligible, unsatisfied element. -/
@[expose] def decrement (demand : List ℕ) (row : Row) : List ℕ :=
  (List.range demand.length).map fun j =>
    if row.mask[j]?.getD false then demand[j]?.getD 0 - 1 else demand[j]?.getD 0

/-- Runtime residual vector and reverse emitted plan. -/
structure State where
  /-- Unary residual requirements. -/
  demand : List ℕ
  /-- Original oracle rows selected so far, newest first. -/
  chosen : List Row
  deriving DecidableEq

/-- Framed unary demand vector followed by the reverse row plan. -/
enc_structure stateEncoding : State where
  demand : (encList encUnary), chosen : (encList rowEncoding)

/-- One actual greedy scan followed by residual update and plan emission. -/
@[expose] def advance (rows : List Row) (state : State) : State :=
  (select state.demand rows).elim state fun row =>
    ⟨decrement state.demand row, row :: state.chosen⟩

/-- Uniform starting vector, built from runtime size and repetition demand. -/
@[expose] def initial (input : Input) : State :=
  ⟨List.replicate input.ground input.repetitions, []⟩

/-- The emitted plan after the source's `n*r` bound, in selection order. -/
@[expose] def batch (input : Input) : List Row :=
  ((advance input.rows)^[input.ground * input.repetitions] (initial input)).chosen.reverse

/-- Source labels for actual selected rows, without replacing them by host choices. -/
@[expose] def labels (input : Input) : List ℕ := (batch input).map Row.label

/-- Every selected runtime row occurs in the actual input table. -/
theorem select_mem (demand : List ℕ) (rows : List Row) {row : Row}
    (h : select demand rows = some row) : row ∈ rows := by
  induction rows with
  | nil => simp [select] at h
  | cons a rows ih =>
    simp only [select, consider] at h
    split_ifs at h with hz
    · exact List.mem_cons_of_mem a (ih h)
    · cases hs : select demand rows with
      | none =>
        simp only [hs, Option.elim_none, Option.some.injEq] at h
        subst row
        exact List.mem_cons_self
      | some b =>
        simp only [hs, Option.elim_some] at h
        split_ifs at h
        · cases Option.some.inj h; exact List.mem_cons_self
        · cases Option.some.inj h; exact List.mem_cons_of_mem a (ih hs)

private theorem row_label : ComputableInPolyTime Row.label rowEncoding encNat :=
  rowEncoding_label_deg.computableInPolyTime
private theorem row_mask : ComputableInPolyTime Row.mask rowEncoding encBits :=
  rowEncoding_mask_deg.computableInPolyTime
private theorem row_cost : ComputableInPolyTime Row.cost rowEncoding encRatBin :=
  rowEncoding_cost_deg.computableInPolyTime
attribute [local fun_prop] row_label row_mask row_cost

/-- Unary demand vector paired with an encoded original row; the vector is framed. -/
abbrev scanEncoding := encPair (encList encUnary) rowEncoding

private theorem gain_computable : ComputableInPolyTime (fun p : List ℕ × Row => gain p.1 p.2)
    scanEncoding encUnary := by
  unfold gain
  fun_prop

private theorem ratio_computable : ComputableInPolyTime (fun p : List ℕ × Row => ratio p.1 p.2)
    scanEncoding encRatBin := by
  have hg := ComputableInPolyTime.unary_to_binary.comp gain_computable
  have hc := row_cost.comp (ComputableInPolyTime.snd (encList encUnary) rowEncoding)
  have hr := ComputableInPolyTime.ratBin_div.comp
    (hc.prod (ComputableInPolyTime.ratBin_natCast.comp hg))
  simpa only [ratio, Function.comp_def] using hr

attribute [local fun_prop] gain_computable ratio_computable

private theorem consider_computable : ComputableInPolyTime
    (fun p : (List ℕ × Option Row) × Row => consider p.1.1 p.1.2 p.2)
    (encFoldStep (encList encUnary) (encOption rowEncoding) rowEncoding)
    (encOption rowEncoding) := by
  let encC := encFoldStep (encList encUnary) (encOption rowEncoding) rowEncoding
  have hd : ComputableInPolyTime (fun p : (List ℕ × Option Row) × Row => p.1.1)
      encC (encList encUnary) :=
    (ComputableInPolyTime.fst (encPair (encList encUnary) (encOption rowEncoding)) rowEncoding).fst'
  have hb : ComputableInPolyTime (fun p : (List ℕ × Option Row) × Row => p.1.2)
      encC (encOption rowEncoding) :=
    (ComputableInPolyTime.fst (encPair (encList encUnary) (encOption rowEncoding)) rowEncoding).snd'
  have hr : ComputableInPolyTime (fun p : (List ℕ × Option Row) × Row => p.2)
      encC rowEncoding := ComputableInPolyTime.snd _ _
  have hgain := gain_computable.comp (hd.prod hr)
  have hz := ComputableInDegree.unary_isZero.computableInPolyTime.comp hgain
  have ho := ComputableInPolyTime.snd encC rowEncoding
  have houter := ComputableInPolyTime.fst encC rowEncoding
  have hleft := ratio_computable.comp ((hd.comp houter).prod (hr.comp houter))
  have hright := ratio_computable.comp ((hd.comp houter).prod ho)
  have hcmp := ComputableInPolyTime.ratBin_le.comp (hleft.prod hright)
  have hpref := ComputableInPolyTime.ite hcmp (hr.comp houter) ho
  have hsome := (ComputableInPolyTime.optionSome rowEncoding).comp hr
  have hbody := (ComputableInPolyTime.optionSome rowEncoding).comp hpref
  have hbody' : ComputableInPolyTime (fun p : ((List ℕ × Option Row) × Row) × Row =>
      some (if decide (ratio p.1.1.1 p.1.2 ≤ ratio p.1.1.1 p.2) then p.1.2 else p.2))
      (encPair encC rowEncoding) (encOption rowEncoding) := by
    simpa only [Function.comp_def] using hbody
  have helim := ComputableInPolyTime.optionElimWithInput
    (body := fun (p : (List ℕ × Option Row) × Row) (other : Row) =>
      some (if decide (ratio p.1.1 p.2 ≤ ratio p.1.1 other) then p.2 else other))
    hb hsome hbody'
  have h := ComputableInPolyTime.ite hz hb helim
  refine h.of_enc_eq ?_
  intro p
  simp only [Function.comp_def, Bool.decide_iff]
  cases p.1.2 <;> simp only [consider, Option.elim_none, Option.elim_some]

private theorem select_fold (demand : List ℕ) (rows : List Row) :
    select demand rows = rows.reverse.foldl (consider demand) none := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [select, List.reverse_cons, List.foldl_append, ih]

/-- The complete runtime eligibility/cost scan, including binary rational
normalization and comparison, is computed by one polynomial-time native machine. -/
theorem select_computable : ComputableInPolyTime
    (fun p : List ℕ × List Row => select p.1 p.2)
    (encPair (encList encUnary) (encList rowEncoding)) (encOption rowEncoding) := by
  have hs := ComputableInPolyTime.foldlWith_of_bounded_growth
    (par := fun p : List ℕ × List Row => p.1) (list := fun p => p.2.reverse)
    (init := fun _ => none) (step := consider)
    (by fun_prop) (by fun_prop) (by fun_prop) consider_computable
    (growth := fun p => (encList rowEncoding p.2).length + 1)
    (((ComputableInPolyTime.snd (encList encUnary) (encList rowEncoding)).polyBounded_length).add
      (.const 1)) ?_
  · simpa only [← select_fold] using hs
  · intro p best row hr
    have hrow := SizedListEncoding.length_elem_le (encA := rowEncoding)
      (encL := encList rowEncoding) p.2 row (List.mem_reverse.mp hr)
    unfold consider
    split_ifs
    · omega
    · cases best with
      | none => simp only [Option.elim_none, encOption_some, List.length_cons]; omega
      | some other =>
        simp only [Option.elim_some]
        split_ifs <;> simp only [encOption_some, List.length_cons] <;> omega

/-- Original rows interpreted as finite source eligibility sets; labels are copied
by the native code and do not affect the numerical greedy comparisons. -/
@[expose] def interpret (n : ℕ) (row : Row) : Oracle (Fin n) :=
  ⟨Finset.univ.filter (fun e => row.mask[e.val]?.getD false), row.cost⟩

/-- Read the encoded residual vector on the source's finite ground prefix. -/
@[expose] def demandOf (n : ℕ) (demand : List ℕ) : Demand (Fin n) :=
  fun e => demand[e.val]?.getD 0

/-- The actual runtime gain counts precisely the source marginal, with no mask
length or demand-value promises needed. -/
theorem gain_eq (demand : List ℕ) (row : Row) :
    Multicover.gain (demandOf demand.length demand) (interpret demand.length row) =
      gain demand row := by
  let s := (interpret demand.length row).eligible.filter
    (fun e => 0 < demandOf demand.length demand e)
  have hm : s.image Fin.val = ((List.range demand.length).filter fun j =>
      (row.mask[j]?.getD false) && decide (0 < demand[j]?.getD 0)).toFinset := by
    ext j
    constructor
    · intro hj
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hm, hd⟩ := Finset.mem_filter.mp he
      have hmask := (Finset.mem_filter.mp hm).2
      apply List.mem_toFinset.mpr
      apply List.mem_filter.mpr
      exact ⟨List.mem_range.mpr e.isLt, by simpa only [Bool.and_eq_true,
        decide_eq_true_eq, demandOf] using (And.intro hmask hd)⟩
    · intro hj
      obtain ⟨hbound, hp⟩ := List.mem_filter.mp (List.mem_toFinset.mp hj)
      have hb := List.mem_range.mp hbound
      have hp' : row.mask[j]?.getD false = true ∧ 0 < demand[j]?.getD 0 := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using hp
      refine Finset.mem_image.mpr ⟨⟨j, hb⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hp'.1⟩, hp'.2⟩
  have hc := Finset.card_image_of_injective s Fin.val_injective
  rw [hm, List.toFinset_card_of_nodup (List.nodup_range.filter _)] at hc
  exact hc.symm

private theorem gain_eq_of_length (n : ℕ) (demand : List ℕ) (hd : demand.length = n)
    (row : Row) :
    Multicover.gain (demandOf n demand) (interpret n row) = gain demand row := by
  subst n
  exact gain_eq demand row

private theorem ratio_eq (n : ℕ) (demand : List ℕ) (hd : demand.length = n) (row : Row) :
    Multicover.ratio (demandOf n demand) (interpret n row) = ratio demand row := by
  rw [Multicover.ratio, gain_eq_of_length n demand hd row]
  rfl

/-- The complete native scan makes exactly the choices of the proved source
selector, including zero-gain rows and earlier-row ties. -/
theorem select_eq (n : ℕ) (demand : List ℕ) (hd : demand.length = n) (rows : List Row) :
    (select demand rows).map (interpret n) =
      choose (demandOf n demand) (rows.map (interpret n)) := by
  induction rows with
  | nil => simp [select, choose]
  | cons row rows ih =>
    rw [select, List.map_cons, choose, ← ih, gain_eq_of_length n demand hd row]
    by_cases hz : gain demand row = 0
    · simp [consider, hz]
    · cases select demand rows with
      | none => simp [consider, hz]
      | some other =>
        by_cases hc : ratio demand row ≤ ratio demand other <;>
          simp [consider, hz, ratio_eq n demand hd, hc]

/-- Decrementing preserves the ground-prefix length. -/
theorem decrement_length (demand : List ℕ) (row : Row) :
    (decrement demand row).length = demand.length := by simp [decrement]

private theorem decrement_get (demand : List ℕ) (row : Row) (j : ℕ)
    (hj : j < demand.length) :
    (decrement demand row)[j]?.getD 0 =
      if row.mask[j]?.getD false then demand[j]?.getD 0 - 1 else demand[j]?.getD 0 := by
  simp [decrement, hj]

/-- The runtime vector update is the source's residual-demand update. -/
theorem decrement_eq (n : ℕ) (demand : List ℕ) (hd : demand.length = n) (row : Row) :
    demandOf n (decrement demand row) = reduce (demandOf n demand) (interpret n row) := by
  funext e
  rw [demandOf, decrement_get demand row e.val (by simpa only [hd] using e.isLt)]
  simp [reduce, interpret, demandOf]

private theorem decrement_computable : ComputableInPolyTime
    (fun p : List ℕ × Row => decrement p.1 p.2) scanEncoding (encList encUnary) := by
  have hl : ComputableInPolyTime (fun p : List ℕ × Row => List.range p.1.length)
      scanEncoding (encList encUnary) := by fun_prop
  apply ComputableInPolyTime.mapWithInput hl
  have hb : ComputableInPolyTime (fun p : (List ℕ × Row) × ℕ =>
      p.1.2.mask[p.2]?.getD false) (encPair scanEncoding encUnary) encBool := by fun_prop
  have hv : ComputableInPolyTime (fun p : (List ℕ × Row) × ℕ => p.1.1[p.2]?.getD 0)
      (encPair scanEncoding encUnary) encUnary := by fun_prop
  have hs := ComputableInPolyTime.unary_sub.comp (hv.prod (.const 1))
  exact ComputableInPolyTime.ite hb hs hv

private theorem decrement_cons (head : ℕ) (tail : List ℕ) (row : Row) :
    decrement (head :: tail) row =
      (if row.mask.headD false then head - 1 else head) ::
        decrement tail { row with mask := row.mask.tail } := by
  simp [decrement, List.range_succ_eq_map, List.map_map, Function.comp_def,
    List.getElem?_tail, List.head?_eq_getElem?, Nat.succ_eq_add_one]

private theorem decrement_size (demand : List ℕ) (row : Row) :
    (encList encUnary (decrement demand row)).length ≤ (encList encUnary demand).length := by
  induction demand generalizing row with
  | nil => simp [decrement]
  | cons head tail ih =>
    rw [decrement_cons]
    have hh : (if row.mask.headD false then head - 1 else head) ≤ head := by split_ifs <;> omega
    have ht := ih {row with mask := row.mask.tail}
    simp only [encList_cons, List.length_append, length_frame,
      encUnary_apply, List.length_replicate] at ht ⊢
    omega

private theorem input_ground : ComputableInPolyTime Input.ground inputEncoding encUnary :=
  inputEncoding_ground_deg.computableInPolyTime
private theorem input_repetitions : ComputableInPolyTime Input.repetitions inputEncoding encUnary :=
  inputEncoding_repetitions_deg.computableInPolyTime
private theorem input_rows : ComputableInPolyTime Input.rows inputEncoding (encList rowEncoding) :=
  inputEncoding_rows_deg.computableInPolyTime
private theorem state_demand : ComputableInPolyTime State.demand stateEncoding (encList encUnary) :=
  stateEncoding_demand_deg.computableInPolyTime
private theorem state_chosen : ComputableInPolyTime State.chosen stateEncoding
    (encList rowEncoding) :=
  stateEncoding_chosen_deg.computableInPolyTime
attribute [local fun_prop] input_ground input_repetitions input_rows state_demand state_chosen

@[local fun_prop] private theorem state_mk_computable {α : Type} {enc : α ↪ List Bool}
    {demand : α → List ℕ} {chosen : α → List Row}
    (hd : ComputableInPolyTime demand enc (encList encUnary))
    (hc : ComputableInPolyTime chosen enc (encList rowEncoding)) :
    ComputableInPolyTime (fun x => State.mk (demand x) (chosen x)) enc stateEncoding :=
  (hd.prod hc).of_enc_eq fun _ => rfl

private theorem initial_computable : ComputableInPolyTime initial inputEncoding stateEncoding := by
  unfold initial
  fun_prop

private theorem advance_computable : ComputableInPolyTime
    (fun p : List Row × State => advance p.1 p.2)
    (encPair (encList rowEncoding) stateEncoding) stateEncoding := by
  let encC := encPair (encList rowEncoding) stateEncoding
  have ht := ComputableInPolyTime.fst (encList rowEncoding) stateEncoding
  have hs := ComputableInPolyTime.snd (encList rowEncoding) stateEncoding
  have hd := state_demand.comp hs
  have hc := state_chosen.comp hs
  have hselected := select_computable.comp (hd.prod ht)
  have houter := ComputableInPolyTime.fst encC rowEncoding
  have hrow := ComputableInPolyTime.snd encC rowEncoding
  have hnewd := decrement_computable.comp ((hd.comp houter).prod hrow)
  have hnewc := ComputableInPolyTime.cons' hrow (hc.comp houter)
  have hbody := state_mk_computable hnewd hnewc
  have h := ComputableInPolyTime.optionElimWithInput
    (body := fun (p : List Row × State) (row : Row) =>
      State.mk (decrement p.2.demand row) (row :: p.2.chosen)) hselected hs hbody
  simpa only [advance, Function.comp_def] using h

/-- All scans, residual updates, copied source rows and final reversal are charged
by one native machine, uniformly in ground size, numerical demand and input costs. -/
theorem batch_computable : ComputableInPolyTime batch inputEncoding (encList rowEncoding) := by
  have hcount := ComputableInPolyTime.unary_mul.comp (input_ground.prod input_repetitions)
  have hi := ComputableInPolyTime.iterateWith_of_bounded_growth
    (par := Input.rows) (count := fun x : Input => x.ground * x.repetitions)
    (init := initial) (step := advance) input_rows hcount initial_computable advance_computable
    (growth := fun x => 2 * (encList rowEncoding x.rows).length + 1)
    (((PolyBounded.const 2).mul input_rows.polyBounded_length).add (.const 1)) ?_
  · have hout : ComputableInPolyTime (fun s : State => s.chosen.reverse)
        stateEncoding (encList rowEncoding) := by fun_prop
    exact (hout.comp hi).of_enc_eq fun _ => rfl
  · intro input state
    cases hs : select state.demand input.rows with
    | none => simp [advance, hs]
    | some row =>
      have hrow := SizedListEncoding.length_elem_le (encA := rowEncoding)
        (encL := encList rowEncoding) input.rows row (select_mem _ _ hs)
      have hd := decrement_size state.demand row
      simp only [advance, hs, Option.elim_some, stateEncoding_apply, stateEncodingFields,
        length_encPair, encList_cons, List.length_append, length_frame]
      omega

/-- Emitting binary source labels after planning also uses a single native machine. -/
theorem labels_computable : ComputableInPolyTime labels inputEncoding (encList encNat) := by
  unfold labels
  exact ComputableInPolyTime.mapWithInput batch_computable
    (row_label.comp (ComputableInPolyTime.snd inputEncoding rowEncoding))

private theorem run_none {n : ℕ} (rows : List (Oracle (Fin n))) (demand : Demand (Fin n))
    (h : choose demand rows = none) (fuel : ℕ) : run rows fuel demand = [] := by
  cases fuel <;> simp [run, h]

private theorem execution_eq (n : ℕ) (rows : List Row) (fuel : ℕ)
    (demand : List ℕ) (chosen : List Row) (hd : demand.length = n) :
    (((advance rows)^[fuel] ⟨demand, chosen⟩).chosen.reverse.map (interpret n)) =
      chosen.reverse.map (interpret n) ++
        run (rows.map (interpret n)) fuel (demandOf n demand) := by
  induction fuel generalizing demand chosen with
  | zero => simp [run]
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    have hsource := select_eq n demand hd rows
    cases hs : select demand rows with
    | none =>
      rw [hs, Option.map_none] at hsource
      simp only [advance, hs, Option.elim_none]
      rw [ih demand chosen hd]
      simp only [run_none _ _ hsource.symm, run, hsource.symm, List.append_nil]
    | some row =>
      rw [hs, Option.map_some] at hsource
      simp only [advance, hs, Option.elim_some]
      rw [ih _ _ ((decrement_length demand row).trans hd)]
      simp only [run, hsource.symm, ← decrement_eq n demand hd row,
        List.reverse_cons, List.map_append, List.map_singleton, List.append_assoc,
        List.singleton_append]

/-- Decoding the actual emitted native plan gives exactly the previously proved
source greedy batch, rather than only an unrelated minimum-ratio guarantee. -/
theorem batch_eq (input : Input) : (batch input).map (interpret input.ground) =
    Multicover.batch (input.rows.map (interpret input.ground)) input.repetitions := by
  have hd : demandOf input.ground (List.replicate input.ground input.repetitions) =
      (fun _ => input.repetitions) := by
    funext e
    simp [demandOf, e.isLt]
  have h := execution_eq input.ground input.rows (input.ground * input.repetitions)
    (List.replicate input.ground input.repetitions) [] (by simp)
  simpa only [batch, initial, hd, Multicover.batch, Fintype.card_fin, List.reverse_nil,
    List.map_nil, List.nil_append] using h

private theorem chosen_mem (rows : List Row) (fuel : ℕ) (state : State)
    (h : ∀ row ∈ state.chosen, row ∈ rows) :
    ∀ row ∈ ((advance rows)^[fuel] state).chosen, row ∈ rows := by
  induction fuel generalizing state with
  | zero => exact h
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    cases hs : select state.demand rows with
    | none => simpa only [advance, hs, Option.elim_none] using h
    | some row =>
      intro a ha
      simp only [advance, hs, Option.elim_some, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact select_mem _ _ hs
      · exact h a ha

/-- The native planner preserves complete original rows and source identifiers. -/
theorem batch_mem (input : Input) {row : Row} (h : row ∈ batch input) : row ∈ input.rows :=
  chosen_mem input.rows _ (initial input) (by simp [initial]) row (List.mem_reverse.mp h)

end Cslib.Algorithms.Lean.Multicover.Native
