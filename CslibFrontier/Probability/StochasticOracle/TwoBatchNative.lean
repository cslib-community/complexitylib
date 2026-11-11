/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.DynamicProgramming.Native
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Tactic.PolyTime
import Mathlib.Tactic

/-!
# Uniform native two-batch selection

[Wang2027], Theorem 2(2), PDF pp. 7–8. Runtime inputs contain the ordered
probability/cost/cutoff triples, deadline,
rational tolerance and a unary inverse-tolerance budget. Invalid inputs are also
processed by the same total program: rounded keys are saturated at a polynomial
budget. On valid inputs saturation is inactive.

The input list determines the population; no population-dependent machine or
arithmetic callback is supplied by the caller. Every rational stays in the
canonical binary encoding. Lists of indices are reconstructed explicitly.

## Main definitions

* `Input`, `encInput`: runtime data and its binary/unary internal representation.
* `choose`, `schedule`: the selector and explicit output of both batches.

## Main results

* `computable_choose`, `computable_schedule`: uniform native implementation of all stages.
-/

public section
namespace Cslib.Probability.StochasticOracle.TwoBatchNative
open Cslib.Algorithms.Lean.DynamicProgramming.MinProduct
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- The uniform runtime input. The budget is unary; the remaining numeric fields
are binary rationals. No validity or runtime certificate is an input field. -/
structure Input where
  /-- Rational approximation tolerance. -/
  epsilon : ℚ
  /-- Cutoff deadline, excluding local selection time. -/
  deadline : ℚ
  /-- Inverse-tolerance budget. -/
  budget : ℕ
  /-- Ordered success probability, expected cost and cutoff triples. -/
  calls : List (ℚ × ℚ × ℚ)
  deriving DecidableEq

/-- Framed runtime data, including the unary inverse-tolerance budget. -/
@[expose] def encInput : Input ↪ List Bool :=
  (⟨fun x => (x.epsilon,x.deadline,x.budget,x.calls), fun x y h => by
    cases x; cases y
    simpa using h⟩ : Input ↪ ℚ × ℚ × ℕ × List (ℚ × ℚ × ℚ)).trans
      (encPair encRatBin (encPair encRatBin
        (encPair encUnary (encList (encPair encRatBin (encPair encRatBin encRatBin))))))

private theorem input_fields : ComputableInPolyTime
    (fun x : Input => (x.epsilon,x.deadline,x.budget,x.calls)) encInput
    (encPair encRatBin (encPair encRatBin
      (encPair encUnary (encList (encPair encRatBin (encPair encRatBin encRatBin)))))) :=
  .of_eq fun _ => rfl

private theorem epsilon_computable : ComputableInPolyTime Input.epsilon encInput encRatBin :=
  input_fields.fst'
private theorem deadline_computable : ComputableInPolyTime Input.deadline encInput encRatBin :=
  input_fields.snd'.fst'
private theorem budget_computable : ComputableInPolyTime Input.budget encInput encUnary :=
  input_fields.snd'.snd'.fst'
private theorem calls_computable : ComputableInPolyTime Input.calls encInput
    (encList (encPair encRatBin (encPair encRatBin encRatBin))) :=
  input_fields.snd'.snd'.snd'

attribute [local fun_prop] epsilon_computable deadline_computable budget_computable calls_computable

/-- The population is enumerated from the runtime list length. -/
@[expose] def population (x : Input) : List ℕ := List.range x.calls.length

/-- Read an opportunity; out-of-range indices receive a fixed default. -/
@[expose] def call (x : Input) (i : ℕ) : ℚ × ℚ × ℚ := x.calls.getD i (0,0,0)

/-- Input success probability. -/
@[expose] def success (x : Input) (i : ℕ) : ℚ := (call x i).1
/-- Input expected cost. -/
@[expose] def cost (x : Input) (i : ℕ) : ℚ :=
  let (_,c,_) := call x i
  c
/-- Input cutoff. -/
@[expose] def cutoff (x : Input) (i : ℕ) : ℚ :=
  let (_,_,l) := call x i
  l
/-- Input failure probability. -/
@[expose] def failure (x : Input) (i : ℕ) : ℚ := 1 - success x i

private theorem population_computable : ComputableInPolyTime population encInput
    (encList encUnary) := by unfold population; fun_prop
private theorem call_computable : ComputableInPolyTime
    (fun p : Input × ℕ => call p.1 p.2) (encPair encInput encUnary)
    (encPair encRatBin (encPair encRatBin encRatBin)) := by unfold call; fun_prop
private theorem success_computable : ComputableInPolyTime
    (fun p : Input × ℕ => success p.1 p.2) (encPair encInput encUnary) encRatBin :=
  call_computable.fst'
private theorem cost_computable : ComputableInPolyTime
    (fun p : Input × ℕ => cost p.1 p.2) (encPair encInput encUnary) encRatBin :=
  call_computable.snd'.fst'
private theorem cutoff_computable : ComputableInPolyTime
    (fun p : Input × ℕ => cutoff p.1 p.2) (encPair encInput encUnary) encRatBin :=
  call_computable.snd'.snd'
private theorem failure_computable : ComputableInPolyTime
    (fun p : Input × ℕ => failure p.1 p.2) (encPair encInput encUnary) encRatBin := by
  unfold failure
  have h := ratBin_sub.comp ((const 1).prod success_computable)
  simpa only [Function.comp_def] using h

attribute [local fun_prop] population_computable call_computable success_computable
  cost_computable cutoff_computable failure_computable

/-- Optional opportunities for the two cutoff thresholds. -/
@[expose] def optional (x : Input) (a b : ℚ) : List ℕ :=
  (population x).filter (fun i => cutoff x i ≤ a ∧ cutoff x i ≤ b)
/-- Opportunities forced into the first batch. -/
@[expose] def forced (x : Input) (b : ℚ) : List ℕ :=
  (population x).filter (fun i => b < cutoff x i)
/-- Independent failure probability of an explicit batch. -/
@[expose] def failureProduct (x : Input) (items : List ℕ) : ℚ :=
  (items.map (failure x)).prod
/-- Cost of an explicit batch. -/
@[expose] def batchCost (x : Input) (items : List ℕ) : ℚ := (items.map (cost x)).sum

private theorem optional_computable : ComputableInPolyTime
    (fun p : (Input × ℚ) × ℚ => optional p.1.1 p.1.2 p.2)
    (encPair (encPair encInput encRatBin) encRatBin) (encList encUnary) := by
  unfold optional
  apply filterWithInput (by fun_prop)
  have hc : ComputableInPolyTime
      (fun p : ((Input × ℚ) × ℚ) × ℕ => cutoff p.1.1.1 p.2)
      (encPair (encPair (encPair encInput encRatBin) encRatBin) encUnary) encRatBin := by
    fun_prop
  have ha : ComputableInPolyTime
      (fun p : ((Input × ℚ) × ℚ) × ℕ => p.1.1.2)
      (encPair (encPair (encPair encInput encRatBin) encRatBin) encUnary) encRatBin := by
    fun_prop
  have hb : ComputableInPolyTime
      (fun p : ((Input × ℚ) × ℚ) × ℕ => p.1.2)
      (encPair (encPair (encPair encInput encRatBin) encRatBin) encUnary) encRatBin := by
    fun_prop
  have h := decide_and (ratBin_le.comp (hc.prod ha)) (ratBin_le.comp (hc.prod hb))
  simpa only [Function.comp_def] using h
private theorem forced_computable : ComputableInPolyTime
    (fun p : Input × ℚ => forced p.1 p.2)
    (encPair encInput encRatBin) (encList encUnary) := by
  unfold forced
  apply filterWithInput (by fun_prop)
  have hc : ComputableInPolyTime
      (fun p : (Input × ℚ) × ℕ => cutoff p.1.1 p.2)
      (encPair (encPair encInput encRatBin) encUnary) encRatBin := by fun_prop
  have h := ratBin_lt.comp (((snd _ _).comp (fst _ _)).prod hc)
  simpa only [Function.comp_def] using h
private theorem failureProduct_computable : ComputableInPolyTime
    (fun p : Input × List ℕ => failureProduct p.1 p.2)
    (encPair encInput (encList encUnary)) encRatBin := by unfold failureProduct; fun_prop
private theorem batchCost_computable : ComputableInPolyTime
    (fun p : Input × List ℕ => batchCost p.1 p.2)
    (encPair encInput (encList encUnary)) encRatBin := by unfold batchCost; fun_prop

attribute [local fun_prop] optional_computable forced_computable failureProduct_computable
  batchCost_computable

/-- Membership is an actual linear scan, rather than an uncharged finite-set operation. -/
@[expose] def member (i : ℕ) (xs : List ℕ) : Bool := xs.any (fun j => decide (i = j))

private theorem member_computable : ComputableInPolyTime
    (fun p : ℕ × List ℕ => member p.1 p.2)
    (encPair encUnary (encList encUnary)) encBool := by unfold member; fun_prop

attribute [local fun_prop] member_computable

/-- Reconstruct the first batch in the same order as the mathematical selector. -/
@[expose] def firstBatch (x : Input) (a b : ℚ) (second : List ℕ) : List ℕ :=
  forced x b ++ (optional x a b).filter (fun i => !(member i second))

/-- Polynomial unary cap for every rounded item key in a valid maximum-member branch. -/
@[expose] def keyCap (x : Input) : ℕ := (x.calls.length + 1) * x.budget

/-- Scaling for a maximum-cost-member branch, counting its mandatory member. -/
@[expose] def scale (x : Input) (r : ℕ) (items : List ℕ) : ℚ :=
  x.epsilon * cost x r / (items.length + 1 : ℕ)

/-- Saturating flooring makes the implementation total and polynomial on invalid
inputs too. The valid-input bridge proves that saturation does not change a key. -/
@[expose] def key (x : Input) (K : ℚ) (i : ℕ) : ℕ :=
  min (keyCap x) (⌊cost x i / K⌋₊ : ℕ)

private theorem keyCap_computable : ComputableInPolyTime keyCap encInput encUnary := by
  unfold keyCap
  fun_prop
private theorem scale_computable : ComputableInPolyTime
    (fun p : (Input × ℕ) × List ℕ => scale p.1.1 p.1.2 p.2)
    (encPair (encPair encInput encUnary) (encList encUnary)) encRatBin := by
  have hlen : ComputableInPolyTime (fun xs : List ℕ => (xs.length + 1 : ℕ))
      (encList encUnary) encUnary := by fun_prop
  have hcast := ratBin_natCast.comp
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary)
  have hden : ComputableInPolyTime
      (fun p : (Input × ℕ) × List ℕ => ((p.2.length + 1 : ℕ) : ℚ))
      (encPair (encPair encInput encUnary) (encList encUnary)) encRatBin :=
    hcast.comp (hlen.comp (snd _ _))
  have hc : ComputableInPolyTime (fun p : (Input × ℕ) × List ℕ => cost p.1.1 p.1.2)
      (encPair (encPair encInput encUnary) (encList encUnary)) encRatBin := by fun_prop
  unfold scale
  have h := ratBin_div.comp ((ratBin_mul.comp
    ((epsilon_computable.comp ((fst _ _).comp (fst _ _))).prod hc)).prod hden)
  simpa only [Function.comp_def] using h
private theorem key_computable : ComputableInPolyTime
    (fun p : (Input × ℚ) × ℕ => key p.1.1 p.1.2 p.2)
    (encPair (encPair encInput encRatBin) encUnary) encUnary := by
  unfold key
  apply binary_min_unary'
  · exact keyCap_computable.comp ((fst _ _).comp (fst _ _))
  · fun_prop

attribute [local fun_prop] keyCap_computable scale_computable key_computable

private theorem firstBatch_computable : ComputableInPolyTime
    (fun p : ((Input × ℚ) × ℚ) × List ℕ => firstBatch p.1.1.1 p.1.1.2 p.1.2 p.2)
    (encPair (encPair (encPair encInput encRatBin) encRatBin) (encList encUnary))
    (encList encUnary) := by
  have hf : ComputableInPolyTime
      (fun p : ((Input × ℚ) × ℚ) × List ℕ => forced p.1.1.1 p.1.2)
      (encPair (encPair (encPair encInput encRatBin) encRatBin) (encList encUnary))
      (encList encUnary) := by fun_prop
  have ho : ComputableInPolyTime
      (fun p : ((Input × ℚ) × ℚ) × List ℕ => optional p.1.1.1 p.1.1.2 p.1.2)
      (encPair (encPair (encPair encInput encRatBin) encRatBin) (encList encUnary))
      (encList encUnary) := optional_computable.comp (fst _ _)
  apply hf.listAppend'
  apply filterWithInput ho
  exact bool_not.comp (member_computable.comp ((snd _ _).prod ((snd _ _).comp (fst _ _))))

attribute [local fun_prop] firstBatch_computable

/-- The actual native recurrence branch: preprocessing, key preparation,
minimum-product DP, witness reconstruction and exact binary arithmetic. -/
@[expose] def maximumBranch (x : Input) (a b : ℚ) (r : ℕ) : List (List ℕ) :=
  let items := (optional x a b).filter (fun i => cost x i ≤ cost x r ∧ i ≠ r)
  let outside := failureProduct x ((optional x a b).filter (fun i => cost x r < cost x i))
  let K := scale x r items
  let initial : Entry ℕ := ⟨key x K r,outside,[r]⟩
  (run (key x K) (failure x) initial items).map (fun e => firstBatch x a b e.selected)

/-- All candidates in a valid cutoff family; emptiness is checked by a list scan. -/
@[expose] def familyCandidates (x : Input) (a b : ℚ) : List (List ℕ) :=
  if (forced x b).all (fun i => decide (cutoff x i ≤ a)) then
    (firstBatch x a b [] :: (optional x a b).flatMap (maximumBranch x a b)).filter
      (fun A => !A.isEmpty)
  else []

/-- Runtime enumeration of both cutoffs and every maximum-cost member. -/
@[expose] def candidates (x : Input) : List (List ℕ) :=
  ((population x).map (cutoff x)).flatMap fun a =>
    (0 :: (population x).map (cutoff x)).flatMap fun b =>
      if a + b ≤ x.deadline then familyCandidates x a b else []

/-- Compute exact savings from binary input and an explicit reconstructed first batch. -/
@[expose] def gain (x : Input) (A : List ℕ) : ℚ :=
  (1 - failureProduct x A) * batchCost x ((population x).filter (fun i => !(member i A)))

/-- Final comparison, including a deterministic tie convention. -/
@[expose] def better (x : Input) (A B : List ℕ) : List ℕ :=
  if gain x A < gain x B then B else A

/-- The total selector, with the concurrent full batch as fallback. -/
@[expose] def choose (x : Input) : List ℕ :=
  (candidates x).foldl (better x) (population x)

private theorem maximumBranch_computable : ComputableInPolyTime
    (fun p : ((Input × ℚ) × ℚ) × ℕ => maximumBranch p.1.1.1 p.1.1.2 p.1.2 p.2)
    (encPair (encPair (encPair encInput encRatBin) encRatBin) encUnary)
    (encList (encList encUnary)) := by
  let input := encPair (encPair (encPair encInput encRatBin) encRatBin) encUnary
  let eligible := fun p : ((Input × ℚ) × ℚ) × ℕ =>
    (optional p.1.1.1 p.1.1.2 p.1.2).filter
      (fun i => cost p.1.1.1 i ≤ cost p.1.1.1 p.2 ∧ i ≠ p.2)
  have hx : ComputableInPolyTime (fun p : ((Input × ℚ) × ℚ) × ℕ => p.1.1.1)
      input encInput := by fun_prop
  have hr : ComputableInPolyTime (fun p : ((Input × ℚ) × ℚ) × ℕ => p.2)
      input encUnary := snd _ _
  have ho : ComputableInPolyTime
      (fun p : ((Input × ℚ) × ℚ) × ℕ => optional p.1.1.1 p.1.1.2 p.1.2)
      input (encList encUnary) := optional_computable.comp (fst _ _)
  have hci : ComputableInPolyTime
      (fun p : (((Input × ℚ) × ℚ) × ℕ) × ℕ => cost p.1.1.1.1 p.2)
      (encPair input encUnary) encRatBin := by
    have h := cost_computable.comp ((hx.comp (fst _ _)).prod
      (ComputableInPolyTime.snd input encUnary))
    simpa only [Function.comp_def] using h
  have hcr : ComputableInPolyTime
      (fun p : (((Input × ℚ) × ℚ) × ℕ) × ℕ => cost p.1.1.1.1 p.1.2)
      (encPair input encUnary) encRatBin := by
    have h := cost_computable.comp ((hx.comp (ComputableInPolyTime.fst input encUnary)).prod
      (hr.comp (ComputableInPolyTime.fst input encUnary)))
    simpa only [Function.comp_def] using h
  have hle := ratBin_le.comp (hci.prod hcr)
  have hlt := ratBin_lt.comp (hcr.prod hci)
  have hne : ComputableInPolyTime
      (fun p : (((Input × ℚ) × ℚ) × ℕ) × ℕ => decide (p.2 ≠ p.1.2))
      (encPair input encUnary) encBool := by fun_prop
  have htest : ComputableInPolyTime
      (fun p : (((Input × ℚ) × ℚ) × ℕ) × ℕ =>
        decide (cost p.1.1.1.1 p.2 ≤ cost p.1.1.1.1 p.1.2 ∧ p.2 ≠ p.1.2))
      (encPair input encUnary) encBool := by
    simpa only [Function.comp_def] using decide_and hle hne
  have hi : ComputableInPolyTime eligible input (encList encUnary) := filterWithInput ho htest
  have houtList := filterWithInput
    (test := fun (p : ((Input × ℚ) × ℚ) × ℕ) i =>
      decide (cost p.1.1.1 p.2 < cost p.1.1.1 i)) ho (show ComputableInPolyTime
      (fun p : (((Input × ℚ) × ℚ) × ℕ) × ℕ =>
        decide (cost p.1.1.1.1 p.1.2 < cost p.1.1.1.1 p.2))
      (encPair input encUnary) encBool from by
        simpa only [Function.comp_def] using hlt)
  have hout : ComputableInPolyTime
      (fun p : ((Input × ℚ) × ℚ) × ℕ =>
        failureProduct p.1.1.1 ((optional p.1.1.1 p.1.1.2 p.1.2).filter
          (fun i => cost p.1.1.1 p.2 < cost p.1.1.1 i))) input encRatBin := by
    have h := failureProduct_computable.comp (hx.prod houtList)
    simpa only [Function.comp_def] using h
  have hK : ComputableInPolyTime
      (fun p : ((Input × ℚ) × ℚ) × ℕ => scale p.1.1.1 p.2 (eligible p))
      input encRatBin := by
    have h := scale_computable.comp ((hx.prod hr).prod hi)
    simpa only [Function.comp_def] using h
  have hkeys : ComputableInPolyTime
      (fun p : (((Input × ℚ) × ℚ) × ℕ) × ℕ =>
        key p.1.1.1.1 (scale p.1.1.1.1 p.1.2 (eligible p.1)) p.2)
      (encPair input encUnary) encUnary := by
    have h := key_computable.comp
      (((hx.comp (fst _ _)).prod (hK.comp (fst _ _))).prod (snd _ _))
    simpa only [Function.comp_def] using h
  have hinitkey : ComputableInPolyTime
      (fun p : ((Input × ℚ) × ℚ) × ℕ => key p.1.1.1
        (scale p.1.1.1 p.2 (eligible p)) p.2) input encUnary := by
    have h := key_computable.comp ((hx.prod hK).prod hr)
    simpa only [Function.comp_def] using h
  have hfields := (hinitkey.prod (hout.prod (hr.cons' (const []))))
  have hinit := (computable_entry encUnary).comp hfields
  have hfailure : ComputableInPolyTime
      (fun p : (((Input × ℚ) × ℚ) × ℕ) × ℕ => failure p.1.1.1.1 p.2)
      (encPair input encUnary) encRatBin := by
    have h := failure_computable.comp ((hx.comp (fst _ _)).prod
      (ComputableInPolyTime.snd input encUnary))
    simpa only [Function.comp_def] using h
  have hrun := computable_run encUnary
    (items := eligible)
    (z := fun (p : ((Input × ℚ) × ℚ) × ℕ) i =>
      key p.1.1.1 (scale p.1.1.1 p.2 (eligible p)) i)
    (q := fun (p : ((Input × ℚ) × ℚ) × ℕ) i => failure p.1.1.1 i)
    hi hinit hkeys hfailure
  have hselected := (computable_entry_fields encUnary).snd'.snd'
  have hmap : ComputableInPolyTime
      (fun p : (((Input × ℚ) × ℚ) × ℕ) × Entry ℕ =>
        firstBatch p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.2.selected)
      (encPair input (encEntry encUnary)) (encList encUnary) := by
    have hctx : ComputableInPolyTime
        (fun p : (((Input × ℚ) × ℚ) × ℕ) × Entry ℕ => p.1.1)
        (encPair input (encEntry encUnary))
        (encPair (encPair encInput encRatBin) encRatBin) := by fun_prop
    have h := firstBatch_computable.comp (hctx.prod (hselected.comp (snd _ _)))
    simpa only [Function.comp_def] using h
  have h := mapWithInput
    (f := fun (p : ((Input × ℚ) × ℚ) × ℕ) (e : Entry ℕ) =>
      firstBatch p.1.1.1 p.1.1.2 p.1.2 e.selected) hrun hmap
  simpa only [Function.comp_def, eligible, maximumBranch] using h

private theorem familyCandidates_computable : ComputableInPolyTime
    (fun p : (Input × ℚ) × ℚ => familyCandidates p.1.1 p.1.2 p.2)
    (encPair (encPair encInput encRatBin) encRatBin) (encList (encList encUnary)) := by
  let input := encPair (encPair encInput encRatBin) encRatBin
  have ho := optional_computable
  have hf : ComputableInPolyTime
      (fun p : (Input × ℚ) × ℚ => forced p.1.1 p.2) input (encList encUnary) := by fun_prop
  have hc : ComputableInPolyTime
      (fun p : ((Input × ℚ) × ℚ) × ℕ => cutoff p.1.1.1 p.2)
      (encPair input encUnary) encRatBin := by fun_prop
  have ha : ComputableInPolyTime
      (fun p : ((Input × ℚ) × ℚ) × ℕ => p.1.1.2)
      (encPair input encUnary) encRatBin := by fun_prop
  have hp : ComputableInPolyTime
      (fun p : ((Input × ℚ) × ℚ) × ℕ => decide (cutoff p.1.1.1 p.2 ≤ p.1.1.2))
      (encPair input encUnary) encBool := by
    simpa only [Function.comp_def] using ratBin_le.comp (hc.prod ha)
  have htest := allWithInput
    (test := fun (p : (Input × ℚ) × ℚ) (i : ℕ) => decide (cutoff p.1.1 i ≤ p.1.2)) hf hp
  have hbranches := flatMapWithInput
    (f := fun (p : (Input × ℚ) × ℚ) (r : ℕ) => maximumBranch p.1.1 p.1.2 p.2 r)
    ho maximumBranch_computable
  have hempty := firstBatch_computable.comp ((ComputableInPolyTime.id').prod (const []))
  have hlist := hempty.cons' hbranches
  have hfilter : ComputableInPolyTime
      (fun p : (Input × ℚ) × ℚ =>
        (firstBatch p.1.1 p.1.2 p.2 [] ::
          (optional p.1.1 p.1.2 p.2).flatMap (maximumBranch p.1.1 p.1.2 p.2)).filter
          (fun A => !A.isEmpty)) input (encList (encList encUnary)) := by
    apply filterWithInput hlist
    fun_prop
  have h := htest.ite hfilter (const [])
  simpa only [Function.comp_def, familyCandidates] using h

private theorem candidates_computable : ComputableInPolyTime candidates encInput
    (encList (encList encUnary)) := by
  have hcutoffs : ComputableInPolyTime
      (fun x : Input => (population x).map (cutoff x)) encInput (encList encRatBin) :=
    mapWithInput population_computable cutoff_computable
  have houter := hcutoffs
  have hinner : ComputableInPolyTime
      (fun p : Input × ℚ => (0 : ℚ) :: (population p.1).map (cutoff p.1))
      (encPair encInput encRatBin) (encList encRatBin) :=
    (const 0).cons' (hcutoffs.comp (fst _ _))
  have hadd : ComputableInPolyTime (fun p : (Input × ℚ) × ℚ => p.1.2 + p.2)
      (encPair (encPair encInput encRatBin) encRatBin) encRatBin := by fun_prop
  have hD : ComputableInPolyTime (fun p : (Input × ℚ) × ℚ => p.1.1.deadline)
      (encPair (encPair encInput encRatBin) encRatBin) encRatBin := by fun_prop
  have htest := ratBin_le.comp (hadd.prod hD)
  have hbody := htest.ite familyCandidates_computable (const [])
  have hb : ComputableInPolyTime
      (fun p : (Input × ℚ) × ℚ => if p.1.2 + p.2 ≤ p.1.1.deadline then
        familyCandidates p.1.1 p.1.2 p.2 else [])
      (encPair (encPair encInput encRatBin) encRatBin) (encList (encList encUnary)) := by
    simpa only [Function.comp_def, decide_eq_true_eq] using hbody
  have hi : ComputableInPolyTime
      (fun p : Input × ℚ => (0 :: (population p.1).map (cutoff p.1)).flatMap
        (fun b => if p.2 + b ≤ p.1.deadline then familyCandidates p.1 p.2 b else []))
      (encPair encInput encRatBin) (encList (encList encUnary)) :=
    flatMapWithInput hinner hb
  have h := flatMapWithInput
    (f := fun x a => (0 :: (population x).map (cutoff x)).flatMap
      (fun b => if a + b ≤ x.deadline then familyCandidates x a b else [])) houter hi
  change ComputableInPolyTime
    (fun x => ((population x).map (cutoff x)).flatMap fun a =>
      (0 :: (population x).map (cutoff x)).flatMap fun b =>
        if a + b ≤ x.deadline then familyCandidates x a b else [])
    encInput (encList (encList encUnary))
  simpa only [Function.comp_def] using h

private theorem gain_computable : ComputableInPolyTime
    (fun p : Input × List ℕ => gain p.1 p.2)
    (encPair encInput (encList encUnary)) encRatBin := by
  have hcomp : ComputableInPolyTime
      (fun p : Input × List ℕ => (population p.1).filter (fun i => !(member i p.2)))
      (encPair encInput (encList encUnary)) (encList encUnary) := by
    apply filterWithInput (population_computable.comp (fst _ _))
    fun_prop
  have hc := batchCost_computable.comp ((fst _ _).prod hcomp)
  have hfail := ratBin_sub.comp ((const 1).prod failureProduct_computable)
  have h := ratBin_mul.comp (hfail.prod hc)
  simpa only [Function.comp_def, gain] using h

private theorem better_computable : ComputableInPolyTime
    (fun p : (Input × List ℕ) × List ℕ => better p.1.1 p.1.2 p.2)
    (encPair (encPair encInput (encList encUnary)) (encList encUnary)) (encList encUnary) := by
  have hleft : ComputableInPolyTime
      (fun p : (Input × List ℕ) × List ℕ => gain p.1.1 p.1.2)
      (encPair (encPair encInput (encList encUnary)) (encList encUnary)) encRatBin :=
    gain_computable.comp (fst _ _)
  have hright : ComputableInPolyTime
      (fun p : (Input × List ℕ) × List ℕ => gain p.1.1 p.2)
      (encPair (encPair encInput (encList encUnary)) (encList encUnary)) encRatBin := by
    have harg : ComputableInPolyTime
        (fun p : (Input × List ℕ) × List ℕ => (p.1.1,p.2))
        (encPair (encPair encInput (encList encUnary)) (encList encUnary))
        (encPair encInput (encList encUnary)) := by fun_prop
    have h := gain_computable.comp harg
    simpa only [Function.comp_def] using h
  have htest := ratBin_lt.comp (hleft.prod hright)
  have h := htest.ite (snd _ _) ((snd _ _).comp (fst _ _))
  simpa only [Function.comp_def, better, decide_eq_true_eq] using h

/-- One fixed native multitape machine processes the entire runtime input,
including threshold enumeration, preprocessing, normalized binary arithmetic,
minimum-product pruning, reconstruction, membership scans, final comparisons
and encoded output. The inverse-tolerance budget is unary, independently of the
binary cost magnitudes. This theorem is unconditional on input validity. -/
theorem computable_choose : ComputableInPolyTime choose encInput (encList encUnary) := by
  have hf := ComputableTidilyInPolyTime.foldlWith_spec
    (encP := encInput) (encA := encList encUnary) (encL := encList (encList encUnary))
    (encB := encList encUnary) (encIn := encInput)
    (par := id) (list := candidates) (init := population) (step := better)
    ComputableTidilyInPolyTime.id' candidates_computable.tidy population_computable.tidy
    better_computable.tidy
    (fun x consumed A => A = population x ∨ A ∈ consumed)
    (by intro x; exact Or.inl rfl) (by
      intro x consumed A B _ hA
      change better x A B = population x ∨ better x A B ∈ consumed ++ [B]
      unfold better
      split_ifs
      · exact Or.inr (by simp)
      · rcases hA with hA | hA
        · exact Or.inl hA
        · exact Or.inr (List.mem_append_left _ hA))
    (size := fun x => (encList encUnary (population x)).length +
      (encList (encList encUnary) (candidates x)).length)
    (population_computable.tidy.polyBounded_length.add
      candidates_computable.tidy.polyBounded_length) ?_
  · exact of_tidy hf.1
  · intro x consumed A hp hA
    rcases hA with rfl | hA
    · exact Nat.le_add_right _ _
    · have hh := SizedListEncoding.length_elem_le
        (encA := encList encUnary) (encL := encList (encList encUnary))
        (candidates x) A (hp.subset hA)
      omega

/-- Emit both batches as explicit lists, charging the final complement scan too. -/
@[expose] def schedule (x : Input) : List ℕ × List ℕ :=
  let A := choose x
  (A,(population x).filter (fun i => !(member i A)))

/-- The complete encoded two-batch output, including its complementary second
batch, is produced by one uniform native polynomial-time implementation. -/
theorem computable_schedule : ComputableInPolyTime schedule encInput
    (encPair (encList encUnary) (encList encUnary)) := by
  have hsecond : ComputableInPolyTime
      (fun x => (population x).filter (fun i => !(member i (choose x))))
      encInput (encList encUnary) := by
    apply filterWithInput population_computable
    have h := bool_not.comp (member_computable.comp
      ((snd encInput encUnary).prod (computable_choose.comp (fst _ _))))
    simpa only [Function.comp_def] using h
  unfold schedule
  exact computable_choose.prod hsecond

end Cslib.Probability.StochasticOracle.TwoBatchNative
