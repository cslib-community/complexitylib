/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.TwoBatchPartition
public import Complexity.Computability.Complexity.Problems.Partition
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Tactic.PolyTime
import Mathlib.Tactic

/-!
# Binary hardness of exact two-turn oracle selection

[Wang2027], Theorem 3(1), PDF p. 9, Appendix A.2, pp. 14–15.
The decision problem asks for a maximum-success failure-oblivious policy of
expected cost at most a supplied rational threshold by the prescribed deadline.
Its competitors include arbitrary real private randomization.

We reuse the library's binary `SubsetSum` hardness and its reduction to `Partition`.
Zero weights are removed before appending the two strictly positive balancing
weights. Repeated positive weights retain separate indexed opportunities.
The emitted probabilities, costs, cutoffs, deadline and threshold use canonical
binary rational encodings; no unary cost advice or optimization certificate is supplied.
## Main results

* `reduction_mem_iff`: soundness and completeness for the actual policy objective.
* `computable_reduction`: one native binary polynomial-time reduction.
* `restrictedDecision_npHard`: hardness with equal cutoffs and cost ratios.
-/

public section
namespace Cslib.Probability.StochasticOracle.TwoBatchHardness
open Finset Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Cslib.Complexity TwoBatchPartition
open scoped List

/-- A binary decision input, with a proof that each oracle has valid parameters.
Proofs are absent from the encoding. The list order distinguishes repeated calls. -/
structure Input where
  /-- Ordered probability/cost/cutoff triples. -/
  calls : List (ℚ × ℚ × ℚ)
  /-- Prescribed cutoff deadline. -/
  deadline : ℚ
  /-- Expected-cost decision threshold. -/
  threshold : ℚ
  /-- The paper excludes zero/certain success and nonpositive costs or cutoffs. -/
  valid : ∀ t ∈ calls, 0 < t.1 ∧ t.1 < 1 ∧ 0 < t.2.1 ∧ 0 < t.2.2

/-- Canonical binary encoding of every numerical parameter, with list/pair framing. -/
@[expose] def encInput : Input ↪ List Bool :=
  (⟨fun x => (x.calls,x.deadline,x.threshold), fun x y h => by
    cases x; cases y; simp_all⟩ : Input ↪ List (ℚ × ℚ × ℚ) × ℚ × ℚ).trans
      (encPair (encList (encPair encRatBin (encPair encRatBin encRatBin)))
        (encPair encRatBin encRatBin))

/-- Decode the indexed oracle instance from the input list. -/
@[expose] def Input.instance (x : Input) : FullCoverInstance (Fin x.calls.length) ℚ where
  success i := (x.calls.get i).1
  success_pos i := (x.valid _ (List.get_mem x.calls i)).1
  success_lt_one i := (x.valid _ (List.get_mem x.calls i)).2.1
  cost i := (x.calls.get i).2.1
  cost_pos i := (x.valid _ (List.get_mem x.calls i)).2.2.1
  cutoff i := (x.calls.get i).2.2
  cutoff_pos i := (x.valid _ (List.get_mem x.calls i)).2.2.2

/-- Actual randomized-policy decision language for two-turn maximum-success selection. -/
@[expose] def Decision : Set Input := {x | ∃ π : Policy (Fin x.calls.length) ℝ 2,
  π.Feasible x.instance.realify (x.deadline : ℝ) ∧
  (π.execution x.instance.realify).mean executionSuccess =
    1 - x.instance.realify.batchFailure univ ∧
  (π.execution x.instance.realify).mean (executionCost x.instance.realify) ≤ (x.threshold : ℝ)}

/-- Remove zero weights without identifying equal positive occurrences. -/
@[expose] def positiveWeights (l : List ℕ) : List ℕ := l.filter (fun n => 0 < n)

private theorem positiveWeights_sum (l : List ℕ) : (positiveWeights l).sum = l.sum := by
  induction l with
  | nil => rfl
  | cons n l ih =>
    by_cases hn : 0 < n
    · simp [positiveWeights, hn, ← ih]
    · have : n = 0 := by omega
      simpa only [positiveWeights, List.filter_cons, this, lt_self_iff_false, decide_false,
        Bool.false_eq_true, ite_false, List.sum_cons, zero_add] using ih

private theorem positiveWeights_subsetSum (l : List ℕ) (t : ℕ) :
    (positiveWeights l,t) ∈ SubsetSum ↔ (l,t) ∈ SubsetSum := by
  simp only [mem_SubsetSum_iff_sublist]
  constructor
  · rintro ⟨s,hs,ht⟩
    exact ⟨s,hs.trans (List.filter_sublist),ht⟩
  · rintro ⟨s,hs,ht⟩
    exact ⟨positiveWeights s,hs.filter _,(positiveWeights_sum s).trans ht⟩

/-- Positive partition weights obtained using the existing subset-sum reduction. -/
@[expose] def weights (x : List ℕ × ℕ) : List ℕ :=
  SubsetSum.toPartition (positiveWeights x.1,x.2)

/-- Half the total of the constructed positive partition instance. -/
@[expose] def halfTotal (x : List ℕ × ℕ) : ℕ := (positiveWeights x.1).sum + x.2 + 1

private theorem weights_pos (x : List ℕ × ℕ) : ∀ n ∈ weights x, 0 < n := by
  intro n hn
  simp only [weights, SubsetSum.toPartition, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hn
  rcases hn with hn | rfl | rfl
  · exact (List.mem_filter.mp hn).2 |> of_decide_eq_true
  · omega
  · omega

private theorem weights_total (x : List ℕ × ℕ) : (weights x).sum = 2 * halfTotal x := by
  simp [weights, SubsetSum.toPartition, halfTotal]
  omega

private theorem halfTotal_pos (x : List ℕ × ℕ) : 0 < halfTotal x := by
  unfold halfTotal
  omega

private theorem weights_nonempty (x : List ℕ × ℕ) : 0 < (weights x).length := by
  simp [weights, SubsetSum.toPartition]

/-- The actual emitted decision instance. All costs and probabilities are binary. -/
@[expose] def reduction (x : List ℕ × ℕ) : Input where
  calls := (weights x).map (fun n : ℕ => ((n : ℚ) / denominator (halfTotal x),(n : ℚ),1))
  deadline := 2
  threshold := TwoBatchPartition.threshold (halfTotal x)
  valid := by
    intro t ht
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp ht
    let a : Fin (weights x).length → ℕ := fun i => (weights x).get i
    have htotal : ∑ i, a i = 2 * halfTotal x := by
      rw [show (∑ i, a i) = (weights x).sum from by simp [a]]
      exact weights_total x
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hn
    let I := instanceOf a (halfTotal x) (halfTotal_pos x)
      (fun j => weights_pos x _ (List.get_mem ..)) htotal
    have hp := I.success_pos i
    have hp' := I.success_lt_one i
    change 0 < (weights x).get i / denominator (halfTotal x) at hp
    change (weights x).get i / denominator (halfTotal x) < 1 at hp'
    rw [hi] at hp hp'
    exact ⟨hp,hp',by change 0 < (n : ℚ); exact_mod_cast weights_pos x n hn,
      by norm_num⟩

/-- Soundness and completeness of the binary reduction for the actual policy objective. -/
theorem reduction_mem_iff (x : List ℕ × ℕ) : reduction x ∈ Decision ↔ x ∈ SubsetSum := by
  classical
  let a : Fin (reduction x).calls.length → ℕ := fun i =>
    (weights x).get ⟨i.val,by simpa only [reduction,List.length_map] using i.isLt⟩
  have hmap : (List.finRange (reduction x).calls.length).map a = weights x := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_finRange]
      exact List.length_map ..
    · intro i hi hi'
      simp [a]
  have htotal : ∑ i, a i = 2 * halfTotal x := by
    have h := congrArg List.sum hmap
    rw [← List.sum_toFinset a (List.nodup_finRange _)] at h
    simpa only [List.toFinset_finRange,weights_total] using h
  have ha : ∀ i, 0 < a i := fun _ => weights_pos x _ (List.get_mem ..)
  have hI : (reduction x).instance = instanceOf a (halfTotal x) (halfTotal_pos x) ha htotal := by
    apply FullCoverInstance.ext <;> intro i <;> simp [Input.instance, reduction, instanceOf, a]
  let : Nonempty (Fin (reduction x).calls.length) :=
    ⟨⟨0,by simpa only [reduction,List.length_map] using weights_nonempty x⟩⟩
  have hpolicy := policy_threshold_iff (halfTotal_pos x) ha htotal
  change (∃ π : Policy (Fin (reduction x).calls.length) ℝ 2,
    π.Feasible (reduction x).instance.realify 2 ∧
    (π.execution (reduction x).instance.realify).mean executionSuccess =
      1 - (reduction x).instance.realify.batchFailure univ ∧
    (π.execution (reduction x).instance.realify).mean
      (executionCost (reduction x).instance.realify) ≤
      (TwoBatchPartition.threshold (halfTotal x) : ℝ)) ↔ _
  rw [hI]
  rw [hpolicy]
  have hsub := map_mem_SubsetSum_iff (List.nodup_finRange _) a (halfTotal x)
  rw [hmap] at hsub
  simp only [List.toFinset_finRange,Finset.subset_univ,true_and] at hsub
  rw [← hsub,mem_SubsetSum_iff_sublist]
  have hpart : (∃ s, s <+ weights x ∧ s.sum = halfTotal x) ↔ weights x ∈ Partition := by
    rw [mem_Partition_iff_sublist,weights_total]
    constructor <;> rintro ⟨s,hs,h⟩ <;> exact ⟨s,hs,by omega⟩
  rw [hpart,weights,SubsetSum.toPartition_mem_iff,positiveWeights_subsetSum]

private theorem positiveWeights_computable : ComputableInPolyTime positiveWeights
    (encList encNat) (encList encNat) := by
  unfold positiveWeights
  fun_prop

attribute [local fun_prop] positiveWeights_computable

private theorem weights_computable : ComputableInPolyTime weights
    (encPair (encList encNat) encNat) (encList encNat) := by
  unfold weights
  fun_prop

private theorem halfTotal_computable : ComputableInPolyTime halfTotal
    (encPair (encList encNat) encNat) encNat := by
  have hs := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.binary_sum).comp
    (positiveWeights_computable.comp (fst (encList encNat) encNat))
  have h := binary_add.comp ((binary_add.comp (hs.prod (snd _ _))).prod (const 1))
  exact h

attribute [local fun_prop] weights_computable halfTotal_computable

private theorem denominator_computable : ComputableInPolyTime
    (fun x : List ℕ × ℕ => denominator (halfTotal x))
    (encPair (encList encNat) encNat) encRatBin := by
  unfold denominator
  simp only [pow_succ,pow_zero]
  fun_prop

attribute [local fun_prop] denominator_computable

/-- One uniform native binary machine computes the complete reduction, including
normalization, cubic denominator, threshold, list framing and repeated entries. -/
theorem computable_reduction : ComputableInPolyTime reduction
    (encPair (encList encNat) encNat) encInput := by
  have hc : ComputableInPolyTime (fun x : List ℕ × ℕ => (reduction x).calls)
      (encPair (encList encNat) encNat)
      (encList (encPair encRatBin (encPair encRatBin encRatBin))) := by
    change ComputableInPolyTime (fun x : List ℕ × ℕ => (weights x).map
      (fun n : ℕ => ((n : ℚ) / denominator (halfTotal x),(n : ℚ),1))) _ _
    apply mapWithInput weights_computable
    have hn := ratBin_natCast.comp (snd (encPair (encList encNat) encNat) encNat)
    have hd := denominator_computable.comp (fst (encPair (encList encNat) encNat) encNat)
    exact (ratBin_div.comp (hn.prod hd)).prod (hn.prod (const (1 : ℚ)))
  have ht : ComputableInPolyTime (fun x : List ℕ × ℕ =>
      TwoBatchPartition.threshold (halfTotal x))
      (encPair (encList encNat) encNat) encRatBin := by
    unfold TwoBatchPartition.threshold
    simp only [pow_two]
    fun_prop
  exact (hc.prod ((const (2 : ℚ)).prod ht)).of_enc_eq (by intro x; rfl)

/-- Restrict to unit cutoffs and a common probability/cost ratio, as in Theorem 3(1). -/
@[expose] def RestrictedDecision : Set Input := {x | x ∈ Decision ∧
  ∃ r : ℚ, ∀ t ∈ x.calls, t.2.2 = 1 ∧ t.1 / t.2.1 = r}

/-- The reduction already has the equal-cutoff/equal-ratio restrictions. -/
theorem reduction_parameters (x : List ℕ × ℕ) :
    ∀ t ∈ (reduction x).calls,
      t.2.2 = 1 ∧ t.1 / t.2.1 = (denominator (halfTotal x))⁻¹ := by
  intro t ht
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp ht
  refine ⟨rfl,?_⟩
  change ((n : ℚ) / denominator (halfTotal x)) / n = _
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (weights_pos x n hn))
  field_simp

/-- Exact two-turn maximum-success selection is NP-hard even with unit cutoffs
and equal probability/cost ratios. Costs, probabilities and the decision threshold
are binary encoded, and the decision quantifies over all real-randomized policies. -/
theorem restrictedDecision_npHard : NPHard encInput RestrictedDecision := by
  apply SubsetSum_npHard.trans
  refine ⟨reduction,computable_reduction,?_⟩
  intro x
  constructor
  · intro hx
    exact ⟨(reduction_mem_iff x).mpr hx,_,reduction_parameters x⟩
  · intro hx
    exact (reduction_mem_iff x).mp hx.1

end Cslib.Probability.StochasticOracle.TwoBatchHardness
