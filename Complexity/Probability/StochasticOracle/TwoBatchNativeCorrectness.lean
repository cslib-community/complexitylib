/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.TwoBatchNative
public import Complexity.Probability.StochasticOracle.TwoBatchGuarantees
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Correctness of uniform binary two-batch selection

The runtime data representation is connected to the original indexed instance,
rounded recurrence and executed selection in [Wang2027], Theorem 2(2), PDF p. 8.
The inverse-tolerance budget bounds
rounded keys; it is not a bound on binary input cost magnitudes.

## Main results

* `key_ofInstance`: valid eligible items never hit the implementation's safety cap.
* `choose_eq`, `schedule_eq`: both decoded native batches equal the reviewed selection.
-/

public section
namespace Cslib.Probability.StochasticOracle.TwoBatchNative
open Cslib.Algorithms.Lean.DynamicProgramming.MinProduct
open Turing.MultiTapeTM

variable {k : ℕ} (I : FullCoverInstance (Fin k) ℚ)

/-- Serialize an indexed instance into the uniform runtime data type. -/
@[expose] def Input.ofInstance (ε D : ℚ) (m : ℕ) : Input :=
  ⟨ε,D,m,(List.finRange k).map (fun i => (I.success i,I.cost i,I.cutoff i))⟩

private theorem calls_length (ε D : ℚ) (m : ℕ) :
    (Input.ofInstance I ε D m).calls.length = k := by simp [Input.ofInstance]

private theorem call_ofInstance (ε D : ℚ) (m : ℕ) (i : Fin k) :
    call (Input.ofInstance I ε D m) i.val = (I.success i,I.cost i,I.cutoff i) := by
  simp [call, Input.ofInstance, i.isLt]

private theorem success_ofInstance (ε D : ℚ) (m : ℕ) (i : Fin k) :
    success (Input.ofInstance I ε D m) i.val = I.success i := by
  simp only [success, call_ofInstance]

private theorem cost_ofInstance (ε D : ℚ) (m : ℕ) (i : Fin k) :
    cost (Input.ofInstance I ε D m) i.val = I.cost i := by
  simp only [cost, call_ofInstance]

private theorem cutoff_ofInstance (ε D : ℚ) (m : ℕ) (i : Fin k) :
    cutoff (Input.ofInstance I ε D m) i.val = I.cutoff i := by
  simp only [cutoff, call_ofInstance]

private theorem failure_ofInstance (ε D : ℚ) (m : ℕ) (i : Fin k) :
    failure (Input.ofInstance I ε D m) i.val = TwoBatchApproximation.failure I i := by
  simp only [failure, success_ofInstance, TwoBatchApproximation.failure]

private theorem population_ofInstance (ε D : ℚ) (m : ℕ) :
    population (Input.ofInstance I ε D m) =
      (TwoBatchApproximation.population (k := k)).map Fin.val := by
  simp only [population, calls_length, TwoBatchApproximation.population]
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp

private theorem optional_ofInstance (ε D a b : ℚ) (m : ℕ) :
    optional (Input.ofInstance I ε D m) a b =
      (TwoBatchApproximation.optional I a b).map Fin.val := by
  simp only [optional, population_ofInstance, TwoBatchApproximation.optional,
    List.filter_map, Function.comp_def, cutoff_ofInstance]

private theorem forced_ofInstance (ε D b : ℚ) (m : ℕ) :
    forced (Input.ofInstance I ε D m) b =
      (TwoBatchApproximation.forced I b).map Fin.val := by
  simp only [forced, population_ofInstance, TwoBatchApproximation.forced,
    List.filter_map, Function.comp_def, cutoff_ofInstance]

private theorem failureProduct_ofInstance (ε D : ℚ) (m : ℕ) (xs : List (Fin k)) :
    failureProduct (Input.ofInstance I ε D m) (xs.map Fin.val) =
      TwoBatchApproximation.failureProduct I xs := by
  simp only [failureProduct, List.map_map, Function.comp_def, failure_ofInstance,
    TwoBatchApproximation.failureProduct]

/-- Saturation is inactive on every item that is at most as costly as the
mandatory maximum member. Its cap is polynomial in population and inverse
accuracy, irrespective of the numerical input costs. -/
theorem key_ofInstance {ε : ℚ} (hε : 0 < ε) (D : ℚ) (m : ℕ) (hm : 1 ≤ ε * m)
    (r : Fin k) (items : List (Fin k)) (hn : items.length ≤ k)
    {i : Fin k} (hi : I.cost i ≤ I.cost r) :
    key (Input.ofInstance I ε D m)
      (scale (Input.ofInstance I ε D m) r.val (items.map Fin.val)) i.val =
      rounded I.cost (branchScale I.cost ε r items) i := by
  have heq : scale (Input.ofInstance I ε D m) r.val (items.map Fin.val) =
      branchScale I.cost ε r items := by
    unfold scale
    rw [cost_ofInstance, List.length_map]
    rfl
  rw [heq]
  have hK : 0 < branchScale I.cost ε r items :=
    div_pos (mul_pos hε (I.cost_pos r)) (by positivity)
  have hr : I.cost r / branchScale I.cost ε r items = (items.length + 1 : ℕ) / ε := by
    unfold branchScale
    field_simp [ne_of_gt (I.cost_pos r), ne_of_gt hε]
  have hm' : (items.length + 1 : ℕ) / ε ≤ ((k + 1) * m : ℕ) := by
    apply (div_le_iff₀ hε).mpr
    have hn' : ((items.length + 1 : ℕ) : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.add_le_add_right hn 1
    have h := mul_le_mul_of_nonneg_left hm (show (0 : ℚ) ≤ k + 1 by positivity)
    push_cast at hn' ⊢
    nlinarith
  have hb := rounded_le_bound I.cost hK (hr ▸ hm') hi
  simp only [key, cost_ofInstance, keyCap, calls_length]
  change min ((k + 1) * m) (rounded I.cost (branchScale I.cost ε r items) i) = _
  exact min_eq_right hb

private theorem member_map (xs : List (Fin k)) (i : Fin k) :
    member i.val (xs.map Fin.val) = decide (i ∈ xs) := by
  apply Bool.eq_iff_iff.mpr
  simp [member, Function.comp_def, List.any_eq_true, Fin.val_injective.eq_iff]

/-- Decode the explicit output indices as a first batch in the original finite population. -/
@[expose] def decode (A : List ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => i.val ∈ A)

private theorem decode_firstBatch (ε D a b : ℚ) (m : ℕ) (second : List (Fin k)) :
    decode (firstBatch (Input.ofInstance I ε D m) a b (second.map Fin.val)) =
      TwoBatchApproximation.firstBatch I a b second := by
  ext i
  simp [decode, firstBatch, forced_ofInstance, optional_ofInstance, member_map,
    TwoBatchApproximation.firstBatch, Fin.val_inj]

private theorem firstBatch_good (x : Input) (a b : ℚ) (second : List ℕ) :
    (firstBatch x a b second).Nodup ∧
      ∀ i ∈ firstBatch x a b second, i < x.calls.length := by
  have hp : (population x).Nodup := List.nodup_range
  have hf : (forced x b).Nodup := hp.filter _
  have ho : ((optional x a b).filter (fun i => !(member i second))).Nodup :=
    (hp.filter _).filter _
  have hdis : ∀ i ∈ forced x b, i ∉ (optional x a b).filter (fun j => !(member j second)) := by
    intro i hi ho
    have hb : b < cutoff x i := of_decide_eq_true (List.mem_filter.mp hi).2
    have hb' : cutoff x i ≤ b :=
      (of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp ho).1).2).2
    exact (not_lt_of_ge hb') hb
  constructor
  · apply List.nodup_append.mpr
    refine ⟨hf,ho,?_⟩
    intro i hi j hj hij
    subst j
    exact hdis i hi hj
  · intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact List.mem_range.mp (List.mem_filter.mp hi).1
    · exact List.mem_range.mp (List.mem_filter.mp (List.mem_filter.mp hi).1).1

private theorem decode_nonempty {A : List ℕ} (hA : ∀ i ∈ A, i < k) :
    (decode A : Finset (Fin k)).Nonempty ↔ A ≠ [] := by
  constructor
  · rintro ⟨i,hi⟩ rfl
    simp [decode] at hi
  · intro hn
    obtain ⟨i,hi⟩ := List.exists_mem_of_ne_nil _ hn
    exact ⟨⟨i,hA i hi⟩,by simp [decode, hi]⟩

private theorem branch_ofInstance {ε : ℚ} (hε : 0 < ε) (D a b : ℚ)
    (m : ℕ) (hm : 1 ≤ ε * m) (r : Fin k) :
    (maximumBranch (Input.ofInstance I ε D m) a b r.val).map decode =
      TwoBatchApproximation.maximumBranch I ε a b r := by
  let items := (TwoBatchApproximation.optional I a b).filter
    (fun i => I.cost i ≤ I.cost r ∧ i ≠ r)
  let outside := TwoBatchApproximation.failureProduct I
    ((TwoBatchApproximation.optional I a b).filter (fun i => I.cost r < I.cost i))
  have hn : items.length ≤ k :=
    (List.length_filter_le ..).trans ((List.length_filter_le ..).trans_eq
      (by simp [TwoBatchApproximation.population]))
  have he : (optional (Input.ofInstance I ε D m) a b).filter
      (fun i => cost (Input.ofInstance I ε D m) i ≤ cost (Input.ofInstance I ε D m) r.val ∧
        i ≠ r.val) = items.map Fin.val := by
    simp only [optional_ofInstance, List.filter_map, Function.comp_def,
      cost_ofInstance, ne_eq, Fin.val_injective.eq_iff, items]
  have hout : failureProduct (Input.ofInstance I ε D m)
      ((optional (Input.ofInstance I ε D m) a b).filter
        (fun i => cost (Input.ofInstance I ε D m) r.val < cost (Input.ofInstance I ε D m) i)) =
      outside := by
    rw [optional_ofInstance, List.filter_map]
    simpa only [Function.comp_def, cost_ofInstance] using
      failureProduct_ofInstance I ε D m
        ((TwoBatchApproximation.optional I a b).filter (fun i => I.cost r < I.cost i))
  have hinit : (⟨key (Input.ofInstance I ε D m)
        (scale (Input.ofInstance I ε D m) r.val (items.map Fin.val)) r.val,
        outside,[r.val]⟩ : Entry ℕ) =
      (branchInitial I.cost ε r outside items).map Fin.val := by
    rw [key_ofInstance I hε D m hm r items hn le_rfl]
    rfl
  have hrun := run_map Fin.val (rounded I.cost (branchScale I.cost ε r items))
    (TwoBatchApproximation.failure I)
    (key (Input.ofInstance I ε D m)
      (scale (Input.ofInstance I ε D m) r.val (items.map Fin.val)))
    (failure (Input.ofInstance I ε D m)) (branchInitial I.cost ε r outside items) items
    (fun i hi => key_ofInstance I hε D m hm r items hn
      (of_decide_eq_true (List.mem_filter.mp hi).2).1)
    (fun i _ => failure_ofInstance I ε D m i)
  unfold maximumBranch
  rw [he, hout]
  dsimp only
  rw [hinit, hrun]
  simp only [List.map_map, Function.comp_def, Entry.map, decode_firstBatch,
    TwoBatchApproximation.maximumBranch,
    Cslib.Algorithms.Lean.DynamicProgramming.MinProduct.branch, items, outside]

private theorem maximumBranch_good (x : Input) (a b : ℚ) (r : ℕ)
    {A : List ℕ} (hA : A ∈ maximumBranch x a b r) :
    A.Nodup ∧ ∀ i ∈ A, i < x.calls.length := by
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hA
  exact firstBatch_good x a b e.selected

private theorem familyCandidates_good (x : Input) (a b : ℚ)
    {A : List ℕ} (hA : A ∈ familyCandidates x a b) :
    A.Nodup ∧ ∀ i ∈ A, i < x.calls.length := by
  unfold familyCandidates at hA
  split_ifs at hA
  · rcases List.mem_cons.mp (List.mem_filter.mp hA).1 with rfl | hA
    · exact firstBatch_good x a b []
    · obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp hA
      exact maximumBranch_good x a b r hr
  · simp at hA

private theorem candidates_good (x : Input) {A : List ℕ} (hA : A ∈ candidates x) :
    A.Nodup ∧ ∀ i ∈ A, i < x.calls.length := by
  obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hA
  obtain ⟨b,_,hb⟩ := List.mem_flatMap.mp ha
  split_ifs at hb
  · exact familyCandidates_good x a b hb
  · simp at hb

private theorem decode_filter (xs : List (List ℕ))
    (hxs : ∀ A ∈ xs, ∀ i ∈ A, i < k) :
    (xs.filter (fun A => !A.isEmpty)).map (decode (k := k)) =
      (xs.map decode).filter (fun A => decide A.Nonempty) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro A hA
  apply Bool.eq_iff_iff.mpr
  simp [decode_nonempty (hxs A hA)]

private theorem family_ofInstance {ε : ℚ} (hε : 0 < ε) (D a b : ℚ)
    (m : ℕ) (hm : 1 ≤ ε * m) :
    (familyCandidates (Input.ofInstance I ε D m) a b).map decode =
      TwoBatchApproximation.familyCandidates I ε a b := by
  have hguard : (forced (Input.ofInstance I ε D m) b).all
      (fun i => decide (cutoff (Input.ofInstance I ε D m) i ≤ a)) =
      (TwoBatchApproximation.forced I b).all (fun i => decide (I.cutoff i ≤ a)) := by
    simp only [forced_ofInstance, List.all_map, Function.comp_def, cutoff_ofInstance]
  unfold familyCandidates
  rw [hguard]
  unfold TwoBatchApproximation.familyCandidates
  split_ifs
  · rw [decode_filter _ (by
      intro A hA
      rcases List.mem_cons.mp hA with rfl | hA
      · simpa only [calls_length] using (firstBatch_good (Input.ofInstance I ε D m) a b []).2
      · obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp hA
        simpa only [calls_length] using (maximumBranch_good _ a b r hr).2)]
    congr 1
    simp only [List.map_cons, List.map_flatMap, optional_ofInstance, List.flatMap_map,
      branch_ofInstance I hε D a b m hm]
    congr 1
    exact decode_firstBatch I ε D a b m []
  · rfl

private theorem candidates_ofInstance {ε : ℚ} (hε : 0 < ε) (D : ℚ)
    (m : ℕ) (hm : 1 ≤ ε * m) :
    (candidates (Input.ofInstance I ε D m)).map decode =
      TwoBatchApproximation.candidates I ε D := by
  simp only [candidates, TwoBatchApproximation.candidates, population_ofInstance,
    List.map_map, Function.comp_def, cutoff_ofInstance, List.map_flatMap]
  congr 1
  funext a
  congr 1
  funext b
  change (if a + b ≤ D then familyCandidates (Input.ofInstance I ε D m) a b else []).map
    decode = if a + b ≤ D then TwoBatchApproximation.familyCandidates I ε a b else []
  split_ifs
  · exact family_ofInstance I hε D a b m hm
  · rfl

private theorem member_eq (i : ℕ) (xs : List ℕ) :
    member i xs = decide (i ∈ xs) := by
  apply Bool.eq_iff_iff.mpr
  simp [member, List.any_eq_true]

private theorem batchFailure_decode (ε D : ℚ) (m : ℕ) (A : List ℕ)
    (hn : A.Nodup) (hb : ∀ i ∈ A, i < k) :
    I.batchFailure (decode A) = failureProduct (Input.ofInstance I ε D m) A := by
  unfold FullCoverInstance.batchFailure failureProduct
  rw [← List.prod_toFinset _ hn]
  apply Finset.prod_bij (fun (i : Fin k) _ => i.val)
  · intro i hi
    simpa [decode] using hi
  · intro i _ j _ hij
    exact Fin.val_injective hij
  · intro j hj
    have hj' := List.mem_toFinset.mp hj
    exact ⟨⟨j,hb j hj'⟩,by simp [decode, hj'],rfl⟩
  · intro i _
    simpa only [TwoBatchApproximation.failure] using (failure_ofInstance I ε D m i).symm

private theorem batchCost_decode (ε D : ℚ) (m : ℕ) (A : List ℕ)
    (hn : A.Nodup) (hb : ∀ i ∈ A, i < k) :
    I.batchCost (decode A) = batchCost (Input.ofInstance I ε D m) A := by
  unfold FullCoverInstance.batchCost batchCost
  rw [← List.sum_toFinset _ hn]
  apply Finset.sum_bij (fun (i : Fin k) _ => i.val)
  · intro i hi
    simpa [decode] using hi
  · intro i _ j _ hij
    exact Fin.val_injective hij
  · intro j hj
    have hj' := List.mem_toFinset.mp hj
    exact ⟨⟨j,hb j hj'⟩,by simp [decode, hj'],rfl⟩
  · intro i _
    exact (cost_ofInstance I ε D m i).symm

private theorem gain_decode (ε D : ℚ) (m : ℕ) (A : List ℕ)
    (hn : A.Nodup) (hb : ∀ i ∈ A, i < k) :
    gain (Input.ofInstance I ε D m) A = TwoBatchApproximation.gain I (decode A) := by
  let second := (population (Input.ofInstance I ε D m)).filter (fun i => !(member i A))
  have hn' : second.Nodup := List.nodup_range.filter _
  have hb' : ∀ i ∈ second, i < k := by
    intro i hi
    have h := List.mem_range.mp (List.mem_filter.mp hi).1
    simpa only [calls_length] using h
  have hsecond : decode second = Finset.univ \ (decode A : Finset (Fin k)) := by
    ext i
    simp [decode, second, population, calls_length, member_eq]
  unfold gain TwoBatchApproximation.gain
  rw [batchFailure_decode I ε D m A hn hb, ← hsecond, batchCost_decode I ε D m second hn' hb']

private theorem better_decode (ε D : ℚ) (m : ℕ) (A B : List ℕ)
    (hA : A.Nodup ∧ ∀ i ∈ A, i < k) (hB : B.Nodup ∧ ∀ i ∈ B, i < k) :
    decode (better (Input.ofInstance I ε D m) A B) =
      TwoBatchApproximation.better I (decode A) (decode B) := by
  unfold better TwoBatchApproximation.better
  rw [gain_decode I ε D m A hA.1 hA.2, gain_decode I ε D m B hB.1 hB.2]
  split_ifs <;> rfl

/-- The actual total runtime selector decodes to the original reviewed selector,
including its exact comparison and tie-breaking behavior. No implementation or
runtime certificate is a hypothesis. -/
theorem choose_eq {ε : ℚ} (hε : 0 < ε) (D : ℚ) (m : ℕ) (hm : 1 ≤ ε * m) :
    decode (choose (Input.ofInstance I ε D m)) = TwoBatchApproximation.choose I ε D := by
  let x := Input.ofInstance I ε D m
  have hf : ∀ (xs : List (List ℕ)),
      (∀ B ∈ xs, B.Nodup ∧ ∀ i ∈ B, i < k) → ∀ A : List ℕ,
      (A.Nodup ∧ ∀ i ∈ A, i < k) →
      decode (xs.foldl (better x) A) =
        (xs.map decode).foldl (TwoBatchApproximation.better I) (decode A) := by
    intro xs
    induction xs with
    | nil => intro _ A _; rfl
    | cons B bs ih =>
      intro hbs A hA
      have hB := hbs B (List.mem_cons_self ..)
      simp only [List.foldl_cons, List.map_cons]
      rw [← better_decode I ε D m A B hA hB]
      apply ih (fun C hC => hbs C (List.mem_cons_of_mem _ hC))
      unfold better
      split_ifs
      · exact hB
      · exact hA
  have hpop : (population x).Nodup ∧ ∀ i ∈ population x, i < k := by
    constructor
    · exact List.nodup_range
    · intro i hi
      have h := List.mem_range.mp hi
      simpa only [x, calls_length] using h
  have hdecode : decode (population x) = (Finset.univ : Finset (Fin k)) := by
    ext i
    simp [decode, population, x, calls_length]
  unfold choose TwoBatchApproximation.choose
  rw [hf (candidates x) (fun B hB => by
    simpa only [x, calls_length] using candidates_good x hB) (population x) hpop,
    hdecode, candidates_ofInstance I hε D m hm]

/-- The second list emitted by the native schedule compiler is exactly the
complementary batch; interpreting the output performs no additional enumeration. -/
theorem schedule_eq {ε : ℚ} (hε : 0 < ε) (D : ℚ) (m : ℕ) (hm : 1 ≤ ε * m) :
    (decode (schedule (Input.ofInstance I ε D m)).1,
      decode (schedule (Input.ofInstance I ε D m)).2) =
      (TwoBatchApproximation.choose I ε D,(TwoBatchApproximation.choose I ε D)ᶜ) := by
  have hsecond (A : List ℕ) : decode
      ((population (Input.ofInstance I ε D m)).filter (fun i => !(member i A))) =
        (decode A : Finset (Fin k))ᶜ := by
    ext i
    simp [decode, population, calls_length, member_eq]
  simp only [schedule, hsecond, choose_eq I hε D m hm]

end Cslib.Probability.StochasticOracle.TwoBatchNative
