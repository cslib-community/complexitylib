/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping
public import Complexity.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Occurrence joins and counts of equal-key groups

Unlike a first-hit matcher, this join preserves every pair of opposite-side
occurrences, including collisions. Counting multiplies the two group populations
and sums without constructing the Cartesian products. Sorted grouping makes the
join exhaustive. The count consumer has an actual polynomial-time bit machine;
its polynomial is in the grouped wire volume, not merely the maximum record width.
Consequently this module does not claim the sharp global source resources.

## Main definitions

* `join`, `count`: exhaustive occurrence pairs and count-only grouped consumption.

## Main results

* `mem_join`, `same_group`: sorted grouping makes the join exhaustive.
* `count_eq_length`, `count_le_square`: occurrence counts and generated-volume bound.
* `join_nodup`: unique tagged payloads give unique pairs despite key collisions.
* `join_polyTime`, `count_polyTime`: actual, conservatively charged bit consumers.
-/

public section
namespace Turing.MultiTapeTM.KeyJoin

/-- Select a side tag, preserving the actual input occurrences. -/
def side (right : Bool) (group : List SortedMatch.Record) : List SortedMatch.Record :=
  group.filter (fun row => decide (row.2 % 2 = if right then 1 else 0))

/-- Emit all pairs of packed witnesses from a single equal-key group. -/
def pairs (group : List SortedMatch.Record) : List (ℕ × ℕ) :=
  (side false group).flatMap (fun a => (side true group).map (fun b => (a.2 / 2, b.2 / 2)))

/-- Count occurrences without materializing the pairs. -/
def population (group : List SortedMatch.Record) : ℕ :=
  (side false group).length * (side true group).length

/-- Consume all groups and emit every cross-side witness pair. -/
def join (groups : List (List SortedMatch.Record)) : List (ℕ × ℕ) := groups.flatMap pairs

/-- The actual count pass only constructs binary counts, not the joined list. -/
def count (groups : List (List SortedMatch.Record)) : ℕ := (groups.map population).sum

/-- Counting includes multiplicities even when keys or payloads collide. -/
theorem count_eq_length (groups : List (List SortedMatch.Record)) :
    count groups = (join groups).length := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
    simp only [count, join, List.map_cons, List.sum_cons, List.flatMap_cons,
      List.length_append] at *
    rw [← ih]
    congr 1
    simp [population, pairs, List.length_flatMap]

/-- Counts are bounded by actual flattened volume, without a supplied class-size bound. -/
theorem count_le_square (groups : List (List SortedMatch.Record)) :
    count groups ≤ groups.flatten.length ^ 2 := by
  induction groups with
  | nil => simp [count]
  | cons group groups ih =>
    have hl : (side false group).length ≤ group.length := List.length_filter_le _ _
    have hr : (side true group).length ≤ group.length := List.length_filter_le _ _
    have hp := Nat.mul_le_mul hl hr
    simp only [count, List.map_cons, List.sum_cons] at ih ⊢
    simp only [population, List.flatten_cons, List.length_append]
    exact (Nat.add_le_add hp ih).trans (by
      nlinarith only [Nat.zero_le (group.length * groups.flatten.length)])

private def key (group : List SortedMatch.Record) : ℕ := (group.headD (0, 0)).1

private theorem key_eq {rows group : List SortedMatch.Record}
    (hg : group ∈ KeyGrouping.run rows) (r : SortedMatch.Record) (hr : r ∈ group) :
    r.1 = key group := by
  have hp := KeyGrouping.group_keys rows group hg
  cases group with
  | nil => simp at hr
  | cons a group =>
    rcases List.mem_cons.mp hr with rfl | hr
    · rfl
    · exact (List.rel_of_pairwise_cons hp hr).symm

private theorem ordered_groups (rows : List SortedMatch.Record)
    (sorted : rows.Pairwise (fun a b => a.1 ≤ b.1)) :
    (KeyGrouping.run rows).Pairwise (fun a b => key a < key b) := by
  have hs : (KeyGrouping.run rows).flatten.Pairwise (fun a b => a.1 ≤ b.1) := by
    simpa only [KeyGrouping.flatten_run] using sorted
  have hb := List.isChain_getLast_head_splitBy (fun a b : SortedMatch.Record =>
    decide (a.1 = b.1)) rows
  change (KeyGrouping.run rows).IsChain _ at hb
  have hc : (KeyGrouping.run rows).IsChain (fun a b => key a < key b) := by
    have aux (groups : List (List SortedMatch.Record))
        (mem : ∀ group ∈ groups, group ∈ KeyGrouping.run rows)
        (hs : groups.flatten.Pairwise (fun a b => a.1 ≤ b.1))
        (hb : groups.IsChain (fun a b => ∃ ha hb,
          decide ((a.getLast ha).1 = (b.head hb).1) = false)) :
        groups.IsChain (fun a b => key a < key b) := by
      induction groups with
      | nil => exact .nil
      | cons a groups ih =>
        cases groups with
        | nil => exact .singleton _
        | cons b groups =>
          have hb' := List.isChain_cons_cons.mp hb
          obtain ⟨ha, hb, hne⟩ := hb'.1
          have hp := (List.pairwise_flatten.mp hs).2
          have hle := List.rel_of_pairwise_cons hp (by simp : b ∈ b :: groups)
            (a.getLast ha) (List.getLast_mem ha) (b.head hb) (List.head_mem hb)
          rw [key_eq (mem a (by simp)) _ (List.getLast_mem ha),
            key_eq (mem b (by simp)) _ (List.head_mem hb)] at hle hne
          have hlt : key a < key b := by
            have hn := of_decide_eq_false hne
            omega
          exact List.isChain_cons_cons.mpr ⟨hlt, ih
            (fun g hg => mem g (List.mem_cons_of_mem _ hg))
            (List.pairwise_append.mp
              (show (a ++ (b :: groups).flatten).Pairwise _ from hs)).2.1 hb'.2⟩
    exact aux _ (fun _ h => h) hs hb
  let : Trans (fun a b : List SortedMatch.Record => key a < key b)
      (fun a b => key a < key b) (fun a b => key a < key b) := ⟨fun h₁ h₂ => h₁.trans h₂⟩
  exact hc.pairwise

/-- Equal keys lie in the same actual group. Sorting and the maximal-run writer establish
this fact; callers do not supply a grouping-completeness assertion. -/
theorem same_group (rows : List SortedMatch.Record)
    (sorted : rows.Pairwise (fun a b => a.1 ≤ b.1))
    (a b : SortedMatch.Record) (ha : a ∈ rows) (hb : b ∈ rows) (he : a.1 = b.1) :
    ∃ group ∈ KeyGrouping.run rows, a ∈ group ∧ b ∈ group := by
  rw [← KeyGrouping.flatten_run rows] at ha hb
  obtain ⟨ga, hga, ha⟩ := List.mem_flatten.mp ha
  obtain ⟨gb, hgb, hb⟩ := List.mem_flatten.mp hb
  have hp := (ordered_groups rows sorted).imp (fun h => Nat.ne_of_lt h)
  let : Std.Symm (fun a b : List SortedMatch.Record => key a ≠ key b) :=
    ⟨fun _ _ h he => h he.symm⟩
  have eq : ga = gb := by
    by_contra hn
    exact hp.forall hga hgb hn ((key_eq hga a ha).symm.trans (he.trans (key_eq hgb b hb)))
  exact ⟨ga, hga, ha, eq ▸ hb⟩

/-- The grouped join of sorted tagged batches is exact, including arbitrary collisions. -/
theorem mem_join (input : SortedMatch.Input)
    (fits : let (width, (left, right)) := input
      ∀ r ∈ left ++ right, r.1 < 2 ^ width) (out : ℕ × ℕ) :
    let (width, (left, right)) := input
    out ∈ join (KeyGrouping.run (RadixSort.sort (width, SortedMatch.tagged input))) ↔
      ∃ a ∈ left, ∃ b ∈ right, a.1 = b.1 ∧ out = (a.2, b.2) := by
  dsimp only at fits ⊢
  let rows := RadixSort.sort (input.1, SortedMatch.tagged input)
  have perm := SortedMatch.sorted_perm input
  have tagged : ∀ r ∈ SortedMatch.tagged input, r.1 < 2 ^ input.1 := by
    intro r hr
    rcases (SortedMatch.mem_tagged input r).mp hr with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · exact fits a (List.mem_append_left _ ha)
    · exact fits b (List.mem_append_right _ hb)
  have sorted := (RadixSort.correct (input.1, SortedMatch.tagged input) tagged).2
  constructor
  · intro h
    obtain ⟨group, hg, a, ha, b, hb, ho⟩ : ∃ group ∈ KeyGrouping.run rows,
        ∃ a ∈ side false group, ∃ b ∈ side true group, (a.2 / 2, b.2 / 2) = out := by
      simpa only [join, pairs, List.mem_flatMap, List.mem_map] using h
    have ha' := (List.mem_filter.mp ha).1
    have hb' := (List.mem_filter.mp hb).1
    have memrow (r : SortedMatch.Record) (hr : r ∈ group) : r ∈ SortedMatch.tagged input :=
      perm.mem_iff.mp (by simpa only [KeyGrouping.flatten_run] using
        (List.mem_flatten.mpr ⟨group, hg, hr⟩ : r ∈ (KeyGrouping.run rows).flatten))
    have same : a.1 = b.1 := (key_eq hg a ha').trans (key_eq hg b hb').symm
    rcases (SortedMatch.mem_tagged input a).mp (memrow a ha') with ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩ <;>
      rcases (SortedMatch.mem_tagged input b).mp (memrow b hb') with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
    · simp [side, SortedMatch.tag] at hb
    · refine ⟨l, hl, r, hr, same, ?_⟩
      simp only [SortedMatch.tag, Bool.false_eq_true, ite_false,
        ite_true, Nat.add_zero] at ho
      apply Prod.ext <;> (have hx := Prod.ext_iff.mp ho; dsimp only at hx ⊢; omega)
    · simp [side, SortedMatch.tag, Nat.add_mod] at ha
    · simp [side, SortedMatch.tag, Nat.add_mod] at ha
  · rintro ⟨a, ha, b, hb, he, rfl⟩
    have ha' : SortedMatch.tag false a ∈ rows :=
      perm.mem_iff.mpr ((SortedMatch.mem_tagged input _).mpr (Or.inl ⟨a, ha, rfl⟩))
    have hb' : SortedMatch.tag true b ∈ rows :=
      perm.mem_iff.mpr ((SortedMatch.mem_tagged input _).mpr (Or.inr ⟨b, hb, rfl⟩))
    obtain ⟨group, hg, hga, hgb⟩ := same_group rows sorted _ _ ha' hb' he
    apply List.mem_flatMap.mpr
    refine ⟨group, hg, List.mem_flatMap.mpr ⟨SortedMatch.tag false a, ?_, ?_⟩⟩
    · simpa [side, SortedMatch.tag] using hga
    · apply List.mem_map.mpr
      refine ⟨SortedMatch.tag true b, ?_, ?_⟩
      · simpa [side, SortedMatch.tag, Nat.add_mod] using hgb
      · apply Prod.ext
        · simp [SortedMatch.tag]
        · change (2 * b.2 + 1) / 2 = b.2
          omega

private theorem side_polyTime (right : Bool) : ComputableTidilyInPolyTime (side right)
    (encList RadixPartition.recordEncoding) (encList RadixPartition.recordEncoding) := by
  apply ComputableTidilyInPolyTime.filter
  apply ComputableTidilyInPolyTime.decide_eq' (encB := encNat)
  · apply ComputableTidilyInPolyTime.binary_mod' <;>
      (dsimp only [RadixPartition.recordEncoding]; fun_prop)
  · exact .const _

/-- Actual encoded enumeration of all occurrence pairs. This generic consumer pays polynomial
cost in grouped volume and joined output; its certificate is not a sharp streaming join bound. -/
theorem join_polyTime : ComputableInPolyTime join KeyGrouping.outputEncoding
    (encList RadixPartition.recordEncoding) := by
  have body : ComputableTidilyInPolyTime
      (fun q : List SortedMatch.Record × SortedMatch.Record =>
        (side true q.1).map (fun b => (q.2.2 / 2, b.2 / 2)))
      (encPair (encList RadixPartition.recordEncoding) RadixPartition.recordEncoding)
      (encList RadixPartition.recordEncoding) := by
    apply ComputableTidilyInPolyTime.mapWithInput
      ((side_polyTime true).comp (ComputableTidilyInPolyTime.fst _ _))
    dsimp only [RadixPartition.recordEncoding]
    apply ComputableTidilyInPolyTime.prod <;>
      (apply ComputableTidilyInPolyTime.binary_div' <;> fun_prop)
  have pair_c : ComputableTidilyInPolyTime pairs
      (encList RadixPartition.recordEncoding) (encList RadixPartition.recordEncoding) :=
    (side_polyTime false).flatMapWithInput body
  exact .of_tidy (ComputableTidilyInPolyTime.flatMapWith
    (pair_c.comp (ComputableTidilyInPolyTime.snd encBool _)) (.const true) .id')

/-- Counting grouped occurrences is an actual encoded computation. Its current generic
consumer pays a polynomial in total grouped wire volume; this is not a near-linear bound. -/
theorem count_polyTime : ComputableInPolyTime count KeyGrouping.outputEncoding encNat := by
  have length_c (right : Bool) : ComputableTidilyInPolyTime
      (fun group => (side right group).length) (encList RadixPartition.recordEncoding) encNat :=
    ComputableTidilyInPolyTime.unary_to_binary.comp
      ((ComputableTidilyInPolyTime.length_list RadixPartition.recordEncoding).comp
        (side_polyTime right))
  have pop : ComputableTidilyInPolyTime population
      (encList RadixPartition.recordEncoding) encNat :=
    ComputableTidilyInPolyTime.binary_mul.comp ((length_c false).prod (length_c true))
  exact .of_tidy (ComputableTidilyInPolyTime.binary_sum.comp (pop.map))

private def payloads (right : Bool) (rows : List SortedMatch.Record) : List ℕ :=
  ((rows.map Prod.snd).filter (fun n => decide (n % 2 = if right then 1 else 0))).map (· / 2)

private theorem payloads_eq (right : Bool) (rows : List SortedMatch.Record) :
    payloads right rows = (side right rows).map (fun r => r.2 / 2) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    dsimp only [payloads, side] at ih ⊢
    cases h : decide (row.2 % 2 = if right then 1 else 0) <;> simp [h, ih]

private theorem payloads_nodup (right : Bool) (rows : List SortedMatch.Record)
    (h : (rows.map Prod.snd).Nodup) : (payloads right rows).Nodup := by
  apply List.Nodup.map_on _ (h.filter _)
  intro a ha b hb he
  have ha' := of_decide_eq_true (List.mem_filter.mp ha).2
  have hb' := of_decide_eq_true (List.mem_filter.mp hb).2
  omega

private theorem pairs_product (group : List SortedMatch.Record) :
    pairs group = (payloads false group) ×ˢ (payloads true group) := by
  simp only [payloads_eq, pairs, SProd.sprod, List.product, List.flatMap_map,
    List.map_map, Function.comp_def]

/-- Globally unique tagged payloads make occurrence pairs unique, even under arbitrary key
collisions. Grouping itself preserves duplicates when the input really has duplicates. -/
theorem join_nodup (groups : List (List SortedMatch.Record))
    (h : (groups.flatten.map Prod.snd).Nodup) : (join groups).Nodup := by
  have hall (right : Bool) : (groups.flatMap (payloads right)).Nodup := by
    have he : groups.flatMap (payloads right) = payloads right groups.flatten := by
      simp only [payloads, List.flatten_eq_flatMap, List.map_flatMap, List.filter_flatMap]
      rfl
    rw [he]
    exact payloads_nodup right _ h
  have hl := List.nodup_flatMap.mp (hall false)
  have hr := List.nodup_flatMap.mp (hall true)
  apply List.nodup_flatMap.mpr
  refine ⟨fun group hg => ?_, hl.2.imp (fun hd => ?_)⟩
  · rw [pairs_product]
    exact (hl.1 group hg).product (hr.1 group hg)
  · apply List.disjoint_left.mpr
    intro out ho ho'
    rw [pairs_product] at ho ho'
    exact List.disjoint_left.mp hd (List.mem_product.mp ho).1 (List.mem_product.mp ho').1

end Turing.MultiTapeTM.KeyJoin
