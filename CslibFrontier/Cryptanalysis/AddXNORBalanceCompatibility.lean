/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORSourceCounterBalance
public import CslibFrontier.Cryptanalysis.AddXNORClassBalance
import all CslibFrontier.Cryptanalysis.AddXNORClassBalance
import all CslibFrontier.Cryptanalysis.AddXNORClassEnumeration
import all CslibFrontier.Cryptanalysis.AddXNORClasses
import all CslibFrontier.Cryptanalysis.AddXNORSourceCounterBalance
import Mathlib.Data.List.OfFn

/-!
# Agreement of generated-class counts with the counter DP

Compare the actual generated class records with the original indexed operator
words, preserving multiplicity through their injective packed witness payloads.
This identifies the search envelope's balance with the new DP scalar; no table
or class-population correctness conclusion is assumed.

## Main results

* `count_eq_projected_counters`: both generated-class populations equal their DP entries.
* `original_balance`: the original-input DP prepass equals the search's computed balance.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.BalanceCompatibility
open Turing.MultiTapeTM

private theorem forward_sum {m p : ℕ} (hp : p ≤ m) (as : List (BitVec m))
    (s : BitVec m) (g : BitVec p) :
    ((operatorWords as.length).map (fun ops =>
      if (eval (ops.zip as) s).setWidth p = g then 1 else 0)).sum =
      (WordTable.classCounters (as.map (BitVec.setWidth p)) (s.setWidth p)).read g := by
  have h := WordTable.projected_classCounters hp (fun i : Fin as.length => as[i.val]) s g
  simp only [List.ofFn_getElem_eq_map] at h
  rw [h, forwardClassCount, WordTable.sum_operatorWords]
  simp only [← WordTable.steps_zip, List.ofFn_getElem]

private theorem count_sum {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (right : Bool) (g : BitVec p) :
    let first := if right then ds.reverse else as
    let second := if right then cs.reverse else bs
    let seed := if right then ~~~t else s
    ClassBalance.count (ProgramGeneration.originalSource p as bs cs ds s t) right g.toNat =
      ((operatorWords (first++second).length).map (fun ops =>
        if (eval (ops.zip (first++second)) seed).setWidth p =
          (if right then ~~~g else g) then 1 else 0)).sum := by
  let first := if right then ds.reverse else as
  let second := if right then cs.reverse else bs
  let seed := if right then ~~~t else s
  let state := fun ops : List Bool =>
    if right then ~~~(eval (ops.zip (first++second)) seed) else eval (ops.zip (first++second)) seed
  let rows := ((operatorWords (first++second).length).filter
    (fun ops => decide ((state ops).setWidth p = g))).map
      (fun ops => ((state ops).toNat, Native.Quarter.encode ops))
  have unique : rows.Nodup := by
    apply List.Nodup.map_on ?_ ((ClassEnumeration.operatorWords_nodup _).filter _)
    intro x hx y hy hxy
    have hx' := (mem_operatorWords x _).mp (List.mem_filter.mp hx).1
    have hy' := (mem_operatorWords y _).mp (List.mem_filter.mp hy).1
    have he := congrArg (fun r : ℕ × ℕ => Native.Quarter.decode (first++second).length r.2) hxy
    have dx : Native.Quarter.decode (first++second).length (Native.Quarter.encode x) = x := by
      simpa only [hx'] using Native.Quarter.decode_encode x
    have dy : Native.Quarter.decode (first++second).length (Native.Quarter.encode y) = y := by
      simpa only [hy'] using Native.Quarter.decode_encode y
    simpa only [dx, dy] using he
  have perm : (ClassBalance.records
      (ProgramGeneration.originalSource p as bs cs ds s t) right g.toNat).Perm rows := by
    apply (List.perm_ext_iff_of_nodup
      (ClassBalance.records_nodup hp as bs cs ds s t right g) unique).mpr
    intro r
    have original := ClassBalance.original_records hp as bs cs ds s t right g r
    dsimp only at original
    rw [original]
    simp only [rows, List.mem_map, List.mem_filter, mem_operatorWords, decide_eq_true_eq,
      List.length_append]
    constructor
    · rintro ⟨ops, hlen, he, hg⟩
      exact ⟨ops, ⟨hlen, hg⟩, he.symm⟩
    · rintro ⟨ops, ⟨hlen, hg⟩, he⟩
      exact ⟨ops, hlen, he.symm, hg⟩
  rw [← ClassBalance.records_length, perm.length_eq]
  simp only [rows, List.length_map, ClassEnumeration.filter_length_eq_sum, decide_eq_true_eq,
    ← ClassBalance.class_reflection hp, state]
  rfl

/-- Generated full-state classes and DP counters compute identical indexed populations.
Backward execution is related through the proved inverse/reversal conjugacy, not a forward
retention dictionary used with different semantics. -/
theorem count_eq_projected_counters {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (right : Bool) (g : BitVec p) :
    ClassBalance.count (ProgramGeneration.originalSource p as bs cs ds s t) right g.toNat =
      if right then (WordTable.backwardCounters ((cs++ds).map (BitVec.setWidth p))
        (t.setWidth p)).read g
      else (WordTable.classCounters ((as++bs).map (BitVec.setWidth p)) (s.setWidth p)).read g := by
  rw [count_sum hp]
  cases right
  · exact forward_sum hp (as++bs) s g
  · simp only [ite_true]
    rw [forward_sum hp]
    simpa only [List.reverse_append, ← List.map_reverse, BitVec.setWidth_not hp] using
      WordTable.backwardCounters_conjugate ((cs++ds).map (BitVec.setWidth p)) (t.setWidth p) g

/-- Exact original-input agreement of the fast scalar prepass and the search-space envelope. -/
theorem original_balance {m : ℕ} (p : ℕ) (s : BitVec m) (tail : List (BitVec m)) :
    SourceCounterBalance.run (Source.ofWords p s tail) =
      ClassBalance.balance (Source.prepare (Source.ofWords p s tail)) := by
  rw [SourceCounterBalance.run_words, Source.prepare_ofWords]
  let d := min p (min m (tail.length/4))
  have dm : d ≤ m := (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  let parts := Source.quarters tail
  let source := ProgramGeneration.originalSource d parts.1.1 parts.1.2 parts.2.1 parts.2.2 s 0
  have entry (g : BitVec d) (right : Bool) := count_eq_projected_counters dm
    parts.1.1 parts.1.2 parts.2.1 parts.2.2 s 0 right g
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro g _
    have h := ClassBalance.class_le_balance source g.toNat g.isLt
    rw [ClassBalance.retained_length] at h
    dsimp only [source] at h
    rw [entry g false, entry g true] at h
    exact h
  · rw [ClassBalance.balance, ClassBalance.table_eq]
    apply listMax_le
    intro pair hp
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
    let key := BitVec.ofNat d g
    have keyval : key.toNat = g := Nat.mod_eq_of_lt (List.mem_range.mp hg)
    have left := entry key false
    have right := entry key true
    rw [keyval] at left right
    rw [left, right]
    exact Finset.le_sup (f := fun g : BitVec d =>
      min ((WordTable.classCounters
        ((SourceCounterCounts.forwardOperands tail).map (BitVec.setWidth d)) (s.setWidth d)).read g)
      ((WordTable.backwardCounters ((SourceCounterCounts.backwardOperands tail).map
        (BitVec.setWidth d)) ((0 : BitVec m).setWidth d)).read g)) (Finset.mem_univ key)

end Cslib.Cryptanalysis.AddXNOR.BalanceCompatibility
