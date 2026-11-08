/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
public import Mathlib.Data.List.Sublists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.List.Dedup

/-!
# Certified bounded list enumeration and deduplication

Fixed-length sublist enumeration is implemented by scans of original suffixes,
with an outer induction on the fixed length. Equality with `List.sublistsLen`
preserves the existing ordering. Deduplication scans original suffixes for the
last occurrence. Both certificates charge traversal, equality tests and writing.
-/

public section

namespace Cslib

open Turing.MultiTapeTM

private theorem sublistsLen_indexed {α : Type} (fallback : α) (k : ℕ) (l : List α) :
    l.sublistsLen (k + 1) = ((List.range l.length).reverse.flatMap fun i =>
      ((l.drop (i + 1)).sublistsLen k).map fun t => l.getD i fallback :: t) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.sublistsLen_succ_cons, ih]
    simp only [List.length_cons, List.range_succ_eq_map, List.reverse_cons, ← List.map_reverse,
      List.flatMap_append, List.flatMap_map, List.flatMap_cons, List.flatMap_nil,
      List.drop_succ_cons, List.getD_cons_succ, List.getD_cons_zero, List.drop_zero,
      List.append_nil]


/-- Every fixed sublist length has a uniform framed-list polynomial-time/space machine.
The length is fixed in the theorem, not supplied in the input. -/
theorem sublistsLen_polytime {α : Type} (enc : α ↪ List Bool) (fallback : α) (k : ℕ) :
    ComputableInPolyTime (List.sublistsLen k : List α → List (List α))
      (encList enc) (encList (encList enc)) := by
  induction k with
  | zero =>
    have h : ComputableInPolyTime (fun _ : List α => ([[]] : List (List α)))
        (encList enc) (encList (encList enc)) := ComputableInPolyTime.const _
    exact h.of_enc_eq fun l => congrArg _ (List.sublistsLen_zero l)
  | succ k ih =>
    have h : ComputableInPolyTime (fun l : List α =>
        (List.range l.length).reverse.flatMap fun i =>
          ((l.drop (i + 1)).sublistsLen k).map fun t => l.getD i fallback :: t)
        (encList enc) (encList (encList enc)) := by
      apply ComputableInPolyTime.flatMapWithInput (by fun_prop)
      have hd : ComputableInPolyTime (fun p : List α × ℕ => p.1.drop (p.2 + 1))
          (encPair (encList enc) encUnary) (encList enc) :=
          ComputableInPolyTime.of_tidy (by fun_prop)
      exact ComputableInPolyTime.mapWithInput (ih.comp hd) (by fun_prop)
    exact h.of_enc_eq fun l => congrArg _ (sublistsLen_indexed fallback k l)

private theorem dedup_indexed {α : Type} [DecidableEq α] (fallback : α) (l : List α) :
    l.dedup = ((List.range l.length).filter fun i =>
      decide (l.getD i fallback ∉ l.drop (i + 1))).map fun i => l.getD i fallback := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.dedup_cons, ih]
    simp only [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map,
      Function.comp_def,
      List.getD_cons_succ, List.drop_succ_cons, List.getD_cons_zero, List.drop_zero]
    split_ifs <;> simp_all

/-- Global list deduplication uses certified suffix scans and encoded equality tests. -/
theorem dedup_polytime {α : Type} [DecidableEq α] (enc : α ↪ List Bool) (fallback : α) :
    ComputableInPolyTime (List.dedup : List α → List α) (encList enc) (encList enc) := by
  have h : ComputableInPolyTime (fun l : List α =>
      ((List.range l.length).filter fun i => decide (l.getD i fallback ∉ l.drop (i + 1))).map
        fun i => l.getD i fallback) (encList enc) (encList enc) := by
    have hd : ComputableInPolyTime (fun p : List α × ℕ => p.1.drop (p.2 + 1))
        (encPair (encList enc) encUnary) (encList enc) :=
          ComputableInPolyTime.of_tidy (by fun_prop)
    have hg : ComputableInPolyTime (fun p : List α × ℕ => p.1.getD p.2 fallback)
        (encPair (encList enc) encUnary) enc := by fun_prop
    have ht := ComputableInPolyTime.decide_not (ComputableInPolyTime.decide_mem hd hg)
    exact ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.filterWithInput (by fun_prop) ht) hg
  exact h.of_enc_eq fun l => congrArg _ (dedup_indexed fallback l)

end Cslib
