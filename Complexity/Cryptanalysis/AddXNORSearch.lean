/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORChain
public import Complexity.DataStructure.BinaryTrie
import Mathlib.Data.List.Defs

/-!
# Executable exact Add/XNOR search

[WangLvShenZhang2027], Proposition 5 (PDF p. 21). The two lists below
contain actual forward and inverse states and their operator witnesses. A binary
trie joins them using the low-to-high bits of the full state, rather than comparing
every pair. Duplicate states retain one witness, which suffices for search.

The resource statements count generated records, calls to chain steps, and
trie nodes inspected or stored. These are concrete operations of this implementation,
not a multitape Turing-machine time certificate. In particular, the pure `BitVec`
operations and list administration are not assigned a desired running time.
The source's bit-operation time and working-space bounds require a separate
implementation/compilation bridge.

## Main definitions

* `operatorWords`, `forwardRecords`, `backwardRecords`: exhaustive witness records.
* `meetSearch`: exact trie-based forward/backward search at any cut.

## Main results

* `meetSearch_sound`, `meetSearch_ne_none_iff`: returned witnesses and completeness.
* `meetSearch_operation_bounds`, `meetSearch_trie_resources`: concrete operation/data-size bounds.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR

open Cslib.DataStructure

/-- Enumerate every operator word exactly once, in lexicographic order. -/
@[expose] def operatorWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (operatorWords n).map (false :: ·) ++ (operatorWords n).map (true :: ·)

theorem operatorWords_length (n : ℕ) : (operatorWords n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [operatorWords, ih, pow_succ, Nat.mul_two]

theorem mem_operatorWords (bs : List Bool) (n : ℕ) :
    bs ∈ operatorWords n ↔ bs.length = n := by
  induction n generalizing bs with
  | zero => simp [operatorWords]
  | succ n ih =>
    cases bs with
    | nil => simp [operatorWords]
    | cons b bs => cases b <;> simp [operatorWords, ih]



/-- The exact, fixed-width key used by the trie. -/
@[expose] def stateKey {m : ℕ} (s : BitVec m) : List Bool :=
  List.ofFn fun i : Fin m => s.getLsbD i

theorem stateKey_injective (m : ℕ) : Function.Injective (stateKey (m := m)) := by
  intro s t h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have he := congrArg (fun l : List Bool => l[i]?) h
  simpa [stateKey, hi] using he

/-- Forward records at a fixed cut. Each contains its complete operator witness. -/
@[expose] def forwardRecords {m : ℕ} (as : List (BitVec m)) (s : BitVec m) :
    List (BitVec m × List Bool) :=
  (operatorWords as.length).map fun bs => (eval (bs.zip as) s, bs)

/-- Backward records at a fixed cut, with operators in their original order. -/
@[expose] def backwardRecords {m : ℕ} (as : List (BitVec m)) (t : BitVec m) :
    List (BitVec m × List Bool) :=
  (operatorWords as.length).map fun bs => (backward (bs.zip as) t, bs)

/-- Build the forward-state dictionary, retaining one complete record per state. -/
@[expose] def recordTrie {m : ℕ} : List (BitVec m × List Bool) →
    BinaryTrie (BitVec m × List Bool)
  | [] => .empty
  | r :: rs => (recordTrie rs).insert (stateKey r.1) r

/-- Dictionary hits are actual input records at exactly the requested state. -/
theorem recordTrie_find {m : ℕ} (rs : List (BitVec m × List Bool)) (s : BitVec m) :
    (∀ r, (recordTrie rs).find (stateKey s) = some r → r ∈ rs ∧ r.1 = s) ∧
      ((recordTrie rs).find (stateKey s) ≠ none ↔ ∃ r ∈ rs, r.1 = s) := by
  induction rs with
  | nil => simp [recordTrie, BinaryTrie.find]
  | cons r rs ih =>
    simp only [recordTrie, BinaryTrie.find_insert]
    by_cases h : stateKey s = stateKey r.1
    · have hs := stateKey_injective m h
      subst s
      simp
    · have hs : s ≠ r.1 := fun he => h (congrArg stateKey he)
      simp only [h, ↓reduceIte, List.mem_cons]
      constructor
      · intro v hv
        obtain ⟨hm, he⟩ := ih.1 v hv
        exact ⟨Or.inr hm, he⟩
      · rw [ih.2]
        constructor
        · rintro ⟨v, hv, he⟩; exact ⟨v, Or.inr hv, he⟩
        · rintro ⟨v, hv | hv, he⟩
          · subst v; exact (hs he.symm).elim
          · exact ⟨v, hv, he⟩

/-- Retained dictionary size is linear in the number of full-width records. -/
theorem recordTrie_nodes_le {m : ℕ} (rs : List (BitVec m × List Bool)) :
    (recordTrie rs).nodes ≤ rs.length * (m + 1) := by
  induction rs with
  | nil => simp [recordTrie, BinaryTrie.nodes]
  | cons r rs ih =>
    have h := BinaryTrie.nodes_insert_le (stateKey r.1) r (recordTrie rs)
    simp only [stateKey, List.length_ofFn] at h
    simp only [recordTrie, List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    change (BinaryTrie.insert (stateKey r.1) r (recordTrie rs)).nodes ≤ _
    simpa only [Nat.add_assoc, stateKey] using h.trans (by omega)

/-- Total insertion-node inspections while building this actual record trie. -/
@[expose] def recordTrieVisits {m : ℕ} : List (BitVec m × List Bool) → ℕ
  | [] => 0
  | r :: rs => BinaryTrie.insertVisits (stateKey r.1) (recordTrie rs) + recordTrieVisits rs

/-- The dictionary builder performs exactly `m+1` insertion inspections per record. -/
theorem recordTrieVisits_eq {m : ℕ} (rs : List (BitVec m × List Bool)) :
    recordTrieVisits rs = rs.length * (m + 1) := by
  induction rs with
  | nil => simp [recordTrieVisits]
  | cons r rs ih => simp [recordTrieVisits, BinaryTrie.insertVisits_eq, stateKey, ih,
      Nat.add_mul, Nat.add_comm]

/-- Count the calls to `step` during the recursive `eval` evaluator. This counts
word operations only: it does not pretend that word addition has unit bit cost. -/
@[expose] def evalStepCalls {m : ℕ} : List (Bool × BitVec m) → ℕ
  | [] => 0
  | _ :: xs => 1 + evalStepCalls xs

/-- Forward and inverse evaluators each make precisely one word operation per entry. -/
theorem evalStepCalls_eq_length {m : ℕ} (xs : List (Bool × BitVec m)) :
    evalStepCalls xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [evalStepCalls, ih, Nat.add_comm]

/-- Calls to the word-step primitive in the complete enumeration, counting
full evaluation separately for every operator witness as implemented above. -/
@[expose] def enumerationStepCalls {m : ℕ} (as : List (BitVec m)) : ℕ :=
  ((operatorWords as.length).map fun bs => evalStepCalls (bs.zip as)).sum

/-- Exact complete-enumeration operation count, including repeated states. -/
theorem enumerationStepCalls_eq {m : ℕ} (as : List (BitVec m)) :
    enumerationStepCalls as = as.length * 2 ^ as.length := by
  unfold enumerationStepCalls
  have h (bs : List Bool) (hb : bs ∈ operatorWords as.length) :
      evalStepCalls (bs.zip as) = as.length := by
    rw [evalStepCalls_eq_length, List.length_zip, (mem_operatorWords _ _).1 hb, min_self]
  rw [List.map_congr_left h]
  simp [operatorWords_length, Nat.mul_comm]

/-- Scan the backward list and stop at the first dictionary match. -/
@[expose] def joinRecords {m : ℕ} (trie : BinaryTrie (BitVec m × List Bool)) :
    List (BitVec m × List Bool) → Option (List Bool × List Bool)
  | [] => none
  | r :: rs => match trie.find (stateKey r.1) with
    | none => joinRecords trie rs
    | some l => some (l.2, r.2)

/-- A returned pair comes from a genuine dictionary lookup and suffix record. -/
theorem joinRecords_sound {m : ℕ} (trie : BinaryTrie (BitVec m × List Bool))
    (rs : List (BitVec m × List Bool)) (xs ys : List Bool)
    (h : joinRecords trie rs = some (xs, ys)) :
    ∃ l r, r ∈ rs ∧ trie.find (stateKey r.1) = some l ∧ l.2 = xs ∧ r.2 = ys := by
  induction rs with
  | nil => simp [joinRecords] at h
  | cons r rs ih =>
    simp only [joinRecords] at h
    cases he : trie.find (stateKey r.1) with
    | none =>
      rw [he] at h
      obtain ⟨l, v, hv, hl, hx, hy⟩ := ih h
      exact ⟨l, v, List.mem_cons_of_mem _ hv, hl, hx, hy⟩
    | some l =>
      rw [he] at h
      have hp := Option.some.inj h
      exact ⟨l, r, List.mem_cons_self, he, congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- The scan succeeds exactly when some suffix record has a dictionary hit. -/
theorem joinRecords_ne_none {m : ℕ} (trie : BinaryTrie (BitVec m × List Bool))
    (rs : List (BitVec m × List Bool)) :
    joinRecords trie rs ≠ none ↔ ∃ r ∈ rs, trie.find (stateKey r.1) ≠ none := by
  induction rs with
  | nil => simp [joinRecords]
  | cons r rs ih =>
    cases he : trie.find (stateKey r.1) <;> simp [joinRecords, he, ih]

/-- Actual dictionary-lookup inspections of the short-circuiting scan. -/
@[expose] def joinVisits {m : ℕ} (trie : BinaryTrie (BitVec m × List Bool)) :
    List (BitVec m × List Bool) → ℕ
  | [] => 0
  | r :: rs => trie.findVisits (stateKey r.1) +
      if trie.find (stateKey r.1) = none then joinVisits trie rs else 0

/-- Even an unsuccessful scan inspects at most `m+1` trie nodes per record. -/
theorem joinVisits_le {m : ℕ} (trie : BinaryTrie (BitVec m × List Bool))
    (rs : List (BitVec m × List Bool)) :
    joinVisits trie rs ≤ rs.length * (m + 1) := by
  induction rs with
  | nil => simp [joinVisits]
  | cons r rs ih =>
    have hv := BinaryTrie.findVisits_le trie (stateKey r.1)
    simp only [stateKey, List.length_ofFn] at hv
    simp only [joinVisits, List.length_cons, Nat.add_mul, Nat.one_mul]
    split <;> simp only [stateKey] at * <;> omega

/-- Exact search at a chosen cut; `left ++ right` is the operand list. -/
@[expose] def meetSearch {m : ℕ} (left right : List (BitVec m)) (s t : BitVec m) :
    Option (List Bool × List Bool) :=
  joinRecords (recordTrie (forwardRecords left s)) (backwardRecords right t)

/-- The two enumerations have exactly their advertised exponential sizes. -/
theorem record_lengths {m : ℕ} (left right : List (BitVec m)) (s t : BitVec m) :
    (forwardRecords left s).length = 2 ^ left.length ∧
      (backwardRecords right t).length = 2 ^ right.length := by
  simp [forwardRecords, backwardRecords, operatorWords_length]

/-- Any returned operator witness has the required lengths and reaches the target. -/
theorem meetSearch_sound {m : ℕ} (left right : List (BitVec m))
    (s t : BitVec m) (xs ys : List Bool) (h : meetSearch left right s t = some (xs, ys)) :
    xs.length = left.length ∧ ys.length = right.length ∧
      eval ((xs ++ ys).zip (left ++ right)) s = t := by
  obtain ⟨l, r, hr, hl, hx, hy⟩ := joinRecords_sound _ _ xs ys h
  obtain ⟨hlmem, hstate⟩ := (recordTrie_find (forwardRecords left s) r.1).1 l hl
  obtain ⟨bs, hbs, hb⟩ := List.mem_map.1 hlmem
  obtain ⟨cs, hcs, hc⟩ := List.mem_map.1 hr
  have hbLen := (mem_operatorWords bs left.length).1 hbs
  have hcLen := (mem_operatorWords cs right.length).1 hcs
  change (eval (bs.zip left) s, bs) = l at hb
  change (backward (cs.zip right) t, cs) = r at hc
  subst l; subst r
  dsimp only at hx hy hstate
  subst xs; subst ys
  refine ⟨hbLen, hcLen, ?_⟩
  rw [List.zip_append hbLen, eval_append_eq_iff]
  exact hstate

/-- The algorithm finds a witness for every solution, including empty sides of the cut. -/
theorem meetSearch_complete {m : ℕ} (left right : List (BitVec m)) (s t : BitVec m)
    (h : Solvable (left ++ right) s t) : meetSearch left right s t ≠ none := by
  obtain ⟨bs, hlen, heval⟩ := h
  let xs := bs.take left.length
  let ys := bs.drop left.length
  have hx : xs.length = left.length := by simp [xs, hlen]
  have hy : ys.length = right.length := by simp [ys, hlen]
  have hcat : xs ++ ys = bs := List.take_append_drop _ _
  have hmeet : eval (xs.zip left) s = backward (ys.zip right) t := by
    rw [← eval_append_eq_iff, ← List.zip_append hx, hcat]
    exact heval
  apply (joinRecords_ne_none _ _).2
  refine ⟨(backward (ys.zip right) t, ys), ?_, ?_⟩
  · exact List.mem_map.2 ⟨ys, (mem_operatorWords _ _).2 hy, rfl⟩
  · apply (recordTrie_find _ _).2.2
    exact ⟨(eval (xs.zip left) s, xs),
      List.mem_map.2 ⟨xs, (mem_operatorWords _ _).2 hx, rfl⟩, hmeet⟩

/-- Soundness and completeness for arbitrary full-width inputs and every cut. -/
theorem meetSearch_ne_none_iff {m : ℕ} (left right : List (BitVec m)) (s t : BitVec m) :
    meetSearch left right s t ≠ none ↔ Solvable (left ++ right) s t := by
  constructor
  · intro h
    cases he : meetSearch left right s t with
    | none => exact (h he).elim
    | some p =>
      obtain ⟨hx, hy, hv⟩ := meetSearch_sound left right s t p.1 p.2 he
      exact ⟨p.1 ++ p.2, by simp [hx, hy], hv⟩
  · exact meetSearch_complete left right s t

/-- Explicit trie storage and lookup bounds, without a collision/balance assumption. -/
theorem meetSearch_trie_resources {m : ℕ} (left right : List (BitVec m)) (s t : BitVec m) :
    (recordTrie (forwardRecords left s)).nodes ≤ 2 ^ left.length * (m + 1) ∧
      joinVisits (recordTrie (forwardRecords left s)) (backwardRecords right t) ≤
        2 ^ right.length * (m + 1) := by
  constructor
  · simpa [forwardRecords, operatorWords_length] using recordTrie_nodes_le (forwardRecords left s)
  · simpa [backwardRecords, operatorWords_length] using
      joinVisits_le (recordTrie (forwardRecords left s)) (backwardRecords right t)

/-- With both cut lengths at most h, actual word-step calls, dictionary
insertions and suffix lookups are bounded by a polynomial times `2^h`.
This deliberately states the three resources independently of machine runtime. -/
theorem meetSearch_operation_bounds {m : ℕ} (left right : List (BitVec m))
    (s t : BitVec m) (h : ℕ) (hl : left.length ≤ h) (hr : right.length ≤ h) :
    enumerationStepCalls left + enumerationStepCalls right ≤
        (left.length + right.length) * 2 ^ h ∧
      recordTrieVisits (forwardRecords left s) ≤ (m + 1) * 2 ^ h ∧
      joinVisits (recordTrie (forwardRecords left s)) (backwardRecords right t) ≤
        (m + 1) * 2 ^ h := by
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hl
  have hq := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hr
  constructor
  · rw [enumerationStepCalls_eq, enumerationStepCalls_eq, Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ hp) (Nat.mul_le_mul_left _ hq)
  · constructor
    · rw [recordTrieVisits_eq, (record_lengths left right s t).1, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ hp
    · exact (meetSearch_trie_resources left right s t).2.trans
        (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (m + 1) hq)

/-- The standard ceiling-half cut meets both length hypotheses above. -/
theorem half_cut_lengths {α : Type*} (as : List α) :
    (as.take ((as.length + 1) / 2)).length ≤ (as.length + 1) / 2 ∧
      (as.drop ((as.length + 1) / 2)).length ≤ (as.length + 1) / 2 := by
  simp only [List.length_take, List.length_drop]
  omega

end Cslib.Cryptanalysis.AddXNOR
