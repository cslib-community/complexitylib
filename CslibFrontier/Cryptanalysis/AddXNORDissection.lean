/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORClassEnumeration
import Mathlib.Tactic.Ring

/-!
# Streaming low-bit dissection

[WangLvShenZhang2027], Theorem 7, PDF p. 22. The program computes
both projected counter tables before visiting classes. At each class it collects
the smaller side, builds a full-state dictionary and folds the other side into
a witness lookup. It never collects both complete half spaces.

This module certifies functional execution, indexed witnesses and dictionary
sizes. It does not promote primitive-operation counts to native WordRAM time
or to compiled peak-space bounds. In particular the counter preprocessing and
streaming/dictionary compilation still need native resource certificates.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR

open Cslib.DataStructure ClassEnumeration

namespace Dissection

/-- The existing full-state dictionary format, with both quarter words joined. -/
@[expose] def pair {m : ℕ} (r : Record m) : BitVec m × List Bool :=
  (r.state, r.first ++ r.second)

/-- Collect just the forward class, in reverse emission order. -/
@[expose] def collectForward {m p : ℕ} (a b : List (BitVec m))
    (s : BitVec m) (g : BitVec p) : List (BitVec m × List Bool) :=
  foldClass (fun acc r => pair r :: acc) a b s g []

/-- Collect just the backward class, in reverse emission order. -/
@[expose] def collectBackward {m p : ℕ} (c d : List (BitVec m))
    (t : BitVec m) (g : BitVec p) : List (BitVec m × List Bool) :=
  foldBackClass (fun acc r => pair r :: acc) c d t g []

private theorem collectForward_eq {m p : ℕ} (a b : List (BitVec m))
    (s : BitVec m) (g : BitVec p) :
    collectForward a b s g = ((classRecords a b s g).map pair).reverse := by
  rw [collectForward, foldClass_eq, List.foldl_flip_cons_eq_append]
  simp

private theorem collectBackward_eq {m p : ℕ} (c d : List (BitVec m))
    (t : BitVec m) (g : BitVec p) :
    collectBackward c d t g = ((backClassRecords c d t g).map pair).reverse := by
  rw [collectBackward, foldBackClass_eq, List.foldl_flip_cons_eq_append]
  simp

/-- One streaming lookup; a hit replaces the earlier witness. A miss preserves
it, so no record list is retained by this consumer. -/
@[expose] def probe {m : ℕ} (trie : BinaryTrie (BitVec m × List Bool))
    (found : Option (List Bool × List Bool)) (r : BitVec m × List Bool) :
    Option (List Bool × List Bool) :=
  match trie.find (stateKey r.1) with
  | none => found
  | some l => some (l.2, r.2)

private theorem probeFold_ne_none {m : ℕ} (trie : BinaryTrie (BitVec m × List Bool))
    (rs : List (BitVec m × List Bool)) (initial : Option (List Bool × List Bool)) :
    rs.foldl (probe trie) initial ≠ none ↔
      initial ≠ none ∨ ∃ r ∈ rs, trie.find (stateKey r.1) ≠ none := by
  induction rs generalizing initial with
  | nil => simp
  | cons r rs ih =>
    rw [List.foldl_cons, ih]
    cases he : trie.find (stateKey r.1) <;> simp [probe, he, List.mem_cons]

private theorem probeFold_sound {m : ℕ} (trie : BinaryTrie (BitVec m × List Bool))
    (rs : List (BitVec m × List Bool)) (initial : Option (List Bool × List Bool))
    (xs ys : List Bool) (h : rs.foldl (probe trie) initial = some (xs, ys)) :
    initial = some (xs, ys) ∨ ∃ l r, r ∈ rs ∧
      trie.find (stateKey r.1) = some l ∧ l.2 = xs ∧ r.2 = ys := by
  induction rs generalizing initial with
  | nil => exact Or.inl h
  | cons r rs ih =>
    obtain hi | ⟨l, v, hv, hl, hx, hy⟩ := ih (probe trie initial r) h
    · cases he : trie.find (stateKey r.1) with
      | none => exact Or.inl (by simpa only [probe, he] using hi)
      | some l =>
        have hp : (l.2, r.2) = (xs, ys) := Option.some.inj (by simpa [probe, he] using hi)
        exact Or.inr ⟨l, r, List.mem_cons_self, he, congrArg Prod.fst hp, congrArg Prod.snd hp⟩
    · exact Or.inr ⟨l, v, List.mem_cons_of_mem r hv, hl, hx, hy⟩

/-- Join a stored class with a streamed class. The two branch orientations are
handled by the caller; the result orders stored operators before streamed ones.
The dictionary is bound outside the consumer, before the streaming fold starts. -/
@[expose] def scanForward {m p : ℕ} (stored : List (BitVec m × List Bool))
    (a b : List (BitVec m)) (s : BitVec m) (g : BitVec p) :
    Option (List Bool × List Bool) :=
  let trie := recordTrie stored
  foldClass (fun acc r => probe trie acc (pair r)) a b s g none

/-- Stream the backward class against a stored dictionary. -/
@[expose] def scanBackward {m p : ℕ} (stored : List (BitVec m × List Bool))
    (c d : List (BitVec m)) (t : BitVec m) (g : BitVec p) :
    Option (List Bool × List Bool) :=
  let trie := recordTrie stored
  foldBackClass (fun acc r => probe trie acc (pair r)) c d t g none

private theorem scanForward_eq {m p : ℕ} (stored : List (BitVec m × List Bool))
    (a b : List (BitVec m)) (s : BitVec m) (g : BitVec p) :
    scanForward stored a b s g =
      ((classRecords a b s g).map pair).foldl (probe (recordTrie stored)) none := by
  simp [scanForward, foldClass_eq, List.foldl_map]

private theorem scanBackward_eq {m p : ℕ} (stored : List (BitVec m × List Bool))
    (c d : List (BitVec m)) (t : BitVec m) (g : BitVec p) :
    scanBackward stored c d t g =
      ((backClassRecords c d t g).map pair).foldl (probe (recordTrie stored)) none := by
  simp [scanBackward, foldBackClass_eq, List.foldl_map]

/-- Search one class, collecting exactly one side. The Boolean is decided from
the counter tables by `search`; it is not a balance hypothesis. -/
@[expose] def searchClass {m p : ℕ} (forward : Bool) (a b c d : List (BitVec m))
    (s t : BitVec m) (g : BitVec p) : Option (List Bool × List Bool) :=
  if forward then scanBackward (collectForward a b s g) c d t g
  else (scanForward (collectBackward c d t g) a b s g).map Prod.swap

/-- The exact finite meeting condition for a single low-bit class. -/
@[expose] def Meets {m p : ℕ} (a b c d : List (BitVec m))
    (s t : BitVec m) (g : BitVec p) : Prop :=
  ∃ l ∈ classRecords a b s g, ∃ r ∈ backClassRecords c d t g, l.state = r.state

/-- Either orientation finds a hit exactly when the class contains a full-state
meeting. Searching a class is complete even if all keys or states coincide. -/
theorem searchClass_ne_none_iff {m p : ℕ} (forward : Bool) (a b c d : List (BitVec m))
    (s t : BitVec m) (g : BitVec p) :
    searchClass forward a b c d s t g ≠ none ↔ Meets a b c d s t g := by
  cases forward <;>
    simp only [searchClass, Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff,
      scanForward_eq, scanBackward_eq, probeFold_ne_none, ne_eq, not_true, false_or,
      recordTrie_find, collectForward_eq, collectBackward_eq, List.mem_reverse,
      List.mem_map, pair, Meets]
  all_goals constructor
  · rintro ⟨v, ⟨r, hr, rfl⟩, l, ⟨l, hl, rfl⟩, he⟩
    exact ⟨r, hr, l, hl, he.symm⟩
  · rintro ⟨l, hl, r, hr, he⟩
    exact ⟨pair l, ⟨l, hl, rfl⟩, pair r, ⟨r, hr, rfl⟩, he.symm⟩
  · rintro ⟨v, ⟨r, hr, rfl⟩, l, ⟨l, hl, rfl⟩, he⟩
    exact ⟨l, hl, r, hr, he⟩
  · rintro ⟨l, hl, r, hr, he⟩
    exact ⟨pair r, ⟨r, hr, rfl⟩, pair l, ⟨l, hl, rfl⟩, he⟩

/-- Enumerate low-bit keys without a choice-based `Finset.toList`. -/
@[expose] def classes (p : ℕ) : List (BitVec p) :=
  List.ofFn fun i : Fin (2 ^ p) => BitVec.ofFin i

private theorem mem_classes {p : ℕ} (g : BitVec p) : g ∈ classes p := by
  exact List.mem_ofFn.2 ⟨g.toFin, rfl⟩

/-- Counter preprocessing is performed once. Only the smaller full-width class
is collected at each key; the other is passed directly to dictionary lookups. -/
@[expose] def search {m : ℕ} (p : ℕ) (a b c d : List (BitVec m))
    (s t : BitVec m) : Option (List Bool × List Bool) :=
  let fc := WordTable.classCounters ((a ++ b).map (BitVec.setWidth p)) (s.setWidth p)
  let bc := WordTable.backwardCounters ((c ++ d).map (BitVec.setWidth p)) (t.setWidth p)
  (classes p).findSome? fun g =>
    searchClass (decide (fc.read g ≤ bc.read g)) a b c d s t g

/-- Searching every low-bit class finds exactly the union of its meeting events. -/
theorem search_ne_none_iff {m : ℕ} (p : ℕ) (a b c d : List (BitVec m)) (s t : BitVec m) :
    search p a b c d s t ≠ none ↔ ∃ g : BitVec p, Meets a b c d s t g := by
  simp only [search, ne_eq, List.findSome?_eq_none_iff, not_forall, searchClass_ne_none_iff,
    exists_prop]
  constructor
  · rintro ⟨g, _, hg⟩; exact ⟨g, hg⟩
  · rintro ⟨g, hg⟩; exact ⟨g, mem_classes g, hg⟩

private theorem forward_spec {m p : ℕ} (hp : p ≤ m) (a b : List (BitVec m))
    (s : BitVec m) (g : BitVec p) (r : Record m) (hr : r ∈ classRecords a b s g) :
    (pair r).2.length = (a ++ b).length ∧
      (pair r).1 = eval ((pair r).2.zip (a ++ b)) s ∧ (pair r).1.setWidth p = g := by
  obtain ⟨ha, hb, he, hg⟩ := (mem_classRecords hp a b s g r).1 hr
  refine ⟨by simp [pair, ha, hb], ?_, hg⟩
  simpa only [pair, List.zip_append ha, eval_append] using he

private theorem backward_spec {m p : ℕ} (hp : p ≤ m) (c d : List (BitVec m))
    (t : BitVec m) (g : BitVec p) (r : Record m) (hr : r ∈ backClassRecords c d t g) :
    (pair r).2.length = (c ++ d).length ∧
      (pair r).1 = backward ((pair r).2.zip (c ++ d)) t ∧ (pair r).1.setWidth p = g := by
  obtain ⟨hc, hd, he, hg⟩ := (mem_backClassRecords hp c d t g r).1 hr
  refine ⟨by simp [pair, hc, hd], ?_, hg⟩
  simpa only [pair, List.zip_append hc, backward_append] using he

private theorem forward_complete {m p : ℕ} (hp : p ≤ m) (a b : List (BitVec m))
    (s : BitVec m) (g : BitVec p) (bs : List Bool)
    (hlen : bs.length = (a ++ b).length)
    (hg : (eval (bs.zip (a ++ b)) s).setWidth p = g) :
    ∃ r ∈ classRecords a b s g, pair r = (eval (bs.zip (a ++ b)) s, bs) := by
  let xs := bs.take a.length
  let ys := bs.drop a.length
  have hx : xs.length = a.length := by simp [xs, hlen]
  have hy : ys.length = b.length := by simp [ys, hlen]
  have hcat : xs ++ ys = bs := List.take_append_drop _ _
  let r : Record m := ⟨xs, ys, eval (bs.zip (a ++ b)) s⟩
  refine ⟨r, (mem_classRecords hp a b s g r).2 ⟨hx, hy, ?_, hg⟩, ?_⟩
  · change eval (bs.zip (a ++ b)) s = _
    rw [← hcat, List.zip_append hx, eval_append]
  · simp only [pair, r, hcat]

private theorem backward_complete {m p : ℕ} (hp : p ≤ m) (c d : List (BitVec m))
    (t : BitVec m) (g : BitVec p) (bs : List Bool)
    (hlen : bs.length = (c ++ d).length)
    (hg : (backward (bs.zip (c ++ d)) t).setWidth p = g) :
    ∃ r ∈ backClassRecords c d t g, pair r = (backward (bs.zip (c ++ d)) t, bs) := by
  let xs := bs.take c.length
  let ys := bs.drop c.length
  have hx : xs.length = c.length := by simp [xs, hlen]
  have hy : ys.length = d.length := by simp [ys, hlen]
  have hcat : xs ++ ys = bs := List.take_append_drop _ _
  let r : Record m := ⟨xs, ys, backward (bs.zip (c ++ d)) t⟩
  refine ⟨r, (mem_backClassRecords hp c d t g r).2 ⟨hx, hy, ?_, hg⟩, ?_⟩
  · change backward (bs.zip (c ++ d)) t = _
    rw [← hcat, List.zip_append hx, backward_append]
  · simp only [pair, r, hcat]

/-- Every unrestricted solution belongs to a searched class, and every class
meeting is an unrestricted solution. No condition on class sizes is needed. -/
theorem exists_meets_iff {m p : ℕ} (hp : p ≤ m) (a b c d : List (BitVec m)) (s t : BitVec m) :
    (∃ g : BitVec p, Meets a b c d s t g) ↔ Solvable ((a ++ b) ++ (c ++ d)) s t := by
  constructor
  · rintro ⟨g, l, hl, r, hr, he⟩
    obtain ⟨hll, hls, _⟩ := forward_spec hp a b s g l hl
    obtain ⟨hrl, hrs, _⟩ := backward_spec hp c d t g r hr
    refine ⟨(pair l).2 ++ (pair r).2, by simp [hll, hrl, Nat.add_assoc], ?_⟩
    rw [List.zip_append hll, eval_append_eq_iff]
    exact hls.symm.trans (he.trans hrs)
  · rintro ⟨bs, hlen, he⟩
    let xs := bs.take (a ++ b).length
    let ys := bs.drop (a ++ b).length
    have hx : xs.length = (a ++ b).length := by simp [xs, hlen]
    have hy : ys.length = (c ++ d).length := by
      simp only [ys, List.length_drop, hlen, List.length_append]
      omega
    have hcat : xs ++ ys = bs := List.take_append_drop _ _
    have hmeet : eval (xs.zip (a ++ b)) s = backward (ys.zip (c ++ d)) t := by
      rw [← eval_append_eq_iff, ← List.zip_append hx, hcat]
      exact he
    let g := (eval (xs.zip (a ++ b)) s).setWidth p
    obtain ⟨l, hl, hpl⟩ := forward_complete hp a b s g xs hx rfl
    obtain ⟨r, hr, hpr⟩ := backward_complete hp c d t g ys hy (by rw [← hmeet])
    refine ⟨g, l, hl, r, hr, ?_⟩
    exact (congrArg Prod.fst hpl).trans (hmeet.trans (congrArg Prod.fst hpr).symm)

/-- Functional correctness of the actual counter-directed streaming search. -/
theorem search_correct {m p : ℕ} (hp : p ≤ m) (a b c d : List (BitVec m)) (s t : BitVec m) :
    search p a b c d s t ≠ none ↔ Solvable ((a ++ b) ++ (c ++ d)) s t := by
  rw [search_ne_none_iff, exists_meets_iff hp]

private theorem joined_sound {m : ℕ} (stored rs : List (BitVec m × List Bool))
    (xs ys : List Bool)
    (h : rs.foldl (probe (recordTrie stored)) none = some (xs, ys)) :
    ∃ l ∈ stored, ∃ r ∈ rs, l.1 = r.1 ∧ l.2 = xs ∧ r.2 = ys := by
  obtain hi | ⟨l, r, hr, hl, hx, hy⟩ := probeFold_sound (recordTrie stored) rs none xs ys h
  · cases hi
  · obtain ⟨hm, he⟩ := (recordTrie_find stored r.1).1 l hl
    exact ⟨l, hm, r, hr, he, hx, hy⟩

private theorem meet_witness {m p : ℕ} (hp : p ≤ m) (a b c d : List (BitVec m))
    (s t : BitVec m) (g : BitVec p) (l r : Record m)
    (hl : l ∈ classRecords a b s g) (hr : r ∈ backClassRecords c d t g)
    (he : l.state = r.state) :
    (pair l).2.length = (a ++ b).length ∧ (pair r).2.length = (c ++ d).length ∧
      eval (((pair l).2 ++ (pair r).2).zip ((a ++ b) ++ (c ++ d))) s = t := by
  obtain ⟨hll, hls, _⟩ := forward_spec hp a b s g l hl
  obtain ⟨hrl, hrs, _⟩ := backward_spec hp c d t g r hr
  refine ⟨hll, hrl, ?_⟩
  rw [List.zip_append hll, eval_append_eq_iff]
  exact hls.symm.trans (he.trans hrs)

/-- Both collection orientations return genuine ordered operator witnesses. -/
theorem searchClass_sound {m p : ℕ} (hp : p ≤ m) (forward : Bool)
    (a b c d : List (BitVec m)) (s t : BitVec m) (g : BitVec p)
    (xs ys : List Bool) (h : searchClass forward a b c d s t g = some (xs, ys)) :
    xs.length = (a ++ b).length ∧ ys.length = (c ++ d).length ∧
      eval ((xs ++ ys).zip ((a ++ b) ++ (c ++ d))) s = t := by
  cases forward with
  | true =>
    change scanBackward (collectForward a b s g) c d t g = _ at h
    rw [scanBackward_eq] at h
    obtain ⟨l, hl, r, hr, he, hx, hy⟩ := joined_sound _ _ xs ys h
    rw [collectForward_eq, List.mem_reverse] at hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    simpa only [hx, hy] using meet_witness hp a b c d s t g l' r' hl' hr' he
  | false =>
    change (scanForward (collectBackward c d t g) a b s g).map Prod.swap = _ at h
    obtain ⟨v, hv, hv'⟩ := Option.map_eq_some_iff.1 h
    have hp' : v = (ys, xs) := by
      have hswap := congrArg Prod.swap hv'
      simpa using hswap
    subst v
    rw [scanForward_eq] at hv
    obtain ⟨r, hr, l, hl, he, hy, hx⟩ := joined_sound _ _ ys xs hv
    rw [collectBackward_eq, List.mem_reverse] at hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    simpa only [hx, hy] using meet_witness hp a b c d s t g l' r' hl' hr' he.symm

/-- Witness recovery, not just a decision flag, for arbitrary full-width input. -/
theorem search_sound {m p : ℕ} (hp : p ≤ m) (a b c d : List (BitVec m))
    (s t : BitVec m) (xs ys : List Bool) (h : search p a b c d s t = some (xs, ys)) :
    xs.length = (a ++ b).length ∧ ys.length = (c ++ d).length ∧
      eval ((xs ++ ys).zip ((a ++ b) ++ (c ++ d))) s = t := by
  obtain ⟨g, _, hg⟩ := List.exists_of_findSome?_eq_some h
  exact searchClass_sound hp _ a b c d s t g xs ys hg

/-- The class retained by the actual branch, before dictionary construction. -/
@[expose] def storedClass {m p : ℕ} (forward : Bool) (a b c d : List (BitVec m))
    (s t : BitVec m) (g : BitVec p) : List (BitVec m × List Bool) :=
  if forward then collectForward a b s g else collectBackward c d t g

/-- Counter preprocessing selects the actual smaller class, not a desired or
assumed balance. The indexed counts include every repeated state. -/
theorem storedClass_length {m p a b c d : ℕ} (hp : p ≤ m)
    (as : Fin a → BitVec m) (bs : Fin b → BitVec m)
    (cs : Fin c → BitVec m) (ds : Fin d → BitVec m) (s t : BitVec m) (g : BitVec p) :
    let fc := WordTable.classCounters
      ((List.ofFn as ++ List.ofFn bs).map (BitVec.setWidth p)) (s.setWidth p)
    let bc := WordTable.backwardCounters
      ((List.ofFn cs ++ List.ofFn ds).map (BitVec.setWidth p)) (t.setWidth p)
    (storedClass (decide (fc.read g ≤ bc.read g))
      (List.ofFn as) (List.ofFn bs) (List.ofFn cs) (List.ofFn ds) s t g).length =
        min (forwardClassCount p (Fin.append as bs) s g)
          (backwardClassCount p (Fin.append cs ds) t g) := by
  have hf := WordTable.projected_classCounters hp (Fin.append as bs) s g
  have hb := WordTable.projected_backwardCounters hp (Fin.append cs ds) t g
  dsimp only
  rw [← List.ofFn_fin_append, List.map_ofFn, ← List.ofFn_fin_append, List.map_ofFn]
  simp only [Function.comp_def]
  simp only [hf, hb]
  simp only [storedClass]
  split
  · simp only [collectForward_eq, List.length_reverse, List.length_map,
      classRecords_length_eq_count hp]
    exact (min_eq_left (of_decide_eq_true ‹_›)).symm
  · simp only [collectBackward_eq, List.length_reverse, List.length_map,
      backClassRecords_length_eq_count hp]
    apply (min_eq_right _).symm
    have hn : ¬ forwardClassCount p (Fin.append as bs) s g ≤
        backwardClassCount p (Fin.append cs ds) t g :=
      fun h => ‹¬ decide _ = true› (decide_eq_true h)
    omega

/-- The actual smaller-class dictionary has at most `(m+1)μ_p` nodes.
This is a retained-data bound; compiled peak storage includes further obligations. -/
theorem storedClass_nodes_le_balance {m p a b c d : ℕ} (hp : p ≤ m)
    (as : Fin a → BitVec m) (bs : Fin b → BitVec m)
    (cs : Fin c → BitVec m) (ds : Fin d → BitVec m) (s t : BitVec m) (g : BitVec p) :
    let fc := WordTable.classCounters
      ((List.ofFn as ++ List.ofFn bs).map (BitVec.setWidth p)) (s.setWidth p)
    let bc := WordTable.backwardCounters
      ((List.ofFn cs ++ List.ofFn ds).map (BitVec.setWidth p)) (t.setWidth p)
    (recordTrie (storedClass (decide (fc.read g ≤ bc.read g))
      (List.ofFn as) (List.ofFn bs) (List.ofFn cs) (List.ofFn ds) s t g)).nodes ≤
        classBalance p (Fin.append as bs) (Fin.append cs ds) s t * (m + 1) := by
  dsimp only
  apply (recordTrie_nodes_le _).trans
  rw [storedClass_length hp]
  exact Nat.mul_le_mul_right _ (min_classCount_le_balance p _ _ s t g)

/-- Actual full-state lookup inspections in the streaming consumer. Every record
is queried once, including after an earlier hit, as `probe` specifies. -/
@[expose] def probeVisits {m : ℕ} (trie : BinaryTrie (BitVec m × List Bool)) :
    List (BitVec m × List Bool) → ℕ
  | [] => 0
  | r :: rs => trie.findVisits (stateKey r.1) + probeVisits trie rs

/-- Streaming lookup inspections are linear in the emitted records and width. -/
theorem probeVisits_le {m : ℕ} (trie : BinaryTrie (BitVec m × List Bool))
    (rs : List (BitVec m × List Bool)) : probeVisits trie rs ≤ rs.length * (m + 1) := by
  induction rs with
  | nil => simp [probeVisits]
  | cons r rs ih =>
    have hf := BinaryTrie.findVisits_le trie (stateKey r.1)
    simp only [stateKey, List.length_ofFn] at hf
    simp only [probeVisits, stateKey, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The sum of all quarter-enumerator chain calls is unconditional. The exact
formula displays the `2^(p+k)` setup term and both half-space output terms;
no per-class expectation or concentration assertion enters its proof. -/
theorem all_chainStepCalls {m p a b c d : ℕ} (hp : p ≤ m)
    (as : Fin a → BitVec m) (bs : Fin b → BitVec m)
    (cs : Fin c → BitVec m) (ds : Fin d → BitVec m) (s t : BitVec m) :
    (∑ g : BitVec p,
      (chainStepCalls (List.ofFn as) (List.ofFn bs) s g +
        backChainStepCalls (List.ofFn cs) (List.ofFn ds) t g)) =
      2 ^ p * (a * 2 ^ a + b * 2 ^ b + d * 2 ^ d + c * 2 ^ c) +
        b * 2 ^ (a + b) + c * 2 ^ (c + d) := by
  simp only [chainStepCalls_eq, backChainStepCalls_eq, List.length_ofFn,
    Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_classRecords_length hp, sum_backClassRecords_length hp]
  have hcard : Fintype.card (BitVec p) = 2 ^ p :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_id]
  ring

private theorem four_quarters {α : Type*} (as : List α) (k : ℕ) :
    ((as.take k ++ (as.drop k).take k) ++
      ((as.drop k |>.drop k).take k ++ (as.drop k |>.drop k |>.drop k))) = as := by
  simp only [List.append_assoc, List.take_append_drop]

/-- Apply the paper's consecutive quarter cut to one operand list. Projection
width is capped at the actual state width; no information is invented above it.
The last quarter keeps the complete remainder, including all three residue cases. -/
@[expose] def solve {m : ℕ} (p : ℕ) (as : List (BitVec m)) (s t : BitVec m) : Option (List Bool) :=
  let k := as.length / 4
  (search (min p m) (as.take k) ((as.drop k).take k)
    ((as.drop k |>.drop k).take k) (as.drop k |>.drop k |>.drop k) s t).map
      (fun (xs, ys) => xs ++ ys)

/-- Unrestricted correctness for the single-list quarter-cut interface. -/
theorem solve_correct {m : ℕ} (p : ℕ) (as : List (BitVec m)) (s t : BitVec m) :
    solve p as s t ≠ none ↔ Solvable as s t := by
  simp only [solve, ne_eq, Option.map_eq_none_iff]
  rw [← ne_eq, search_correct (Nat.min_le_right p m), four_quarters]

/-- The returned single operator word has the exact input length and solves
the actual modular Add/XNOR instance. -/
theorem solve_sound {m : ℕ} (p : ℕ) (as : List (BitVec m)) (s t : BitVec m)
    (bs : List Bool) (h : solve p as s t = some bs) :
    bs.length = as.length ∧ eval (bs.zip as) s = t := by
  obtain ⟨⟨xs, ys⟩, he, hcat⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hx, hy, hv⟩ := search_sound (Nat.min_le_right p m) _ _ _ _ s t xs ys he
  change xs ++ ys = bs at hcat
  subst bs
  rw [four_quarters] at hv
  refine ⟨?_, hv⟩
  rw [List.length_append, hx, hy, ← List.length_append, four_quarters]

end Dissection

end Cslib.Cryptanalysis.AddXNOR
